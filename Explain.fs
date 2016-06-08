module Explain

open GlobalOptions
open Util
open Literal
open Clause
open BitVector
open Trail
open State
open BooleanValuation
open RLEBVTheory
open BoundsTheory
open TheoryRelation
open Learning
open PropagationRules
open Z3Check
open TheoryRelation
open System.Collections.Generic

let explainEmptyDomain (s:State) (bvVar:Var) =
    let trail = (!s.trail)
    let mutable expl = []
    let mutable trailPtr = trail.getTrailPtr

    for i in 0 .. trailPtr do
        let t = trail.get i
        match t with
        | Some (BoolDecision l )
        | Some (Imp (_, l)) when (!s.theoryDB).isDefined (lit2var l) ->
            let tRel = (!s.theoryDB).getThRelation (lit2var l)
            if (List.exists (fun x -> x = bvVar) tRel.variableArguments) then
                expl <- (Negate l)::expl
        | _ -> ()
    newClauseFromList expl

// Chooses literals in the conflict which have a valueT
// Some literals might be part of the conflict purely from a boolean perspective
// AZ: Checking s.bVal.valueT is cheaper, but I am not relying that it is set consistently.
let getSupportedTLiterals (s:State) (cnflct: Literal array) =
    let tDB = s.theoryDB

    [| for lit in cnflct do
        let var = lit2var lit
        if ((!tDB).isDefined var) then
            let tRel = (!tDB).getThRelation var
            if tHolds tRel s.bvVal s.numeralDB <> Undefined ||
               tbndsHolds tRel s.bounds s.numeralDB <> Undefined then
                yield tRel |]

let rewritePositiveEqualities (s:State) (sbox:State)  (cnflct: Literal []) =
    let mutable rwCnflct = []
    let mutable origLits = []
    let mutable rwttnEQs = []

    for l in cnflct do
        let var = lit2var l
        let isPos = isPositive l

        if (!sbox.theoryDB).isDefined var then
            let t = (!sbox.theoryDB).getThRelation var

            if t.isPAPredicate && isPos &&
                ( tHolds t s.bvVal s.numeralDB <> Undefined ||
                  tbndsHolds t s.bounds s.numeralDB <> Undefined) then
                let var = t.getPAPredicateVariable
                let num = t.getPAPredicateValue sbox.numeralDB

                if num.isConcreteValue then
                    let lower = getLowerBoundPredicate sbox.database var num sbox.bVal sbox.bvVal sbox.bounds
                    if not (Array.exists (fun (x:Literal) -> x = lower.getBoolVar) cnflct) then
                        rwCnflct <- rwCnflct @ [lower.getBoolVar]

                    let upper = getUpperBoundPredicate sbox.database var num sbox.bVal sbox.bvVal sbox.bounds
                    if not (Array.exists (fun  (x:Literal) -> x = upper.getBoolVar) cnflct) then
                        rwCnflct <- rwCnflct @ [upper.getBoolVar]

                    rwttnEQs <- (var2lit lower.getBoolVar, var2lit upper.getBoolVar, var2lit t.getBoolVar) :: rwttnEQs
            else
                origLits <- l :: origLits
        else
            origLits <- l :: origLits

    (List.toArray origLits, List.toArray rwCnflct, rwttnEQs)


let assertLiterals (sbox:State) (conflict:Literal []) =
    assert ((!sbox.trail).getCount = 0)
    assert (not sbox.IsConflicted)

    let trail = sbox.trail

    // Assert the conflicting literals while filtering
    // for the relaxed literal
    for l in conflict do
        match (!sbox.bVal).getValueB l with
        | True -> () //Already implied by the trail, can be omitted to avoid assertion violations
        | _ -> sbox.Push (BoolDecision l)




    while not sbox.IsConflicted && (!trail).hasPropagationsPending do
        PropagateTheories sbox (!trail).nextPropagation



let cleanTrailTo (sbox:State) (restorePoint: int)=
    while (!sbox.trail).getCount > restorePoint do
        sbox.Pop
    sbox.clearConflict()

let cleanTrail sbox =
    cleanTrailTo sbox 0

let propagateTrailContents (sbox:State) =
    while not sbox.IsConflicted && (!sbox.trail).hasPropagationsPending do
        PropagateTheories sbox (!sbox.trail).nextPropagation


let checkGeneralizationUsingZ3 (sbox:State) (generalizedConflict: Literal []) =
    let mutable explArray = Array.map Negate generalizedConflict
    let clauseToCheck = newClauseFromArray (explArray)
    checkIsGeneralizedExplanationValid sbox.database clauseToCheck true


let isLiteralGeneralizationValid (sbox:State) (l:Literal) =
    assert (not sbox.IsConflicted)
    let restorePoint = (!sbox.trail).getCount

    let bValue = (!sbox.bVal).getValueB l
    let isValid =   match bValue with                    
                    | Undefined ->  sbox.Push (BoolDecision l)
                                    propagateTrailContents sbox
                                    sbox.IsConflicted
                    | _ -> assert(false)
                           false

    cleanTrailTo sbox restorePoint
    isValid


//let isGeneralizationValid (sbox:State) (conflict:Literal []) =
//    assert ((!sbox.trail).getCount = 0)
//    assert (not sbox.IsConflicted)
//
//    let trail = sbox.trail
//
//    // Assert the conflicting literals while filtering
//    // for the relaxed literal
//    for l in conflict do
//        sbox.Push (BoolDecision (l,None))
//
//    // Propagate everything on the trail.
//    while not sbox.IsConflicted && (!trail).hasPropagationsPending do
//        PropagateTheories sbox (!trail).nextPropagation
//
//    // If a conflict is observed then the generalization is VALID
//    let isGenValid = sbox.IsConflicted
//
//    // Clean the sanbox trail
//    while (!sbox.trail).getCount > 0 do
//        sbox.Pop
//    sbox.clearConflict()
//
//    // Sanity check using z3
//    let mutable explArray = Array.map Negate conflict
//    let clauseToCheck = newClauseFromArray (explArray)
//    let z3Says = checkIsGeneralizedExplanationValid sbox.database clauseToCheck true
//    assert(not isGenValid || z3Says) // AZ: Since some operations are not fully implemented we do not have equavalence here.
//    isGenValid

let stepwiseRelaxTRel (sbox:State) (conflict : Literal []) (updateFn) (t:TheoryRelation) =
    assert (t.isBoundsPredicate)

    let origNum =   if t.isPAPredicate then  t.getPAPredicateValue sbox.numeralDB
                    else
                        let interval = t.getBoundsPredicateValue sbox.numeralDB
                        if t.isLowerBoundPredicate then interval.Lower
                        elif t.isUpperBoundPredicate then interval.Upper
                        else UNREACHABLE "Non-existant bounds case"


    let mutable tRel = t
    if DBG then printfn  "------------------------------------------------------"
    if DBG then printfn "Attempting to relax: %s" (t.ToString sbox.numeralDB)

    let fixedLiterals = [| for l in conflict do
                                if lit2var l <> t.getBoolVar then
                                    yield l
                          |]
    assert (Array.exists (fun x -> lit2var x = t.getBoolVar) conflict)
    let isPos =  Array.exists (fun x -> x = t.getBoolVar) conflict

    assertLiterals sbox fixedLiterals

    let mutable num = origNum
    let mutable position = num.Length - 1
    let mutable step = 1
    let mutable generalization_suceeded = false


    let bvVar = if tRel.isPAPredicate then tRel.getPAPredicateVariable
                else tRel.getBoundsPredicateVariable
        
    while position >= 0 do
        let newNum =  updateFn num position step


       
        position <- position - step - 1
        step <- 2 * step
        if step > position + 1 then
            step <- position + 1
        if not ( BitVector.bvEQ newNum num) then
            let newT = mkRelaxedTRel sbox.database t newNum sbox.bVal sbox.bvVal sbox.bounds
            (!sbox.database).addToOccurenceLists newT
            if DBG then
                printfn  "------------------------------------------------------"
                printfn "Proposed relaxation: %s" (newT.ToString (sbox.numeralDB))
            let lit = if isPos then newT.getBoolVar else Negate newT.getBoolVar

            //let z3Says = checkGeneralizationUsingZ3 sbox (Array.append (Array.map Negate fixedLiterals) [|Negate lit|])
            //RUNZ3CHECKS <- false
            if isLiteralGeneralizationValid sbox lit then
                //assert (z3Says) // Z3 has to agree with us that it is valid
                generalization_suceeded <- true
                num <- newNum
                tRel <- newT
                if DBG then printfn "Relaxation successful! Replacing %s by %s" (t.ToString sbox.numeralDB) (newT.ToString sbox.numeralDB)

                //Update on success
                position <- position - step - 1
                step <- 2 * step
                if step > position + 1 then
                    step <- position + 1

            else
                //assert(not z3Says)
                if DBG then printfn "Relaxation failed, retaining %s" (t.ToString sbox.numeralDB)
                //Update on failure to generalize
                if step = 1 then
                    position <- position - 1
                else
                    step <- max 1 (step / 2)

            //  RUNZ3CHECKS <- true

            let idx = (!sbox.theoryDB).bool2ThRel.[newT.getBoolVar]
            (!sbox.watchManager).removeReference bvVar idx
    cleanTrail sbox
    if generalization_suceeded && not (BitVector.bvEQ num origNum) then
        Some tRel
    else
        None


let relaxTRel (sbox:State) (conflict : Literal []) (updateFn) (t:TheoryRelation) =
    assert (t.isBoundsPredicate)
    let origNum =   if t.isPAPredicate then  t.getPAPredicateValue sbox.numeralDB
                    else
                        let interval = t.getBoundsPredicateValue sbox.numeralDB
                        if t.isLowerBoundPredicate then interval.Lower
                        elif t.isUpperBoundPredicate then interval.Upper
                        else UNREACHABLE "Non-existant bounds case"

    let mutable num = origNum
    let mutable tRel = t
    if DBG then printfn  "------------------------------------------------------"
    if DBG then printfn "Attempting to relax: %s" (t.ToString sbox.numeralDB)

    let fixedLiterals = [| for l in conflict do
                                if lit2var l <> t.getBoolVar then
                                    yield l
                          |]
    assert (Array.exists (fun x -> lit2var x = t.getBoolVar) conflict)
    let isPos =  Array.exists (fun x -> x = t.getBoolVar) conflict

    assertLiterals sbox fixedLiterals

    for i in 0 .. num.Length - 1 do
        let newNumO = updateFn num (num.Length - 1 - i)
        match newNumO with
        | None -> ()
        | Some newNum ->
            let newT = mkRelaxedTRel sbox.database t newNum sbox.bVal sbox.bvVal sbox.bounds
//            printfn  "------------------------------------------------------"
//            printfn "Proposed relaxation: %s" (newT.ToString (sbox.numeralDB))
            let lit = if isPos then newT.getBoolVar else Negate newT.getBoolVar

            let z3Says = checkGeneralizationUsingZ3 sbox (Array.append fixedLiterals [|lit|])
            if isLiteralGeneralizationValid sbox lit then
                assert (z3Says) // Z3 has to agree with us that it is valid
                num <- newNum
                tRel <- newT
                if DBG then printfn "Relaxation successful! Replacing %s by %s" (t.ToString sbox.numeralDB) (newT.ToString sbox.numeralDB)
            else
                if DBG then printfn "Relaxation failed, retaining %s" (t.ToString sbox.numeralDB)

    cleanTrail sbox
    if not (BitVector.bvEQ num origNum) then
        Some tRel
    else
        None


let relaxPAPredicate (sbox:State) (conflict : Literal []) (t:TheoryRelation) =
    stepwiseRelaxTRel sbox conflict (BitVector.changeBits false Bit.U) t

let relaxLowerBound (sbox:State) (conflict : Literal []) (t:TheoryRelation) =
    stepwiseRelaxTRel sbox conflict (BitVector.changeBits true Bit.Zero) t

let relaxUpperBound  (sbox:State) (conflict : Literal []) (t:TheoryRelation) =
    stepwiseRelaxTRel sbox conflict (BitVector.changeBits true Bit.One) t

let tryToRelax (sbox:State) (cnflct: Literal []) (t: TheoryRelation) =
    assert (Array.exists (fun x -> lit2var x = t.getBoolVar) cnflct )
    let isPos =  Array.exists (fun x -> x = t.getBoolVar) cnflct

    if not t.isBoundsPredicate then
        None
    elif t.isPAPredicate then
        relaxPAPredicate sbox  cnflct t
    elif (t.isLowerBoundPredicate && isPos) ||
            (t.isUpperBoundPredicate && not isPos) then
        relaxLowerBound sbox  cnflct t
    elif (t.isLowerBoundPredicate && not isPos) ||
            (t.isUpperBoundPredicate && isPos) then
        relaxUpperBound sbox  cnflct t
    else
        UNREACHABLE "Conflict generalization: uncovered case"
        None

// For each literal in the conflict, omit it and check if the
// conflict persists. If it does, remove that literal permanently.
let minimize (sbox:State) (rwCnflct: Literal []) =
    let mutable rest = Array.toList rwCnflct
    let mutable kept = []
    let mutable current = rest.Head
    rest <- rest.Tail
    let mutable literals = List.toArray (kept@rest)

    while rest <> [] do
        literals <- List.toArray (kept@rest)
        assertLiterals sbox literals

        if not sbox.IsConflicted then
           kept <- current :: kept

        cleanTrail sbox
        current <- rest.Head
        rest <- rest.Tail

    literals <- List.toArray (kept@rest)
    assertLiterals sbox literals
    if not sbox.IsConflicted then
        kept <- current :: kept
    cleanTrail sbox
    List.toArray kept


//    // Conflict minimization
//    let keep = Array.create rwCnflct.Length true
//    for l in 0 .. rwCnflct.Length - 1 do
//        keep.[l] <- false
//        let cnflictWithoutC = [| for i in 0 .. keep.Length - 1 do
//                                    if keep.[i] then
//                                        yield rwCnflct.[i]|]
//        if not (isGeneralizationValid sbox cnflictWithoutC) then
//            keep.[l] <- true
//            //printfn "|Minimization -> Keeping %d" rwCnflct.[l]
//        else
//            //printfn "|Minimization -> Removing %d" rwCnflct.[l]
//            ()
//    let minimized =
//        [|  for i in 0 .. keep.Length - 1 do
//            if keep.[i] then
//                yield rwCnflct.[i]|]
//    if DBG then printfn "\nConflict after minimization:"
//    if DBG then sbox.printCube (ref (newClauseFromArray minimized))
//    minimized

// New variables are introduced in TEMP mode if their identifier is
// greater than the snapshot taken when entering TEMP mode.
let isNew (s:State) (l:Literal) =
    (!s.variableDB).getSnapshot <= lit2var l

// Generalize conflict by repeatedly:
// 1) relaxing a literal
// 2) checking if the conflict persist

let generalize (s:State) (sbox:State) (genCnflct:Literal []) =
   // Conflict generalization
    let current = [|for l in genCnflct do yield l|]
    for i in  0 .. current.Length - 1 do
        let lit = current.[i]
        if (!sbox.theoryDB).isDefined lit then
            let t =  (!sbox.theoryDB).getThRelation (lit2var lit)
            if  tHolds t s.bvVal s.numeralDB <> Undefined ||
                tbndsHolds t s.bounds s.numeralDB <> Undefined then
                let newLit = tryToRelax sbox current t                
                if newLit.IsSome then
                    genCnflct.[i] <-  if isPositive (current.[i]) then
                                            (newLit.Value).getBoolVar
                                      else
                                            Negate (newLit.Value).getBoolVar
    if DBG then printfn  "Explanation after generalization: "
    let genExpl = newClauseFromArray genCnflct
    if DBG then s.printClause (ref genExpl)

// Splits the generalized conflict into generalized and original literals
// Also computes the highest conflict level among the old literals
let splitLiterals (s:State) (sbox:State) (genCnflct:Literal[]) =
    let mutable genLits = []
    let mutable rwLits = []
    let mutable oldLits = []
    let mutable phantomLvl = 0
    for i in 0 .. genCnflct.Length - 1 do
        let l = genCnflct.[i]
        let v = lit2var l
        if (isNew sbox genCnflct.[i]) && ((!s.theoryDB).isDefined v) then
            let t = (!sbox.theoryDB).getThRelation v
            if t.isSimpleRelation then
                let isPos = isPositive l
                genLits <- (   if t.isLowerBoundPredicate then
                                    (LowerBound, isPos, t.getBoundsPredicateVariable,(t.getBoundsPredicateValue sbox.numeralDB).Lower)
                               elif t.isUpperBoundPredicate then
                                    (UpperBound, isPos, t.getBoundsPredicateVariable, (t.getBoundsPredicateValue sbox.numeralDB).Upper)
                               elif t.isPAPredicate then
                                    (PAPredicate, isPos, t.getPAPredicateVariable, BitVector.Copy (t.getPAPredicateValue sbox.numeralDB))
                               else
                                    UNREACHABLE "Generalized literals have to involve least one numeral"
                                    (NotSimple, false, 0, BitVector.Invalid)
                           ) :: genLits
            else
                oldLits <- genCnflct.[i] :: oldLits
        elif (!s.bVal).getValueB l = Undefined then
            rwLits <- l :: rwLits
        else
            oldLits <- genCnflct.[i] :: oldLits
            phantomLvl <- max phantomLvl ( (!s.bVal).getBLvl l)

    (genLits,oldLits, rwLits, phantomLvl)

// Reintroduces permanently the generalized literals
let translateGeneralizedLiterals (s:State) (genLits: (SimpleRelationType*bool*Var*BitVector) list) =
    let mutable translatedGenLits : Literal list = []
    for (case, isPos, var, value) in genLits do
        let t = match case with
                    | LowerBound -> getBoundPredicate s.database var value true s.bVal s.bvVal s.bounds
                    | UpperBound -> getBoundPredicate s.database var value false s.bVal s.bvVal s.bounds
                    | PAPredicate -> getModelAssignmentPredicate s.database var value s.bVal s.bvVal s.bounds
                    | _ -> UNREACHABLE "Generalized an unknown predicate type"

        if DBG then printfn "Making a permanent copy of %s" (t.ToString())
        translatedGenLits <- (if isPos then  t.getBoolVar else Negate t.getBoolVar) :: translatedGenLits
    translatedGenLits

let timeWalkTheState (s:State) (bLits: Literal list) (rwLits: Literal list) (genLits:Literal list) (backjumpLvl:int) (noGen:bool) (noMin : bool) (mCubeSubsetBaseCube: bool) =
    assert (backjumpLvl >= 0)
    // Explanation to be:
    //  (/\ oldLits) -> tseitinVar
    // and tseitinVar = (\/ newlits)

    let uncertainLiterals = List.map Negate (genLits @ rwLits)
    let baseLits = List.map Negate bLits

    if noGen && noMin  then
        if DBG then printfn "Leaving original conflict"
        () // No generalization, proceed with boolean conflict resolution
    elif noGen &&  mCubeSubsetBaseCube then
            // Conflict is minimized, and all literals are on the trail,
            // replace the existing conflict with a smaller one
            if DBG then printfn "Minimized conflict"
            s.SetConflict (Some (ref (newClauseFromList (baseLits @ uncertainLiterals))))
    elif uncertainLiterals.Length = 0 then
            () // Everything has a value and rewriting made the conflict bigger but didn't yield anything to generalize from.
    else
        let originalCC = s.GetConflictClause
        s.clearConflict()
        if DBG then printfn "Generalized conflict clause"
        // GenLits have no value on the trail, while rwLits might have a value on the trail
        assert (uncertainLiterals.Length > 0) // Otherwise, no generalization and no minimization took place and we shouldn't be here

        if DBG then s.printClause (ref (newClauseFromList (baseLits @ uncertainLiterals)))


        let (impliedLit, newCC) =
             let lit = if uncertainLiterals.Length > 1 then                            
                            s.defineTseitinVariable uncertainLiterals
                       else
                            uncertainLiterals.Head
             let extendedResolutionExpl = newClauseFromList  (lit ::  baseLits)
             (lit, extendedResolutionExpl)

        // Time-walking a conflict: (old1 \/ old2 \/ ...\/ oldk \/ impliedLit
        // If impliedLit is undefined, that is because it is newly introduced:
        // impL = genL1 \/ genL2 \/ ... \/ genLn
        // TODO: What about rwLits?
        // First we want to backtrack the trail to the highest decision level
        // involving some oldi and there propagate generalized literals
        // using correct explanations, as if they were discovered on time.

        match (!s.bVal).getValueB impliedLit with
        | Undefined ->
            // Backtracking the trail to highest decision lvl involving some oldi
            if DBG then printfn "Poping the trail to lvl %d" backjumpLvl
            assert (backjumpLvl > -1)
            while (!s.trail).getNumDecisions > backjumpLvl do
                s.Pop

            // Get implications of generalized literals
            let twImps = [|for l in uncertainLiterals do
                            assert ((!s.theoryDB).isDefined (lit2var l))
                            let t = (!s.theoryDB).getThRelation (lit2var l)
                            let rleHlds = tHolds t s.bvVal s.numeralDB
                            let bndsHlds = tbndsHolds t s.bounds s.numeralDB
                            if  rleHlds <> Undefined then
                                yield (tGetImplication s (ref t) rleHlds)
                            elif bndsHlds <> Undefined then
                                yield (tbndsGetImplication s (ref t) bndsHlds)
                         |]

            // Propagate found implications
            for (imp, l) in twImps do
                if lit2var l <> lit2var impliedLit then //AZ: impliedLit is not defined on the trail and will be implied by the remainder of this function
                    if DBG then
                        printf "Implication: "
                        s.printClause (ref imp)
                    if (!s.bVal).getValueB l = Undefined then
                        (s.Push (Imp (ref imp, l)))
                    else
                        assert ((!s.bVal).getValueB l = True)

            // Learn the new generalized cc with a Tseitin variable
            //if DBG then printfn "Learning implication %s" (clauseToString newCC)
            if (!s.clauseDB).isRegisteredTseitin (lit2var impliedLit) then
                //Backjump-Decide
                assert (uncertainLiterals.Length > 0)
                
                s.Push (Imp (ref newCC, impliedLit))
                
                //Deciding on a literal
                let mutable decided = false
                let mutable lits = uncertainLiterals

                while not decided && lits <> [] do
                    let l = lits.Head
                    lits <- lits.Tail

                    if (!s.bVal).getValueB l = Undefined then
                        s.Push (BoolDecision l)
                        decided <- true
                    else
                        assert ((!s.bVal).getValueB l = False)

                if not decided then
                    let c = (Negate impliedLit :: uncertainLiterals)
                    List.map (fun x -> assert ((!s.bVal).getValueB x = False)) c |> ignore
                    s.SetConflict (Some (ref ( newClauseFromList c )))
                
            else
                s.Push (Imp (ref newCC, impliedLit))
                                
                if DBG && (!s.theoryDB).isDefined (lit2var impliedLit) then
                    let tLit = (!s.theoryDB).getThRelation (lit2var impliedLit)
                    let theory_value = tHolds tLit s.bvVal s.numeralDB
                    let bounds_value = tbndsHolds tLit s.bounds s.numeralDB

                    match (isPositive impliedLit, theory_value, bounds_value) with
                    | (true, False, _)
                    | (false, True, _)
                    | (true, _, False)
                    | (false, _, True) -> 
                        printfn "CONFLICT UNDETECTED!"
                        printfn "Generalization propagated literal %d : %s " impliedLit (tLit.ToString())
                        printfn "Value on trail %s" ((isPositive impliedLit).ToString())
                        printfn "rle_eval says %s" (theory_value.ToString())
                        printfn "bounds_eval says %s" (bounds_value.ToString())
                        assert(s.IsConflicted)
                    | _ -> ()
        | False 
        | True ->            
            //AZ: Then it must be a theory detected conflict  
          
            assert ((!s.theoryDB).isDefined (lit2var impliedLit))
            let tLit = (!s.theoryDB).getThRelation (lit2var impliedLit)
            let theory_value = tHolds tLit s.bvVal s.numeralDB
            let bounds_value = tbndsHolds tLit s.bounds s.numeralDB

            match (isPositive impliedLit, theory_value, bounds_value) with
            | (true, False, _)
            | (false, True, _)
            | (true, _, False)
            | (false, _, True) ->    
                s.SetConflict (Some (ref (newCC)))                
                () //AZ: This is ok, we expect a conflict and it is a conflict in the theory.
            | _ -> 
                //AZ: We expect a conflict but we don't see one, and  this is a problem.
                s.SetConflict (Some originalCC)  
           

            
            



let getCnflctTrigger (s:State) =
    match (!s.trail).trail.[(!s.trail).getCount - 1] with
    | MAssgnmnt (v, _, _)
    | BAssgnmnt (v, _, _) -> Some v
    | _ -> None

let xTExplanationGeneralization (s:State) (sbox:State) =
    assert (s.IsConflicted)

    if DBG then printfn "------------------------------"
    if DBG then printfn "|           SANDBOX          |"
    if DBG then printfn "------------------------------"
    if DBG then printfn "****Conflict generalization****"

    let cc = !s.GetConflictClause
    let baseConflictCube = [|for i in 1 .. getSize cc do yield  Negate cc.[i] |]

    //if DBG then (!s.trail).forcePrint ("Trail:\n", s.bvVal, s.bounds)
    if DBG then printfn " Base conflict clause: "
    if DBG then s.printClause s.GetConflictClause

    sbox.enterTempMode s    

    let tLitsInvolved = [|for l in baseConflictCube do
                            if (!s.theoryDB).isDefined  (lit2var l) then
                                yield (!s.theoryDB).getThRelation (lit2var l)
                        |]
    
    // Setup watches
    for tLit in tLitsInvolved do         
        (!sbox.database).addToOccurenceLists tLit

    //let evalTLits = Array.filter (fun x -> tHolds x s.bvVal s.numeralDB <> Undefined) tLitsInvolved

    let isArithmeticInvolved = Array.exists TheoryRelation.isArithmetic tLitsInvolved

    let (bLits, newLits, rewrittenEQs) =
        if isArithmeticInvolved then
            verbose <| (lazy "Arithmetic conflict")
            rewritePositiveEqualities s sbox baseConflictCube
        else
            (baseConflictCube, [||],[])

    for b in bLits do
        assert (Array.exists (fun x ->  x = b) baseConflictCube)
    for n in newLits do
        assert (not (Array.exists (fun x ->  x = n) baseConflictCube))
        assert (not (Array.exists (fun x ->  x = n) bLits))

    // TODO: Rewrite conflict minimization in spirit of generalization
    let toMinimize = (Array.append bLits newLits)
    let minCube = minimize sbox toMinimize

    let mutable mCubeSubsetBaseCube = true //Array.fold (fun s t -> s && Array.exists (fun x -> x = t) baseConflictCube) true minCube
    for m in minCube do
        let mutable found = false
        for b in baseConflictCube do
            if m = b then
                found <- true
        mCubeSubsetBaseCube <- mCubeSubsetBaseCube && found

    let genCube = [|for m in minCube do yield m|]
    generalize s sbox genCube

    let gCubeSubsetMCube = Array.fold (fun s t -> s && Array.exists (fun x -> x = t) minCube) true genCube
    let noMinimization = minCube.Length >= toMinimize.Length && mCubeSubsetBaseCube

    for (l,u,e) in rewrittenEQs do
        let lInd = Array.tryFindIndex (fun x -> x = l) genCube
        let uInd = Array.tryFindIndex (fun x -> x = u) genCube
        if lInd.IsSome && uInd.IsSome then
            genCube.[lInd.Value] <- e
            genCube.[uInd.Value] <- e

    let mutable noDupCube = []
    for l in genCube do
        if not (List.exists (fun x -> x = l) noDupCube) then
            noDupCube <- l :: noDupCube

    let newGenCube = List.toArray noDupCube

    if DBG then
        printfn "Explanation after compacting"
        s.printClause (ref (newClauseFromArray newGenCube))
    let (annotatedGenLits, baseLits, rwLits, twLvl) = splitLiterals s sbox newGenCube
    sbox.leaveTempMode()
    if DBG then printfn "------------------------------"
    if DBG then printfn "|      Leaving SANDBOX       |"
    if DBG then printfn "------------------------------"


    let translatedGenLits = translateGeneralizedLiterals s annotatedGenLits



    


    timeWalkTheState s baseLits rwLits translatedGenLits twLvl gCubeSubsetMCube noMinimization mCubeSubsetBaseCube
