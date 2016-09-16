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

let rewritePositiveEqualities (s:State) (sbox:State) (cube:Literal []) =
    let is_rw_target = (fun l ->
        if (!sbox.theoryDB).isDefined (lit2var l) then
            let t = (!sbox.theoryDB).getThRelation (lit2var l)
            (t.isPAPredicate && (isPositive l) &&
             (tHolds t s.bvVal s.numeralDB <> Undefined ||
              tbndsHolds t s.bounds s.numeralDB <> Undefined) &&
             (t.getPAPredicateValue sbox.numeralDB).isConcreteValue)
        else
            false
    )
    let f = (fun (origLits, newLits, rwttnEQs) l ->
        if is_rw_target l then
            let t = (!sbox.theoryDB).getThRelation (lit2var l)
            let var = t.getPAPredicateVariable
            let num = t.getPAPredicateValue sbox.numeralDB

            let lb = getLowerBoundPredicate sbox.database var num sbox.bVal sbox.bvVal sbox.bounds
            let lbbv = lb.getBoolVar
            let lbv = if not (Array.exists (fun x -> (lit2var x) = lbbv) cube) then [lbbv] else []
            let lbl = var2lit lbbv

            let ub = getUpperBoundPredicate sbox.database var num sbox.bVal sbox.bvVal sbox.bounds
            let ubbv = ub.getBoolVar
            let ubv = if not (Array.exists (fun x -> (lit2var x) = ubbv) cube) then [ubbv] else []
            let ubl = var2lit ubbv

            let tv = var2lit t.getBoolVar
            (origLits, lbv @ ubv @ newLits, (lbl, ubl, tv) :: rwttnEQs)
        else
            (l :: origLits, newLits, rwttnEQs)
    )
    let (o, n, r) = Array.fold f ([], [], []) cube
    for l in o do
        assert (Array.contains l cube)
    for l in n do
        assert (not (Array.contains l cube))
        assert (not (List.contains l o))
    (List.toArray (o @ n), r)

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

let stepwiseRelaxTRel (sbox:State) (conflict:Literal[]) (updateFn) (t:TheoryRelation) (isPos:bool) =
    assert (t.isBoundsPredicate)

    let origNum = if t.isPAPredicate then
                    t.getPAPredicateValue sbox.numeralDB
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
                               yield l |]
    assert (Array.exists (fun x -> lit2var x = t.getBoolVar) conflict)

    assertLiterals sbox fixedLiterals

    let mutable num = origNum
    let mutable position = num.Length - 1
    let mutable step = 1
    let mutable generalization_suceeded = false

    let bvVar = if tRel.isPAPredicate then tRel.getPAPredicateVariable
                else tRel.getBoundsPredicateVariable

    while position >= 0 do
        let newNum = updateFn num position step
        position <- position - step - 1
        step <- 2 * step
        if step > position + 1 then
            step <- position + 1
        if not (BitVector.bvEQ newNum num) then
            let newT = mkRelaxedTRel sbox.database t newNum sbox.bVal sbox.bvVal sbox.bounds
            (!sbox.database).addToOccurenceLists newT
            if DBG then
                printfn "------------------------------------------------------"
                printfn "Proposed relaxation: %s" (newT.ToString (sbox.numeralDB))
            let lit = if isPos then newT.getBoolVar else Negate newT.getBoolVar

            //let z3Says = checkGeneralizationUsingZ3 sbox (Array.append (Array.map Negate fixedLiterals) [|Negate lit|])
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

            let ptr = (!sbox.theoryDB).bool2ThRel.[newT.getBoolVar]
            (!sbox.watchManager).removeReference bvVar ptr
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

let relaxPAPredicate (sbox:State) (conflict:Literal[]) (t:TheoryRelation) (isPos:bool) =
    stepwiseRelaxTRel sbox conflict (BitVector.changeBits false Bit.U) t isPos

let relaxLowerBound (sbox:State) (conflict:Literal[]) (t:TheoryRelation) (isPos:bool) =
    stepwiseRelaxTRel sbox conflict (BitVector.changeBits true Bit.Zero) t isPos

let relaxUpperBound  (sbox:State) (conflict:Literal[]) (t:TheoryRelation) (isPos:bool) =
    stepwiseRelaxTRel sbox conflict (BitVector.changeBits true Bit.One) t isPos

let tryToRelax (sbox:State) (cnflct:Literal[]) (t:TheoryRelation) (isPos:bool) =
    if not t.isBoundsPredicate then
        None
    elif t.isPAPredicate then
        relaxPAPredicate sbox cnflct t isPos
    elif (t.isLowerBoundPredicate && isPos) ||
         (t.isUpperBoundPredicate && not isPos) then
        relaxLowerBound sbox  cnflct t isPos
    elif (t.isLowerBoundPredicate && not isPos) ||
         (t.isUpperBoundPredicate && isPos) then
        relaxUpperBound sbox  cnflct t isPos
    else
        UNREACHABLE "Conflict generalization: uncovered case"
        None

// For each literal in the conflict, omit it and check if the
// conflict persists. If it does, remove that literal permanently.
let minimize (sbox:State) (cube:Literal[]) =
    let f = (fun s x ->
        let otherLits = (Array.filter (fun y -> y <> x) s)
        assertLiterals sbox otherLits
        let is_conflicted = sbox.IsConflicted
        cleanTrail sbox
        if is_conflicted then
            if DBG then printfn "Dropping %d from conflict cube." x
            otherLits
        else
            s)
    Array.fold f cube cube

// New variables are introduced in TEMP mode if their identifier is
// greater than the snapshot taken when entering TEMP mode.
let isNew (s:State) (l:Literal) =
    (!s.variableDB).getSnapshot <= lit2var l

// Generalize conflict by repeatedly:
// 1) relaxing a literal
// 2) checking if the conflict persists

let generalize (s:State) (sbox:State) (cube:Literal[]) =
    let f = (fun lit ->
        let isPos = isPositive lit
        if (!sbox.theoryDB).isDefined lit then
            let t = (!sbox.theoryDB).getThRelation (lit2var lit)
            if  (tHolds t s.bvVal s.numeralDB) <> Undefined ||
                (tbndsHolds t s.bounds s.numeralDB) <> Undefined then
                let newLit = tryToRelax sbox cube t isPos
                if newLit.IsSome then
                    let nv = (newLit.Value).getBoolVar
                    if isPos then nv else Negate nv
                else
                    lit
            else
                lit
        else
            lit
    )
    let res = Array.map f cube
    if DBG then printfn "Explanation after generalization: ";
                s.printCube (ref (newClauseFromArray cube))
    res

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
        translatedGenLits <- (if isPos then t.getBoolVar else Negate t.getBoolVar) :: translatedGenLits
    translatedGenLits

let timeWalkTheState (s:State) (bLits:Literal list) (rwLits:Literal list) (genLits:Literal list) (backjumpLvl:int) (noGen:bool) (noMin:bool) (mCubeSubsetBaseCube:bool) =
    assert (backjumpLvl >= 0)
    // Explanation to be:
    //  (/\ oldLits) -> tseitinVar
    // and tseitinVar = (\/ newlits)

    let uncertainLiterals = List.map Negate (genLits @ rwLits)
    let baseLits = List.map Negate bLits

    if noGen && noMin then
        if DBG then printfn "Leaving original conflict unchanged"
        () // No generalization, proceed with boolean conflict resolution
    elif noGen && mCubeSubsetBaseCube then
        // Conflict is minimized, and all literals are on the trail,
        // replace the existing conflict with a smaller one.
        if DBG then printfn "Minimized conflict"
        s.SetConflict (Some (ref (newClauseFromList (baseLits @ uncertainLiterals))))
    elif uncertainLiterals.Length = 0 then
        // Everything has a value, no new literals, but possible shorter conflict clause.
        s.SetConflict (Some (ref (newClauseFromList baseLits)))
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
             let extendedResolutionExpl = newClauseFromList (lit :: baseLits)
             (lit, extendedResolutionExpl)

        let impliedVar = lit2var impliedLit

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
            if DBG then printfn "Popping the trail to lvl %d" backjumpLvl
            assert (backjumpLvl > -1)
            while (!s.trail).getNumDecisions > backjumpLvl do
                s.Pop

            // Get implications of generalized literals
            let twImps = [| for l in uncertainLiterals do
                                assert ((!s.theoryDB).isDefined (lit2var l))
                                let t = (!s.theoryDB).getThRelation (lit2var l)
                                let rleHlds = tHolds t s.bvVal s.numeralDB
                                let bndsHlds = tbndsHolds t s.bounds s.numeralDB
                                if  rleHlds <> Undefined then
                                    yield (tGetImplication s (ref t) rleHlds)
                                elif bndsHlds <> Undefined then
                                    yield (tbndsGetImplication s (ref t) bndsHlds) |]

            // Propagate found implications
            for (imp, l) in twImps do
                if lit2var l <> impliedVar then // AZ: impliedLit is not defined on the trail and will be implied by the remainder of this function.
                    if DBG then
                        printf "Implication: "
                        s.printClause (ref imp)
                    if (!s.bVal).getValueB l = Undefined then
                        (s.Push (Imp (ref imp, l)))
                    else
                        assert ((!s.bVal).getValueB l = True)

            // Learn the new generalized cc with a Tseitin variable
            if (!s.clauseDB).isRegisteredTseitin impliedVar then
                // Backjump-Decide
                assert (uncertainLiterals.Length > 0)
                s.Push (Imp (ref newCC, impliedLit))

                // Deciding on a literal
                let find_undef_lit = (fun l ->
                    let is_u = (!s.bVal).getValueB l = Undefined
                    if not is_u then assert ((!s.bVal).getValueB l = False)
                    is_u)
                match (List.tryFind find_undef_lit uncertainLiterals) with
                | Some(dec) ->
                    s.Push (BoolDecision dec) // CMW: OK; note that there is no conflict anymore.
                | None ->
                    let c = (Negate impliedLit :: uncertainLiterals)
                    List.map (fun x -> assert ((!s.bVal).getValueB x = False)) c |> ignore
                    s.SetConflict (Some (ref (newClauseFromList c)))
            else
                s.Push (Imp (ref newCC, impliedLit))

                if (!s.theoryDB).isDefined impliedVar then
                    let tr = (!s.theoryDB).getThRelation impliedVar
                    let theory_value = tHolds tr s.bvVal s.numeralDB
                    let bounds_value = tbndsHolds tr s.bounds s.numeralDB

                    match (isPositive impliedLit, theory_value, bounds_value) with
                    | (true, False, _)
                    | (false, True, _)
                    | (true, _, False)
                    | (false, _, True) ->
                        // CMW: Skeleton and theories disagree, i.e., we have a reason
                        // for impliedLit but we also have another reason for
                        // (Negate impliedLit).
                        let (expl, l) = tGetImplication s (ref tr) theory_value
                        s.SetConflict (Some (ref expl))
                    | _ ->
                        () // CMW: OK; note that there is no conflict anymore.

        | False ->
            // CMW: OK, proper conflict, nothing more to do.
            s.SetConflict (Some (ref newCC))

        | True ->
            if (!s.theoryDB).isDefined impliedVar then
                let tRel = (!s.theoryDB).getThRelation impliedVar
                assert ((!s.theoryDB).isDefined tRel.getBoolVar)

                let theory_value = tHolds tRel s.bvVal s.numeralDB
                let bounds_value = tbndsHolds tRel s.bounds s.numeralDB

                match (theory_value, bounds_value) with
                | (True, False)
                | (False, True) -> UNREACHABLE("Theories unsound")
                | (Undefined, Undefined) -> UNREACHABLE("Theories incomplete")
                | _ -> ()

            // CMW: This case should really be unreachable. If we get to this
            // point in the code, it means that we are learning something that
            // we already knew to be true (in Skeleton _and_ theories). We can
            // not ignore this, because it would make the solver incomplete.
            // There are two approaches to resolving this situation:

            // 1: Don't allow the generalization to come up with such things:
            // UNREACHABLE("unexpected lack of confliction.")

            // 2: Allow the generalization to produce these things, but then
            // throw them away and keep the old conflict:
            s.SetConflict (Some originalCC)


let getCnflctTrigger (s:State) =
    match (!s.trail).trail.[(!s.trail).getCount - 1] with
    | MAssgnmnt (v, _, _)
    | BAssgnmnt (v, _, _) -> Some v
    | _ -> None

let xTExplanationGeneralization (s:State) (sbox:State) =
    assert (s.IsConflicted)

    if DBG then printfn "------------------------------";
                printfn "|           SANDBOX          |";
                printfn "------------------------------";
                printfn "****Conflict generalization****"

    let baseConflictClause = !s.GetConflictClause
    let baseConflictCube = (Array.map Negate (getLiterals baseConflictClause))

    if DBG then
        printf " Base conflict clause:"
        for i in 1 .. (getSize baseConflictClause) do
            printf " %d" baseConflictClause.[i]
        printfn "\n =="
        s.printClause (ref baseConflictClause)

    sbox.enterTempMode s

    let tRelsInvolved = [| for i in 1 .. (getSize baseConflictClause) do
                            let l = baseConflictClause.[i]
                            if (!s.theoryDB).isDefined (lit2var l) then
                                yield (!s.theoryDB).getThRelation (lit2var l) |]

    // Set up temporary watchlists
    Array.map (!sbox.database).addToOccurenceLists tRelsInvolved |> ignore

    let isArithmeticInvolved = Array.exists TheoryRelation.isArithmetic tRelsInvolved

    // TODO: Rewrite conflict minimization in spirit of generalization
    let (toMinimize, rewrittenEQs) =
        if isArithmeticInvolved then
            verbose <| (lazy "Arithmetic conflict")
            rewritePositiveEqualities s sbox baseConflictCube
        else
            (baseConflictCube, [])

    let minCube = minimize sbox toMinimize
    let minCubeIsSubsetOfBaseCube = Array.fold (fun a x -> (Array.contains x baseConflictCube) && a) true minCube

//    let minimizedCC = newClauseFromArray (Array.map (fun l -> Negate l) minCube)
//    checkExplanation s.trail s.database s.bvVal s.bounds minimizedCC false true true
//    s.SetConflict (Some (ref minimizedCC))

    let genCube = generalize s sbox minCube
    let genCubeIsSubsetOfMinCube = Array.fold (fun a x -> (Array.contains x minCube) && a) true genCube

    let noMinimization = minCube.Length >= toMinimize.Length && minCubeIsSubsetOfBaseCube

    for (l, u, e) in rewrittenEQs do
        let lInd = Array.tryFindIndex (fun x -> x = l) genCube
        let uInd = Array.tryFindIndex (fun x -> x = u) genCube
        if lInd.IsSome && uInd.IsSome then
            genCube.[lInd.Value] <- e
            genCube.[uInd.Value] <- e

    let newGenCube = Array.distinct genCube

    if DBG then printfn "Explanation after compacting";
                s.printCube (ref (newClauseFromArray newGenCube))

    let (annotatedGenLits, baseLits, rwLits, twLvl) = splitLiterals s sbox newGenCube

    sbox.leaveTempMode()

    if DBG then printfn "------------------------------";
                printfn "|      Leaving SANDBOX       |";
                printfn "------------------------------"

    let translatedGenLits = translateGeneralizedLiterals s annotatedGenLits
    timeWalkTheState s baseLits rwLits translatedGenLits twLvl genCubeIsSubsetOfMinCube noMinimization minCubeIsSubsetOfBaseCube
