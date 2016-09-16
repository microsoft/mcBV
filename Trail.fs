module Trail

open Microsoft.Z3
open Util
open Stats
open Interval
open GlobalOptions
open BitVector
open Literal
open Clause
open BooleanValuation
open BitVectorValuation
open BoundsValuation
open Database
open TheoryRelation
open Learning

let bumpOrder (db:Ref<Database>) (v:Var) =
    //(!(!db).Variables).varOrder.bump v

    if (!(!db).Theory).isDefined v then
        let tRel = (!(!db).Theory).getThRelation v
        for a in tRel.variableArguments do
            (!(!db).Variables).varOrder.bump a


[<NoComparison>]
type TrailElement =
    | BAssgnmnt of Var*(Literal*Literal)*Interval // Bounds Assignment: BvVar, (previous l expl, previous u expl), previous interval
    | MAssgnmnt of Var*Literal*BitVector // Model Assignment: BvVar, prevBoolExplanation, prevBVset, previous order
    | BoolDecision of Literal
    | Imp of Ref<Clause>*Literal

let isImplication (e:TrailElement) =
    match e with
    | Imp _ -> true
    | _ -> false

let isBoolLiteral (e:TrailElement) =
    match e with
    | BAssgnmnt _
    | MAssgnmnt _ -> false
    | _ -> true

let getBoolLiteral (e:TrailElement) =
    assert(isBoolLiteral e)
    match e with
    | BoolDecision l -> l
    | Imp (c, l) -> l
    | _ -> 0

let getBVVar (e:TrailElement) =
    assert(not (isBoolLiteral e))
    match e with
    | MAssgnmnt (v,_,_) -> v
    | BAssgnmnt (v,_,_) -> v
    | _ -> 0

let updateVarOrder (db:Ref<Database>) (v:Var) =
    (!(!db).Variables).varOrder.suspend v
    if (!(!db).Theory).isDefined v then
        let t = (!(!db).Theory).getThRelation v
        let vars = t.variableArguments
        for bv in vars do
            (!(!db).Variables).varOrder.bump bv

type Trail (sz:int) =
    let mutable size = sz //Allocated space
    let mutable topPtr = 0 //Elements on the trail
    let mutable trailPtr = 0 //Next element to propagate

    let mutable printCount = 0

    let mutable numDecisions = 0
    let mutable numAssignments = 0
    let nullClause = [|0|]

    member r.hasPropagationsPending = trailPtr < topPtr
    member r.getCount = topPtr

    member val trail:TrailElement array = Array.create size (BoolDecision 0) with get, set

    member r.getTrailPtr = trailPtr

    member r.nextPropagation =
        assert(r.hasPropagationsPending) //Safe only if hasPropagationPending returns true
        let l = r.trail.[trailPtr]

        trailPtr <- trailPtr + 1
        l

    member r.lastPropagation =
        assert(trailPtr>0)
        r.trail.[trailPtr - 1]

    member r.propagationDone =
        trailPtr <- trailPtr + 1

    member r.getNumDecisions = numDecisions

    member r.getLiteral(i:int) : Literal =
         if i <= topPtr then
            match r.trail.[i] with
            |BoolDecision l -> l
            |Imp (_,l) -> l
            |_->(0:Literal)
         else
            (0:Literal)

    member r.getExplanation(i:int) : Ref<Clause> =
         if i < topPtr then
            match r.trail.[i] with
            |Imp (e, l) -> e
            |_-> ref nullClause
         else
            ref nullClause

    member r.get(i:int):TrailElement option =
        if i < topPtr then
            Some (r.trail.[i])
        else
            None

    member r.realloc()=
        r.trail <- Array.append r.trail (Array.create size (BoolDecision 0))
        size<- 2*size


    member r. ElementToString (e:TrailElement) =
        match e with
//        | BAssgnmnt (v,_,_) -> "BA" + v.ToString()
//        | MAssgnmnt (v,_,_,_) -> "MA " + v.ToString()
        | BoolDecision l -> "no reason"
        | Imp (e,l) -> (clauseToString (!e)) + " -> " + (l.ToString())
        | _ -> ""


    member private r.pushElement (e:TrailElement) =
        if topPtr >= size then
            r.realloc()
        r.trail.[topPtr]<-e
        topPtr <- topPtr + 1



    member r.Push (bVal:Ref<BooleanValuation>)
                  (bvVal:Ref<BitVectorValuation>)
                  (bounds:Ref<BoundsValuation>)
                  (db:Ref<Database>)
                  (stats:Ref<Statistics>)
                  (e:TrailElement) =
        match e with
        | BoolDecision l ->
            assert ((!bVal).getValueB l = Undefined)
            numDecisions <- numDecisions + 1
            (!bVal).setValueB l r.getNumDecisions |> ignore
            (!stats).Decision()
            updateVarOrder db (lit2var l)
            dbg <| (lazy sprintf "> Decision: %d!" l)
            r.pushElement (BoolDecision l)

        | Imp (cRef, l) ->
            assert ((!bVal).getValueB l = Undefined)
            assert (Array.exists (fun x -> x = 0) !cRef = false)
            assert ((!cRef).[1] = l) // CMW: Required for soundness of Boolean conflict resolution.
            (!bVal).setValueB l r.getNumDecisions |> ignore
            updateVarOrder db (lit2var l)
            (!stats).Implication()
            verbose <| (lazy sprintf " | ==> %d (because of %s)" l (clauseToString !cRef))
            r.pushElement (Imp (cRef, l))
        | MAssgnmnt (v, r, value) ->
           if ((!bvVal).getValue v).isConcreteValue then
              (!(!db).Variables).varOrder.suspend v
        | BAssgnmnt _->
            () //AZ: All the necessary book-keeping has been done beforehand in pushMA,
               //    at this point their role is to trigger visitOccurences in propagation.
        match e with
        | BoolDecision l
        | Imp (_, l) -> r.pushMA l bVal bvVal bounds db stats
        | _ -> None


    member private r.popElement () =
        assert (topPtr > 0)
        //r.dbgPrint ("Pop: " + (trailElem2String r.trail.[topPtr - 1]))
        topPtr <- topPtr - 1

        match r.trail.[topPtr] with
        | BoolDecision _ ->
            numDecisions <- numDecisions - 1
            assert(numDecisions >= 0)
        | MAssgnmnt _ -> ()
        | BAssgnmnt _ -> ()
        | _ -> ()

        if trailPtr > topPtr then
            trailPtr <- topPtr

        r.trail.[topPtr]

    member r.Pop (bVal:Ref<BooleanValuation>)
                 (pAss:Ref<BitVectorValuation>)
                 (bounds:Ref<BoundsValuation>)
                 (db:Ref<Database>) =
        let e = r.popElement ()

        if TRC then
            r.print ("Pop : "+ (r.ElementToString e), pAss, bounds)

        match e with
        | MAssgnmnt (bvVar, oldExplain, oldValue) ->
            assert (bvVar <> 0)
            if oldValue.Length <> 0 then // normal model assignment.
                if ((!pAss).getValue bvVar).isConcreteValue then
                    assert (not oldValue.isConcreteValue)
                    (!(!db).Variables).varOrder.restore bvVar
                (!pAss).mAssignmntsExplanations.[bvVar] <- oldExplain
                (!pAss).setValue bvVar oldValue
        | BAssgnmnt (bvVar, (oldLExplain, oldUExplain), oldBounds) ->
            assert (bvVar <> 0)
            (!bounds).L_explanation.[bvVar] <- oldLExplain
            (!bounds).U_explanation.[bvVar] <- oldUExplain
            (!bounds).set bvVar oldBounds
        | BoolDecision l  ->
            (!bVal).resetValueTAboveCurrentDecisionLevel r.getNumDecisions
            assert (l <> 0)
            (!bVal).resetVal (lit2var l) |> ignore

            (!(!db).Variables).varOrder.restore (lit2var l)
        | Imp (_,l) ->
            assert (l <> 0)
            (!bVal).resetVal (lit2var l) |> ignore
            (!(!db).Variables).varOrder.restore (lit2var l)

    member r.Reset() =  topPtr <- 0
                        trailPtr <- 0

    member r.printClsOrCubeVerbose  (db:Ref<Database>)
                                    (connective:string)
                                    (clause:Ref<Clause>)
                                    =
        let cls_sz = (getSize (!clause)) in
        for j in 1 .. cls_sz do
            let i = (!clause).[j]
            let v = (lit2var i)
            //if j <> 1 then printf "       "
            if (!(!db).Theory).isDefined v  then
                if i < 0 then
                    printf "-"
                else
                    printf " "
                printf "%s" (((!(!db).Theory).getThRelation v).ToString((!db).Numerals))
            else
                printf "%d" i
            printf " (L %02d)" (r.getLevelExpensive v)
            if j < cls_sz then
                printfn " %s " connective
        printfn ""

    member r.printClauseVerbose (db:Ref<Database>) (clause:Ref<Clause>) =
        r.printClsOrCubeVerbose db "\/" clause

    member r.printCubeVerbose (db:Ref<Database>) (cube:Ref<Clause>) =
        r.printClsOrCubeVerbose db "/\\" cube

    member r.print (s:string, bvVal:Ref<BitVectorValuation>, bounds:Ref<BoundsValuation>) =
        if VRB && printCount % 10000 = 0 then
            r.forcePrint (s, bvVal, bounds)
            printCount <- printCount + 1

    member r.forcePrint (s:string, bvVal:Ref<BitVectorValuation>, bounds:Ref<BoundsValuation>) =
        printfn "%s" s
        let mutable lvl = 0
        printfn "==================================================="
        printfn "L %02d ----------------------------------------------" lvl
        for i  in 0 .. topPtr - 1 do
            if i = trailPtr then
                printfn " <---- "
            match r.trail.[i] with
            | MAssgnmnt (var, oe,_) ->
                //lvl <- lvl + 1
                let mutable reason = (!bvVal).mAssignmntsExplanations.[var].ToString()
                let mutable value = ((!bvVal).getValue var).ToString()
                let mutable j = i + 1
                while j < topPtr - 1 do
                    match r.trail.[j] with
                    | MAssgnmnt(v, oldexpl, oldval) when v = var ->
                        value <- oldval.ToString()
                        reason <- oldexpl.ToString()
                        j <- topPtr
                    | _ -> ()
                    j <- j + 1
                printfn " [%s] <-> %d:bv = %s " reason var value
            | BAssgnmnt (var, (oLe, oUe), oldBounds) ->
                let mutable lE = (!bounds).L_explanation.[var].ToString()
                let mutable uE = (!bounds).U_explanation.[var].ToString()
                let mutable intvl = ((!bounds).get var).ToString()
                let mutable j = i + 1
                while j < topPtr - 1 do
                    match r.trail.[j] with
                    | BAssgnmnt(v, (oldL, oldU), oldintvl) when v = var ->
                        intvl <- oldintvl.ToString()
                        lE <- oldL.ToString()
                        uE <- oldU.ToString()
                        j <- topPtr
                    | _ -> ()
                    j <- j + 1
                printfn " [%s /\ %s] <-> %d:bv \in %s " lE uE var intvl
            | BoolDecision l ->
                lvl <- lvl + 1
                printfn "L %02d ----------------------------------------------" lvl
                printfn " * %d" l
            | Imp (e,l) -> printfn " %s -> %s " (clauseToString !e) (l.ToString())
        printfn "==================================================="


    member r.getLevelExpensive (l:Literal) =
        let var = lit2var(l)
        let mutable found = false
        let mutable i = 0
        let mutable lvl = 0

        while (not found && i < r.getCount) do
            match r.trail.[i] with
            | Imp(_, m) -> if var = lit2var(m) then found <- true
            | MAssgnmnt(v, _,_) -> if v = var then found <- true
            | BAssgnmnt(v, _, _) -> if v = var then found <- true
            | BoolDecision m ->
                if var = (lit2var m) then
                     found <- true
                lvl <- lvl + 1
            i <- i + 1
        lvl


    member private r.makeRLEMA (bv:Var, newExpl:Var, newPttrn:BitVector)
                (pAss:Ref<BitVectorValuation>)
                (bounds:Ref<BoundsValuation>)
                (db:Ref<Database>)
                (stats:Ref<Statistics>) =
        let oldPttrn = (!pAss).getValue bv
        let oldExpl = (!pAss).mAssignmntsExplanations.[bv]
        let oldBounds = (!bounds).get bv

        let intrsctn = (BitVector.Intersect newPttrn oldPttrn)
        if intrsctn.isInvalid then
            // Bounds implied model assignment violating a bitpattern
            // CMW: Definitely always cross-theory?
            // AZ: Yes, if a value is invalid within single theory
            //     it wouldn't try to make an assignment.
            let cls = collectLiterals [ Negate newExpl; Negate oldExpl ]
            (None, Some (ref (newClauseFromList cls)))
        elif intrsctn.isConcreteValue && not (oldBounds.Contains intrsctn) then
            // Bit-pattern implied assignment violates bounds
            let violatedBound = if not (BitVector.bvULEQ intrsctn oldBounds.Upper) then
                                    (!bounds).U_explanation.[bv]
                                else
                                    (!bounds).L_explanation.[bv]
            let cls = collectLiterals [ Negate newExpl; Negate oldExpl; Negate violatedBound ]
            (None, Some (ref (newClauseFromList cls)))
        else
            let value_is_a_subset = (BitVector.bvEQ newPttrn intrsctn)

            if value_is_a_subset then
                (!pAss).setValue bv newPttrn
                (!pAss).mAssignmntsExplanations.[bv] <- newExpl
                (!stats).ModelAssignment()
                if newPttrn.isConcreteValue then
                   (!(!db).Variables).varOrder.suspend bv
                trace <| (lazy sprintf  " | ==> %d:bv = %s (because of %d)" bv (newPttrn.ToString()) newExpl)
                (Some (MAssgnmnt (bv, oldExpl, oldPttrn)), None)
            elif not (BitVector.bvEQ newPttrn oldPttrn) then
                // CMW: In this case we may still be able to "learn" something, but it doesn't
                // have the shape of an RLE expression, but a nice regular expression might exist.
                (None, None)
            else
                // This can happen when a Boolean variable gets activated,
                // but the corresponding theory relation and it's variable
                // are already more concrete.
                (None, None)


    member private r.makeBoundsMA (bv:Var, newExpl:Literal, newBounds:Interval)
                                  (bounds:Ref<BoundsValuation>)
                                  (db:Ref<Database>)
                                  (stats:Ref<Statistics>) =
        assert(newExpl <> 0) // CMW: newExpl is the reason for whatever changed in the bounds;
                             // could be lower, could be upper, could be both.

        if newBounds.isEmpty then
            (None, Some (ref (newClauseFromList [Negate newExpl])))
        else
            let newLB, newUB = newBounds.Lower, newBounds.Upper
            let oldBnds = (!bounds).get bv

            // CMW: New bounds are usually tighter than the old ones
            let lower_tighter = (BitVector.bvULT oldBnds.Lower newLB)
            let upper_tighter = (BitVector.bvULT newUB oldBnds.Upper)

            let rel = (!(!db).Theory).getThRelation (lit2var newExpl)
            assert(not (lower_tighter && upper_tighter) || rel.isPAPredicate)

            if lower_tighter || upper_tighter then
                let nL = if lower_tighter then newLB else oldBnds.Lower
                let nU = if upper_tighter then newUB else oldBnds.Upper
                let oldLExpl = (!bounds).L_explanation.[bv]
                let oldUExpl = (!bounds).U_explanation.[bv]

                if BitVector.bvUGT nL nU then
                    //xTheory conflict
                    let mutable cls = []
                    for l in [ oldLExpl; oldUExpl; newExpl ] do
                        let already_in_cls = (List.exists (fun x -> x = (Negate l)) cls)
                        if l <> 0 && not already_in_cls then
                            cls <- (Negate l) :: cls
                    let cc = newClauseFromList cls
                    assert(not (clauseContainsDuplicates cc))
                    (None, Some (ref cc))
                else
                    // These explanations have to be updated here, otherwise the conflict resolution
                    // for the conflict in the previous case will be wrong.
                    if lower_tighter then (!bounds).L_explanation.[bv] <- newExpl
                    if upper_tighter then (!bounds).U_explanation.[bv] <- newExpl
                    let newBnds = Interval(nL, nU)
                    (!bounds).set bv (newBnds)
                    bumpOrder db bv
                    (!stats).ModelAssignment()
                    trace <| (lazy sprintf  " | ==> %d:bv is in %s (because of %d)" bv (newBnds.ToString()) newExpl)
                    (Some (BAssgnmnt (bv, (oldLExpl, oldUExpl), oldBnds)), None)
            else
                // CMW: This can happen, e.g., when we see a new constraint that has weaker bounds
                // than an old one. There's a chance that we run into non-termination issues
                // if we ignore them here (could erroneously learn weak bounds forever).
                (None, None)


    member private r.pushMA (l:Literal)
                            (bVal:Ref<BooleanValuation>)
                            (bvVal:Ref<BitVectorValuation>)
                            (bounds:Ref<BoundsValuation>)
                            (db:Ref<Database>)
                            (stats:Ref<Statistics>) =
        let mutable cnflct = None
        if (!(!db).Theory).isDefined (lit2var l) then
            let rel = (!(!db).Theory).getThRelation (lit2var l)

            // CMW: in a more general framework we would iterate
            // over all theories here and ask each of them for "news".
            // For now, we have only the following two theories.

            // RLEBV Theory hook.
            if rel.isPAPredicate then
                let v = rel.getPAPredicateVariable
                let value = rel.getPAPredicateValue (!db).Numerals

                if isPositive(l) then
                    // Positive PAPredicate
                    let args = (v, rel.getBoolVar, value)
                    let te = r.makeRLEMA args bvVal bounds db stats
                    match te with
                    | (Some(e),None) -> r.pushElement e
                    | (None, Some cRef) ->  cnflct <- Some cRef //xTheory conflict
                    | _ -> ()
                else
                    // Negative PAPredicate
                    if not (value.isConcreteValue) then

                            let oldValue = (!bvVal).getValue v
                            let oldExpl = (!bvVal).getExplanation v
                            let negPABool = Negate rel.getBoolVar

                            let intersection =  BitVector.Intersect oldValue value

                            if intersection.isInvalid then
                                assert (oldExpl <> Negate l)

                                // v_eq_old_value := v == oldValue
                                //    oldExpl =>
                                let v_eq_old_value = TheoryRelation(v, Z3_decl_kind.Z3_OP_EQ, (!db).mkNumeral oldValue)
                                let oq = (!(!db).Theory).getThRelationVar v_eq_old_value
                                let v_eq_old_value_lit = match oq with
                                                         | (true, var) -> var
                                                         | (false, _) ->
                                                            let newBool = (!db).mkFreshBooleanVariable ()
                                                            v_eq_old_value.setBoolvar newBool
                                                            (!db).addTheoryRelation v_eq_old_value
                                                            newBool

                                // v_eq_value_lit := v == value
                                // l => v_eq_value_lit
                                let v_eq_value = TheoryRelation(v, Z3_decl_kind.Z3_OP_EQ, (!db).mkNumeral value)
                                let nq = (!(!db).Theory).getThRelationVar v_eq_value
                                let v_eq_value_lit = match nq with
                                                     | (true, var) -> var
                                                     | (false, _) ->
                                                        let newBool = (!db).mkFreshBooleanVariable ()
                                                        v_eq_value.setBoolvar newBool
                                                        (!db).addTheoryRelation v_eq_value
                                                        newBool

                                // (... /\ value != oldValue)

                                // if we already know that v_eq_value_lit is false, then
                                // there is a conflict (-v_eq_old_value_lit \/ -v_eq_value_lit)
                                if (((!bVal).getValueB v_eq_value_lit) = True) then
                                    let cls = collectLiterals([ Negate v_eq_old_value_lit; Negate v_eq_value_lit; ])
                                    cnflct <- Some (ref (newClauseFromList cls))

                            elif USE_BOUNDS then
//                                 let oldBnds = (!bounds).get v
//
//                                 if BitVector.bvULT intersection.Maximum oldBnds.Lower then
//                                    let cls = collectLiterals([ negPABool;
//                                                                Negate (!bounds).L_explanation.[v];
//                                                                Negate oldExpl;
//                                                                ])
//                                    cnflct <- Some (ref (newClauseFromList cls))
//
//                                 elif cnflct = None && BitVector.bvULT oldBnds.Upper intersection.Minimum then
//                                    let cls = collectLiterals([ negPABool;
//                                                                Negate (!bounds).U_explanation.[v];
//                                                                Negate oldExpl;
//                                                                ])
//                                    cnflct <- Some (ref (newClauseFromList cls))
//                                 else
//                                    //Now we can introduce extractions to block unwanted model assignment attempts.
                                    ()
                    else //value.isConcreteValue

                        if USE_BOUNDS then

//                            let oldBnds = ((!bounds).get v)
//                            let negPABool = rel.getBoolVar
//
//
//                            // This is a special cross-theory case where
//                            // a negatively asserted model assignment
//                            // can refine the bounds slightly.
//
//                            // Note: Previously we had reasons for the lower and upper bound, now we
//                            // refine one of them based on information from a PAPredicate. To make
//                            // this work correctly, we need to introduce a new _bounds_ predicate,
//                            // such that we have oldBnds /\ not PAPredicate => newBoundsPredicate.
//
//                            let (newBnds, newPred, oldExpl) =
//                                if (BitVector.bvEQ oldBnds.Lower value) then
//                                    let newLower = BitVector.bvAdd oldBnds.Lower (BitVector.One oldBnds.Lower.Length)
//                                    (Interval(newLower, oldBnds.Upper),
//                                     (getLowerBoundPredicate db v newLower bVal bvVal bounds),
//                                     (!bounds).L_explanation.[v])
//                                elif (BitVector.bvEQ oldBnds.Upper value) then
//                                    let newUpper = BitVector.bvSub oldBnds.Upper (BitVector.One oldBnds.Upper.Length)
//                                    (Interval(oldBnds.Lower, newUpper),
//                                     (getUpperBoundPredicate db v newUpper bVal bvVal bounds),
//                                     (!bounds).U_explanation.[v])
//                                else
//                                    (oldBnds, TheoryRelation.EmptyThRel, 0)
//
//                            let newBool = newPred.getBoolVar
//                            let newBoolVal = (!bVal).getValueB newBool
//
//                            if newBnds.isEmpty then
//                                let cls = collectLiterals([ negPABool;
//                                                            Negate (!bounds).L_explanation.[v];
//                                                            Negate (!bounds).U_explanation.[v] ])
//                                cnflct <- Some (ref (newClauseFromList cls))
//                            elif newBoolVal = False then
//                                let cls = collectLiterals([ negPABool;
//                                                            Negate (!bounds).L_explanation.[v];
//                                                            Negate (!bounds).U_explanation.[v];
//                                                            newBool ])
//                                cnflct <- Some (ref (newClauseFromList cls))
//                            elif newBoolVal = Undefined && oldBnds <> newBnds then
//                                    // CMW: collectLiterals reverses the order of the literals;
//                                    // we have to make sure that `newBool' is first.
//                                    let cls = collectLiterals [ Negate oldExpl; negPABool; newBool ]
//                                    let ic = newClauseFromList cls
//                                    cnflct <- r.Push bVal bvVal bounds db stats (Imp (ref ic, newBool))
//                            else
//                                 // We can learn that: not (x = a) => x < a \/ x >a
//                                 // which is equivalent to  x=a \/ not x<=a \/ not x>=a
////                                 let x_leq_value = getUpperBoundPredicate db v value bVal pAss bounds
////                                 let value_leq_x = getLowerBoundPredicate db v value bVal pAss bounds
////                                 let gt =  Negate (x_leq_value.getBoolVar)
////                                 let lt = Negate (value_leq_x.getBoolVar)
////                                 let implication = [rel.getBoolVar; gt; lt ]
////                                 let c = newClauseFromList implication
////
////                                 let gtVal = (!bVal).getValueB gt
////                                 let ltVal = (!bVal).getValueB lt
////                                 assert ( (!bVal).getValueB (rel.getBoolVar) = False)
////                                 assert ( gtVal = Undefined || ltVal = Undefined)
////
////                                 if not ((!(!db).Clauses).isStored c) then
////                                     let status = (!db).addAndWatchClause bVal c
////
////                                     match status with
////                                     | Clause.Unsat -> assert(false)
////                                     | Clause.Implication ->
////                                         assert ( (!bVal).getValueB c.[1] = Undefined)
////                                         cnflct <- r.Push bVal pAss bounds db stats (Imp (ref c, c.[1], None))
////                                     | _ -> ()
//                                ()
                                    ()












            if USE_BOUNDS then
                // Bounds theory hook.

                if rel.isBoundsPredicate && (not rel.isPAPredicate || isPositive l) then //AZ: This is to avoid duplicate propagation of x =/= cnst,
                                                                                         //    since it is already handled above.
                    let v = rel.getBoundsPredicateVariable
                    let newBnds = rel.getBoundsPredicateValue (!db).Numerals


                    let args = if isPositive l then (v, l, newBnds)
                               else (v, l, newBnds.Complement())

                    //if isPositive(l) then
                    // Positive BoundsPredicate
                    //let args = (v, rel.getBoolVar, newBnds)
                    let te = r.makeBoundsMA args bounds db stats
                    match te with
                    | (Some(e), None) -> r.pushElement e
                    | (None,Some cRef) -> cnflct <- Some cRef //xTheory conflict
                    | (Some _, Some _) -> UNREACHABLE "Propagation in a conflict state"
                    | _ -> ()

                    let bnds = ((!bounds).get v)
                    if cnflct.IsNone && (fst te).IsSome && bnds.isSingleton then
                        let oldValue = (!bvVal).getValue v
                        let newValue = bnds.Lower

                        if BitVector.bvEQ oldValue newValue then
                            ()
                        else
                            // Note: This is a new RLE theory assignment with bounds theory reasons,
                            // i.e., this is a cross-theory implication. This could create trouble
                            // later, if we assume all reasons are exclusively bounds reasons, or
                            // exclusively MA reasons.

                            let newPred = getModelAssignmentPredicate db v newValue bVal bvVal bounds

                            let newBool = newPred.getBoolVar
                            let (lExpl,uExpl) = (!bounds).getExplanations v

                            // CMW: collectLiterals reverses the order of the literals;
                            // we have to make sure that `newBool' is first.
                            let explanation = newClauseFromList (collectLiterals([ Negate lExpl; Negate uExpl; newBool ]))

                            match (!bVal).getValueB newBool with
                            | True -> assert(false) // AZ: Deriving old knowledge should not be possible here
                            | False ->  cnflct <- Some (ref explanation) //xTheory conflict
                            | Undefined -> //xTheory propagation
                            cnflct <- r.Push bVal bvVal bounds db stats (Imp (ref explanation, newBool))
                        ()
                    ()
//                    else
//                        // Negative BoundsPredicate
//
//                        // CMW: Todo. We should be able to use negative bounds information too,
//                        // but I'm not sure whether we absolutely have to catch this case to
//                        // get enough information for decisions/conflict resolution not to fail.
//                        ()



        cnflct