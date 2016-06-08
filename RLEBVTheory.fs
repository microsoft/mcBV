module RLEBVTheory

open Microsoft.Z3
open GlobalOptions
open Util
open Literal
open BooleanValuation
open Clause
open BitVectorValuation
open NumeralDB
open TheoryDB
open Trail
open State
open TheoryRelation
open BitVector
open Learning
open Z3Check
open RLEBVOperations


let tHolds (r:TheoryRelation) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
        //assert (r.numUnpropagatedArgs pVal = 0)

        let x_is_constant = if r.isSimpleRelation then r.isArgumentNumeral 0 else false
        let y_is_constant = r.isRhsNumeral

        let relOp =
                (fun (x:BitVector) (y:BitVector) ->
                    match r.getRelationOP with
                    | Z3_decl_kind.Z3_OP_EQ when x.isConcreteValue && y.isConcreteValue -> if BitVector.bvEQ x y then True else False
                    | Z3_decl_kind.Z3_OP_ULEQ when x.isConcreteValue && y.isConcreteValue -> if BitVector.bvULEQ x y  then True else False
                    | _ ->

                        match r.getRelationOP with
                        | Z3_decl_kind.Z3_OP_EQ ->
                                let intersection = (BitVector.Intersect x y)
                                let empty = not intersection.isValid
                                let x_is_subset_of_y = lazy ( BitVector.bvEQ x intersection)
                                let y_is_subset_of_x = lazy (BitVector.bvEQ y intersection)

                                if empty then False
                                elif x_is_constant && y_is_constant then
                                    if BitVector.bvEQ x y then True else False
                                elif x_is_subset_of_y.Force() && y_is_constant ||
                                     y_is_subset_of_x.Force() && x_is_constant then
                                    True
                                else Undefined
                        | Z3_decl_kind.Z3_OP_ULEQ -> let x_min = x.Minimum
                                                     let x_max = x.Maximum
                                                     let y_min = y.Minimum
                                                     let y_max = y.Maximum
                                                     if BitVector.bvULEQ x_max y_min then True
                                                     elif not (BitVector.bvULEQ x_min y_max) then False
                                                     elif x_is_constant && y_is_constant then
                                                        assert(false) // No 1:num = 2:num
                                                        Undefined
                                                     else Undefined
                        | _ -> assert (false)
                               Undefined) // Error

        let rhs = getRhsValue r pVal pNumerals
        let lhs = getLhsValue r pVal pNumerals
        assert(rhs.Length = lhs.Length)

        relOp lhs rhs


let tGetAntecedents (s:State) (tRel:Ref<TheoryRelation>) : Literal list =
    let MAexpls = (!s.bvVal).getMAssignmentExplRef

    // Note: BV variables occurring in PA constraints can have
    // the same PA constraint's boolVar as a reason (e.g., when they
    // appear on decision level 0).
    // CMW: Not completely sure this is true in the RLE theory.

    let boolVar = (!tRel).getBoolVar
    let mutable t = []
    for i in 0 .. (!tRel).numArguments do
        if not ((!tRel).isArgumentNumeral i) then
            let e = (!MAexpls).[(!tRel).getArgument i]
            let lit = (Negate e)
            if lit <> 0 && e <> boolVar && not (List.exists (fun x -> x = lit) t) then
                t <- lit :: t
    t


let tGetImplication (s:State) (tRel:Ref<TheoryRelation>) (holds:Val) : (Clause * Literal) =
    // Whenever this function is called, we know that tHolds is True or False.
    assert (holds <> Undefined)

    let boolVar = (!tRel).getBoolVar
    let ants = (tGetAntecedents s tRel)
    let lit = if holds = True then var2lit boolVar else Negate boolVar
    let cl = newClauseFromList (lit :: ants)
    checkExplanation s.trail s.database s.bvVal s.bounds cl false false true
    (cl, lit)


let tGeneralize (s:State) (expl:Clause) : Clause =
    // TODO: RLE-encoded conflict generalization
    expl


//let tCheckConsistency (s:State) (wRel:Ref<TheoryRelation>) =
//    let holds = tHolds (!wRel) s.partAssignment s.numeralDB
//    let valB = (!s.bVal).getValueB (!wRel).getBoolVar
//    match (holds, valB) with
//    | (True,False)
//    | (False,True) ->
//        let cnflctCls = tExplainConflict s wRel
//        s.conflict <- Some (ref cnflctCls)
//    | _ -> ()


let tImplyNewValue (s:State) (antecedants:Literal list option) (bvVar:Var) (newValue:BitVector) =
    // We have:
    // oldReason => oldValue
    // impAntecedents => newValue
    // If oldValue /\ newValue = False then
    //    Conflict: not oldReason \/ not (impAntecedents)
    // else
    //    oldReason /\ impAntecedents => newMAPredicate

    let oldValue = (!s.bvVal).getValue bvVar
    let newRel = getModelAssignmentPredicate s.database bvVar newValue s.bVal s.bvVal s.bounds
    let b = newRel.getBoolVar
    let is_more_concrete = newValue.isMoreConcreteThan oldValue

    // Theoretically, b could already be true, because we may
    // be seeing the same predicate a second time. b = False means
    // that there is an old partial assignment for one part of the relation
    // and the new partial assignment for the other part is conflicting.

    match (!s.bVal).getValueB (b) with
    | True -> ()
    | Undefined when is_more_concrete ->

        match antecedants with
        | Some(a) ->
            let imp = (newClauseFromList (b :: a))
            checkExplanation s.trail s.database s.bvVal s.bounds imp false false true
            s.Push (Imp (ref imp, b))
        | None -> s.Push (BoolDecision b)

        assert (tHolds newRel (s.bvVal) (s.numeralDB) <> Undefined || s.IsConflicted)

    | Undefined -> // when not is_more_concrete
                   assert(false)
    | False ->
        // AZ: This could yield a conflict, if the predicate b
        // is not new, it can be negated on the trail already.
        match antecedants with
        | Some(a) -> s.SetConflict (Some (ref (newClauseFromList (b :: a))))
        | None -> UNREACHABLE("tImplyNewValue called for a decision.")
        ()


let tGetImpliedPartialAssignment (s:State) (tRel:Ref<TheoryRelation>) =
    assert((!s.bVal).getValueB (!tRel).getBoolVar = True)
    let (bvVar, newValue) = tGetNewValues (!tRel) s.bvVal s.numeralDB

    let boolVar = (!tRel).getBoolVar
    let oldValue = if bvVar <> 0 then ((!s.bvVal).getValue bvVar) else newValue
    let expl = Negate boolVar :: (tGetAntecedents s tRel)

    if (bvVar = 0 || (newValue.isValid && (BitVector.bvEQ newValue oldValue))) then
        ()
    elif newValue.isInvalid then
        verbose <| (lazy (sprintf " | ==> Domain of %s:bv is empty; %s => False" (bvVar.ToString()) (clauseToString (newClauseFromList expl))))

        let cc = newClauseFromList (expl)
        s.SetConflict (Some (ref cc))
    else
        tImplyNewValue s (Some expl) bvVar newValue


let tEvaluateConcat (s:State) (tRel:Ref<TheoryRelation>) =
    assert (numUnpropagatedVariables  (!tRel) s.bvVal <= 2)
    let watchedRel = !tRel
    let pPAs = s.bvVal
    let pNums = s.numeralDB
    let MAexpls = (!s.bvVal).mAssignmntsExplanations

    let mutable argValList = getArgValuePairs watchedRel pPAs pNums
    assert (List.length argValList = 2)

    // (concat a0 a1) <-> rhs

    let (a0, v0) = argValList.Head
    let (a1, v1) = argValList.Tail.Head
    let (rhs, vr) = (watchedRel.getRhs, getRhsValue watchedRel pPAs pNums)

    let nr = BitVector.bvConcat v0 v1
    let nvr = BitVector.Intersect vr nr
    let rr = if watchedRel.isRhsNumeral || MAexpls.[rhs] = 0 then [] else [ - MAexpls.[rhs]]

    let na0 = BitVector.bvExtract (vr.Length - 1) (vr.Length - v0.Length) vr
    let nv0 = BitVector.Intersect v0 na0
    let r0 = if watchedRel.isArgumentNumeral 0 || MAexpls.[a0] = 0  then [] else [ - MAexpls.[watchedRel.getArgument 0]]

    let na1 = BitVector.bvExtract (v1.Length - 1) 0 vr
    let nv1 = BitVector.Intersect v1 na1
    let r1 = if watchedRel.isArgumentNumeral 1 || MAexpls.[a1] = 0 then [] else [ - MAexpls.[watchedRel.getArgument 1]]

    let mutable rhs_expl = []
    for lst in [ r0; r1; rr ] do
        for l in lst do
            if l <> 0 && not (List.exists (fun x -> x = l) rhs_expl) then
                rhs_expl <- l :: rhs_expl

    for (newVar, oldValue, newValue, rsns) in [ (rhs, vr, nvr, rhs_expl);
                                                (a0, v0, nv0, r0 @ rr);
                                                (a1, v1, nv1, r1 @ rr) ] do
        if not s.IsConflicted then
            let impl = (Negate watchedRel.getBoolVar) :: rsns
            if newValue.isValid then
                assert(nr.isValid)

                if not (BitVector.bvEQ newValue oldValue) then
                    // We have a new implication:
                    tImplyNewValue s (Some impl) newVar newValue
            else
                // intersect is not valid, so build an explanation (= conflict clause)
                // oldReason /\ concat /\ reasons ==> False
                // concat /\ reasons ==> - oldReason (trivial rewriting of  ==>)
                let cc = newClauseFromList impl
                s.SetConflict (Some (ref cc))


let tEvaluateDiv0 (s:State) (tRel:Ref<TheoryRelation>) =
    assert (numUnpropagatedVariables (!tRel) s.bvVal <= 2)
    assert ((!tRel).numArguments = 2)
    let watchedRel = !tRel

    let maExpl = (!s.bvVal).getMAssignmentExplRef
    let pPAs = s.bvVal
    let pNums = s.numeralDB
    let boolVar = watchedRel.getBoolVar

    let bvVar = watchedRel.getRhs
    let oldValue = getRhsValue watchedRel pPAs pNums
    let rhsExpl = (!maExpl).[bvVar]
    let width = oldValue.Length

    let a0 = watchedRel.getArgument 0 // always there?
    let v0 = getArgumentValue watchedRel pPAs pNums 0

    let a1 = watchedRel.getArgument 1
    let v1 = getArgumentValue watchedRel pPAs pNums 1
    assert(BitVector.isAllZero v1) // is a udiv/0 or sdiv/0.


    let mutable reasons = (Negate watchedRel.getBoolVar) :: (tGetAntecedents s (ref watchedRel))

    let res = BitVector width
    match watchedRel.getBVOP with
    | Z3_decl_kind.Z3_OP_BUDIV ->
        // The "hardware interpretation" for (bvudiv x 0) is #xffff
        res.Bits <- [(width, Bit.One)]

        let v0_rsn = if watchedRel.isArgumentNumeral 0 then 0 else (!maExpl).[a0]
        reasons <- List.filter (fun x -> x <> v0_rsn) reasons

    | Z3_decl_kind.Z3_OP_BSDIV when (snd v0.Bits.Head) <> Bit.U ->
        // The "hardware interpretation" for (bvsdiv x 0) is (ite (bvslt x #x0000) #x0001 #xffff)
        match v0.Bits.Head with
        | (_, Bit.One)  -> res.Bits <- [(width-1, Bit.Zero); (1, Bit.One)]
        | (_, Bit.Zero) -> res.Bits <- [(width, Bit.One)]
        | _ -> UNREACHABLE("unexpected bit")
    | Z3_decl_kind.Z3_OP_BSDIV ->
        // Sign not determined yet.
        res.Length <- 0
        res.Bits <- [(0, Bit.U)]
    | _ -> UNREACHABLE("not a divison op")

    if res.isValid then
        let newValue = BitVector.Intersect oldValue res
        if newValue.isValid then
            assert(oldValue.isValid)

            if not (BitVector.bvEQ newValue oldValue) then
                // We have a new implication:
                tImplyNewValue s (Some reasons) bvVar newValue
        else
            // newValue is not valid, so build an explanation (= conflict clause)
            // oldReason /\ concat /\ reasons ==> False
            // concat /\ reasons ==> - oldReason (trivial rewriting of  ==>)
            let cc = newClauseFromList reasons
            s.SetConflict (Some (ref cc))


let tEvaluate0U (s:State) (tRel:Ref<TheoryRelation>) =
    assert(numUnpropagatedVariables (!tRel) s.bvVal = 0)

    // The TRel can be fully evaluated and checked against the trail.
    // If it agrees with the trail, it's valueT is set
    // If it contradicts the trail, a conflict is detected.
    // If it is not present on the trail, it is propagated.
    let pVal = s.bVal
    let mAsgnmt = s.bvVal
    let numerals = s.numeralDB
    let watchedRel = !tRel
    let boolVar = watchedRel.getBoolVar

    let holds = (tHolds watchedRel mAsgnmt numerals)
    let bval = ((!pVal).getValueB boolVar)
    match (holds, bval) with

    | (True, True) -> (!pVal).setValueT boolVar (!s.trail).getNumDecisions |> ignore
    | (False, False) -> (!pVal).setValueT (Negate boolVar) (!s.trail).getNumDecisions |> ignore

    | (True, False)
    | (False, True) ->
        let (expl, l) = tGetImplication s tRel holds
        s.SetConflict (Some (ref expl))

    | (True, Undefined)
    | (False, Undefined) ->
        let (expl, l) = tGetImplication s tRel holds
        s.Push (Imp (ref expl, l))

    | (Undefined, _) -> assert(false)


let tEvaluate1U (s:State) (tRel:Ref<TheoryRelation>) =
    assert(numUnpropagatedVariables (!tRel) s.bvVal = 1)
    // assert((!wRel).holds s.partAssignment s.numeralDB = Undefined)
    // CMW: Not true, can hold even with unpropagated arguments (e.g., extract .. x = num)

    let mas = s.bvVal
    let nums = s.numeralDB
    let pVal = s.bVal
    let rel = !tRel
    let boolVar = rel.getBoolVar

    match rel.getRelationOP with
    | Z3_decl_kind.Z3_OP_EQ ->
        let bVal = (!pVal).getValueB boolVar
        match bVal with
        | True -> match rel.getBVOP with
                  | Z3_decl_kind.Z3_OP_CONCAT -> tEvaluateConcat s tRel
                  | Z3_decl_kind.Z3_OP_BUDIV
                  | Z3_decl_kind.Z3_OP_BSDIV
                        when (BitVector.isAllZero (getArgumentValue rel mas nums 1)) ->
                            tEvaluateDiv0 s tRel
                  | _ -> tGetImpliedPartialAssignment s tRel
        | False -> ()
            // Note 1: Could be a conflict, which is checked below.
            // Note 2: Theoretically there could be only one value
            // for the unpropagated argument, but it seems too expensive
            // to get that here.
        | _ ->
            let holds = tHolds (!tRel) s.bvVal s.numeralDB
            if holds <> Undefined then
                let (expl, l) = tGetImplication s tRel holds
                s.Push (Imp (ref expl, l))
                assert(not s.IsConflicted)

    | Z3_decl_kind.Z3_OP_ULEQ ->
        let bVal = (!pVal).getValueB boolVar
        let holds = tHolds (!tRel) s.bvVal s.numeralDB
        match bVal with
        | True -> 
            if holds = False then
                let c = Negate (!tRel).getBoolVar :: (tGetAntecedents s tRel)
                s.SetConflict (Some (ref (newClauseFromList c)))
            elif holds = True then
                (!s.bVal).setValueT boolVar (!s.trail).getNumDecisions |> ignore
        | False -> 
            if holds = True then
                let c = (!tRel).getBoolVar :: (tGetAntecedents s tRel)
                s.SetConflict (Some (ref (newClauseFromList c)))
             elif holds = False then
                (!s.bVal).setValueT (Negate boolVar) (!s.trail).getNumDecisions |> ignore
        | _ ->  
                if holds <> Undefined then
                    let (expl, l) = tGetImplication s tRel holds
                    s.Push (Imp (ref expl, l))
                    //assert(not s.IsConflicted) AZ: This is not guaranteed. See the similar assertion in BDecide.

    | _ -> assert(false)

    // CMW: This would be an optimization.
    // tCheckConsistency s tRel


let tEvaluate2U (s:State) (tRel:Ref<TheoryRelation>) =
    assert(numUnpropagatedVariables (!tRel) s.bvVal = 2)

    let rel = !tRel
    let mas = s.bvVal
    let nums = s.numeralDB

    match rel.getRelationOP with
    | Z3_decl_kind.Z3_OP_EQ ->
        match rel.getBVOP with
        | Z3_decl_kind.Z3_OP_CONCAT -> tEvaluateConcat s tRel
        | Z3_decl_kind.Z3_OP_BUDIV
        | Z3_decl_kind.Z3_OP_BSDIV
                when (BitVector.isAllZero (getArgumentValue rel mas nums 1)) ->
                    tEvaluateDiv0 s tRel
        | _ -> ()

        // CMW: This would be an optimization.
        // tCheckConsistency s tRel

    | Z3_decl_kind.Z3_OP_ULEQ ->
        ()

    | _ -> assert(false)


let tEvaluate (s:State) (tRel:Ref<TheoryRelation>) =
    let mAsgnmt = s.bvVal

    match (numUnpropagatedVariables !tRel mAsgnmt) with
    | 0 -> tEvaluate0U s tRel
    | 1 -> tEvaluate1U s tRel
    | 2 -> tEvaluate2U s tRel
    | _ -> () // Nothing new to learn.
