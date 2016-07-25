module BoundsTheory

open Microsoft.Z3
open GlobalOptions
open Util
open Numeral
open Literal
open BooleanValuation
open BitVectorValuation
open BoundsValuation
open NumeralDB
open Clause
open Trail
open State
open TheoryRelation
open BitVector
open Learning
open Interval
open Z3Check
open BoundsOperations

type BoundType =
    | Lower
    | Upper
    | Interval

// CMW: Global Note: All the functions in this file implement some bounds-specific
// function. The idea is that they can reason over bounds _only_. Quick sanity check:
// If one of the functions has a BitVectorEvaluation as an argument, it automatically
// depends on RLEBVTheory, which we don't want. We rather want the Interval[] in
// s.partAssignment.bounds
// We can exploit the combination of the two theories later (e.g., in tDecide and
// tGeneralize). For now, we can have all Boolean combinations of RLEBV constraints
// (PAs) and bounds constraints (Intervals), which does not require any implementation
// work, it will happen automatically once each of the theories has generated a few
// clauses (over their theory only), and the Boolean engine starts to resolve them with
// each other.
// Further theory dependency check: change the order of RLEBVTheory.fs and
// BoundsTheory.fs in the project, everything should compile regardless of the
// order of those two files.

let tbndsHolds (r:TheoryRelation) (pBounds:Ref<BoundsValuation>) (pNumerals:Ref<NumeralDB>) =
        let relOp =
                (fun (xBnds:Interval) (yBnds:Interval) ->
                    match r.getRelationOP with
                    | Z3_decl_kind.Z3_OP_EQ when xBnds.isSingleton && yBnds.isSingleton ->
                        if BitVector.bvEQ (xBnds.Singleton) (yBnds.Singleton) then True else False
                    | Z3_decl_kind.Z3_OP_ULEQ when xBnds.isSingleton && yBnds.isSingleton ->
                        if BitVector.bvULEQ (xBnds.Singleton) (yBnds.Singleton) then True else False
                    | Z3_decl_kind.Z3_OP_EQ ->
                            if (xBnds.isSingleton) then
                                if not (yBnds.Contains(xBnds.Singleton)) then False else Undefined
                            elif (yBnds.isSingleton) then
                                if not (xBnds.Contains(yBnds.Singleton)) then False else Undefined
                            else
                            Undefined
                    | Z3_decl_kind.Z3_OP_ULEQ ->
                        if (BitVector.bvULEQ xBnds.Upper yBnds.Lower) then
                            True
                        elif not (BitVector.bvULEQ xBnds.Lower yBnds.Upper) then
                            False
                        else
                            Undefined
                    | _ -> assert (false)
                           Undefined) // Error

        let rhs = getRhsBounds r pBounds pNumerals
        let lhs = getLhsBounds r pBounds pNumerals
        if rhs.isEmpty || lhs.isEmpty then
            False
        else
            let res = relOp lhs rhs

//            dbg <| (lazy (sprintf " | %s in %s %s %s in %s => %s"
//                                (if (r.isSimpleRelation) then
//                                     (r.getArgumentString 0)
//                                 elif r.numArguments = 2 then
//                                     (r.getBVOP.ToString()) + " " +
//                                     r.getArgumentString 0 + " " +
//                                     r.getArgumentString 1
//                                 elif r.numArguments = 1 then
//                                     (r.getBVOP.ToString()) + " " +
//                                      r.getArgumentString 0
//                                 else
//                                    assert(false)
//                                    "")
//                                (lhs.ToString())
//                                (if r.getRelationOP = Z3_decl_kind.Z3_OP_EQ then "=" else "<=")
//                                (if r.isRhsNumeral then ((!pNumerals).getNumeral (- r.getRhs)).ToString() else (r.getRhs.ToString()) + ":bv")
//                                (rhs.ToString())
//                                (res.ToString())))

            res


let tbndsGetAntecedents (s:State) (tRel:Ref<TheoryRelation>) : Literal list =
    let lex = (!s.bounds).L_explanation
    let uex = (!s.bounds).U_explanation

    // The situation is tRel: (op a0 a1) = rhs
    // the antecedents of tRel are the bounds for a0, a1, and rhs,
    // i.e., a maximum of 6 different Boolean variables (negated).

    // Note: BV variables occurring in bounds constraints can have
    // the same bounds constraint's boolVar as a reason (e.g., when they
    // appear on decision level 0).

    let nbv = Negate ((!tRel).getBoolVar)
    let mutable t = []
    for i in 0 .. (!tRel).numArguments do
        if not ((!tRel).isArgumentNumeral i) then
            let ll = Negate lex.[(!tRel).getArgument i]
            let ul = Negate uex.[(!tRel).getArgument i]
            for lit in [ll; ul] do
                if lit <> 0 && lit <> nbv &&
                   not (List.exists (fun x -> x = lit) t) then
                    t <- lit :: t
    t


let tbndsGetImplication (s:State) (tRel:Ref<TheoryRelation>) (holds:Val) =
    // Whenever this function is called, we know that tbndsHolds is True or False.
    assert (holds <> Undefined)

    // CMW: The name of this function is not great, here's a description:
    // Suppose there is a conflict between (...) -> boolVar and
    // (only bounds) -> -boolVar. We need to make the latter explicit by
    // providing a clause that contains all antecedents, and which
    // implies -boolVar (swap polarity when holds = False)

    let boolVar = (!tRel).getBoolVar
    let ants = (tbndsGetAntecedents s tRel)
    let lit = if holds = True then var2lit boolVar else Negate boolVar
    let ants_contains_lit = (List.tryFind(fun x -> x = lit) ants).IsSome
    assert(not ants_contains_lit)
    let cl = newClauseFromList (lit :: ants)
    checkExplanation s.trail s.database s.bvVal s.bounds cl false false true
    (cl, lit)


let tbndsGeneralize (s:State) (expl:Clause) : Clause =
    // TODO: Bounds generalization
    expl


//let tbndsCheckConsistency (s:State) (wRel:Ref<TheoryRelation>) =
//    let holds = tbndsHolds (!wRel) s.bounds s.numeralDB
//    let valB = (!s.bVal).getValueB (!wRel).getBoolVar
//    match (holds,valB) with
//    | (True,False)
//    | (False,True) ->
//        let cnflctCls = tbndsExplainConflict s wRel
//        s.conflict <- Some (ref cnflctCls)
//    | _ -> ()


let implyBoundPredicate (s:State) (antecedants:Literal list) (boundPred:Ref<TheoryRelation>) =
    assert(not antecedants.IsEmpty)
    let lbVar = (!boundPred).getBoolVar
    let imp = newClauseFromList (lbVar :: antecedants)

    match  (!s.bVal).getValueB lbVar with
    | True ->
        // AZ: If the predicates are normalized then this should work
        // CMW: So, are they normalized?
        ()
    | False -> s.SetConflict (Some (ref imp))
    | Undefined ->
        checkExplanation s.trail s.database s.bvVal s.bounds imp false false true
        s.Push (Imp (ref imp, lbVar))
        //assert(not s.IsConflicted) AZ: cross theory conflcits can occur


let tbndsImplyNewInterval (s:State) (antecedants:Literal list) (bvVar:Var) (newIntvl:Interval) =

    // The situation is newInterval.lower < bvVar < newInterval.upper.
    // See tImplyNewValue in RLEBVTheory.
    // For the bounds, the difference is that we need to introduce
    // "interval-Predicates" instead of MAPredicates.

    let oldIntvl = (!s.bounds).get bvVar

    if not (BitVector.bvEQ oldIntvl.Lower newIntvl.Lower) then
        let lbPredicate = getLowerBoundPredicate s.database bvVar newIntvl.Lower s.bVal s.bvVal s.bounds
        implyBoundPredicate s antecedants (ref lbPredicate)

    if s.IsSearch then
        if not (BitVector.bvEQ oldIntvl.Upper newIntvl.Upper) then
            let ubPredicate = getUpperBoundPredicate s.database bvVar newIntvl.Upper s.bVal s.bvVal s.bounds
            implyBoundPredicate s antecedants (ref ubPredicate)


let tbndsGetImpliedBounds (s:State) (tRel:Ref<TheoryRelation>) (polarity:Val) =
    assert ((!s.bVal).getValueB ((!tRel).getBoolVar) <> Undefined)
    let boolVar = (!tRel).getBoolVar
    let varBoundPairs = tbndsGetNewValues (!tRel) polarity s.bounds s.numeralDB

    let expl = (if polarity = True then Negate boolVar else boolVar) :: (tbndsGetAntecedents s tRel)

    for (bvVar, newBounds) in varBoundPairs do
        let oldBounds = (!s.bounds).get bvVar

        if s.IsConflicted || bvVar = 0 || (Interval.Equal newBounds oldBounds) then
            ()
        else if newBounds.isEmpty then
            verbose <| (lazy (sprintf " | ==> Domain of %s:bv is empty; %s => False" (bvVar.ToString()) (clauseToString (newClauseFromList expl))))
            let cc = newClauseFromList (expl)
            s.SetConflict (Some (ref cc))
        else
            // CMW: bvVar is assigned new bounds (newBnds), but that new Interval
            // does not necessarily depend on all the literals in `expl`, so
            // this can be optimized. (Maybe add explanation finding to evalBounds?)
            tbndsImplyNewInterval s expl bvVar newBounds


let tbndsEvaluateAtLeast1U (s:State) (tRel:Ref<TheoryRelation>) =
    let nums = s.numeralDB
    let pVal = s.bVal
    let rel = !tRel
    let boolVar = rel.getBoolVar
    let bVal = (!pVal).getValueB boolVar    

    if bVal = Undefined then
        let holds = tbndsHolds (!tRel) s.bounds s.numeralDB
        if holds <> Undefined then
            let (expl, l) = tbndsGetImplication s tRel holds
            s.Push (Imp (ref expl, l))
            // assert(not s.IsConflicted || s.isInTempMode)
    else
        tbndsGetImpliedBounds s tRel bVal

    // CMW: this is an optimization to get conflicts earlier.
    // tbndsCheckConsistency  s tRel


let tbndsEvaluate0U (s:State) (tRel:Ref<TheoryRelation>) =
    // The TRel can be fully evaluated and checked against the trail.
    // If it agrees with the trail, it's valueT is set
    // If it contradicts the trail, a conflict is detected.
    // If it is not present on the trail, it is propagated.
    let pVal = s.bVal
    let boolVar = (!tRel).getBoolVar

    let holds = tbndsHolds (!tRel) s.bounds s.numeralDB
    let bval = ((!pVal).getValueB boolVar)
    match (holds, bval) with

    | (True, True) -> (!pVal).setValueT boolVar (!s.trail).getNumDecisions |>ignore
    | (False, False) -> (!pVal).setValueT (Negate boolVar) (!s.trail).getNumDecisions |>ignore

    | (True, False)
    | (False, True) ->
        let (expl, l) = tbndsGetImplication s tRel holds
        s.SetConflict (Some (ref expl))

    | (True, Undefined)
    | (False, Undefined) ->
        let (expl, l) = tbndsGetImplication s tRel holds
        s.Push (Imp (ref expl, l))

    | (Undefined, _) ->
        // While this case can't happen in the RLEBV theory, it can be triggered
        // in the bounds theory when the bounds are not strong enough.
        ()


let tbndsEvaluate (s:State) (tRel:Ref<TheoryRelation>) =
//    match (numUnboundedVariables !tRel s.bounds) with
//    | 0 ->
//        // Problem: 0 unbounded variables means this is called very
//        // often, with small chance of success.
//        tbndsEvaluate0U s tRel
//    | _ ->
//        tbndsEvaluateAtLeast1U s tRel

    // CMW: In each iteration, first run bounds update,
    // then check for conflict/implication/etc. "numUnboundedVariables"
    // is not a good indicator for whether we will see bounds updates.
    tbndsEvaluateAtLeast1U s tRel
    tbndsEvaluate0U s tRel