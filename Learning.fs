module Learning

open Microsoft.Z3
open Literal
open Numeral
open BitVector
open BooleanValuation
open BitVectorValuation
open BoundsValuation
open TheoryRelation
open Database


let private EnsureVariableNumber (bVal:Ref<BooleanValuation>) (bvVal:Ref<BitVectorValuation>) (bounds:Ref<BoundsValuation>) (v:Var) (size:int) =
    (!bVal).newVar v
    (!bvVal).newVar v size
    (!bounds).newVar v size


let getTseitinVar (db:Ref<Database>) (bVal:Ref<BooleanValuation>) (bvVal:Ref<BitVectorValuation>) (bounds:Ref<BoundsValuation>) =
    let newBool = (!db).mkFreshBooleanVariable()
    EnsureVariableNumber bVal bvVal bounds newBool 0
    newBool

let getModelAssignmentPredicate (db:Ref<Database>) (bvVar:Var) (value:BitVector) (bVal:Ref<BooleanValuation>) (bvVal:Ref<BitVectorValuation>) (bounds:Ref<BoundsValuation>) =
    assert (bvVar > 0)
    let newNum = (!db).mkNumeral value
    let thRel = TheoryRelation(newNum, Z3_decl_kind.Z3_OP_EQ, bvVar)
    match (!(!db).Theory).getThRelationVar thRel with
    | (true, boolVar) -> (!(!db).Theory).getThRelation boolVar
    | (false, _) ->
        let newBool = (!db).mkFreshBooleanVariable ()
        thRel.setBoolvar newBool
        (!db).addTheoryRelation thRel
        EnsureVariableNumber bVal bvVal bounds newBool 0
        thRel


let getBoundPredicate (db:Ref<Database>) (bvVar:Var) (value:BitVector) (isLower:bool) (bVal:Ref<BooleanValuation>) (bvVal:Ref<BitVectorValuation>) (bounds:Ref<BoundsValuation>) =
    assert (value.isConcreteValue)
    let newNum = (!db).mkNumeral value
    let thRel = if isLower then
                    TheoryRelation(newNum, Z3_decl_kind.Z3_OP_ULEQ, bvVar)
                else
                    TheoryRelation(bvVar, Z3_decl_kind.Z3_OP_ULEQ, newNum)
    match (!(!db).Theory).getThRelationVar thRel with
    | (true, bVar) -> (!(!db).Theory).getThRelation bVar
    | (false, _) ->
        let newBool = (!db).mkFreshBooleanVariable ()
        thRel.setBoolvar newBool
        (!db).addTheoryRelation thRel
        EnsureVariableNumber bVal bvVal bounds newBool 0
        thRel

let mkRelaxedTRel (db:Ref<Database>) (t:TheoryRelation) (value : BitVector) (bVal:Ref<BooleanValuation>) (bvVal:Ref<BitVectorValuation>) (bounds:Ref<BoundsValuation>) =
    assert (t.isSimpleRelation)

    let lhs = t.getArgument 0
    let rhs = t.getArgument 1

    assert (isVar lhs || isVar rhs)
    assert (not (isVar lhs) || not (isVar rhs))

    let num = (!db).mkNumeral value

    let newTRel = if isVar lhs then TheoryRelation (lhs, t.getRelationOP, num)
                  else  TheoryRelation (num, t.getRelationOP, rhs)

    match (!(!db).Theory).getThRelationVar newTRel with
    | (true, bVar) -> (!(!db).Theory).getThRelation bVar
    | (false, _) ->
        let newBool = (!db).mkFreshBooleanVariable ()
        newTRel.setBoolvar newBool
        (!db).addTheoryRelation newTRel
        EnsureVariableNumber bVal bvVal bounds newBool 0
        newTRel

let getLowerBoundPredicate (db:Ref<Database>) (bvVar:Var) (value:BitVector) (bVal:Ref<BooleanValuation>) (bvVal:Ref<BitVectorValuation>) (bounds:Ref<BoundsValuation>) =
    getBoundPredicate db bvVar value true bVal bvVal bounds

let getUpperBoundPredicate (db:Ref<Database>) (bvVar:Var) (value:BitVector) (bVal:Ref<BooleanValuation>) (bvVal:Ref<BitVectorValuation>) (bounds:Ref<BoundsValuation>) =
    getBoundPredicate db bvVar value false bVal bvVal bounds
