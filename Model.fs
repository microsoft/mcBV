module Model

open BitVectorValuation
open BooleanValuation

type Model = class
    val bvValues : BitVectorValuation
    val boolValues : BooleanValuation

    new (bvs, bools) = { bvValues = bvs; boolValues = bools; }

    member this.getValueBool (i : int) = this.boolValues.getValueB i
    member this.getValueBV (i : int) = this.bvValues.getValue i
end