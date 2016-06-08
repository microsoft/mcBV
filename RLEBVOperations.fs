module RLEBVOperations

open Microsoft.Z3
open GlobalOptions
open Util
open Literal
open Numeral
open BitVector
open BitVectorValuation
open TheoryRelation
open NumeralDB

// Functions related to the RLEBV theory (they depend on BitVectorValuation)

let unpropagatedArguments (t:TheoryRelation) (rVal:Ref<BitVectorValuation>) =
    let mutable args = []
    for i in 0 .. t.numArguments do
        let arg = t.getArgument i
        if  not (t.isArgumentNumeral i) &&
            not ((!rVal).isAssigned arg) &&
            (List.filter (fun x -> x = arg) args).Length = 0 then
            args <- arg :: args
    args

let unpropagatedVariables (t:TheoryRelation) (rVal:Ref<BitVectorValuation>) =
    unpropagatedArguments t rVal


//AZ: This considers only the LHS
let numUnpropagatedArguments (t:TheoryRelation) (rVal:Ref<BitVectorValuation>) =
    List.length (unpropagatedArguments t rVal)

let numUnpropagatedVariables (t:TheoryRelation) (rVal:Ref<BitVectorValuation>) =
    List.length (unpropagatedVariables t rVal)

let propagatedArguments (t:TheoryRelation) (rVal:Ref<BitVectorValuation>)=
    let mutable args = []
    for i in 0 .. t.numArguments - 1 do
        let arg = t.getArgument i
        if not (t.isArgumentNumeral i) &&
            ((!rVal).isAssigned arg) &&
            (List.filter (fun x -> x = arg) args).Length = 0 then
            args <- arg :: args
    args

let separateArguments (t:TheoryRelation) (rVal:Ref<BitVectorValuation>)=
    let mutable assignedArgs = []
    let mutable unassignedArgs = []
    for i in 0 .. t.numArguments - 1 do
        let arg = t.getArgument i

        if not (isNum arg) && not ((!rVal).isAssigned arg) &&
            (List.filter (fun x -> x = arg) unassignedArgs).Length = 0 then
            unassignedArgs <- arg :: unassignedArgs
        elif (List.filter (fun x -> x = arg) assignedArgs).Length = 0 then
            assignedArgs <- arg :: assignedArgs

    (assignedArgs, unassignedArgs)


let getArgumentValue (t:TheoryRelation) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) (i:int) =
    assert (i >= 0 && i <= t.numArguments)
    if t.isArgumentNumeral i then
        (!pNumerals).getNumeral (abs (t.getArgument i))
    else
        (!pVal).getValue (t.getArgument i)


let evaluateBVOP (t:TheoryRelation) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>)  =
    assert (t.hasBVOP)
    let mutable param = []
    for i in 0 .. t.numParameters - 1 do
        param <- param @ [t.getParameter i]
    let lhsOp = z3OP2bvOP t.getBVOP param
    let args = [ for i in 0 .. t.numArguments - 1 do
                    yield (getArgumentValue t pVal pNumerals i) ]
    let res = lhsOp args
    if TRC then
        printf " |  eval %s" (t.getBVOP.ToString())
        for a in args do
            printf " %s" (a.ToString())
        printfn " => %s" (res.ToString())
    res

let getLhsValue (t:TheoryRelation) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    if t.hasBVOP then
        evaluateBVOP t pVal pNumerals
    else
        getArgumentValue t pVal pNumerals 0

let getRhsValue (t:TheoryRelation) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    getArgumentValue t pVal pNumerals t.numArguments

let ReverseConcat (t:TheoryRelation) (lhs:BitVector) (rhs:BitVector) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    assert (numUnpropagatedVariables t pVal = 1)
    assert (rhs <> lhs)
    assert (rhs.Length = lhs.Length)
    assert (rhs.isConcreteValue)
    assert (not lhs.isConcreteValue)

    // (concat a0 a1) = rhs
    let a0_arg = t.getArgument 0
    let a0_val = getArgumentValue t pVal pNumerals 0

    let a1_arg = t.getArgument 1
    let a1_val = getArgumentValue t pVal pNumerals 1

    let a0_conc = a0_val.isConcreteValue
    let a1_conc = a1_val.isConcreteValue

    match (a0_conc, a1_conc) with
    | (true, true)   -> UNREACHABLE("Expected at least one non-concrete argument.")
    | (true, false)  -> let t = (BitVector.TakeLowest a1_val.Length rhs)
                        let c = (BitVector.bvConcat a0_val t)
                        assert (BitVector.bvEQ rhs c)
                        (a1_arg, t)
    | (false, true)  -> let t = (BitVector.TakeHighest a0_val.Length rhs)
                        let c = (BitVector.bvConcat t a1_val)
                        assert (BitVector.bvEQ rhs c)
                        (a0_arg, t)
    | (false, false) -> // CMW: We could actually propagate both, a0_arg _and_ a1_arg,
                        // but I think we won't get here in the case of more than one
                        // unpropagated argument.
                        assert(a0_arg = a1_arg)
                        let t_0 = (BitVector.TakeLowest a1_val.Length rhs)
                        let t_1 = (BitVector.TakeHighest a0_val.Length rhs)
                        let c = (BitVector.bvConcat t_0 t_1)
                        if BitVector.bvEQ rhs c then
                            (a0_arg, t_0)
                        else
                            (a0_arg, BitVector.Invalid)
                        //UNREACHABLE("More than one unpropagated argument to concat.")


let ReverseRepeat (t:TheoryRelation) (rhs:BitVector) =
    // ((_ repeat param) var) = rhs
    let param = t.getParameter 0
    let var = t.getArgument 0
    assert (rhs.Length % param = 0)
    let resLen = rhs.Length / param
    let res = BitVector.TakeHighest resLen rhs
    assert (BitVector.bvEQ rhs (BitVector.bvRepeat param res))  // AZ: Raise a conflict!
    (var, res)


let ReverseAdd (t:TheoryRelation) (rhs:BitVector) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    assert (numUnpropagatedVariables t pVal = 1)
    assert (rhs.isConcreteValue)

    // (bvadd a0 a1) <- rhs

    let a0_arg = t.getArgument 0
    let a0_val = getArgumentValue t pVal pNumerals 0
    let a0_is_zero = BitVector.isAllZero a0_val

    let a1_arg = t.getArgument 1
    let a1_val = getArgumentValue t pVal pNumerals 1
    let a1_is_zero = BitVector.isAllZero a1_val

    let rhs_is_zero = BitVector.isAllZero rhs

    let a1_conc = a1_val.isConcreteValue
    let a0_conc = a0_val.isConcreteValue

    match (a0_conc, a1_conc) with
    | (true, true)   -> UNREACHABLE("Expected at least one non-concrete argument.")
    | (true, false)  -> // a0 + a1 = rhs --> a1 = rhs - a0
                        assert(not (t.isArgumentNumeral 1))
                        (a1_arg, BitVector.bvSub rhs a0_val)
    | (false, true)  -> // a0 + a1 = rhs --> a0 = rhs - a1
                        assert(not (t.isArgumentNumeral 0))
                        (a0_arg, BitVector.bvSub rhs a1_val)
    | (false, false) -> (0, BitVector.Invalid)


let ReverseNot (t:TheoryRelation) (rhs:BitVector) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    assert (numUnpropagatedVariables t pVal = 1)
    // (not a) = rhs
    let a_arg = t.getArgument 0
    let a_val = getArgumentValue t pVal pNumerals 0
    (a_arg, (BitVector.bvNot a_val))


let ReverseAnd (t:TheoryRelation) (rhs:BitVector) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    // (bvand a0 a1) = rhs
    let (concrete,unknown) = separateArguments t pVal
    assert (concrete.Length = 1 && unknown.Length = 1)
    let con = concrete.Head
    let arg = if con > 0  then    (!pVal).getValue con else (!pNumerals).getNumeral (abs con)
    (unknown.Head, BitVector.revBvAND arg rhs)

let ReverseOr (t:TheoryRelation) (rhs:BitVector) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    // (bvor a0 a1) = rhs
    let (concrete, unknown) = separateArguments t pVal
    assert (concrete.Length = 1 && unknown.Length = 1)
    let con = concrete.Head
    let arg = if con > 0  then (!pVal).getValue con else (!pNumerals).getNumeral (abs con)
    (unknown.Head, BitVector.revBvOr arg rhs)

let ReverseXOr (t:TheoryRelation) (rhs:BitVector) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    // (bvxor a0 a1) = rhs
    let (concrete, unknown) = separateArguments t pVal
    assert (concrete.Length = 1 && unknown.Length = 1)
    let con = concrete.Head
    let arg = if con > 0  then (!pVal).getValue con else (!pNumerals).getNumeral (abs con)
    (unknown.Head, BitVector.revBvXOr arg rhs)


let ReverseExtract (t:TheoryRelation) (rhs:BitVector) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    // ((_ extract i j) var) = rhs

    let var = t.getArgument 0
    let u = t.getParameter 0
    let l = t.getParameter 1
    let sz = ((!pVal).getValue var).Length - 1

    let mutable rbits = []
    if (u < sz) then rbits <- [(sz-u, Bit.U)]
    rbits <- List.append rbits rhs.Bits
    if (l > 0) then rbits <- List.append rbits [(l, Bit.U)]

    let mutable res = BitVector (u-l+1)
    res <- (res.SetFromBitTuples rbits)
    res.CheckInvariant()
    (var, res)


let ReverseShift (t:TheoryRelation) (right:bool) (arith:bool) (rhs:BitVector) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    assert (numUnpropagatedVariables t pVal = 1)
    assert (rhs.isConcreteValue)

    // (ashr a n) = rhs
    let a_arg = t.getArgument 0
    let a_val = getArgumentValue t pVal pNumerals 0

    let n_arg = t.getArgument 1
    let n_val = getArgumentValue t pVal pNumerals 1

    let a_conc = a_val.isConcreteValue
    let n_conc = n_val.isConcreteValue

    // dbg <| (lazy sprintf "rev (= (bvashr %s %s) %s)" (a_val.ToString()) (n_val.ToString()) (rhs.ToString()))

    match (a_conc, n_conc) with
    | (true, true)   -> UNREACHABLE("Expected at least one non-concrete argument.")
    | (true, false)  -> (0, BitVector.Invalid) // CMW: Many possible n, thus no implication.
    | (false, true)  -> (0, BitVector.Invalid) // CMW: At least two solutions, so no implication.
    | (false, false) -> // CMW: There's no implication, as there are many possible
                        // solutions with different a/n
                        (0, BitVector.Invalid)


let ReverseMul (t:TheoryRelation) (rhs:BitVector) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    assert (numUnpropagatedVariables t pVal = 1)
    assert (rhs.isConcreteValue)

    // (bmul a n) <- rhs

    let a0_arg = t.getArgument 0
    let a0_val = getArgumentValue t pVal pNumerals 0
    let a0_is_zero = BitVector.isAllZero a0_val

    let a1_arg = t.getArgument 1
    let a1_val = getArgumentValue t pVal pNumerals 1
    let a1_is_zero = BitVector.isAllZero a1_val

    let rhs_is_zero = BitVector.isAllZero rhs

    let a1_conc = a1_val.isConcreteValue
    let a0_conc = a0_val.isConcreteValue

    match (a0_conc, a1_conc) with
    | (true, true)   -> UNREACHABLE("Expected at least one non-concrete argument.")
    | (true, false)  -> // a0 * a1 = rhs --> a1 = rhs / a0
                        assert(not (t.isArgumentNumeral 1))
                        // CMW: UDiv uses the `hardware interpretation' of x/0 = -1,
                        // but in that case we don't actually know anything about a1_arg,
                        // so we need to add a special case for that.
                        if (a0_is_zero) then
                            if rhs_is_zero then
                                (0, BitVector.Invalid) // OK, nothing new
                            else
                                (a1_arg, BitVector.Invalid) // conflict; 0 * ? = 1 is unsat.
                        else
                            // a0 * ? = rhs can have multiple solutions for a1, if a0 and rhs
                            // are not relatively prime, so we just return "no news".
                            (0, BitVector.Invalid)
    | (false, true)  -> // a0 * a1 = rhs --> a0 = rhs / a1
                        assert(not (t.isArgumentNumeral 0))
                        if (a1_is_zero) then
                            if rhs_is_zero then
                                (0, BitVector.Invalid) // OK, nothing new
                            else
                                (a0_arg, BitVector.Invalid) // conflict; ? * 0 = 1 is unsat
                        else
                            // ? * a1 = rhs can have multiple solutions for a0, if a1 and rhs
                            // are not relatively prime, so we just return "no news".
                            (0, BitVector.Invalid)
    | (false, false) -> // CMW: There's no implication, as there are at least two
                        // solutions, even for prime numbers.
                        (0, BitVector.Invalid)


let ReverseUDiv (t:TheoryRelation) (rhs:BitVector) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    assert (numUnpropagatedVariables t pVal = 1)
    assert (rhs.isConcreteValue)

    // (budiv a0 a1) <- rhs

    let a0_arg = t.getArgument 0
    let a0_val = getArgumentValue t pVal pNumerals 0

    let a1_arg = t.getArgument 1
    let a1_val = getArgumentValue t pVal pNumerals 1

    let a1_conc = a1_val.isConcreteValue
    let a0_conc = a0_val.isConcreteValue

    match (a0_conc, a1_conc) with
    | (true, true)   -> UNREACHABLE("Expected at least one non-concrete argument.")

    | (true, false)  -> // a0 / a1 = rhs --> a1 = a0 / rhs
                        assert(not (t.isArgumentNumeral 1))
                        if BitVector.isAllZero a0_val then
                            (0, BitVector.Invalid) // conflict.
                        elif BitVector.isAllZero rhs then
                            (0, BitVector.Invalid) // conflict.
                        else
                            (a1_arg, BitVector.bvUDiv a0_val rhs)

    | (false, true)  -> if BitVector.isAllZero a1_val then
                            // The "hardware interpretation" for (bvudiv x 0) is #xffff
                            if BitVector.isAllOnes rhs then
                                (0, BitVector.Invalid) // nothing new.
                            else
                                (a0_arg, BitVector.Invalid) // conflict.
                        else
                            // a0 / a1 = rhs --> a0 = a1 * rhs
                            assert(not (t.isArgumentNumeral 0))
                            (a0_arg, BitVector.bvMul a1_val rhs)

    | (false, false) -> (0, BitVector.Invalid) // Nothing to propagate


let ReverseSDiv (t:TheoryRelation) (rhs:BitVector) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    assert (numUnpropagatedVariables t pVal = 1)
    assert (rhs.isConcreteValue)

    // (bsdiv a0 a1) <- rhs

    let a0_arg = t.getArgument 0
    let a0_val = getArgumentValue t pVal pNumerals 0
    let a0_n = if (snd a0_val.Bits.Head) = Bit.One then true else false
    let a0_vabs = if a0_n then BitVector.bvNegate a0_val else a0_val;

    let a1_arg = t.getArgument 1
    let a1_val = getArgumentValue t pVal pNumerals 1
    let a1_n = if (snd a1_val.Bits.Head) = Bit.One then true else false
    let a1_vabs = if a1_n then BitVector.bvNegate a1_val else a1_val;

    let a1_conc = a1_val.isConcreteValue
    let a0_conc = a0_val.isConcreteValue

    let res = match (a0_conc, a1_conc) with
                | (true, true)   -> UNREACHABLE("Expected at least one non-concrete argument.")

                | (true, false)  -> // a0 / a1 = rhs --> a1 = a0 / rhs
                                    assert(not (t.isArgumentNumeral 1))
                                    if BitVector.isAllZero a0_vabs then
                                        (0, BitVector.Invalid)
                                    elif BitVector.isAllZero rhs then
                                        (0, BitVector.Invalid)
                                    else
                                        (a1_arg, BitVector.bvSDiv a0_vabs rhs)
                | (false, true)  -> if BitVector.isAllZero a1_vabs then
                                        // The "hardware interpretation" for (bvudiv x 0) is #xffff
                                        if BitVector.isAllOnes rhs then
                                            (0, BitVector.Invalid) // OK, no new knowledge about a0
                                        else
                                            (a0_arg, BitVector.Invalid) // conflict.

                                    else
                                        // a0 / a1 = rhs --> a0 = a1 * rhs
                                        assert(not (t.isArgumentNumeral 0))

                                        // CMW: The following is not correct; there is often more
                                        // than one a0 that satisfies a0 = a1 * rhs, for instance,
                                        // when we have a0 / 2^n = 0, then all a0 up to 2^{n-1} work.
                                        // (a0_arg, BitVector.bvMul a1_vabs rhs)

                                        (0, BitVector.Invalid) // no new knowledge

                | (false, false) -> (0, BitVector.Invalid) // Nothing to propagate

    res


let ReverseURem (t:TheoryRelation) (rhs:BitVector) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    assert (numUnpropagatedVariables t pVal = 1)
    assert (rhs.isConcreteValue)

    // (burem a0 a1) <- rhs

    let a0_arg = t.getArgument 0
    let a0_val = getArgumentValue t pVal pNumerals 0

    let a1_arg = t.getArgument 1
    let a1_val = getArgumentValue t pVal pNumerals 1

    let a0_conc = a0_val.isConcreteValue
    let a1_conc = a1_val.isConcreteValue

    let res = match (a0_conc, a1_conc) with
                | (true, true)   -> UNREACHABLE("Expected at least one non-concrete argument.")
                | (true, false)  -> (0, BitVector.Invalid) // For now, we know nothing.
                | (false, true)  -> (0, BitVector.Invalid)
                | (false, false) -> (0, BitVector.Invalid) // Nothing to propagate

    res


let ReverseSRem (t:TheoryRelation) (rhs:BitVector) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    assert (numUnpropagatedVariables t pVal = 1)
    assert (rhs.isConcreteValue)

    // (bsrem a0 a1) <- rhs

    let a0_arg = t.getArgument 0
    let a0_val = getArgumentValue t pVal pNumerals 0

    let a1_arg = t.getArgument 1
    let a1_val = getArgumentValue t pVal pNumerals 1

    let a0_conc = a0_val.isConcreteValue
    let a1_conc = a1_val.isConcreteValue

    let res = match (a0_conc, a1_conc) with
                | (true, true)   -> UNREACHABLE("Expected at least one non-concrete argument.")
                | (true, false)  -> (0, BitVector.Invalid) // For now, we know nothing.
                | (false, true)  -> (0, BitVector.Invalid)
                | (false, false) -> (0, BitVector.Invalid) // Nothing to propagate

    res

let ReverseSMod (t:TheoryRelation) (rhs:BitVector) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) =
    assert (numUnpropagatedVariables t pVal = 1)
    assert (rhs.isConcreteValue)

    // (bvsmod a0 a1) <- rhs

    let a0_arg = t.getArgument 0
    let a0_val = getArgumentValue t pVal pNumerals 0

    let a1_arg = t.getArgument 1
    let a1_val = getArgumentValue t pVal pNumerals 1

    let a0_conc = a0_val.isConcreteValue
    let a1_conc = a1_val.isConcreteValue

    let res = match (a0_conc, a1_conc) with
                | (true, true)   -> UNREACHABLE("Expected at least one non-concrete argument.")
                | (true, false)  -> (0, BitVector.Invalid) // For now, we know nothing.
                | (false, true)  -> (0, BitVector.Invalid)
                | (false, false) -> (0, BitVector.Invalid) // Nothing to propagate

    res

let revEvaluate (t:TheoryRelation) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>)  =
    let mutable res : (Var * BitVector) = (0, BitVector.Invalid) // Unassigned variable, Reconstructed value

    match t.getRelationOP with
    | Z3_decl_kind.Z3_OP_EQ ->
        if t.hasBVOP then
            let rhs = getRhsValue t pVal pNumerals
            res <- match t.getBVOP with
                    | Z3_decl_kind.Z3_OP_CONCAT -> let lhs = getLhsValue t pVal pNumerals
                                                   (ReverseConcat t lhs rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_REPEAT -> (ReverseRepeat t rhs)
                    | Z3_decl_kind.Z3_OP_BADD -> (ReverseAdd t rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_BAND -> (ReverseAnd t rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_BOR -> (ReverseOr t rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_BXOR -> (ReverseXOr t rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_BNOT -> (ReverseNot t rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_EXTRACT -> (ReverseExtract t rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_BASHR -> (ReverseShift t true true rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_BLSHR -> (ReverseShift t true false rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_BSHL -> (ReverseShift t false false rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_BMUL -> (ReverseMul t rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_BUDIV -> (ReverseUDiv t rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_BSDIV -> (ReverseSDiv t rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_BUREM -> (ReverseURem t rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_BSREM -> (ReverseSRem t rhs pVal pNumerals)
                    | Z3_decl_kind.Z3_OP_BSMOD -> (ReverseSMod t rhs pVal pNumerals)
                    | _ -> NOT_YET_IMPLEMENTED(sprintf "Reverse equality evaluation for %s" (t.getBVOP.ToString()))
        else // Trivial equality, Boolean or BV.
            assert (t.isSimpleRelation)
            assert (numUnpropagatedVariables t pVal = 1)
            if t.isArgumentNumeral 0 then
                res <- (t.getArgument 1, getLhsValue t pVal pNumerals)
            else
                res <- (t.getArgument 0, getRhsValue t pVal pNumerals)
    | Z3_decl_kind.Z3_OP_ULEQ
    | Z3_decl_kind.Z3_OP_SLEQ
    | Z3_decl_kind.Z3_OP_ULT
    | Z3_decl_kind.Z3_OP_SLT
    | _ -> NOT_YET_IMPLEMENTED(sprintf "Reverse evaluation for %s" (t.getRelationOP.ToString()))

    (snd res).CheckInvariant()
    res

let evalArg (t:TheoryRelation) (pVal:Ref<BitVectorValuation>) (pNumerals:Ref<NumeralDB>) (i:int)  =
    if t.isArgumentNumeral i then
        (!pNumerals).getNumeral (abs (t.getArgument i))
    else
        (!pVal).getValue (t.getArgument i)


let getArgValuePairs (t:TheoryRelation) (mAss:Ref<BitVectorValuation>) (nums:Ref<NumeralDB>) =
    [for i in 0 .. t.numArguments - 1 do
        yield (t.getArgument i, evalArg t mAss nums i)]


let tGetNewValues (t:TheoryRelation) (mAss:Ref<BitVectorValuation>) (nums:Ref<NumeralDB>) =
    // Note that this function depends on partial assignments (BitVectorValuation) only.
    // It produces a pair (var, value) indicating a variable that has been assigned a new value.

    let (var, value) = if (!mAss).isAssigned t.getRhs then
                           (revEvaluate t mAss nums)
                       else
                           (t.getRhs, getLhsValue t mAss nums)

    if (var = 0) then
        (var, value)
    else
        // CMW: Intersection is done here, so whatever comes out of tGetNewValues
        // represents the final new value for var.
        if (value.isInvalid) then
            (var, value)
        else
            (var, BitVector.Intersect ((!mAss).getValue var) value)

