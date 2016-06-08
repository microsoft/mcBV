module Interval

open BitVector
open System.Numerics
open Microsoft.Z3
open Util

// Interval [lower,upper)
// CMW: I.e., lower is included, but upper is not.
// However, when constructing a new Interval, we always
// provide an _inclusive_ upper bound. From the outside,
// we don't care how Intervals are saved internally, but
// we always want to provide an inclusive upper bound,
// because it's easier to think inclusive.
type Interval private (l:BitVector, u:BitVector, fr:bool) =
    do assert(l.Length = u.Length)
    do assert(l.isConcreteValue)
    do assert(u.isConcreteValue)

    // CMW: The following are private; this is the internal state of
    // the Interval object, they are never leaked outside of this class.
    member private this.dimension = l.Length
    member private this.lower = l
    member private this.upper = u

    static member Empty (dim:int) = Interval(BitVector.AllOne dim, BitVector.AllOne dim, false)
    static member Full (dim:int) = Interval(BitVector.AllZero dim, BitVector.AllOne dim, true)

    // This is the constructor for the user; upper is inclusive.
    new(lower:BitVector, upper:BitVector) =
        assert (upper.Length = lower.Length)
        let dim = lower.Length
        let upper_plus_one = (BitVector.bvAdd upper (BitVector.One upper.Length))
        let l, u, f =
            if BitVector.bvEQ lower upper_plus_one then
                BitVector.AllZero dim, BitVector.AllOne dim, true // full
            elif BitVector.bvULT upper lower then
                upper, (BitVector.bvAdd lower (BitVector.One dim)), false // normalized
            else
                lower, upper_plus_one, false
        Interval(l, u, f)

    // This is the constructor for one-sided intervals, i.e., [bound, +oo] if
    // is_lower = true and [-oo, bound] otherwise.
    new(bound:BitVector, is_lower:bool) =
        if is_lower then
            Interval(bound, BitVector.AllOne bound.Length)
        else
            Interval(BitVector.AllZero bound.Length, bound)

    // CMW: What is the definition of "full" and "range" here?
    // Is "upperIsIncluded" a better description, or does it mean something else?
    member private this.fullRange = fr

    // CMW: The following three are functions to access the dimension, the lowest and
    // the uppermost element of the interval. The user thinks in inclusive upper
    // bounds and doesn't care what the internal representation is like.
    // So, we need to translate from exclusive to inclusive in this.Upper.
    member this.Dimension = this.dimension

    member this.Lower = assert(not this.isEmpty)
                        this.lower

    member this.Upper = if this.isFull then
                            BitVector.AllOne this.dimension
                        else
                            assert(not this.isEmpty)
                            BitVector.bvSub this.upper (BitVector.One this.dimension)

    member this.isEmpty = (not this.fullRange && BitVector.bvEQ this.lower this.upper)

    member this.isFull = (this.fullRange) // AZ: This or case causes problems on length one intervals. Singleton [0,0] is represented as [0,1] and not full, but it meets the conditions of the or case of the test.
                                          //|| ((BitVector.isAllZero this.lower) && (BitVector.isAllOnes this.upper))

    member this.containsZero = (BitVector.isAllZero this.lower)

    // CMW: I haven't checked/tested any of the functions below after changing
    // the interface of the Interval class.

    member this.Complement() = //AZ: this might still be buggy
        if this.isFull then
            Interval.Empty(this.dimension)
        elif this.isEmpty then
            Interval.Full(this.dimension)
        else
            Interval(this.upper, BitVector.bvSub this.Lower (BitVector.One this.Dimension)) //AZ: Note the small upper!


    override this.ToString() =
        if this.isEmpty then
            "]["
        else
            "[" + (this.Lower.ToString()) + ", " + (this.Upper.ToString()) + "]"

    member this.estimateSearchSpace() = if this.isFull then this.Dimension
                                        elif this.isEmpty then 0
                                        else
                                            let diff = BitVector.bvSub this.Upper this.Lower
                                            diff.Length - diff.LeadingZeros

    member this.AddConstantShift (b:BitVector) =
        Interval(BitVector.bvAdd this.lower b, BitVector.bvAdd this.upper b,this.fullRange)

    member this.SubstractConstantShift (b:BitVector) =
        Interval(BitVector.bvSub this.lower b, BitVector.bvSub this.upper b,this.fullRange)

    member this.isEqual (other:Interval) =
        this.dimension = other.dimension &&
        this.fullRange = other.fullRange &&
        BitVector.bvEQ this.upper other.upper &&
        BitVector.bvEQ this.lower this.lower

    static member iULEQ (lhs:Interval) (rhs:Interval) =
        // lhs <= rhs can only cut off one side of the interval
        // rhs cuts off lhs.upper
        // lhs cuts off rhs.lower
        let nLhsBounds =  if BitVector.bvUGT lhs.upper rhs.upper then
                             Interval(lhs.lower,rhs.upper,false)
                          else
                              lhs
        let nRhsBounds = if BitVector.bvUGT lhs.lower rhs.lower then
                             Interval(lhs.lower,rhs.upper,false)
                          else
                             rhs

        (nLhsBounds,nRhsBounds)

//    static member iEQ (a:Interval) (b:Interval) =
//       if BitVector.bvULEQ a.upper b.lower then Val.True
//       elif BitVector.bvULEQ b.upper a.lower then Val.False
//       else Val.U
//
//    static member iULEQ (a:Interval) (b:Interval) =
//        BitVector.bvEQ (a.getSingletonElement()) (b.getSingletonElement())

    member this.Normalize () =
        this.SubstractConstantShift this.lower

    member this.isSupersetRotational (sub:Interval) =
            if this.fullRange then
                true
            elif sub.fullRange then
                false
            elif sub.isEmpty then
                true
            else
                //Normalize the intervals
                let nThis = this.Normalize()
                let nSub = sub.SubstractConstantShift this.lower

                BitVector.bvULEQ nThis.lower nSub.lower &&
                BitVector.bvULEQ nSub.lower nSub.upper &&
                BitVector.bvULEQ nSub.upper this.upper

    member this.isSuperset (sub:Interval) =
            not this.isEmpty &&
            BitVector.bvULEQ this.Lower sub.Lower &&
            BitVector.bvULEQ sub.Upper this.Upper


    member this.isSubset(sup:Interval) =
        sup.isSuperset(this)


    member this.isSingleton =
        if this.isEmpty then //Necessarry check due to assertions in this.Lower and this.Upper
            false
        elif (BitVector.bvEQ this.Lower this.Upper) then
            true
        else
            false


    member this.Singleton =
        if this.isSingleton then
            this.lower
        else
            BitVector.Invalid


// CMW: The following functions are highly inefficient and only needed when
// rotational BVs are used.
//    member this.Size() =
//        if this.fullRange then
//            BitVector.AllOne(this.dimension).toBigInt()
//        else
//            let norm = this.Normalize()
//            let sz = (BitVector.bvSub norm.upper norm.lower)
//            sz.toBigInt()
//
//    member this.RotationalUnion (i:Interval) =
//        let isFullRange = this.isSuperset (i.Complement())
//
//        if isFullRange then
//            Interval(this.lower,this.lower,isFullRange)
//        else
//            let (lMin,lMax) = if BitVector.bvULEQ this.lower i.lower then
//                                    (this.lower,i.lower)
//                                else
//                                    (i.lower, this.lower)
//            let (uMin, uMax) = if BitVector.bvULEQ this.upper i.upper then
//                                    (i.upper, this.upper)
//                               else
//                                    (this.upper, i.upper)
//
//            let lowerUpper = Interval(lMin,uMax,false)
//            let upperLower = Interval(uMin,lMax,false)
//
//            if lowerUpper.Size() < upperLower.Size() then
//                lowerUpper
//            else
//                upperLower

    member this.Union (other:Interval) =
        let l = BitVector.Min this.Lower other.Lower
        let u = BitVector.Max this.Upper other.Upper
        let res = Interval(l,u)
        assert (res.isSuperset this && res.isSuperset other)
        res

    member this.Intersection (other:Interval) =
        if this.isEmpty then
            this
        elif other.isEmpty then
            other
        else
            let l = BitVector.Max this.lower other.lower
            let u = BitVector.Min this.Upper other.Upper
            if BitVector.bvULEQ l u then
                let res = Interval (l, u)
                assert (res.isSubset this && res.isSubset other)
                res
            else
                Interval.Empty(this.Dimension)


    member this.Contains (value:BitVector) =
        (BitVector.bvULEQ this.Lower value) &&
        (BitVector.bvULEQ value this.Upper)

    member this.RemoveValue (value:BitVector) =
        if BitVector.bvEQ value this.Lower then
            Interval (BitVector.bvAdd (this.Lower) (BitVector.One this.Dimension),this.Upper)
        elif BitVector.bvEQ value this.Upper then
            Interval (this.Upper, BitVector.bvSub (this.Upper) (BitVector.One this.Dimension))
        else
            this

    static member Add (a:Interval) (b:Interval) =
        assert (not a.isEmpty)
        assert (not b.isEmpty)
        assert (a.dimension = b.dimension)

        if a.fullRange then a
        elif b.fullRange then b
        elif a.isSingleton && b.isSingleton then
            let q = (BitVector.bvAdd a.lower b.lower)
            Interval(q, q)
        else
            let n = a.dimension
            let extra_bits = 1
            let big_al = (BitVector.bvConcat (BitVector.AllZero extra_bits) a.Lower)
            let big_au = (BitVector.bvConcat (BitVector.AllZero extra_bits) a.Upper)
            let big_bl = (BitVector.bvConcat (BitVector.AllZero extra_bits) b.Lower)
            let big_bu = (BitVector.bvConcat (BitVector.AllZero extra_bits) b.Upper)
            let big_l = (BitVector.bvAdd big_al big_bl)
            let big_u = (BitVector.bvAdd big_au big_bu)
            let big_l_overflow = not (BitVector.isAllZero (BitVector.bvExtract ((n+extra_bits)-1) n big_l))
            let big_u_overflow = not (BitVector.isAllZero (BitVector.bvExtract ((n+extra_bits)-1) n big_u))
            if not big_l_overflow && not big_u_overflow then
                let l = (BitVector.bvExtract (n-1) 0 big_l)
                let u = (BitVector.bvExtract (n-1) 0 big_u)
                Interval(l, u)
            else
                Interval.Full n

    static member Sub (a:Interval) (b:Interval) =
        assert (not a.isEmpty)
        assert (not b.isEmpty)
        assert (a.dimension = b.dimension)

        if a.fullRange then a
        elif b.fullRange then b
        elif a.isSingleton && b.isSingleton then
            let q = (BitVector.bvSub a.lower b.lower)
            Interval(q, q)
        else
            let n = a.dimension
            let extra_bits = 1
            let big_al = (BitVector.bvConcat (BitVector.AllZero extra_bits) a.Lower)
            let big_au = (BitVector.bvConcat (BitVector.AllZero extra_bits) a.Upper)
            let big_bl = (BitVector.bvConcat (BitVector.AllZero extra_bits) b.Lower)
            let big_bu = (BitVector.bvConcat (BitVector.AllZero extra_bits) b.Upper)
            let big_l = (BitVector.bvSub big_al big_bu)
            let big_u = (BitVector.bvSub big_au big_bl)
            let big_l_overflow = not (BitVector.isAllZero (BitVector.bvExtract ((n+extra_bits)-1) n big_l))
            let big_u_overflow = not (BitVector.isAllZero (BitVector.bvExtract ((n+extra_bits)-1) n big_u))
            if not big_l_overflow && not big_u_overflow then
                let l = (BitVector.bvExtract (n-1) 0 big_l)
                let u = (BitVector.bvExtract (n-1) 0 big_u)
                Interval(l, u)
            else
                Interval.Full n

    static member Mul (a:Interval) (b:Interval) =
        assert (not a.isEmpty)
        assert (not b.isEmpty)
        assert (a.dimension = b.dimension)
        if a.fullRange then a
        elif b.fullRange then b
        elif a.isSingleton && b.isSingleton then
            let q = (BitVector.bvMul a.lower b.lower)
            Interval(q, q)
        else
            let n = a.dimension
            let extra_bits = n
            let big_al = (BitVector.bvConcat (BitVector.AllZero extra_bits) a.Lower)
            let big_au = (BitVector.bvConcat (BitVector.AllZero extra_bits) a.Upper)
            let big_bl = (BitVector.bvConcat (BitVector.AllZero extra_bits) b.Lower)
            let big_bu = (BitVector.bvConcat (BitVector.AllZero extra_bits) b.Upper)
            let big_l = (BitVector.bvMul big_al big_bl)
            let big_u = (BitVector.bvMul big_au big_bu)
            let big_l_overflow = not (BitVector.isAllZero (BitVector.bvExtract ((n+extra_bits)-1) n big_l))
            let big_u_overflow = not (BitVector.isAllZero (BitVector.bvExtract ((n+extra_bits)-1) n big_u))
            if not big_l_overflow && not big_u_overflow then
                let l = (BitVector.bvExtract (n-1) 0 big_l)
                let u = (BitVector.bvExtract (n-1) 0 big_u)
                Interval(l, u)
            else
                Interval.Full n

    static member UDiv (a:Interval) (b:Interval) =
        assert (not a.isEmpty)
        assert (not b.isEmpty)
        assert (a.dimension = b.dimension)
        if a.fullRange then a
        elif b.fullRange then b
        elif (BitVector.isAllZero b.Upper) ||
             (BitVector.isAllZero b.Lower) then
             Interval.Full a.Dimension
        else
            // l and u can only be smaller than a.Lower and a.Upper,
            // so no overflow detection is necessary.
            let l = (BitVector.bvUDiv a.Lower b.Upper)
            let u = (BitVector.bvUDiv a.Upper b.Lower)
            Interval(l, u)

    static member SDiv (a:Interval) (b:Interval) =
        assert (not a.isEmpty)
        assert (not b.isEmpty)
        assert (a.dimension = b.dimension)
        if a.fullRange then a
        elif b.fullRange then b
        elif a.isSingleton && b.isSingleton then
            let q = (BitVector.bvSDiv a.lower b.lower)
            Interval(q, q)
        elif (BitVector.isAllZero b.Lower) ||
             (BitVector.isAllZero b.Upper) then
             Interval.Full a.Dimension
        else
            // CMW: The values within the interval are not ordered correctly
            // for signed division (e.g., Upper can be negative while Lower
            // is positive). To get around that, we could just translate
            // everything into an unsigned scale, run an unsigned divison,
            // and then translate the results back. For now, we just give
            // up and throw it away:
            Interval.Full a.Dimension

    static member Neg (a:Interval) =
        if a.fullRange then
            a
        else
            assert(false)
            // CMW: This is not necessarily the kind of "negation" we want.
            // It transforms [l, u] into [-u, -l], while often we will want [0, l] || [u, 1...1].
            // The latter will of course usually have to be approximated to the full interval
            // (or the exclusive-upper interval with negation, etc).
            let l = BitVector.bvNegate (a.Upper)
            let u = BitVector.bvAdd (BitVector.bvNegate a.lower) (BitVector.One a.dimension)
            Interval (l, u, false)

    static member Extract (u:int) (l:int) (b:Interval) =
        let nL = BitVector.bvExtract u l (b.Lower)
        let nU = BitVector.bvExtract u l (b.Upper)
        Interval(nL, nU)

    static member Concat (a:Interval) (b:Interval) =
        let nL = BitVector.bvConcat a.Lower b.Lower
        let nU = BitVector.bvConcat a.Upper b.Upper
        Interval(nL, nU)

    static member Equal (a:Interval) (b:Interval) =
        assert(a.dimension = b.dimension)
        BitVector.bvEQ a.lower b.lower && BitVector.bvEQ a.upper b.upper

    static member RLEToInterval (b: BitVector) =
        if not (b.isConcreteValue) then
            let l = b.Minimum
            let u = b.Maximum
            Interval(l, u)
        else
            Interval(b, BitVector.bvAdd b (BitVector.One b.Length), false)