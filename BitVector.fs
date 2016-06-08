module BitVector

open System
open System.Numerics
open System.Collections
open System.Collections.Generic

open Microsoft.Z3
open GlobalOptions
open Bit
open Util

type BString = (int*Bit) list

//BitVector Indexing
//|size - 1| size - 2 | ...| 2 | 1 | 0 |
//


type BitVector (size:int) =
    member val Length = size:int with get, set
    member val Bits = [(size, U)] with get, set

    // CMW: reactivate member val for isConcrete instead of member r.?
    member r.isConcreteValue = if not r.isValid then
                                    false
                               else
                                    not (List.exists (fun (n, b) -> n <= 0 || not (isConcrete b)) r.Bits)

    member r.isPartiallyConcreteValue = if not r.isValid then
                                            false
                                        else
                                            List.exists (fun (n, b) -> n <= 0 || (isConcrete b)) r.Bits

    member r.isFullyUndefined = (r.Bits.Length = 1 && (snd r.Bits.Head) = U)
    member r.isValid = r.Length <> 0
    member r.isInvalid = not r.isValid
    member r.markInvalid = r.Bits <- [(0, U)] ; r.Length <- 0


    static member Invalid =
        let res = (BitVector 0)
        assert not res.isValid
        res

    static member Copy (bv:BitVector) = 
        let cpy = BitVector bv.Length
        cpy.setBits bv.Bits
        cpy    

    member r.CheckInvariant () =
        if r.Length = 0 then
            assert (r.Bits.Length = 1)
            let cnt = (fst r.Bits.[0])
            let bit = (snd r.Bits.[0])
            assert (cnt = 0)
        else
            r.CheckNonbits()
            r.CheckZeros()
            r.CheckCompactness()

    member r.CheckCompactness () =
        // CMW: (snd x) <> N in the function definition below means bit-vectors should
        // never have any N bits in them. Unclear whether this is what we want.
        // AZ: Compactness should be that no two consecutive elements have the same Bit value
        //     I.e., (1, Zero) :: (1:Zero)::[] shouldn't occur, since (2,Zero)::[] is the
        //     cannon representation
        let r = (fst (List.fold (fun a x -> let q = (snd x) <> N &&
                                                    ((snd a) = N || (snd x) <> (snd a))
                                            ((q && (fst a)), (snd x)))
                                            (true, N)
                                            r.Bits))
        assert(r)

    member r.CheckZeros () =
        let r = (List.fold (fun a x -> a || (fst x) = 0) false r.Bits)
        assert(not r)

    member r.CheckNonbits () =
        let r = List.fold (fun a (i, x) -> (a || x = N) ) false r.Bits
        assert(not r)


    member r.SetFromBitTuples (l:(int * Bit) list) =
        let f = (fun (i, b) (acc : (int * ((int*Bit) list))) ->
            let curl = fst acc
            let curlist = snd acc
            match curlist with
            | h::t -> let h = curlist.Head
                      if b = (snd h) then
                          (curl + i, ((fst h) + i, b) :: curlist.Tail)
                      else
                          (curl + i, (List.append [(i, b)] curlist))
            | [] -> (i, [i, b]))
        let (length, bits) = List.foldBack f l (0, [])
        r.Length <- length
        r.Bits <- bits
        if (DBG) then r.CheckInvariant()
        r

    override r.ToString () =
        let mutable res = ""
        for i in 0 .. r.Bits.Length - 1 do
            if (fst r.Bits.[i]) = 0 then
                res <- res + "*" + (bitToString (snd r.Bits.[i])) + "*"
            else
                let (cnt, bit) = r.Bits.[i]
                if cnt > BV_SEGMENT_STRING_LIMIT then
                    let b = (bitToString bit)
                    res <- res + b + ".." + b
                else
                    for j in 1 .. cnt do
                        res <- res + (bitToString bit)
        res

    member r.setBits (bString: BString, ?isConcrete:bool) =
        r.Bits <- bString
        r.CheckInvariant()

    member r.isMoreConcreteThan (other:BitVector) =
        let i = (BitVector.Intersect r other) :> BitVector
        i.isValid && (BitVector.bvEQ r i) && not (BitVector.bvEQ i other)

    member r.Contains (value:BitVector) =
        (BitVector.Intersect r value).isValid

    member r.StartsWith (b:Bit) =
        r.Bits.Length > 0 &&
        (fst r.Bits.[0]) > 0 &&
        (snd r.Bits.[0]) = b

    member r.LeadingZeros =
        if r.isInvalid then
            0
        else
            match (snd r.Bits.Head) with
            | Bit.Zero -> (fst r.Bits.Head)
            | Bit.One -> 0
            | Bit.U -> 0 // CMW: Do we want to count this as "possibly 0"?
            | Bit.N -> assert(false) ; 0


    override this.GetHashCode () =
        let mutable res = this.Bits.Length
        for i in 0 .. this.Bits.Length - 1 do
            let bit = (snd this.Bits.[i])
            res <- (res <<< 1) ^^^ (match bit with U -> 3 | Bit.One -> 2 | _ -> 1)
        res

    override this.Equals obj =
        if obj = null then
            false
        else match obj with
             | :? BitVector as other ->
                if this.Length <> other.Length || this.Bits.Length <> other.Bits.Length then
                    false
                else
                    assert(this.Length = other.Length && this.Bits.Length = other.Bits.Length)
                    let mutable res = 0
                    let f = fun a (xi, xb) (yi, yb) -> a && xi = yi && xb = yb
                    List.fold2 f true this.Bits other.Bits
             | _ -> false

    interface IComparable<BitVector> with
        member this.CompareTo(other:BitVector) =
            if this.Length < other.Length then
                -1
            elif this.Length > other.Length then
                +1
            elif this.Bits.Length < other.Bits.Length then
                -1
            elif this.Bits.Length  > other.Bits.Length then
                +1
            else
                assert(this.Length = other.Length && this.Bits.Length = other.Bits.Length)
                let f = fun a (xi, xb) (yi, yb) -> if a <> 0 then a
                                                   elif xi < yi || xb < yb then -1
                                                   elif xi > yi || xb > yb then +1
                                                   else 0
                List.fold2 f 0 this.Bits other.Bits

    interface IComparable with
        member this.CompareTo obj =
            if obj = null then
                1
            else
                match obj with
                | :? BitVector as other -> (this :> IComparable<_>).CompareTo other
                | _ -> invalidArg "obj" "not a BitVector"

    interface IEquatable<BitVector> with
        member this.Equals (other:BitVector) =
            this.Equals other

    //TODO: Make binary search steps?
    static member int2BV (num:int64) (bvSize:int) =
        let mutable result = []
        let mutable counter = 1
        let mutable current = num &&& 1L

        for i in 1 .. bvSize - 1 do
            if num &&& (1L <<< i) = (current <<< i) then
                counter <- counter + 1
            else
                result <- (counter, bitFromInt current) :: result
                counter <- 1
                current <- 1L - current //Equivalent to Not, Numbers do not contain Undefined bits

        result <- (counter , bitFromInt current) :: result
        let bv = BitVector bvSize
        bv.Bits <- result
        bv.CheckInvariant()
        bv

    static member private bigint2BV (num:BigInteger) (bvSize:int) =
        let mutable result = []
        let mutable counter = 1
        let mutable current = num &&& BigInteger.One

        for i in 1 .. bvSize - 1 do
            if num &&& (BigInteger.One <<< i) = (current <<< i) then
                counter <- counter + 1
            else
                result <- (counter, bitFromBigInt current) :: result
                counter <- 1
                current <- BigInteger.One - current //Equivalent to Not, Numbers do not contain Undefined bits

        result <- (counter , bitFromBigInt current) :: result
        let bv = BitVector bvSize
        bv.Bits <- result
        bv.CheckInvariant()
        bv

    static member powerOf2 (m:int) (size:int) =
        assert (m < size)
        let res = BitVector size
        let pre = if size - m - 1 > 0 then [(size - m - 1,Zero)] else []
        let post = if m > 0 then [(m,Zero)] else []

        res.setBits (pre @ ((1,One)::post),true)
        res.CheckInvariant()
        res

    static member powerOf2Minus1 (m:int) (size:int) =
        assert ( 0 < m && m < size )
        let res = BitVector size
        let pre = if m - size > 1 then [(m-size,Zero)] else []
        res.setBits (pre @ [(m - 1,One)],true)
        res.CheckInvariant()
        res

    static member BitOne =
        let res = BitVector 1
        res.setBits ([(1,One)], true)
        res

    static member BitZero =
        let res = BitVector 1
        res.setBits ([(1,Zero)], true)
        if (DBG) then res.CheckInvariant()
        res

    static member BitVectorFromExpr (e:Expr) =
        assert (e.FuncDecl.DeclKind = Z3_decl_kind.Z3_OP_BNUM)
        let bvNum = e :?> BitVecNum
        let res = BitVector.bigint2BV bvNum.BigInteger (int bvNum.SortSize)
        res.CheckInvariant()
        res


    member private r.toBigInt () =
        assert (r.isConcreteValue)
        assert (r.Length > 0)
        let mutable res = BigInteger.Zero
        let mutable pos = r.Length - 1


        for el in r.Bits do
            match el with
            | (n, One) ->
                for k in  0 .. n - 1 do
                    res <- res + (BigInteger.One <<< (pos - k) )
                pos <- pos - n
            | (n, Zero) -> pos <- pos - n
            | _ -> printf "Error in BitVector.toInt()"
                   assert (false)
        res

    member private r.toBigIntEncoding () =
        assert (r.Length > 0)
        let mutable res = BigInteger.Zero
        let mutable pos = r.Length - 1

        for el in r.Bits do
            match el with
            | (n, One) ->
                for k in  0 .. n - 1 do
                    res <- res + (BigInteger.One <<< (pos - k) )
                pos <- pos - n
            | (n, U) ->
                for k in  0 .. n - 1 do
                    res <- res + (BigInteger.One <<< (r.Length + pos - k) )
                pos <- pos - n
            | (n, Zero) -> pos <- pos - n
            | _ -> printf "Error in BitVector.toInt()"
                   assert (false)
        res


    static member padHighest (bit:Bit) (n:int) (bv:BitVector) =
        assert (bv.Length > 0 && n > 0)
        let res = BitVector (n + bv.Length)
        let (hCnt, hBit) = bv.Bits.Head
        let newHighest = if hBit = bit then
                            (n + hCnt, bit)
                         else
                            (n, bit)
        if fst newHighest =  n then
            res.setBits (newHighest::bv.Bits, bv.isConcreteValue)
        else
            res.setBits (newHighest::(bv.Bits.Tail), bv.isConcreteValue)
        res.CheckInvariant()
        if (DBG) then res.CheckInvariant()
        res

    static member padLowest (bit:Bit) (n:int) (bv:BitVector) =
        assert (bv.Length > 0 && n >= 0)
        let res = BitVector (n + bv.Length)
        let mutable revBits = List.rev bv.Bits
        let (lCnt,lBit) = revBits.Head
        if (bit = lBit) then
            res.setBits (List.rev ((lCnt + n, lBit)::(revBits.Tail)), bv.isConcreteValue)
        else
            res.setBits (List.rev ((n,bit)::revBits), bv.isConcreteValue)
        if (DBG) then res.CheckInvariant()
        res

    static member padHighestZero n bv =
        BitVector.padHighest Zero n bv

    static member padHighestOne n bv =
        BitVector.padHighest One n bv

    static member padHighestZeroToLen (len:int) (bv:BitVector) =
        assert (len >= bv.Length)
        BitVector.padHighest Zero (len - bv.Length) bv

    static member padHighestUToLen (len:int) (bv:BitVector) =
        assert (len >= bv.Length)
        BitVector.padHighest U (len - bv.Length) bv


    static member padHighestOneToLen (len:int) (bv:BitVector) =
        assert (len >= bv.Length)
        BitVector.padHighest One (len - bv.Length) bv

    static member padLowestZero n bv =
        BitVector.padLowest Zero n bv

    static member padLowestOne n bv =
        BitVector.padLowest One n bv

    static member padLowestZeroToLen (len:int) (bv:BitVector) =
        assert (len >= bv.Length)
        BitVector.padLowest Zero (len - bv.Length) bv

    static member padLowestOneToLen (len:int) (bv:BitVector) =
        assert (len >= bv.Length)
        BitVector.padLowest One (len - bv.Length) bv


    static member TakeHighest (k:int) (bv:BitVector) =
        assert (k <= bv.Length)
        let mutable srcBits = bv.Bits

        if k = bv.Length then
            bv
        elif k > bv.Length then
            UNREACHABLE("Unexpected extraction")
        else
            let mutable bits = []
            let mutable len = 0
            while len < k do
                let cnt = fst srcBits.Head
                let bit = snd srcBits.Head
                let nbits = if len + cnt > k then k - len else cnt
                len <- len + nbits
                bits <- List.append bits [(nbits, bit)]
                srcBits <- srcBits.Tail
            assert(len = k)
            let mutable res = BitVector.Invalid
            res <- (res.SetFromBitTuples bits)
            res.CheckInvariant()
            res

    static member TakeLowest (k:int) (bv:BitVector) =
        assert (k <= bv.Length)

        if k = bv.Length then
            bv
        elif k > bv.Length then
            UNREACHABLE("Illegal extraction")
        else
            let mutable srcBits = (List.rev bv.Bits)
            let mutable bits = []
            let mutable len = 0
            while len < k do
                let cnt = fst srcBits.Head
                let bit = snd srcBits.Head
                let nbits = if len + cnt > k then k - len else cnt
                len <- len + nbits
                bits <- (nbits, bit) :: bits
                srcBits <- srcBits.Tail
            assert(len = k)
            let mutable res = BitVector.Invalid
            res <- (res.SetFromBitTuples bits)
            res.CheckInvariant()
            res


    static member DropHighest (k:int) (bv:BitVector) =
        if k = 0 then
            bv
        elif k >= bv.Length then
            // CMW: This would create an empty bit-vector BitVector(0),
            // which seems to be undesirable judging by other pieces of code.
            assert(false)
            BitVector (0)
        else
            assert (0 < k && k < bv.Length)

            let res = BitVector (bv.Length - k)
            let mutable srcBits = bv.Bits
            let mutable resBits = []
            let mutable dropped = 0
            let mutable bit = N

            while dropped < k do
                let nhead = fst srcBits.Head
                bit <- snd srcBits.Head
                if (dropped + nhead > k) then
                    let ndrop = k - dropped
                    dropped <- dropped + ndrop
                    srcBits <- (nhead-ndrop, bit)::srcBits.Tail
                else
                    dropped <- dropped + nhead
                    srcBits <- srcBits.Tail

            res.setBits srcBits
            res.CheckInvariant()
            res

    static member meld (nonConcrete:BitVector) (concrete:BitVector) =
        // Sequentially replace U bits in nonConcrete with bits from concrete.
        assert (not nonConcrete.isConcreteValue)
        assert (concrete.isConcreteValue)
        assert (nonConcrete.estimateSearchSpace() = concrete.Length)

        let mutable src = concrete.Bits
        let mutable rev_res = []

        let mutable last_cnt = 0
        let mutable last_bit = N
        let mutable cncrete_cnt = 0
        let mutable bit = N

        for p in nonConcrete.Bits do
            match p with
            | (cnt, U) ->
                let mutable todo = cnt

                while todo > 0 do
                    assert(cncrete_cnt >= 0)
                    assert(cncrete_cnt = 0 || bit <> N)

                    if cncrete_cnt = 0 then
                        cncrete_cnt <- fst src.Head
                        bit <- snd src.Head
                        src <- src.Tail

                    // Determine how many concrete bits we are instantiating, and if any are left over.
                    let inst_cnt = if cncrete_cnt > todo then
                                        cncrete_cnt <- cncrete_cnt - todo
                                        todo
                                   else
                                        let c = cncrete_cnt
                                        cncrete_cnt <- 0
                                        c

                    // If the bit matches the previous one, increase its count
                    // otherwise,  insert last bit-cnt pair and record current pair as the last
                    if last_bit = bit then
                        last_cnt <- last_cnt + inst_cnt
                    else
                        if last_cnt > 0 then
                            assert (last_bit <> N)
                            rev_res <- (last_cnt, last_bit) :: rev_res
                        last_bit <- bit
                        last_cnt <- inst_cnt

                    // Record how many bits we've instantiated this iteration
                    todo <- todo - inst_cnt

            | (cnt, One)
            | (cnt, Zero) ->
                let bit = snd p

                if last_bit = bit then
                    last_cnt <- last_cnt + cnt
                else
                    if last_cnt > 0 then
                        assert (last_bit <> N)
                        rev_res <- (last_cnt, last_bit) :: rev_res
                    last_bit <- bit
                    last_cnt <- cnt
            | (_,N)-> assert(false)

        if last_cnt > 0 then
            rev_res <- (last_cnt, last_bit) :: rev_res

        let res = BitVector.Invalid.SetFromBitTuples (List.rev rev_res)
        res.CheckInvariant()
        assert (res.Length = nonConcrete.Length)
        //assert (BitVector.bvEQ (BitVector.Unify res nonConcrete) nonConcrete)
        res


    // Changes #infix_len bits starting from #start_position
    // If strictly flag is true, then it changes only the U bits (if any)
    // otherwise, it will overwrite the concrete bits in the affected range.
    static member changeBits (strictly:bool) (set_to:Bit) (bv:BitVector) (start_position:int) (infix_len:int) =
        assert ( start_position + 1 >= infix_len) //From any given position, we can change at most that many bits plus one (due to counting from zero)
        assert ( 0 <= start_position && start_position < bv.Length)
        assert (infix_len > 0)

        let prefix_len = bv.Length - 1 - start_position
        let suffix_len = bv.Length - prefix_len - infix_len
        assert (prefix_len >= 0)
        assert (suffix_len >= 0)
        assert (bv.Length = prefix_len + infix_len + suffix_len)
        assert (not strictly || set_to = One || set_to = Zero)

        let prefix = if prefix_len > 0 then
                        Some (BitVector.TakeHighest prefix_len bv)
                     else
                        None

        let infix_o = BitVector.TakeHighest infix_len (BitVector.DropHighest prefix_len bv)

        let infix = if not strictly  then
                        match set_to with
                        | Bit.One -> BitVector.AllOne infix_len
                        | Bit.Zero -> BitVector.AllZero infix_len
                        | Bit.U -> BitVector infix_len
                        | _ -> UNREACHABLE "Introducing N bit"
                    else
                        match set_to with
                        | Bit.One -> infix_o.Maximum
                        | Bit.Zero -> infix_o.Minimum
                        | Bit.U -> infix_o
                        | _ -> UNREACHABLE "Introducing N bit"


        let suffix = if suffix_len > 0 then
                        Some (BitVector.DropHighest (prefix_len + infix_len) bv)
                        else
                        None

        let highEnd = if prefix.IsSome then
                        BitVector.bvConcat prefix.Value infix
                        else
                        infix
        let res = if suffix.IsSome then
                        BitVector.bvConcat highEnd suffix.Value
                    else
                        highEnd
        res

    static  member  private changeKthBit (bv:BitVector) (k:int) (cond) (init)=
        assert (0 <= k && k < bv.Length)

        let suffix = BitVector.DropHighest (bv.Length - (k + 1) ) bv
        let kthBit = snd suffix.Bits.Head

        if cond kthBit then
          let prefix = if bv.Length - 1 - k > 0 then
                            Some (BitVector.TakeHighest  (bv.Length - 1 - k) bv)
                       else
                            None
          let infix = init
          let suffix = if k > 0 then
                         Some (BitVector.DropHighest (bv.Length - k) bv)
                       else
                         None
          let res = (   match  prefix with
                        | Some p -> BitVector.bvConcat p
                        | None -> fun x -> x )
                    <|
                    (   match  suffix with
                        | Some s -> BitVector.bvConcat infix s
                        | None ->  infix)
          Some res
        else
           None

    static member changeKthBitDownwards (bv:BitVector) (k:int)=
        assert (bv.isConcreteValue)
        BitVector.changeKthBit bv k (fun (x:Bit) -> x = One) (BitVector.BitZero)

    static member changeKthBitToU (bv:BitVector) (k:int) =
        BitVector.changeKthBit bv k (fun (x:Bit) -> x = Zero || x = One) (BitVector 1)

    static member changeKthBitUpwards (bv:BitVector) (k:int) =
        assert (bv.isConcreteValue)
        BitVector.changeKthBit bv k (fun (x:Bit) -> x = Zero) (BitVector.BitOne)

    static member getCommonPrefix (aBV:BitVector) (bBV:BitVector) =
        assert(aBV.Length > 0 && bBV.Length > 0)
        assert(aBV.Length = bBV.Length)
        assert(aBV.Bits <> [] && bBV.Bits <> [])
        assert(aBV.isConcreteValue)
        assert(bBV.isConcreteValue)

        let mutable a = aBV.Bits
        let mutable b = bBV.Bits
        let mutable res = []

        let mutable total = aBV.Length
        let mutable todo = aBV.Length
        let mutable did = 0
        let mutable finished = false //AZ: This will be set to false if an N bit appears in the result
        while todo > 0  && not finished do
            let mutable (aCnt, aBit) = a.Head
            let mutable (bCnt, bBit) = b.Head
            assert(aBit <> N && bBit <> N)

            let curCnt = min aCnt bCnt

            match (aBit, bBit) with
            | (One,One)
            | (Zero,Zero) -> res <- List.append res [(curCnt, aBit)]
                             todo <- todo - curCnt
                             did <- did + curCnt
            | (N,_)
            | (_,N) -> assert(false)
            | _ ->
                res <- List.append res [(todo, U)]
                did <- did + todo
                todo <- 0
                finished <- true

            if (aCnt = curCnt) then a <- a.Tail else a <- (aCnt - curCnt, aBit)::a.Tail
            if (bCnt = curCnt) then b <- b.Tail else b <- (bCnt - curCnt, bBit)::b.Tail


        assert(todo = 0 && did = total)

        let r = BitVector.Invalid.SetFromBitTuples res
        if (DBG) then r.CheckInvariant()
        r

    // Takes a binary bit operation and applies it to two bit-vectors
    // bitOp should return N bit if an error occurs,
    // Bitwise whould return a zero length (non) Bitvector then.
    static member Bitwise (bitOp: Bit -> Bit -> Bit) (aBV:BitVector) (bBV:BitVector) =

        assert(aBV.Length > 0 && bBV.Length > 0)
        assert(aBV.Length = bBV.Length)
        assert(aBV.Bits <> [] && bBV.Bits <> [])

        let mutable a = aBV.Bits
        let mutable b = bBV.Bits
        let mutable res = []

        let mutable total = aBV.Length
        let mutable todo = aBV.Length
        let mutable did = 0
        let mutable valid = true //AZ: This will be set to false if an N bit appears in the result
        while todo > 0  && valid do
            let mutable (aCnt, aBit) = a.Head
            let mutable (bCnt, bBit) = b.Head
            assert(aBit <> N && bBit <> N)

            let curCnt = min aCnt bCnt
            let curBit = bitOp aBit bBit

            if curBit = N then
                valid <- false //Result is invalid, stop the computation

            res <- List.append res [(curCnt, curBit)]

            if (aCnt = curCnt) then a <- a.Tail else a <- (aCnt - curCnt, aBit)::a.Tail
            if (bCnt = curCnt) then b <- b.Tail else b <- (bCnt - curCnt, bBit)::b.Tail
            todo <- todo - curCnt
            did <- did + curCnt

        assert( (todo = 0 && did = total) || not valid)
        if valid then
            let r = BitVector.Invalid.SetFromBitTuples res
            if (DBG) then r.CheckInvariant()
            r
        else
            BitVector.Invalid

    static member Intersect (aBV:BitVector) (bBV:BitVector) =
        BitVector.Bitwise Intersect aBV bBV

    static member bvAND (aBV:BitVector) (bBV:BitVector) =
        BitVector.Bitwise And aBV bBV

    static member revBvAND (aBV:BitVector) (bBV:BitVector) =
        BitVector.Bitwise (fun a r -> if a = Zero then Bit.U else r) aBV bBV

    static member revBvOr (aBV:BitVector) (bBV:BitVector) =
        BitVector.Bitwise (fun x y -> if ((x = One && y = Zero) || (x = Zero && y = One)) then Bit.One else Bit.U) aBV bBV

    static member revBvXOr (aBV:BitVector) (bBV:BitVector) =
        BitVector.Bitwise (fun x y -> if ((x = Zero && y = One) || (x = One && y = Zero)) then Bit.One
                                      elif ((x = Zero && y = Zero) || (x = One && y = One)) then Bit.Zero
                                      else Bit.U) aBV bBV

    static member bvOR (aBV:BitVector) (bBV:BitVector) =
        BitVector.Bitwise Or aBV bBV

    static member bvXOR (aBV:BitVector) (bBV:BitVector) =
        BitVector.Bitwise XOr aBV bBV

    member r.estimateSearchSpace () =
        List.fold (fun a pair -> if (snd pair) = Bit.U then a + (fst pair) else a) 0 r.Bits

    member r.Minimum =
        assert(r.Length <> 0)
        if r.isConcreteValue then
            r
        else
            let f = (fun (i:int, x:Bit) (acc:(int * Bit) list) ->
                match x with
                | U    -> if (acc.Length > 0) && ((snd acc.Head) = Zero) then
                              ((fst acc.Head) + i, Zero) :: acc.Tail
                          else
                              (i, Zero) :: acc
                | Zero -> if (acc.Length > 0) && ((snd acc.Head) = Zero) then
                              ((fst acc.Head) + i, Zero) :: acc.Tail
                          else
                              (i, Zero) :: acc
                | _ -> (i, x) :: acc)
            let new_rbits = List.foldBack f r.Bits []
            let res = BitVector r.Length
            res.setBits new_rbits //r.Bits <- new_rbits
            if (DBG) then res.CheckInvariant()
            assert (res.isConcreteValue)
            res

    member r.Maximum =
        assert(r.Length <> 0)
        if r.isConcreteValue then
            r
        else
            let f = (fun (i:int, x:Bit) (acc:(int * Bit) list) ->
                match x with
                | U    -> if (acc.Length > 0) && ((snd acc.Head) = One) then
                              ((fst acc.Head) + i, One) :: acc.Tail
                          else
                              (i, One) :: acc
                | One  -> if (acc.Length > 0) && ((snd acc.Head) = One) then
                              ((fst acc.Head) + i, One) :: acc.Tail
                          else
                              (i, One) :: acc
                | _ -> (i, x) :: acc)
            let new_rbits = List.foldBack f r.Bits []
            let res = BitVector r.Length
            res.setBits new_rbits //r.Bits <- new_rbits
            if (DBG) then res.CheckInvariant()
            assert (res.isConcreteValue)
            res

    member r.lowestSignedValueFromSet () =
        if r.isConcreteValue then
            r
        elif snd r.Bits.Head = U then
            let (cnt,bit) = r.Bits.Head
            let res = BitVector r.Length
            let bits = if cnt > 1 then
                          (1,One)::(cnt-1,U)::r.Bits.Tail
                       else
                           (1,One)::r.Bits.Tail
            res.setBits (List.map (fun (x,y) -> if y = U then (x,Zero) else (x,y)) bits, true)
            if (DBG) then res.CheckInvariant()
            res
        else
            let res = BitVector r.Length
            res.setBits ((List.map (fun (x,y) -> if y = U then (x,Zero) else (x,y)) r.Bits), true)
            if (DBG) then res.CheckInvariant()
            res

    member r.highestSignedValueFromSet () =
        if r.isConcreteValue then
            r
        elif snd r.Bits.Head = U then
            let (cnt,bit) = r.Bits.Head
            let res = BitVector r.Length
            let bits = if cnt > 1 then
                          (1,Zero)::(cnt-1,U)::r.Bits.Tail
                       else
                           (1,Zero)::r.Bits.Tail
            res.setBits (List.map (fun (x,y) -> if y = U then (x,Zero) else (x,y)) bits, true)
            if (DBG) then res.CheckInvariant()
            res
        else
            let res = BitVector r.Length
            res.setBits ((List.map (fun (x,y) -> if y = U then (x, One) else (x,y)) r.Bits), true)
            if (DBG) then res.CheckInvariant()
            res

    //member r.medUpValueFromSet () = Alternate zeroes and ones from undef to undef bit, maybe if done in chunks?
    // This will end up exploding the encoding

    static member bvShiftLeftInt (bv:BitVector) (n:int) =
        assert (n > 0)
        let mutable res = BitVector bv.Length
        for i in 0 .. n - 1 do
            match bv.Bits.Head with
            | (n, b) when n > 1 -> res.Bits <- (n-1, b) :: bv.Bits.Tail
            | (n, b) when n = 1 -> res.Bits <- bv.Bits.Tail
            | _ -> ()
        let last = res.Bits.Item (res.Bits.Length - 1)
        match last with
        | (n, Zero) -> res.Bits <- List.rev ((n+1, Zero) :: (List.rev res.Bits).Tail)
        | _ -> res.Bits <- List.append res.Bits [(1, Zero)]
        res.CheckInvariant()
        res

    static  member private bvShiftSkeleton (shiftF) (bv:BitVector) (n:BitVector) =
        if not n.isConcreteValue then
            BitVector bv.Length // Undef.
        else
            let mutable pos = n.Length
            let mutable res = bv
            for (cnt, bit) in n.Bits do
                match bit with                
                | One ->
                    assert (pos >= cnt)
                    //AZ: We only care about stretches of ones and their value is 2^(fst_pos + 1) - 2 ^ last_pos
                    res <- shiftF res ( (1 <<< pos) - (1 <<< (pos - cnt)))
                | Zero ->  ()       
                | _ -> UNREACHABLE("bvAShiftRight: U or N bit in the shift operand")
                
                pos <- pos - cnt     
            if (DBG) then res.CheckInvariant()
            res


    static member _bvShiftLeft (bv:BitVector) (n:int) =
        assert ( 0 <= n )
        if n = 0 then
            bv
        elif n >= bv.Length then
            BitVector.AllZero bv.Length
        else
            assert(n <=System.Int32.MaxValue)
            let res = BitVector.padLowestZeroToLen bv.Length (BitVector.DropHighest n bv)
            if (DBG) then res.CheckInvariant()
            res

    static member bvShiftLeft (bv:BitVector) (n:BitVector) =
        if BitVector.isAllZero bv || BitVector.isAllZero n then
            bv
        else
            BitVector.bvShiftSkeleton (BitVector._bvShiftLeft) bv n

    static member _bvLShiftRight (bv:BitVector) (n:int) =
        assert ( 0 <= n && n <= bv.Length)

        if n = 0 then
            bv
        elif n >= bv.Length then
            BitVector.AllZero bv.Length
        else
            assert(n <=System.Int32.MaxValue)
            let res = BitVector.padHighestZeroToLen bv.Length (BitVector.TakeHighest (bv.Length - n) bv)
            if (DBG) then res.CheckInvariant()
            res
    
    static member bvLShiftRight (bv:BitVector) (n:BitVector) =
        if BitVector.isAllZero bv || BitVector.isAllZero n then
            bv
        else
            BitVector.bvShiftSkeleton (BitVector._bvLShiftRight) bv n
        

    static member _bvAShiftRight (bv:BitVector) (n:int) =
        assert ( 0 <= n && n <= bv.Length)
        if n = 0 then
            bv
        elif n >= bv.Length then
            let res = BitVector bv.Length
            res.Bits <- [(bv.Length, (snd bv.Bits.Head))]
            res
        else
            assert(n <=System.Int32.MaxValue)
            let bit = snd (bv.Bits.Head)
            let res = match bit with
                      | One -> BitVector.padHighestOneToLen bv.Length (BitVector.TakeHighest (bv.Length - n) bv)
                      | Zero -> BitVector.padHighestZeroToLen bv.Length (BitVector.TakeHighest (bv.Length - n) bv)
                      | U ->  BitVector.padHighestUToLen bv.Length (BitVector.TakeHighest (bv.Length - n) bv)
                      | _ -> UNREACHABLE "N bit in a BV"                      
            if (DBG) then res.CheckInvariant()
            res
    
    
           
    static member bvAShiftRight (bv:BitVector) (n:BitVector) =
        if  BitVector.isAllOnes bv || BitVector.isAllZero bv || BitVector.isAllZero n then
            bv
        else
            BitVector.bvShiftSkeleton (BitVector._bvAShiftRight) bv n

    static member bvExtract (u:int) (l:int) (aBV:BitVector) =
        assert (0 <= l)
        assert (l <= u) //Zero extractions are disallowed
        assert (u <= aBV.Length)

        let res = BitVector.TakeHighest (u - l + 1) (BitVector.DropHighest (aBV.Length - u - 1) aBV)
        if (DBG) then res.CheckInvariant()
        res

    static member bvConcat (aBV:BitVector) (bBV:BitVector) =
        assert (aBV.Length > 0 && bBV.Length > 0)
        let a = aBV.Bits
        let b = bBV.Bits
        let mutable res = BitVector.Invalid //result in reverse order

        res.Bits <- []

        let (bFirstCnt, bFirstBit) = b.Head
        let (aLastCnt, aLastBit) = (List.rev a).Head

        if aLastBit = bFirstBit then
            let fuseEl = (aLastCnt + bFirstCnt, aLastBit)
            res.Bits <- (List.rev (List.rev a).Tail) @ (fuseEl :: b.Tail)
        else
            res.Bits <- a @ b

        res.Length <- aBV.Length + bBV.Length
        res.CheckInvariant()
        res

    static member bvRepeat (n:int) (aBV:BitVector) =
        assert (n > 0) //Q: Repeat 1 should be simplified?
        let a = aBV.Bits
        let mutable res = BitVector.Invalid
        let (firstCnt, firstBit) = a.Head
        let revA = List.rev a
        let (lastCnt, lastBit) = revA.Head

        res.Bits <- []

        if a.Length = 1 then
            res.Bits <- ( n * firstCnt, firstBit) :: res.Bits
        else if firstBit = lastBit then
            //|first|middle|last|first|middle|last|first|middle|last|
            //|first|middle|   fuse   |middle|   fuse   |    tail   |
            let fuseEl = (firstCnt + lastCnt, firstBit)
            let middle = List.rev (revA.Tail)
            res.Bits <- a.Tail

            for i in 1 .. n - 1 do
                res.Bits <- fuseEl :: res.Bits
                res.Bits <- middle @ res.Bits

            res.Bits <- a.Head :: res.Bits
        else
            for i in 1 .. n do
                res.Bits <- a @ res.Bits

        res.Length <- aBV.Length * n
        res.CheckInvariant()
        res

    static member bvNot (aBV:BitVector) =
        let res = BitVector aBV.Length
        res.setBits (List.map (fun (x,y) -> (x, Not y)) aBV.Bits, aBV.isConcreteValue)
        res.CheckInvariant()
        res

    static member bvSub aBV bBV =
       BitVector.bvAdd aBV (BitVector.bvNegate bBV)

    //BVADD in triLogic: a,b,c \in {One,Zero,U}
    // bvAdd (len, a) (len, b) c
    //Group I: a = not b, c <> U
    // c' = c, r = (len, not c) //Can be unified with Group IV
    //Group II: a = b, c = Not a | U
    // c' = a, r = [(len-1, a); (1,c)]
    //Group III: a = b = c
    // c' = c, r = c
    //Group IV: exactly one a or b is U, c <> U
    // c' = c, r = (len, U)
    //Group V: rest
    // c' = U, r = (len, U)
    static member bvAdd (aBV:BitVector) (bBV:BitVector) =
        assert (aBV.Length = bBV.Length)

        let resLen = aBV.Length

        let mutable revARem = List.rev aBV.Bits
        let mutable revBRem = List.rev bBV.Bits

        let mutable (aCnt,aBit) = revARem.Head
        revARem <- revARem.Tail
        let mutable (bCnt,bBit) = revBRem.Head
        revBRem <- revBRem.Tail

        let mutable c = Zero
        let mutable rbits = []
        let mutable curPos = 0
        let mutable (prevCnt, prevBit) = (0, N)
        let mutable (curCnt, resBit) = (0, N)

        while curPos < resLen do
            let len = (min aCnt bCnt)
            //Bulk addition
            match (aBit, bBit, c) with
            //Group I
            | ( One, Zero, Zero) | (Zero, One, Zero)
            | ( Zero, One, One)  | ( One, Zero, One) ->
                // c' = c, r = (len, One)

                //  One + Zero + Zero =  One, c = Zero
                // Zero +  One + Zero =  One, c = Zero
                // Zero +  One +  One = Zero, c =  One
                //  One + Zero +  One = Zero, c =  One
                resBit <- Not c
                if resBit = prevBit then
                    prevCnt <- prevCnt + len
                else
                    if prevCnt > 0 then
                        rbits <- (prevCnt, prevBit)::rbits
                    prevCnt <- len
                    prevBit <- resBit
            //Group II:
            | (Zero, Zero, One) | (One, One, Zero)
            | (Zero, Zero, U)   | (One, One, U) ->
                // Zero + Zero +  One =  One, c = Zero
                //  One +  One + Zero = Zero, c =  One
                // Zero + Zero +   U  =   U , c = Zero
                //  One +  One +   U  =   U , c =  One
                // c = aBit
                //  [(len-1, a); (1,c)]
                // assert (aBit = bBit)
                // assert (aBit <> c)
//                if c = prevBit then
//                    prevCnt <- prevCnt + 1

                if len > 1 then // there will be an element with a bit in the list, a <> c
                    if c = prevBit then
                       rbits <- (prevCnt + 1, prevBit)::rbits
                    elif prevCnt > 0 then
                       rbits <- (1,c)::(prevCnt, prevBit)::rbits
                    else
                       rbits <- (1,c)::rbits

                    c <- aBit
                    prevCnt <- len - 1
                    prevBit <- aBit
                else // c becomes the prevElement
                    if c <> prevBit then
                        if prevCnt > 0 then
                            rbits <- (prevCnt, prevBit)::rbits
                        prevCnt <- 1
                    else
                        prevCnt <- prevCnt + 1
                    prevBit <- c
                    c <- aBit
            //Group III:
            | (Zero, Zero, Zero) | (One, One, One) | (U, U, U) ->
                // c' = c, r = (len, aBit)
                resBit <- aBit
                if resBit = prevBit then
                    prevCnt <- prevCnt + len
                else
                    if prevCnt > 0 then
                        rbits <- (prevCnt, prevBit)::rbits
                    prevCnt <- len
                    prevBit <- resBit
            //Group IV
            | (Zero, U, Zero) | (One, U, One)
            | (U, Zero, Zero) | (U, One, One) ->
               // c' = c, r = (len, U)
               resBit <- U
               if resBit = prevBit then
                    prevCnt <- prevCnt + len
               else
                    if prevCnt > 0 then
                        rbits <- (prevCnt, prevBit)::rbits
                    prevCnt <- len
                    prevBit <- resBit
            //Group V
            | (_,_,_) when aBit <> N && bBit <> N && c <> N ->
                // c = U, r = (len, U)
                resBit <- U
                if resBit = prevBit then
                    prevCnt <- prevCnt + len
                else
                    if prevCnt > 0 then
                        rbits <- (prevCnt, prevBit)::rbits
                    prevCnt <- len
                    prevBit <- resBit
                c <- U
            | _ -> printf "Error bvADD, N bit occurs somewhere"
                   assert(false)

            assert (rbits.Length <= 0 || (fst rbits.Head) > 0)
            assert (prevCnt > 0)

            curPos <- curPos + len
            aCnt <- aCnt - len
            bCnt <- bCnt - len

            while aCnt <= 0 && revARem <> [] do
                aCnt <- aCnt + fst revARem.Head
                aBit <- snd revARem.Head
                revARem <- revARem.Tail

            while bCnt <= 0 && revBRem <> [] do
                bCnt <- bCnt + fst revBRem.Head
                bBit <- snd revBRem.Head
                revBRem <- revBRem.Tail

        let actualLength = List.sum (List.map fst rbits)
        if prevCnt > 0 && actualLength < resLen then
            assert (prevCnt >= resLen - actualLength)
            rbits <- (resLen - actualLength, prevBit)::rbits

        let res = BitVector resLen
        res.setBits (rbits, aBV.isConcreteValue && bBV.isConcreteValue)
        res.CheckInvariant()
        if (res.Bits.Length = 1 && (snd res.Bits.[0]) = U) then
            res
        else
            res


    static member bvZeroExtend (bv:BitVector) (k:int) =
        if k = 0 then
            bv
        else
            let res = BitVector (bv.Length+k)
            match bv.Bits.Head with
            | (n, Zero) -> res.Bits <- (k+n, Zero) :: bv.Bits.Tail
            | _ -> res.Bits <- (k, Zero) :: bv.Bits
            res.CheckInvariant()
            res

    static member bvSignExtend (bv:BitVector) (k:int) =
        if k = 0 then
            bv
        else
            let res = BitVector (bv.Length+k)
            match bv.Bits.Head with
            | (n, b) -> res.Bits <- (k+n, b) :: bv.Bits.Tail
            res

    static member flipFirst (bv:BitVector) =
        assert(bv.Length >= 2)
        let frst = (BitVector.bvExtract (bv.Length - 1) (bv.Length - 1) bv)
        let rest = (BitVector.bvExtract (bv.Length - 2) 0 bv)
        BitVector.bvConcat (BitVector.bvNot frst) rest

    static member One (width:int) =
        let mutable res = BitVector width
        if width > 1 then
            res.Bits <- [(width-1, Zero); (1, One)]
        else
            res.Bits <- [(1, One)]
        res

    static member AllZero (width:int) =
        let mutable res = BitVector width
        res.Bits <- [(width, Zero)]
        res

    static member AllOne (width:int) =
        let mutable res = BitVector width
        res.Bits <- [(width, One)]
        res

    static member MinusOne (width:int) =
        BitVector.AllOne width

    static member isAllOnes(bv:BitVector) =
        bv.Bits.Length = 1 && (fst bv.Bits.Head) = bv.Length && (snd bv.Bits.Head = One)

    static member isAllZero (bv:BitVector) =
        bv.Bits.Length = 1 && (fst bv.Bits.Head) = bv.Length && (snd bv.Bits.Head = Zero)

    static member isOne (bv:BitVector) =
        bv.Bits.Length = 2 &&
        (fst bv.Bits.Head) = bv.Length - 1 && (snd bv.Bits.Head = Zero) &&
        (fst bv.Bits.Tail.Head) = 1 && (snd bv.Bits.Tail.Head = One)

    static member bvMul (aBV:BitVector) (bBV:BitVector) =
        assert (aBV.Length = bBV.Length)

        if BitVector.isAllZero aBV then
            aBV
        elif BitVector.isAllZero bBV then
            bBV
        elif BitVector.isOne aBV then
            bBV
        elif BitVector.isOne bBV then
            aBV
        elif aBV.isConcreteValue && bBV.isConcreteValue then
            let aList = aBV.Bits
            let bList = bBV.Bits

            let len = aBV.Length
            let width = aBV.Length + bBV.Length
            assert (len = bBV.Length)
            assert (2*len = width)

            let mutable toSumUp = []
            let mutable aPos = len
            let mutable bPos = len

            // dbg <| (lazy sprintf "MUL: a=%s" (aBV.ToString()))
            // dbg <| (lazy sprintf "MUL: b=%s" (bBV.ToString()))

            for a in aList do
                aPos <- aPos - (fst a)

                for b in bList do
                    bPos <- bPos - (fst b)

                    match (a, b) with
                    | ((m, One), (k, One)) ->
                        let t = BitVector width
                        let post = aPos + bPos

                        let mutable acc = BitVector (m+k)
                        let mutable inc = BitVector (m+k)
                        acc.Bits <- [(m+k, Zero)]
                        inc.Bits <- [(k, Zero); (m, One)]

                        if m = 1 || k = 1 then
                            let r = max m k
                            t.setBits ((width-r-post, Zero) :: (r, One) ::
                                if post <> 0 then [(post, Zero)] else [])
                        else
                            for i in 0 .. k - 1 do
                                let du = acc
                                // dbg <| (lazy sprintf " i=%d u=%s" i (du.ToString()))
                                acc <- BitVector.bvShiftLeftInt acc 1
                                let du = acc
                                acc <- BitVector.bvAdd acc inc

                            acc <- BitVector.bvZeroExtend acc (width-post-acc.Length)
                            if post <> 0 then
                                let postfix = BitVector post
                                postfix.Bits <- [(post, Zero)]
                                acc <- BitVector.bvConcat acc postfix
                            t.setBits acc.Bits

                        toSumUp <- t :: toSumUp
                        // dbg <| (lazy sprintf "MUL: PSH: %s" (t.ToString()))
                    | ((_, One), (_, Zero))
                    | ((_, Zero), (_, One))
                    | ((_, Zero), (_, Zero)) ->
                        ()
                    | _ -> ()

                bPos <- len

            let mutable res = BitVector (width)
            res.setBits ([(width, Zero)], true)

            for s in toSumUp do
                // dbg <| (lazy sprintf "MUL: ADD: %s" (s.ToString()))
                res <- BitVector.bvAdd res s
            res <- BitVector.DropHighest len res

            let r = res
            // dbg <| (lazy sprintf "MUL: r=%s" (r.ToString()))
            res

        else
            assert(not aBV.isConcreteValue || not bBV.isConcreteValue);
            // CMW: There still a few special cases that we could add, e.g.
            // 11U...U11 * 00U...U00 will still allow us to propagate some bits.
            BitVector aBV.Length


    // CMW: When rewriter.hi_div == true, x/0 is an uninterpreted function. We don't want
    // to care about that for now. When rewriter.hi_div == false, we can decide what we
    // want x/0 to be here; we just need to decide what to fix it to.

    // For reference, we can use the respective definitions from the Z3 source (from bv_rewriter.cpp):
    // The "hardware interpretation" for (bvudiv x 0) is #xffff
    // The "hardware interpretation" for (bvsdiv x 0) is (ite (bvslt x #x0000) #x0001 #xffff)

    static member bvUDiv (aBV:BitVector) (bBV:BitVector) =
        assert (aBV.Length = bBV.Length)

        if BitVector.isAllZero bBV then
            // The "hardware interpretation" for (bvudiv x 0) is #xffff
            let hi = BitVector aBV.Length
            hi.Bits <- [(aBV.Length, One)]
            hi
        elif BitVector.isAllZero aBV then
            aBV
        elif BitVector.isOne bBV then
            aBV
        elif aBV.isConcreteValue && bBV.isConcreteValue then
            //AZ: Cheating, but implementing things regularly seemed a bit too involved atm.
            let aBig = aBV.toBigInt()
            let bBig = bBV.toBigInt()
            let rBig = BigInteger.Divide(aBig, bBig)
            let res = BitVector.bigint2BV rBig aBV.Length
            res
        else
            BitVector aBV.Length


    static member bvSDiv (aBV:BitVector) (bBV:BitVector) =
        assert (aBV.Length = bBV.Length)

        if BitVector.isAllZero bBV then
            // The "hardware interpretation" for (bvsdiv x 0) is (ite (bvslt x #x0000) #x0001 #xffff)
            let hi = BitVector aBV.Length
            if (snd aBV.Bits.Head) = One then
                hi.Bits <- [(aBV.Length-1, One); (1, One)]
            else
                hi.Bits <- [(aBV.Length, One)]
            hi
        elif BitVector.isAllZero aBV then
            aBV
        elif BitVector.isOne bBV then
            aBV
        elif aBV.isConcreteValue && bBV.isConcreteValue then
            let aIsNegative = (snd aBV.Bits.Head) = One
            let bIsNegative = (snd bBV.Bits.Head) = One
            let aBig = (if aIsNegative then (BitVector.bvNegate aBV) else aBV).toBigInt()
            let bBig = (if bIsNegative then (BitVector.bvNegate bBV) else bBV).toBigInt()
            let mutable rBig = BigInteger.Divide(aBig, bBig)
            if (aIsNegative <> bIsNegative) then rBig <- -rBig
            let res = BitVector.bigint2BV rBig aBV.Length
            res
        else
            BitVector aBV.Length


    static member bvURem (aBV:BitVector) (bBV:BitVector) =
        assert (aBV.Length = bBV.Length)

        if BitVector.isAllZero aBV ||
           BitVector.isAllZero bBV then
            // The "hardware interpretation" for (bvurem x 0) is x
            aBV
        elif aBV.isConcreteValue && bBV.isConcreteValue then
            let aBig = aBV.toBigInt()
            let bBig = bBV.toBigInt()
            let rBig = BigInteger.Remainder(aBig, bBig)
            let res = BitVector.bigint2BV rBig aBV.Length
            res
        else
            BitVector aBV.Length


    static member bvSRem (aBV:BitVector) (bBV:BitVector) =
        assert (aBV.Length = bBV.Length)

        if BitVector.isAllZero aBV ||
           BitVector.isAllZero bBV then
            // The "hardware interpretation" for (bvsrem x 0) is x
            aBV
        elif aBV.isConcreteValue && bBV.isConcreteValue then
            let aBig = aBV.toBigInt()
            let bBig = bBV.toBigInt()
            let aSgn = (snd aBV.Bits.Head) = One
            let bSgn = (snd bBV.Bits.Head) = One
            let aaBig = BigInteger.Abs(aBig)
            let abBig = BigInteger.Abs(bBig)
            let mutable rBig = BigInteger.Remainder(aaBig, abBig)
            let res = BitVector.bigint2BV rBig aBV.Length
            if (aSgn <> bSgn) then rBig <- -rBig
            let res = BitVector.bigint2BV rBig aBV.Length
            res
        else
            BitVector aBV.Length

    static member bvSMod (aBV:BitVector) (bBV:BitVector) =
        assert (aBV.Length = bBV.Length)

        if BitVector.isAllZero aBV ||
           BitVector.isAllZero bBV then
            aBV
        elif aBV.isConcreteValue && bBV.isConcreteValue then
            let r = BitVector.bvSRem aBV bBV
            let aIsNegative = (snd aBV.Bits.Head) = One
            let bIsNegative = (snd bBV.Bits.Head) = One
            let rIsNegative = (snd r.Bits.Head) = One
            if bIsNegative = rIsNegative then
                r
            else
                BitVector.bvNegate r
        else
            BitVector aBV.Length


    static member bvNegate(aBV:BitVector) =
        if not aBV.isConcreteValue then
            BitVector aBV.Length
        elif BitVector.isAllOnes aBV then
            BitVector.One aBV.Length
        elif BitVector.isAllZero aBV then
            aBV
        else
            let width = aBV.Length
            BitVector.bvAdd (BitVector.bvNot aBV) (BitVector.One width)

    //TODO: Compactness properties, need to make sure that they are maintained!!!

    //AZ: This check can be made even easier, if they are equal their rle structure needs to be identical.
    static member bvEQ (aBV:BitVector) (bBV:BitVector) =
        assert ( aBV.Length = bBV.Length)
        let a = aBV.Bits
        let b = bBV.Bits
        let mutable guard = true
        let mutable res = true
        let mutable (aCnt,aBit) = a.Head
        let mutable aRem = a.Tail
        let mutable (bCnt,bBit) = b.Head
        let mutable bRem = b.Tail

        let mutable resCnt = min aCnt bCnt

        while guard do

            if aBit = bBit then
                resCnt <- min aCnt bCnt //TODO: If Compactness -> max aCnt bCnt
                aCnt <- aCnt - resCnt
                bCnt <- bCnt - resCnt

                while aCnt <= 0 && aRem <> [] do
                    aCnt <- aCnt + fst aRem.Head
                    aBit <- snd aRem.Head
                    aRem <- aRem.Tail

                while bCnt <= 0 && bRem <> [] do
                    bCnt <- bCnt + fst bRem.Head
                    bBit <- snd bRem.Head
                    bRem <- bRem.Tail

                if aCnt = 0 && bCnt = 0 then
                    guard <- false
                else
                    assert (aCnt > 0 && bCnt> 0)
            else
                guard <- false
                res <- false
        res


    static member bvULEQ (aBV:BitVector) (bBV:BitVector) =
        assert (aBV.Length = bBV.Length)
        assert (aBV.isConcreteValue && bBV.isConcreteValue)
        let a = aBV.Bits
        let b = bBV.Bits
        let mutable guard = true
        let mutable result = true
        let mutable (aCnt,aBit) = a.Head
        let mutable aRem = a.Tail
        let mutable (bCnt,bBit) = b.Head
        let mutable bRem = b.Tail
        let mutable resCnt = min aCnt bCnt

        while guard do

            match (aBit,bBit) with
            | (One,Zero) -> result <- false
                            guard  <- false
            | (Zero, Zero)
            | (One,One) ->  () //Continue

            | (U,U)      //ToDO: Double check this one, it could be that it is infeasible
            | (Zero, One)
            | (U, One)
            | (Zero, U) ->  guard <- false
            | (U, Zero) ->  ()
            | (One, U) ->   ()
            | _ ->  printfn "N bit appears in a bitvector!"
                    assert(false)
                    ()

            //Update bit counts
            resCnt <- min aCnt bCnt
            aCnt <- aCnt - resCnt
            bCnt <- bCnt - resCnt

            while aCnt <= 0 && aRem <> [] do
                aCnt <- aCnt + fst aRem.Head
                aBit <- snd aRem.Head
                aRem <- aRem.Tail

            while bCnt <= 0 && bRem <> [] do
                bCnt <- bCnt + fst bRem.Head
                bBit <- snd bRem.Head
                bRem <- bRem.Tail

            if aCnt = 0 && bCnt = 0 then
                guard <- false
            else
                assert (aCnt > 0 && bCnt> 0)

        result

    static member bvULT (a:BitVector) (b:BitVector) =
        (BitVector.bvULEQ a b) && not (BitVector.bvEQ a b)

    static member bvUGT (a:BitVector) (b:BitVector) =
        not (BitVector.bvULEQ a b)

    static member Max (a:BitVector) (b:BitVector) =
        if BitVector.bvULEQ a b then
            b
        else
            a

    static member Min (a:BitVector) (b:BitVector) =
        if BitVector.bvULEQ a b then
            a
        else
            b

    member r.toZ3Expr (ctx:Context) =
        ctx.MkBV(r.toBigInt().ToString(), (uint32)r.Length) :> Expr


let numParameters (declKind:Z3_decl_kind) =
    match declKind with
    |Z3_decl_kind.Z3_OP_EXTRACT -> 2
    |Z3_decl_kind.Z3_OP_REPEAT -> 1
    | _ -> 0


let supportedBVOP (declKind:Z3_decl_kind) =
    match declKind with
    |Z3_decl_kind.Z3_OP_EQ //Where is it actually used?
    |Z3_decl_kind.Z3_OP_BAND
    |Z3_decl_kind.Z3_OP_BNEG
    |Z3_decl_kind.Z3_OP_BNOT
    |Z3_decl_kind.Z3_OP_BOR
    |Z3_decl_kind.Z3_OP_BXOR
    |Z3_decl_kind.Z3_OP_REPEAT
    |Z3_decl_kind.Z3_OP_CONCAT
    |Z3_decl_kind.Z3_OP_EXTRACT
    |Z3_decl_kind.Z3_OP_BADD
    |Z3_decl_kind.Z3_OP_BSUB
    |Z3_decl_kind.Z3_OP_BMUL
    |Z3_decl_kind.Z3_OP_BSDIV
    |Z3_decl_kind.Z3_OP_BUDIV
    |Z3_decl_kind.Z3_OP_BSDIV0
    |Z3_decl_kind.Z3_OP_BUDIV0
    |Z3_decl_kind.Z3_OP_BNUM
    |Z3_decl_kind.Z3_OP_UNINTERPRETED
// CMW: The following 4 are not for bit-vectors.
//    |Z3_decl_kind.Z3_OP_LE
//    |Z3_decl_kind.Z3_OP_GE
//    |Z3_decl_kind.Z3_OP_LT
//    |Z3_decl_kind.Z3_OP_GT
    |Z3_decl_kind.Z3_OP_ULEQ
    |Z3_decl_kind.Z3_OP_SLEQ
    |Z3_decl_kind.Z3_OP_SGEQ
    |Z3_decl_kind.Z3_OP_UGEQ
    |Z3_decl_kind.Z3_OP_ULT
    |Z3_decl_kind.Z3_OP_UGT
    |Z3_decl_kind.Z3_OP_SLT
    |Z3_decl_kind.Z3_OP_SGT
    |Z3_decl_kind.Z3_OP_AND
    |Z3_decl_kind.Z3_OP_IMPLIES
     -> true
    | _ -> //printfn "Not supported: %s " (declKind.ToString())
           false


//TODO: Populate
let z3OP2bvOP (declKind:Z3_decl_kind) (param:int list)=
    //assert (supportedBVOP declKind)
    match declKind with
    |Z3_decl_kind.Z3_OP_BAND ->
        (fun (args:BitVector list) ->
            assert (args.Length = 2)
            BitVector.bvAND args.Head args.Tail.Head)
    |Z3_decl_kind.Z3_OP_BOR ->
         (fun (args:BitVector list) ->
            assert (args.Length = 2)
            BitVector.bvOR args.Head args.Tail.Head)
    |Z3_decl_kind.Z3_OP_BXOR ->
        (fun (args:BitVector list) ->
            assert (args.Length = 2)
            BitVector.bvXOR args.Head args.Tail.Head)
    |Z3_decl_kind.Z3_OP_REPEAT ->
         assert (param.Length = numParameters Z3_decl_kind.Z3_OP_REPEAT )
         (fun (args:BitVector list) ->
            assert (args.Length = 1)
            BitVector.bvRepeat param.Head args.Head)
    |Z3_decl_kind.Z3_OP_CONCAT ->
        (fun (args:BitVector list) ->
            assert (args.Length >= 2)
            (List.fold (fun acc x -> (BitVector.bvConcat acc x)) args.Head args.Tail))
    |Z3_decl_kind.Z3_OP_EXTRACT ->
         assert (param.Length = numParameters Z3_decl_kind.Z3_OP_EXTRACT )
         (fun (args:BitVector list) ->
            assert (args.Length = 1 )
            BitVector.bvExtract param.Head param.Tail.Head args.Head)
    |Z3_decl_kind.Z3_OP_BADD ->
        (fun (args:BitVector list) ->
            assert (args.Length = 2)
            BitVector.bvAdd args.Head args.Tail.Head)
    |Z3_decl_kind.Z3_OP_BNEG ->
        (fun (args:BitVector list) ->
            assert (args.Length = 1)
            BitVector.bvNegate args.Head)
    |Z3_decl_kind.Z3_OP_BNOT ->
        (fun (args:BitVector list) ->
            assert (args.Length = 1)
            BitVector.bvNot args.Head)
    |Z3_decl_kind.Z3_OP_BLSHR ->
        (fun (args:BitVector list) ->
            assert (args.Length = 2)
            BitVector.bvLShiftRight args.Head args.Tail.Head)
    |Z3_decl_kind.Z3_OP_BASHR ->
        (fun (args:BitVector list) ->
            assert (args.Length = 2)
            BitVector.bvAShiftRight args.Head args.Tail.Head)
    |Z3_decl_kind.Z3_OP_BSHL ->
        (fun (args:BitVector list) ->
            assert (args.Length = 2)
            BitVector.bvShiftLeft args.Head args.Tail.Head)
    |Z3_decl_kind.Z3_OP_BMUL ->
        (fun (args:BitVector list) ->
            assert (args.Length = 2)
            BitVector.bvMul args.Head args.Tail.Head)
    |Z3_decl_kind.Z3_OP_BUREM ->
        (fun (args:BitVector list) ->
            assert (args.Length = 2)
            BitVector.bvURem args.Head args.Tail.Head)
    |Z3_decl_kind.Z3_OP_BSREM ->
        (fun (args:BitVector list) ->
            assert (args.Length = 2)
            BitVector.bvSRem args.Head args.Tail.Head)
    |Z3_decl_kind.Z3_OP_BUDIV ->
        (fun (args:BitVector list) ->
            assert (args.Length = 2)
            BitVector.bvUDiv args.Head args.Tail.Head)
    |Z3_decl_kind.Z3_OP_BSDIV ->
        (fun (args:BitVector list) ->
            assert (args.Length = 2)
            BitVector.bvSDiv args.Head args.Tail.Head)
    |Z3_decl_kind.Z3_OP_BSMOD ->
        (fun (args:BitVector list) ->
            assert (args.Length = 2)
            BitVector.bvSMod args.Head args.Tail.Head)
    |Z3_decl_kind.Z3_OP_BSREM0
    |Z3_decl_kind.Z3_OP_BUREM0
    |Z3_decl_kind.Z3_OP_BSDIV0
    |Z3_decl_kind.Z3_OP_BUDIV0 ->
        NOT_YET_IMPLEMENTED("bit-vector division by 0, signed and unsigned")
        fun x -> BitVector.Invalid
    |Z3_decl_kind.Z3_OP_UNINTERPRETED ->
        UNREACHABLE("UFs should have been removed in a preprocessor.")
    | _ -> NOT_YET_IMPLEMENTED (declKind.ToString())
           fun x -> BitVector.Invalid