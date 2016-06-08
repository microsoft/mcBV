module BoundsOperations

open Microsoft.Z3
open GlobalOptions
open Util
open Literal
open BitVector
open Interval
open TheoryRelation
open NumeralDB
open BoundsValuation
open BooleanValuation

let unboundedVariables (t:TheoryRelation) (bounds:Ref<BoundsValuation>)=        
    let mutable args = []
    for i in 0 .. t.numArguments do 
        let arg = t.getArgument i
        if  not (t.isArgumentNumeral i) && 
            (((!bounds).get arg).isFull) &&
            (List.filter (fun x -> x = arg) args).Length = 0 then
            args <- arg :: args
    args

let numUnboundedVariables (t:TheoryRelation) (bounds:Ref<BoundsValuation>) =
    List.length (unboundedVariables t bounds)


let getArgumentBounds (t:TheoryRelation) (bounds:Ref<BoundsValuation>) (pNumerals:Ref<NumeralDB>) (i:int) =
    assert (0 <= i && i <= t.numArguments)
    if t.isArgumentNumeral i then
        Interval.RLEToInterval ((!pNumerals).getNumeral (abs (t.getArgument i)))
    else
        (!bounds).get (t.getArgument i)

let getRhsBounds (t:TheoryRelation) (bounds:Ref<BoundsValuation>) (numerals:Ref<NumeralDB>) =
    getArgumentBounds t bounds numerals t.numArguments


let tbndsGetNewValueAdd (width:int) (position:int) (polarity:Val) (pBounds:Ref<BoundsValuation>) (nums:Ref<NumeralDB>) =    
    match polarity with 
    | True -> 
        match position with
        | 0 -> // ?x + y = z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)
                let x = bounds.Head
                let y = bounds.Tail.Head
                let z = bounds.Tail.Tail.Head
                let q = (Interval.Sub z y)
                let r = q.Intersection x
                r)
        | 1 -> // x + ?y = z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)
                let x = bounds.Head
                let y = bounds.Tail.Head
                let z = bounds.Tail.Tail.Head
                let q = (Interval.Sub z x)
                let r = q.Intersection y
                r)
        | 2 -> // x + y = ?z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)
                let x = bounds.Head
                let y = bounds.Tail.Head
                let z = bounds.Tail.Tail.Head
                let q = (Interval.Add x y)
                let r = q.Intersection z
                r)
        | _ -> UNREACHABLE("Bogus position")
    | _ -> 
        (fun (bounds:Interval list) -> Interval.Full width) // No news.


let tbndsGetNewValueSub (width:int) (position:int) (polarity:Val) (pBounds:Ref<BoundsValuation>) (nums:Ref<NumeralDB>) =    
    match polarity with 
    | True -> 
        match position with
        | 0 -> // ?x - y = z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)
                let x = bounds.Head
                let y = bounds.Tail.Head
                let z = bounds.Tail.Tail.Head
                let q = (Interval.Add z y)
                let r = q.Intersection x
                r)
        | 1 -> // x - ?y = z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)
                let y = bounds.Tail.Head
                y) // TODO: Refine
        | 2 -> // x - y = ?z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)
                let x = bounds.Head
                let y = bounds.Tail.Head
                let z = bounds.Tail.Tail.Head
                let q = (Interval.Sub x y)
                let r = q.Intersection z
                r)
        | _ -> UNREACHABLE("Bogus position")
    | _ -> 
        (fun (bounds:Interval list) -> Interval.Full width) // No news.


let tbndsGetNewValueMul (width:int) (position:int) (polarity:Val) (pBounds:Ref<BoundsValuation>) (nums:Ref<NumeralDB>) =    
    match polarity with 
    | True -> 
        match position with
        | 0 -> // ?x * y = z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)
                let x = bounds.Head
                x) // TODO: Refine
        | 1 -> // x * ?y = z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)                
                let y = bounds.Tail.Head                
                y) // TODO: Refine
        | 2 -> // x * y = ?z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)
                let x = bounds.Head
                let y = bounds.Tail.Head
                let z = bounds.Tail.Tail.Head
                let q = (Interval.Mul x y)
                let r = q.Intersection z
                r)
        | _ -> UNREACHABLE("Bogus position")
    | _ -> 
        (fun (bounds:Interval list) -> Interval.Full width) // No news.

let tbndsGetNewValueUDiv (width:int) (position:int) (polarity:Val) (pBounds:Ref<BoundsValuation>) (nums:Ref<NumeralDB>) =    
    match polarity with 
    | True -> 
        match position with
        | 0 -> // ?x u/ y = z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)
                let x = bounds.Head
                x) // TODO: Refine
        | 1 -> // x u/ ?y = z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)                
                let y = bounds.Tail.Head                
                y) // TODO: Refine
        | 2 -> // x u/ y = ?z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)
                let x = bounds.Head
                let y = bounds.Tail.Head
                let z = bounds.Tail.Tail.Head
                let q = (Interval.UDiv x y)
                let r = q.Intersection z
                r)
        | _ -> UNREACHABLE("Bogus position")
    | _ -> 
        (fun (bounds:Interval list) -> Interval.Full width) // No news.


let tbndsGetNewValueSDiv (width:int) (position:int) (polarity:Val) (pBounds:Ref<BoundsValuation>) (nums:Ref<NumeralDB>) =    
    match polarity with 
    | True -> 
        match position with
        | 0 -> // ?x u/ y = z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)
                let x = bounds.Head
                x) // TODO: Refine
        | 1 -> // x u/ ?y = z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)                
                let y = bounds.Tail.Head                
                y) // TODO: Refine
        | 2 -> // x u/ y = ?z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)
                let x = bounds.Head
                let y = bounds.Tail.Head
                let z = bounds.Tail.Tail.Head
                let q = (Interval.SDiv x y)
                let r = q.Intersection z
                r)
        | _ -> UNREACHABLE("Bogus position")
    | _ -> 
        (fun (bounds:Interval list) -> Interval.Full width) // No news.


let tbndsGetNewValueConcat (width:int) (position:int) (polarity:Val) (pBounds:Ref<BoundsValuation>) (nums:Ref<NumeralDB>) =    
    match polarity with 
    | True -> 
        match position with
        | 0 -> // ?x concat y = z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)
                let x = bounds.Head
                let y = bounds.Tail.Head
                let z = bounds.Tail.Tail.Head
                let q = (Interval.Extract (z.Dimension - 1) y.Dimension z)
                let r = q.Intersection x
                r) 
        | 1 -> // x concat ?y = z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)                
                let x = bounds.Head
                let y = bounds.Tail.Head
                let z = bounds.Tail.Tail.Head
                // CMW: This is wwrong:
                // let q = (Interval.Extract (y.Dimension - 1) 0 z)
                // let r = q.Intersection y
                // We can't simply extract y from z, because those values 
                // are not the lower/upper bound on y. The best
                // we can do is to keep the old interval for y.                
                y)
        | 2 -> // xconcat y = ?z
            (fun (bounds:Interval list) -> 
                assert (bounds.Length >= position)
                assert (bounds.Length = 3)
                let x = bounds.Head
                let y = bounds.Tail.Head
                let z = bounds.Tail.Tail.Head
                let q = (Interval.Concat x y)
                let r = q.Intersection z
                r)
        | _ -> UNREACHABLE("Bogus position")
    | _ -> 
        (fun (bounds:Interval list) -> Interval.Full width) // No news.


let tbndsGetNewValue (tRel:TheoryRelation) (position:int) (polarity:Val) (pBounds:Ref<BoundsValuation>) (nums:Ref<NumeralDB>) =
    let parms = tRel.getParameterList
    assert(polarity <> Undefined)

    if tRel.isSimpleRelation then
        
        match (tRel.getRelationOP) with
        | (Z3_decl_kind.Z3_OP_EQ) -> 
            match (polarity, position) with
            | (False, _) -> 
                // CMW: Theoretically there could be only one particular 
                // value left in the domain of the variable(s), but it
                // seems too expensive to check that here. Thus, we return 
                // the origin intervals, i.e., "nothing changed"
                (fun (bounds:Interval list) -> 
                    let x = bounds.Head
                    let y = bounds.Tail.Head
                    if position = 0 then 
                        if y.isSingleton then
                            x.RemoveValue y.Lower
                        else
                            x 
                     else 
                        if x.isSingleton then
                            y.RemoveValue x.Lower
                        else
                            y)
        
            | (True, p) when 0 <= p && p <= 1-> // ?x = y -> propagate x -> y or y -> x
                (fun (bounds:Interval list) -> 
                    assert (bounds.Length >= position)
                    assert (bounds.Length = 2)
                    let x = bounds.Head
                    let y = bounds.Tail.Head
                    if p = 0 then y else x)

            | _ -> UNREACHABLE("")
                
        | (Z3_decl_kind.Z3_OP_ULEQ) -> 
            match (polarity, position) with
            | (True, 0) -> // ?x <= y -> propagate upper bound of y 
                (fun (bounds:Interval list) -> 
                    assert (bounds.Length >= position)
                    assert (bounds.Length = 2)
                    let x = bounds.Head
                    let y = bounds.Tail.Head
                    Interval(BitVector.AllZero x.Dimension, 
                             y.Upper)
                             .Intersection x)

            | (True, 1) -> // x <= ?y -> propagate lower bound of x
                (fun (bounds:Interval list) -> 
                    assert (bounds.Length >= position)
                    assert (bounds.Length = 2)
                    let x = bounds.Head
                    let y = bounds.Tail.Head
                    Interval(x.Lower, 
                             BitVector.AllOne x.Dimension)
                             .Intersection y)

            | (False, 0) -> // ?x > y -> propagate lower bound of y + 1
                (fun (bounds:Interval list) -> 
                    assert (bounds.Length >= position)
                    assert (bounds.Length = 2)
                    let x = bounds.Head
                    let y = bounds.Tail.Head
                    Interval(BitVector.bvAdd y.Lower (BitVector.One y.Dimension), 
                             BitVector.AllOne x.Dimension)
                             .Intersection x)

            | (False, 1) -> // x > ?y -> propagate upper bound of x - 1
                (fun (bounds:Interval list) -> 
                    assert (bounds.Length >= position)
                    assert (bounds.Length = 2)
                    let x = bounds.Head
                    let y = bounds.Tail.Head
                    Interval(BitVector.AllZero x.Dimension,
                             BitVector.bvSub x.Upper (BitVector.One x.Dimension))
                             .Intersection y)
            
            | _ -> UNREACHABLE("unexpected polarity and/or position")

        | _ -> UNREACHABLE("unexpected relation op")

    else // Non-simple cases.

        let bvop = tRel.getBVOP
        let missing_arg = tRel.getArgument position
        let missing_dim = if missing_arg < 0 then ((!nums).getNumeral -missing_arg).Length 
                           else ((!pBounds).get missing_arg).Dimension

        match (tRel.getRelationOP, bvop, polarity) with
        | (Z3_decl_kind.Z3_OP_EQ, Z3_decl_kind.Z3_OP_BADD, _) ->
               tbndsGetNewValueAdd missing_dim position polarity pBounds nums

        | (Z3_decl_kind.Z3_OP_EQ, Z3_decl_kind.Z3_OP_BSUB, _) ->
               tbndsGetNewValueSub missing_dim position polarity pBounds nums

        | (Z3_decl_kind.Z3_OP_EQ, Z3_decl_kind.Z3_OP_BMUL, _) ->
               tbndsGetNewValueMul missing_dim position polarity pBounds nums

        | (Z3_decl_kind.Z3_OP_EQ, Z3_decl_kind.Z3_OP_BUDIV, _) ->
               tbndsGetNewValueUDiv missing_dim position polarity pBounds nums

        | (Z3_decl_kind.Z3_OP_EQ, Z3_decl_kind.Z3_OP_BSDIV, _) ->
               tbndsGetNewValueSDiv missing_dim position polarity pBounds nums

        | (Z3_decl_kind.Z3_OP_EQ, Z3_decl_kind.Z3_OP_CONCAT, _) ->
               tbndsGetNewValueConcat missing_dim position polarity pBounds nums

        | _ -> 
            match (tRel.getRelationOP) with 
            | (Z3_decl_kind.Z3_OP_EQ) -> 
                match (polarity, position) with
                | (False, _) 
                | (True, _) ->                     
                    // CMW: For now, we know nothing. 
                    (fun (bounds:Interval list) -> Interval.Full missing_dim)
                | _ -> UNREACHABLE("unexpected polarity and/or position")

            | (Z3_decl_kind.Z3_OP_ULEQ) -> 
                match (polarity, position) with
                | (False, _) 
                | (True, _) -> 
                    // CMW: For now, we know nothing. 
                    (fun (bounds:Interval list) -> Interval.Full missing_dim)
                | _ -> UNREACHABLE("unexpected polarity and/or position")

            | _ -> UNREACHABLE("unexpected relation op")


let getLhsBounds (t:TheoryRelation) (pBounds:Ref<BoundsValuation>) (pNumerals:Ref<NumeralDB>) =
    if t.isSimpleRelation then
        if t.isArgumentNumeral 0 then
            Interval.RLEToInterval ((!pNumerals).getNumeral (abs (t.getArgument 0)))
        else
            (!pBounds).get (t.getArgument 0)
    else
        let rhs_size = (getArgumentBounds t pBounds pNumerals t.numArguments).Dimension
        let args = [for i in 0 .. t.numArguments - 1 do yield getArgumentBounds t pBounds pNumerals i ]  @                   
                   [ Interval.Full rhs_size ] // RHS replaced with full interval; slow, but sound.
        let nb = (tbndsGetNewValue t t.numArguments True pBounds pNumerals) args 
        nb

let tbndsGetNewValues (t:TheoryRelation) (polarity:Val) (pBounds:Ref<BoundsValuation>) (pNumerals:Ref<NumeralDB>) = 
    // Note that this function depends on bounds only (no BitVectorValuation, only Intervals).
    
    let mutable newBounds = []    
    let argBnds = [for i in 0 .. t.numArguments do yield getArgumentBounds t pBounds pNumerals i ]    

    for j in 0 .. t.numArguments do 
        if not (t.isArgumentNumeral j) then        
            newBounds <- newBounds @ [ (t.getArgument j, (tbndsGetNewValue t j polarity pBounds pNumerals) argBnds) ]

    if DBG then
        printf " |   >  "
        if t.hasBVOP then printf "%s" (t.getBVOP.ToString())
        for p in List.toArray (t.getParameterList) do
            printf " %s" (p.ToString())
        for i in 0 .. argBnds.Length - 2 do
            printf " %s" (argBnds.[i].ToString())
        printf " %s" (if t.getRelationOP = Z3_decl_kind.Z3_OP_ULEQ then "<=" else "=")
        printfn " %s" (argBnds.[argBnds.Length - 1].ToString())
        //bounds implied by this constraint alone)
        for nb in newBounds do
            printfn " | ==>  %s:bv in %s" ((fst nb).ToString()) ((snd nb).ToString())

    // CMW: Intersection is done here, so whatever comes out of tbndsGetNewValues 
    // represents the final new Interval for var. I'd prefer it to be done in 
    // tbndsGetNewValue (the name implies that the final "new value" will come out of it).
    // At the moment, intersection is done twice; here and in tbndsGetNewValues until
    // further notice.
    List.map (fun (var, intrvl) -> (var, ((!pBounds).get var).Intersection intrvl)) newBounds
    

