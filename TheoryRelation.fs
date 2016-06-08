module TheoryRelation

open Microsoft.Z3
open System
open System.Collections
open System.Collections.Generic
open System.Numerics
open Numeral
open BitVector
open Interval
open Literal
open Util
open BitVectorValuation
open NumeralDB
open BooleanValuation

// Array of ints representing:
// lhs relOp rhs
// where Lhs and Rhs can be the following combinations:
//| LHS | RHS |
//| Num | Num |
//| Var | Var |
//|BVapp| Var |
//| Var | Num |

// Structure:
// Size
// Relational OP (mandatory)
// BVOP - can be missing in the case of 2 Numerals or 2 Variables, Size = 5 is an indicator for these cases
// RHS -> always positioned at size - 1

// | 0  |   1  |  2   |  3 |   4   | ...  | size - 1|
// |size| bool | relOP|bvOP| params| args |   rhs   |

type SimpleRelationType =
| PAPredicate
| LowerBound
| UpperBound
| NotSimple


let sizeInd = 0
let boolVarInd = sizeInd + 1
let relOpInd = boolVarInd + 1
let bvOpInd = relOpInd + 1
let offset = bvOpInd + 1
let minSize = offset + 2

type TheoryRelation private (size:int, boolVar:int, bvOp:Z3_decl_kind, ps:int list, lhs:int list, relOp:Z3_decl_kind, rhs:int) =
    member val private data =
        assert(size >= minSize)
        assert(ps.Length = numParameters bvOp)
        let a = Array.create size -1;
        if size > 0 then a.[sizeInd] <- size
        a.[boolVarInd] <- boolVar
        a.[relOpInd] <- (int relOp)
        a.[bvOpInd] <- (int bvOp)
        let mutable i = 0
        for p in ps do
            a.[offset + i] <- p
            i <- i + 1
        i <- 0
        for arg in lhs do
            a.[offset + ps.Length + i] <- arg
            i <- i + 1
        a.[a.[sizeInd] - 1] <- rhs
        a
        with get, set

    new(lhs, relOp, rhs) = assert(relOp = Z3_decl_kind.Z3_OP_EQ || relOp = Z3_decl_kind.Z3_OP_ULEQ)
                           let a, b =
                               if relOp = Z3_decl_kind.Z3_OP_EQ &&
                                  ((isNum lhs) || not (isNum rhs)) then
                                  (rhs, lhs)
                               else
                                  (lhs, rhs)
                           TheoryRelation(minSize, 0, enum<Z3_decl_kind>(-1), [], [a], relOp, b)

    new(bvOp, lhs:int list, relOp, rhs) = TheoryRelation(minSize + lhs.Length - 1, 0, bvOp, [], lhs, relOp, rhs)
    new(bvOp, parms:int list, lhs:int list, relOp, rhs) = TheoryRelation(minSize + parms.Length + lhs.Length - 1, 0, bvOp, parms, lhs, relOp, rhs)

    interface IComparable<TheoryRelation> with
        member this.CompareTo(other:TheoryRelation) =
            // TheoryRelation ordering is lexicographic over
            // all elements. This is needed for Set<Theoryrelation>
            // and similar. Note that this.getBoolVar is not referred to
            // below, so that we can use a Dictionary<TheoryRelation, Var>
            // to track the mapping between TheoryRelations and their
            // boolvars.
            if this.getSize < other.getSize then
                -1
            elif this.getSize > other.getSize then
                +1
            elif this.getRelationOP < other.getRelationOP then
                -1
            elif this.getRelationOP > other.getRelationOP then
                +1
            elif this.getBVOP < other.getBVOP then
                -1
            elif this.getBVOP > other.getBVOP then
                +1
            elif this.numParameters < other.numParameters then
                -1
            elif this.numParameters > other.numParameters then
                +1
            elif this.numArguments < other.numArguments then
                -1
            elif this.numArguments > other.numArguments then
                +1
            elif this.getRhs < other.getRhs then
                -1
            elif this.getRhs > other.getRhs then
                +1
            else
                let mutable res = 0
                let mutable i = 0
                while i < this.numParameters && res = 0 do
                    if (this.getParameter i) < (other.getParameter i) then
                        res <- -1
                    elif (this.getParameter i) > (other.getParameter i) then
                        res <- +1
                    i <- i + 1
                i <- 0
                while i < this.numArguments && res = 0 do
                    let tai = (this.getArgument i)
                    let oai = (other.getArgument i)
                    if tai < oai then
                        res <- -1
                    elif tai > oai then
                        res <- +1
                    i <- i + 1
                res

    interface IComparable with
        member this.CompareTo obj =
            if obj = null then
                1
            else
                match obj with
                | :? TheoryRelation as other -> (this :> IComparable<_>).CompareTo other
                | _ -> invalidArg "obj" "not a TheoryRelation"

    interface IEquatable<TheoryRelation> with
        member this.Equals (other) =
            if this.getSize <> other.getSize ||
                this.getRelationOP <> other.getRelationOP ||
                this.getBVOP <> other.getBVOP ||
                this.numParameters <> other.numParameters ||
                this.numArguments <> other.numArguments ||
                this.getRhs <> other.getRhs then
                false
            else
                let mutable res = true
                let mutable i = 0
                while i < this.numParameters && res do
                    if (this.getParameter i) <> (other.getParameter i) then
                        res <- false
                    i <- i + 1
                i <- 0
                while i < this.numArguments && res do
                    let tai = (this.getArgument i)
                    let oai = (other.getArgument i)
                    if tai < oai || tai > oai then
                        res <- false
                    i <- i + 1
                res

    override this.Equals obj =
        match obj with
        | :? TheoryRelation as other -> (this :> IEquatable<_>).Equals other
        | _  -> invalidArg "obj" "not a TheoryRelation"

    override this.GetHashCode () =
        let mutable r = this.getSize
        r <- r ^^^ (int) this.getRelationOP
        r <- r ^^^ (int) this.getBVOP
        r <- r ^^^ this.numParameters
        for i in 0 .. this.numParameters - 1 do
            r <- r ^^^ this.getParameter i
        r <- r ^^^ this.numArguments
        for i in 0 .. this.numArguments - 1 do
            r <- r ^^^ this.getArgument i
        r

    member private r.firstArgumentIndex = offset + r.numParameters
    member private r.getSize = r.data.[sizeInd]

    //AZ: r.numArguments is the arguments of the LHS and includes the RHS when 0 .. r.numArguments
    member r.numArguments =  r.getSize - 1 - r.firstArgumentIndex
    member r.numParameters = if r.hasBVOP then (numParameters r.getBVOP) else 0
    member r.getRelationOP = enum<Z3_decl_kind>(r.data.[relOpInd])
    member r.getBVOP = enum<Z3_decl_kind>(r.data.[bvOpInd])

    member r.getBoolVar : Var =
        assert (r.getSize > boolVarInd)
        r.data.[boolVarInd]

    member r.setBoolvar (v:Var) =  r.data.[boolVarInd] <- v

    member r.getParameter (i:int) =
        assert (i >= 0 && i < r.numParameters)
        r.data.[offset + i]

    // Accesses arguments of the theory relation.
    // Indexes from 0 up to r.numArguments - 1 are LHS
    // Index r.numArguments is the RHS
    member r.getArgument (i:int) : int =
        assert (i >= 0 && i <= r.numArguments)
        r.data.[r.firstArgumentIndex + i]

    member r.getArgumentString (i:int) =
        if r.isArgumentNumeral i then
            (-(r.getArgument i)).ToString() + ":num"
        else
            (r.getArgument i).ToString() + ":bv"

    member r.hasBVOP = r.data.[bvOpInd] > -1

    // CMW: What is the definition of "simple"? Is this the same as r.numArguments = 1?
    // AZ: Simple relation does not involve a bit-vector operation, only a relational symbol
    //     E.g., x = y, x <= 3, ...
    member r.isSimpleRelation = r.data.[bvOpInd] = -1

    member r.isArgumentNumeral (i:int) =
        assert(i >= 0 && i <= r.numArguments)
        r.getArgument i < 0

    member r.getRhs : Var = r.getArgument r.numArguments

    member r.isRhsNumeral = r.getRhs < 0

    member r.variableArguments =
        let mutable args = []
        for i in 0 .. r.numArguments do
            let arg = r.getArgument i
            if not (isNum arg) && (List.filter (fun x -> x = arg) args).Length = 0 then
                //AZ: Should we allow repetition here?
                args <- arg :: args
        args

    member r.getParameterList =
        let mutable param = []
        for i in 0 .. numParameters r.getBVOP - 1 do
            param <- param @ [r.getParameter i]
        param

    override r.ToString() = r.toString()
    member r.ToString(nDB:Ref<NumeralDB>) = r.toString(nDB)
    member r.ToString(nDB:Ref<NumeralDB>, include_bool_var:bool) = r.toString(nDB, include_bool_var)

    member private r.toString (?nDB:Ref<NumeralDB>, ?include_bool_var:bool) =
        let mutable res = match include_bool_var with
                          | None
                          | Some(true) -> "[" + r.getBoolVar.ToString() + "] := "
                          | _ -> ""

        if r.hasBVOP then
            let nParam = numParameters r.getBVOP
            if nParam > 0 then
                res <- res + "( _ "
            match r.getBVOP with
            | Z3_decl_kind.Z3_OP_BNOT -> res <- res + "bvnot "
            | Z3_decl_kind.Z3_OP_BOR -> res <- res + "bvor "
            | Z3_decl_kind.Z3_OP_BAND -> res <- res + "bvand "
            | Z3_decl_kind.Z3_OP_BXOR -> res <- res + "bvxor "
            | Z3_decl_kind.Z3_OP_BNAND -> res <- res + "bvnand "
            | Z3_decl_kind.Z3_OP_BNOR -> res <- res + "bvnor "
            | Z3_decl_kind.Z3_OP_BNEG -> res <- res + "bvneg "
            | Z3_decl_kind.Z3_OP_EXTRACT ->  res <- res + "extract "
            | Z3_decl_kind.Z3_OP_CONCAT ->  res <- res + "concat "
            | Z3_decl_kind.Z3_OP_REPEAT ->  res <- res + "repeat "
            | Z3_decl_kind.Z3_OP_BADD -> res <- res + "+ "
            | Z3_decl_kind.Z3_OP_BSUB-> res <- res + "- "
            | Z3_decl_kind.Z3_OP_BMUL -> res <- res + "* "
            | Z3_decl_kind.Z3_OP_BSDIV -> res <- res + "s/ "
            | Z3_decl_kind.Z3_OP_BUDIV -> res <- res + "u/ "
            | Z3_decl_kind.Z3_OP_BASHR -> res <- res + ">> "
            | Z3_decl_kind.Z3_OP_BLSHR -> res <- res + ">>> "
            | Z3_decl_kind.Z3_OP_BSHL -> res <- res + "<< "
            | x -> if int x <> -1 then  res <- res + "? "

            for j in 0 .. nParam - 1 do
                res <- res + (r.getParameter j).ToString() + " "
            if nParam > 0 then
                res <- res + ") "

        for i in 0 .. r.numArguments - 1 do
            match nDB with
            | Some (nDB) ->
               if r.isArgumentNumeral i then
                  res <- res + (((!nDB).getNumeral (abs (r.getArgument i))).ToString()) + " "
               else
                  res <- res + ((r.getArgument i).ToString()) + ":bv "
            | None ->
                res <- res + (abs (r.getArgument i)).ToString() + (if r.isArgumentNumeral i then ":num " else ":bv ")

        res <- res + (match r.getRelationOP with
                     | Z3_decl_kind.Z3_OP_EQ -> "= "
                     | Z3_decl_kind.Z3_OP_ULT
                     | Z3_decl_kind.Z3_OP_SLT -> "< "
                     | Z3_decl_kind.Z3_OP_UGT
                     | Z3_decl_kind.Z3_OP_SGT -> "> "
                     | Z3_decl_kind.Z3_OP_ULEQ
                     | Z3_decl_kind.Z3_OP_SLEQ  -> "<= "
                     | Z3_decl_kind.Z3_OP_UGEQ
                     | Z3_decl_kind.Z3_OP_SGEQ -> ">= "
                     | _ -> failwith "Unknown relation" )

        match nDB with
            | Some (nDB) -> res <- res +
                                 if r.isRhsNumeral then
                                    ((!nDB).getNumeral (abs r.getRhs)).ToString()
                                 else
                                    (r.getRhs.ToString() + ":bv")
            | None -> res <- res +  (abs r.getRhs).ToString() + (if r.isRhsNumeral then ":num " else ":bv")

        res

    member t.isPAPredicate =
        t.isSimpleRelation &&
        t.getRelationOP = Z3_decl_kind.Z3_OP_EQ  &&
        (t.isArgumentNumeral 0 || t.isArgumentNumeral 1)

    member t.getPAPredicateVariable =
        assert (t.isPAPredicate)
        if (t.isArgumentNumeral 0) then
            t.getArgument 1 //t.getRhs
        else
            t.getArgument 0

    member t.getPAPredicateValue (nums:Ref<NumeralDB>) =
        assert (t.isPAPredicate)
        if (t.isArgumentNumeral 0) then
            (!nums).getNumeral (abs (t.getArgument 0))
        else
            (!nums).getNumeral (abs t.getRhs)


    member t.isUpperBoundPredicate =
        t.isSimpleRelation &&
        t.getRelationOP = Z3_decl_kind.Z3_OP_ULEQ &&
        not (t.isArgumentNumeral 0) &&
        t.isArgumentNumeral 1 //t.isRhsNumeral

    member t.isLowerBoundPredicate =
        t.isSimpleRelation &&
        t.getRelationOP = Z3_decl_kind.Z3_OP_ULEQ &&
        (t.isArgumentNumeral 0) &&
        not (t.isArgumentNumeral 1) // not t.isRhsNumeral

    member t.isBoundsPredicate =
        t.isLowerBoundPredicate || t.isUpperBoundPredicate || t.isPAPredicate //AZ: I don't like this, but don't know how else to do it in an elegant way

    member t.getBoundsPredicateVariable =
        assert (t.isBoundsPredicate)
        if (t.isArgumentNumeral 0) then
            t.getArgument 1
        else
            t.getArgument 0

    member t.getBoundsPredicateValue (nums:Ref<NumeralDB>) =
        assert (t.isBoundsPredicate)
        if t.isPAPredicate then
            let pattern = t.getPAPredicateValue nums
            let lb = pattern.Minimum
            let ub = pattern.Maximum
            Interval(lb,ub)
        elif t.isArgumentNumeral 0 then
            let lb = (!nums).getNumeral (abs (t.getArgument 0))
            let ub = (BitVector lb.Length)
            ub.Bits <- [(lb.Length, Bit.One)]
            Interval(lb, ub)
        else
            assert(t.isRhsNumeral)
            let ub = (!nums).getNumeral (abs t.getRhs)
            let lb = (BitVector ub.Length)
            lb.Bits <- [(lb.Length, Bit.Zero)]
            Interval(lb, ub)

    static member isArithmetic (t:TheoryRelation) =
        t.getRelationOP = Z3_decl_kind.Z3_OP_ULEQ ||
            match t.getBVOP with
            | Z3_decl_kind.Z3_OP_BADD
            | Z3_decl_kind.Z3_OP_BMUL
            | Z3_decl_kind.Z3_OP_BSUB
            | Z3_decl_kind.Z3_OP_BSDIV
            | Z3_decl_kind.Z3_OP_BUDIV -> true
            | _ -> false

let EmptyThRel = TheoryRelation (0, Z3_decl_kind.Z3_OP_EQ, 0)


let lookUp (expr2Var:Dictionary<Expr,Var>) (numExpr2Id:Dictionary<Expr,int>) (e:Expr) =
    let mutable res = 0
    if expr2Var.TryGetValue(e, &res) then
        Some res
    else if numExpr2Id.TryGetValue(e, &res) then
        Some res
    else
        None


let thRelFromRel (expr2Var:Dictionary<Expr,Var>) (numExpr2Id:Dictionary<Expr,int>) (nDB:ref<NumeralDB>) (e:Expr) =
    assert (supportedBVOP e.FuncDecl.DeclKind)
    assert (isBoolRelation e)

    let mutable args = []
    let mutable bvOpArgs = []
    let mutable bvParams = []
    let mutable numInds = -1

    let boolVar = match lookUp expr2Var null e with
                  | Some v -> v
                  | None -> assert(false)
                            (0:Var)

    for i in 0 .. (int e.NumArgs) - 1 do
        let currArg = e.Args.[i]
        match lookUp expr2Var numExpr2Id currArg with
        | Some v ->
            args <- args @ [v]
            numInds <- i
        | _ ->
            let aargs = Array.map (lookUp expr2Var numExpr2Id) currArg.Args
            for j in 0 .. (Array.length aargs) - 1 do
                match aargs.[j] with
                | Some(q) -> bvOpArgs <- bvOpArgs @ [q]
                | _ -> printf "Error in constructing ThRel"
                       assert(false)
            for k in 0 .. (int currArg.FuncDecl.NumParameters - 1) do
                let p = currArg.FuncDecl.Parameters.[k]
                assert(p.ParameterKind = Z3_parameter_kind.Z3_PARAMETER_INT)
                bvParams <- bvParams @ [currArg.FuncDecl.Parameters.[k].Int]

    assert(args.Length <> 0)

    // |sz|2|relOP|numeral|numeral| / |var|var|

    let res =   if args.Length = 2 then
                    let lhs = args.Head
                    let rhs = args.Tail.Head

                    if e.FuncDecl.DeclKind =  Z3_decl_kind.Z3_OP_EQ && rhs < 0 then
                        TheoryRelation (rhs, e.FuncDecl.DeclKind, lhs)
                    else
                        TheoryRelation (lhs, e.FuncDecl.DeclKind, rhs)
                else
                    assert (args.Length = 1) // There has to be a RHS
                    let bvop = e.Args.[1-numInds].FuncDecl.DeclKind   //1-numInds works as not
                    TheoryRelation (bvop, bvParams, bvOpArgs, e.FuncDecl.DeclKind, args.Head)

    res.setBoolvar boolVar
    dbg <| (lazy sprintf "| %s    [ = Z3's %s]" (res.ToString(nDB)) (e.ToString()))
    res


//TO-DONE: There is no boolean variable introduced for the as-of-yet non-existant equality!
//         A placeholder variable is introduced of sort boolean, it will have the number of e + 1!
let newThRelFromBVOP (expr2Var:Dictionary<Expr,Var>) (numExpr2Id:Dictionary<Expr,int>) (nDB:ref<NumeralDB>) (e:Expr)  =
    assert (e.IsBV)
    assert (supportedBVOP e.FuncDecl.DeclKind)

    let boolVar = match lookUp expr2Var null e with
                  | Some v -> v + 1
                  | _ -> 0

    let rhs = match lookUp expr2Var numExpr2Id e with
              | Some v -> v
              | _ -> printf "Error - bvExpr didn't have a variable introduced"
                     0

    let aargs = Array.map (lookUp expr2Var numExpr2Id) e.Args
    let bvArgs = Array.zeroCreate (int e.NumArgs)
    let mutable bvParams = []
    for j in 0  ..  Array.length aargs - 1 do
        bvArgs.[j] <-   match aargs.[j] with
                        | Some v -> v
                        | _ -> printf "Error in constructing ThRel"
                               0
    for j in 0 .. (int e.FuncDecl.NumParameters - 1 ) do
        let p = e.FuncDecl.Parameters.[j]
        assert(p.ParameterKind = Z3_parameter_kind.Z3_PARAMETER_INT)
        if p.ParameterKind = Z3_parameter_kind.Z3_PARAMETER_INT then
            bvParams <- e.FuncDecl.Parameters.[j].Int :: bvParams
    let res = TheoryRelation (e.FuncDecl.DeclKind, (List.rev bvParams), (Array.toList bvArgs), Z3_decl_kind.Z3_OP_EQ, rhs)
    res.setBoolvar boolVar
    dbg <| (lazy sprintf "Implicit theory equality: %s == %s" (res.ToString(nDB)) (e.ToString()))
    res
