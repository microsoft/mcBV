module Z3Check

open System.IO
open System.Collections.Generic
open Microsoft.Z3

open GlobalOptions
open Util
open Bit
open BitVector
open Interval
open Literal
open BooleanValuation
open BitVectorValuation
open BoundsValuation
open Database
open Clause
open TheoryRelation
open Trail


let mutable private constants : Expr list = []

let bv2expr (ctx:Context) (bv:BitVector) (width:int)=
    if bv.isFullyUndefined then
        ctx.MkFreshConst("z3check-0", ctx.MkBitVecSort(uint32 width)) :?> BitVecExpr
    else
        let chunks = [
            for (n, b) in bv.Bits do
                match b with
                | One  -> yield ctx.MkRepeat((uint32 n), ctx.MkBV((uint32 1), (uint32 1))) :> Expr
                | Zero -> yield ctx.MkRepeat((uint32 n), ctx.MkBV((uint32 0), (uint32 1))) :> Expr
                | U    ->
                    let c = ctx.MkFreshConst("z3check-u", ctx.MkBitVecSort((uint32 n)))
                    constants <- c :: constants
                    yield c
                | N -> UNREACHABLE("unexpected N bits")
        ]


        let f = (fun (a:Expr) (x:Expr) -> ctx.MkConcat(a :?> BitVecExpr, x :?> BitVecExpr).Simplify())
        List.fold f chunks.Head chunks.Tail :?> BitVecExpr


let thRel2expr (ctx:Context) (trel:TheoryRelation) (db:Ref<Database>) (vars:Expr[]) =
    let vDB = !(!db).Variables
    let nDB = !(!db).Numerals
    let rhs = if trel.getRhs >= 0 then
                vars.[trel.getRhs] :?> BitVecExpr
              else
                let nmrl = (nDB.getNumeral (abs trel.getRhs))
                (bv2expr ctx nmrl nmrl.Length)

    let args = [| for i in 0 .. trel.numArguments - 1 do
                    let ai = trel.getArgument i
                    if trel.isArgumentNumeral i then
                        let nmrl = nDB.getNumeral (abs ai)
                        yield bv2expr ctx nmrl nmrl.Length
                    else
                        assert(not (vDB.isBoolean ai))
                        yield vars.[ai] :?> BitVecExpr |]

    let lhs =
        if not trel.hasBVOP then
            assert (args.Length = 1)
            args.[0]
        else
            match trel.getBVOP with
            | Z3_decl_kind.Z3_OP_BADD ->
                assert(args.Length = 2)
                ctx.MkBVAdd(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_BSUB ->
                assert(args.Length = 2)
                ctx.MkBVSub(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_BMUL->
                assert(args.Length = 2)
                ctx.MkBVMul(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_BSDIV ->
                assert(args.Length = 2)
                ctx.MkBVSDiv(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_BUDIV ->
                assert(args.Length = 2)
                ctx.MkBVUDiv(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_BSREM ->
                assert(args.Length = 2)
                ctx.MkBVSRem(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_BUREM ->
                assert(args.Length = 2)
                ctx.MkBVURem(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_BSMOD ->
                assert(args.Length = 2)
                ctx.MkBVSMod(args.[0], args.[1])

            | Z3_decl_kind.Z3_OP_BASHR ->
                assert(args.Length = 2)
                ctx.MkBVASHR(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_BLSHR ->
                assert(args.Length = 2)
                ctx.MkBVLSHR(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_BSHL ->
                assert(args.Length = 2)
                ctx.MkBVSHL(args.[0], args.[1])

            | Z3_decl_kind.Z3_OP_CONCAT ->
                assert(args.Length = 2)
                ctx.MkConcat(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_EXTRACT ->
                assert(args.Length = 1)
                ctx.MkExtract((uint32 (trel.getParameter 0)), (uint32 (trel.getParameter 1)), args.[0])
            | Z3_decl_kind.Z3_OP_REPEAT ->
                assert(args.Length = 1)
                ctx.MkRepeat((uint32 (trel.getParameter 0)), args.[0])

            | Z3_decl_kind.Z3_OP_BNOT ->
                assert(args.Length = 1)
                ctx.MkBVNot(args.[0])
            | Z3_decl_kind.Z3_OP_BNEG ->
                assert(args.Length = 1)
                ctx.MkBVNeg(args.[0])
            | Z3_decl_kind.Z3_OP_BAND  ->
                assert(args.Length = 2)
                ctx.MkBVAND(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_BOR  ->
                assert(args.Length = 2)
                ctx.MkBVOR(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_BXOR ->
                assert(args.Length = 2)
                ctx.MkBVXOR(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_BXNOR ->
                assert(args.Length = 2)
                ctx.MkBVXNOR(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_BNAND ->
                assert(args.Length = 2)
                ctx.MkBVNAND(args.[0], args.[1])
            | Z3_decl_kind.Z3_OP_BNOR ->
                assert(args.Length = 2)
                ctx.MkBVNOR(args.[0], args.[1])

            | _ -> NOT_YET_IMPLEMENTED(sprintf "%s" (trel.getBVOP.ToString()))

    let res =
        match trel.getRelationOP with
        | Z3_decl_kind.Z3_OP_EQ ->
            if trel.isPAPredicate then
                // Partial assignments may contain U-bits, we need to constrain
                // the LHS
                let r = ctx.MkEq(lhs, rhs)
                r
            else
                ctx.MkEq(lhs, rhs)
        | Z3_decl_kind.Z3_OP_ULEQ -> ctx.MkBVULE(lhs, rhs)
        | _ -> NOT_YET_IMPLEMENTED(sprintf "%s" (trel.getRelationOP.ToString()))

    res


let mkZ3Vars (ctx:Context) (db:Ref<Database>) =
    let vDB = (!(!db).Variables)
    [|  yield ctx.MkBoolConst("v0") :> Expr;
        for i in 1 .. vDB.highestVarInUse do
            if vDB.isBoolean i then
                yield (ctx.MkBoolConst(i.ToString())) :> Expr
            else
                assert(vDB.isBitVector i)
                let vs = vDB.getBitVectorLength i
                yield (ctx.MkBVConst(i.ToString() + ":bv", (uint32 vs))) :> Expr |]


let mkZ3Clause (ctx:Context) (vars:Expr[]) (c:Clause) =
    if isEmptyClause(c) then
        ctx.MkFalse()
    else
        ctx.MkOr([| for i in 1 .. c.Length - 1 do
                        let cl = c.[i]
                        let cv = lit2var cl
                        assert(vars.[cv].IsBool)
                        let ctxv = vars.[cv] :?> BoolExpr
                        if cl < 0 then
                            yield ctx.MkNot(ctxv)
                        else
                            yield ctxv
                |]).Simplify() :?> BoolExpr


let getClauseConstraints (ctx:Context) (db:Ref<Database>) (vars:Expr[]) (c:Clause) =
    let tDB = (!(!db).Theory)
    let trels = [|
        for i in 1 .. getSize(c) do
            let cl = c.[i]
            let cv = lit2var cl
            assert (vars.[cv].IsBool)
            let trv = vars.[cv]
            let asmptn = (if cl < 0 then ctx.MkNot(trv :?> BoolExpr) else trv :?> BoolExpr)
            if tDB.isDefined cv then
                let z3tr = (thRel2expr ctx (tDB.getThRelation cv) db vars).Simplify()
                yield (asmptn, ctx.MkEq(trv :?> BoolExpr, z3tr))
            else
                yield (asmptn, ctx.MkTrue())
             |]
    (Array.map (fun (x, y) -> x) trels, Array.map (fun x -> (snd x)) trels)


let mkTrailConstraints (ctx:Context) (trail:Ref<Trail>) (db:Ref<Database>) (bvVal:Ref<BitVectorValuation>) (bounds:Ref<BoundsValuation>) (vars:Expr[]) (include_bounds:bool) =
    let vDB = !(!db).Variables
    let descrs = new Dictionary<BoolExpr, string>()

    let ma_old_MAs = new Dictionary<int, (int * BitVector)>()
    let ma_old_BAs = new Dictionary<int, ((int * int) * Interval)>()

    let mutable res = []
    // CMW: I'm assuming that everything between trail.getTrailPtr
    // and trail.getCount is previous garbage that hasn't been removed.
    for i = (!trail).getTrailPtr - 1 downto 0 do
        match (!trail).trail.[i] with
        | BoolDecision l ->
            let v = vars.[lit2var l] :?> BoolExpr
            let l = if l < 0 then ctx.MkNot v else v
            let fc = ctx.MkFreshConst("z3check", ctx.BoolSort) :?> BoolExpr
            descrs.Add(fc, "decision " + l.ToString())
            res <- ctx.MkImplies(fc, l) :: res
        | Imp (rc, l) ->
            let c = mkZ3Clause ctx vars !rc
            let fc = ctx.MkFreshConst("z3check", ctx.BoolSort) :?> BoolExpr
            descrs.Add(fc, "implication of " + l.ToString())
            res <- ctx.MkImplies(fc, c) :: res
        | MAssgnmnt (v, prev_expl, prev_val) ->
            let z3v = vars.[v] :?> BitVecExpr
            let ss = (int (vDB.getBitVectorLength v))

            let (current_expl, current_val) =
                match (ma_old_MAs.TryGetValue v) with
                | (true, m) -> m
                | (false, _) -> ((!bvVal).mAssignmntsExplanations.[v], (!bvVal).getValue v)
            assert(current_val.isFullyUndefined || current_expl <> 0)

            let fc = ctx.MkFreshConst("z3check", ctx.BoolSort) :?> BoolExpr
            let ve = (bv2expr ctx current_val ss)
            let c = ctx.MkEq(vars.[v], ve)

            let ex_var = lit2var current_expl
            let ex_z3_var = vars.[ex_var] :?> BoolExpr
            let ex_z3_lit = if current_expl > 0 then ex_z3_var else ctx.MkNot(ex_z3_var)
            res <- ctx.MkImplies(ctx.MkAnd(fc, ex_z3_lit), c) :: res
            descrs.Add(fc, sprintf "model assignment %d:bv = %s" v (current_val.ToString()))

            ma_old_MAs.[v] <- (prev_expl, prev_val)
            let nv = ctx.MkBVConst((sprintf "%d:bv-%d" v prev_expl), (uint32 ss))
            vars.SetValue(nv, v)
        | BAssgnmnt  (v, prev_expl, prev_intvl) ->
            let z3v = vars.[v] :?> BitVecExpr
            let ss = (int (vDB.getBitVectorLength v))

            let (current_expl, current_intvl) =
                match (ma_old_BAs.TryGetValue v) with
                | (true, m) -> m
                | (false, _) -> let q = (!bounds).get v
                                let expls = ((!bounds).getExplanations v)
                                (expls, ((!bounds).get v))
            assert(current_intvl.isFull || (fst current_expl) <> 0 || (snd current_expl) <> 0)

            let fc_lb = ctx.MkFreshConst("z3check", ctx.BoolSort) :?> BoolExpr
            let c_lb = ctx.MkBVULE((bv2expr ctx current_intvl.Lower ss), z3v)
            res <- ctx.MkImplies(fc_lb, c_lb) :: res
            descrs.Add(fc_lb, sprintf "lower bound %s <= %d:bv" (current_intvl.Lower.ToString()) v)

            let fc_ub = ctx.MkFreshConst("z3check", ctx.BoolSort) :?> BoolExpr
            let c_ub = ctx.MkBVULE(z3v, (bv2expr ctx current_intvl.Upper ss))
            res <- ctx.MkImplies(fc_ub, c_ub) :: res
            descrs.Add(fc_ub, sprintf "upper bound %d:bv <= %s" v (current_intvl.Upper.ToString()))

            ma_old_BAs.[v] <- (prev_expl, prev_intvl)
            let nv = ctx.MkBVConst((sprintf "%d:bv-(%d,%d)" v (fst prev_expl) (snd prev_expl)), (uint32 ss))
            vars.SetValue(nv, v)

    let assumptions = [| for r in descrs do yield r.Key |]
    (assumptions, Array.ofList res, descrs)


let mkProblemConstraints (ctx:Context) (db:Ref<Database>) (vars:Expr[]) =
    let cDB = !(!db).Clauses
    let tDB = !(!db).Theory
    let units = [| for u in cDB.units do
                        yield mkZ3Clause ctx vars u |]

    let cs = [| for cinx in 0 .. cDB.count - 1 do
                    if not (cDB.isLearned cinx) then
                        let c = cDB.getClauseRef cinx
                        yield mkZ3Clause ctx vars !c |]

    // CMW: There appear to be cases where we can't verify an explanation using
    // solely the tRel definitions from the variables appearing in the original
    // clauses. I'm not convinced this is correct, but the definitions via
    // equalities below should be relatively safe to add, even if not all of
    // the definitions are really necessary.

//    let trels = [|  for c in cDB.originalClauses do
//                        for i in 1 ..  (getSize c) do
//                        let v = lit2var c.[i]
//                        if tDB.isDefined v then
//                            let trv = vars.[v]
//                            assert (trv.IsBool)
//                            let z3tr = (thRel2expr ctx (tDB.getThRelation v) db vars).Simplify()
//                            yield (trv, ctx.MkEq(trv :?> BoolExpr, z3tr)) |]

    let vDB = (!(!db).Variables) in
    let trels = [| for v in 1 .. vDB.highestVarInUse do
                   if vDB.isBoolean(v) && tDB.isDefined v then
                       let trv = vars.[v]
                       assert (trv.IsBool)
                       let z3tr = (thRel2expr ctx (tDB.getThRelation v) db vars).Simplify()
                       yield (trv, ctx.MkEq(trv :?> BoolExpr, z3tr)) |]

    let assmpts = units
    let cnstrns = (Array.append cs (Array.map (fun x -> (snd x)) trels))
    (assmpts, cnstrns)


let explainCore (ctx:Context) (core:BoolExpr[]) (descrs:Dictionary<BoolExpr, string>) =
    printfn "Z3> Unsatisfiable; the following constraints are involved:"
    for e in core do
        assert(e.IsBool && e.IsConst)
        printfn "Z3> %s" descrs.[e]
    ()


let explainCounterexample (ctx:Context) (db:Ref<Database>) (m:Model) (c:Clause) (vars:Expr[]) =
    let nDB = !(!db).Numerals
    let vDB = !(!db).Variables
    let tDB = !(!db).Theory

    // printfn "Z3> Raw model: %s" (m.ToString())

    printfn "Z3> Counterexample:"
    if isEmptyClause c then
        printfn "Z3> Always."
    else
        let mutable seen = []
        for i in 1 .. getSize(c) do
            let cl = c.[i]
            let cv = lit2var cl
            let z3v = vars.[cv]
            let ci = m.ConstInterp(z3v)
            printf "Z3> %d=%s" cv (if ci.IsTrue then "T" else "F")

            if tDB.isDefined cv then
                printf " <==> "
                if ci.IsFalse then printf "not "
                let trel = (tDB.getThRelation cv)
                printf "%s" (trel.ToString(ref nDB))
                for k in trel.variableArguments do
                    match List.tryFind (fun x -> x = k) seen with
                    | Some(n) -> ()
                    | None -> seen <- k :: seen

            printfn ""

        if seen.Length <> 0 then
            printfn "Z3> This is the case when, for instance, we have "
            let mutable first = true
            for v in seen do
                let z3mv = m.ConstInterp(vars.[v])
                let z3num = (z3mv :?> BitVecNum)
                let z3ms = if z3mv.IsBool then z3mv.ToString() else (BigIntegerToBinaryString (z3num.BigInteger) z3num.SortSize)
                printfn "Z3> %d%s = %s" v (if vDB.isBitVector v then ":bv" else "") z3ms
    ()


let checkTrailConsistency (ctx:Context) (trail:Ref<Trail>) (db:Ref<Database>) (bvVal:Ref<BitVectorValuation>) (bounds:Ref<BoundsValuation>) (vars:Expr[]) (include_bounds:bool) (silent:bool) =
    constants <- []
    let (tr_assmptns, tr_cnstrnts, descrs) = mkTrailConstraints ctx trail db bvVal bounds vars include_bounds

    if not silent then
        verbose <| (lazy "Z3> constraints:")
        for c in tr_cnstrnts do
            verbose <| (lazy ("Z3> " + (c.ToString())))
        verbose <| (lazy "Z3> Assumptions:")
        for a in tr_assmptns do
            verbose <| (lazy ("Z3> " + (a.ToString())))


    let body = ctx.MkAnd [| ctx.MkAnd tr_cnstrnts;
                            ctx.MkAnd tr_assmptns |]

    let cnstr = (if constants.Length > 0 then
                    // Trail consistency is established if there is at least one
                    // model, therefore \exists constants ...
                    ctx.MkExists(List.toArray constants, body) :> BoolExpr
                else
                    body)

    let mutable rs = Status.UNKNOWN
    let slvr = ctx.MkSolver()

    try
        slvr.Add cnstr
        rs <- slvr.Check()
    with ex ->
        printfn "Z3> caught exception: %s" ex.Message

    match rs with
    | Status.SATISFIABLE ->
        verbose <| (lazy "Z3> OK, trail consistent.")
    | Status.UNSATISFIABLE ->
        printfn "Z3> Error, trail inconsistent."
        explainCore ctx slvr.UnsatCore descrs
    | _ -> printfn "Z3> Gave up; probably because of quantifiers."

    rs = Status.SATISFIABLE || rs = Status.UNKNOWN


let checkTrailImpliesExplanation (ctx:Context) (trail:Ref<Trail>) (db:Ref<Database>) (bvVal:Ref<BitVectorValuation>) (bounds:Ref<BoundsValuation>) (vars:Expr[]) (c:Clause) (trailMustImplyC:bool) (include_bounds:bool) (silent:bool) =
    constants <- []
    let (trailAssumptions, trailConstraints, descrs) = mkTrailConstraints ctx trail db bvVal bounds vars include_bounds
    let (clauseAssumptions, clauseConstraints) = getClauseConstraints ctx db vars c
    let lhs = ctx.MkAnd(trailAssumptions)
    let rhs = ctx.MkOr(clauseAssumptions)
    let p = ctx.MkNot(ctx.MkImplies(lhs, rhs))

    if not silent then
        verbose <| (lazy "Z3> constraints:")
        for c in trailConstraints do
            verbose <| (lazy ("Z3> " + (c.ToString())))
        verbose <| (lazy "Z3> assumptions:")
        for a in trailAssumptions do
            verbose <| (lazy ("Z3> " + (a.ToString())))
        verbose <| (lazy ("Z3> p = " + (p.ToString())))

    let body = ctx.MkAnd [| ctx.MkAnd trailConstraints;
                            ctx.MkAnd clauseConstraints;
                            p |]

    let cnstr = (if constants.Length > 0 then
                    // to prove trail -> c we need to check
                    // \forall constants ...
                    ctx.MkForall(List.toArray constants, body) :> BoolExpr
                else
                    body)

    let mutable rs = Status.UNKNOWN
    let slvr = ctx.MkSolver()

    try

        slvr.Add cnstr
        rs <- slvr.Check()
    with ex ->
        printfn "Z3> caught exception: %s" ex.Message

    match rs with
    | Status.UNSATISFIABLE ->
        verbose <| (lazy "Z3> OK, trail implies explanation.")
    | Status.SATISFIABLE ->
        if trailMustImplyC then
            printfn "Z3> Error, trail does not imply explanation."
            explainCounterexample ctx db slvr.Model c vars
        else
            verbose <| (lazy "Z3> OK, trail does not imply explanation, but that's fine.")
    | _ -> printfn "Z3> Gave up; probably because of quantifiers."

    rs = Status.UNSATISFIABLE || rs = Status.UNKNOWN


let checkProblemImpliesExplanation (ctx:Context) (trail:Ref<Trail>) (db:Ref<Database>) (bvVal:Ref<BitVectorValuation>) (bounds:Ref<BoundsValuation>) (vars:Expr[]) (c:Clause) (silent:bool) =
    constants <- []
    let (passmptns, pcnstrnts) = mkProblemConstraints ctx db vars
    let (cassmptns, ccnstrnts) = getClauseConstraints ctx db vars c
    let lhs = ctx.MkAnd(passmptns)
    let rhs = ctx.MkOr(cassmptns)
    let p = ctx.MkNot(ctx.MkImplies(lhs, rhs))

    if not silent then
        verbose <| (lazy "Z3> constraints:")
        for c in pcnstrnts do
            verbose <| (lazy ("Z3> " + (c.ToString())))
        verbose <| (lazy "Z3> assumptions:")
        for a in passmptns do
            verbose <| (lazy ("Z3> " + (a.ToString())))
        verbose <| (lazy "Z3> clause constraints:")
        for c in ccnstrnts do
            verbose <| (lazy ("Z3> " + (c.ToString())))
        verbose <| (lazy "Z3> clause assumptions:")
        for a in cassmptns do
            verbose <| (lazy ("Z3> " + (a.ToString())))
        verbose <| (lazy ("Z3> p = " + (p.ToString())))

    let body = ctx.MkAnd [| ctx.MkAnd pcnstrnts;
                            ctx.MkAnd ccnstrnts;
                            p |]

    let cnstr = (if constants.Length > 0 then
                    // to prove problem -> c we need to check
                    // \forall constants ...
                    ctx.MkForall(List.toArray constants, body) :> BoolExpr
                else
                    body)

    let mutable rs = Status.UNKNOWN
    let slvr = ctx.MkSolver()
//    let p = ctx.MkParams()
//    p.Add("timeout", 1000ul)
//    slvr.Parameters <- p

    try
        slvr.Add cnstr
        rs <- slvr.Check()
    with ex ->
        printfn "Z3> caught exception: %s" ex.Message

    match rs with
    | Status.UNSATISFIABLE ->
        verbose <| (lazy "Z3> OK, problem implies explanation.")
    | Status.SATISFIABLE ->
        printfn "Z3> Error, problem does not imply explanation."
        explainCounterexample ctx db slvr.Model c vars
    | _ -> printfn "Z3> Gave up; probably because of quantifiers."

    rs = Status.UNSATISFIABLE || rs = Status.UNKNOWN


let checkClauseIsFalse (bVal:Ref<BooleanValuation>) (c:Clause) =
    let mutable is_false = true;
    for i in 1 .. getSize(c) do
        let leval = (!bVal).getValueB(c.[i])
        if leval <> BooleanValuation.False then
            printfn "Z3> Error, literal in conflict clause is not false (%d=%s)" c.[i] (leval.ToString())
            is_false <- false
    is_false


let checkClauseConsistency (c:Clause) =
    let nonzero =
        match Array.tryFind(fun x -> x = 0) c with
        | Some(_)  ->
            printfn "Z3> Error, clause contains 0."
            false
        | None -> true

    let mutable nodupes = true
    for i in 1 .. getSize(c) do
        for j in i + 1 .. getSize(c) do
            if c.[i] = c.[j] then
                printfn "Z3> Error, clause contains duplicates (%d \/ %d)" c.[i] c.[j]
                nodupes <- false

    let mutable tautological = false
    for i in 1 .. getSize(c) do
        for j in i + 1 .. getSize(c) do
            if c.[i] = (Literal.Negate c.[j]) then
                printfn "Z3> Error, clause is tautological (%d \/ %d \/ ...)" c.[i] c.[j]
                tautological <- true

    nonzero && nodupes && (not tautological)

let checkUNSAT (trail:Ref<Trail>) (db:Ref<Database>) (bvVal:Ref<BitVectorValuation>)
               (bounds:Ref<BoundsValuation>) (include_bounds:bool) =
//    let logfn = Path.GetRandomFileName() + ".log"
//    (printfn "Writing Z3 interaction log to %s" logfn)
//    (Log.Open logfn) |> ignore

    let sttngs = Dictionary<string, string>()
    sttngs.Add("model", "true")
    sttngs.Add("unsat_core", "true")
    Global.SetParameter("pp.min_alias_size", "1000")

    let ctx = new Context(sttngs)
    let g = ctx.MkGoal(true, false, false)
    let vars = (mkZ3Vars ctx db)

    let res = (checkTrailConsistency ctx trail db bvVal bounds vars include_bounds false)

    try
        ctx.Dispose()
        System.GC.Collect()
        //System.GC.WaitForPendingFinalizers()
        //System.GC.WaitForFullGCComplete() |> ignore
        //System.GC.Collect()
    with
    | :? System.AccessViolationException as ex -> printfn("Context disposal exception ignored.")

//    Log.Close()

    if not res then
        polite <| (lazy "Trail is indeed UNSAT")
    else
        failwith "UNSAT validation failed!"
    ()

let checkExplanation (trail:Ref<Trail>) (db:Ref<Database>) (bvVal:Ref<BitVectorValuation>) (bounds:Ref<BoundsValuation>)
                     (c:Clause) (trailMustImplyC:bool) (include_bounds:bool) (silent:bool) =
    if not RUNZ3CHECKS then
        ()
    else
        let first = lit2var c.[1]
        if DBG then printfn "Z3> Checking validity of %s." (clauseToString c)

//        let logfn = Path.GetRandomFileName() + ".log"
//        (printfn "writing z3 interaction log to %s" logfn)
//        (Log.Open logfn) |> ignore

        let sttngs = Dictionary<string, string>()
        sttngs.Add("model", "true")
        sttngs.Add("unsat_core", "true")
        Global.SetParameter("pp.min_alias_size", "1000")

        let ctx = new Context(sttngs)
        let g = ctx.MkGoal(true, false, false)
        let vars = (mkZ3Vars ctx db)

        let mutable res = (checkClauseConsistency c)

        if res then
            let a = (checkTrailConsistency ctx trail db bvVal bounds vars include_bounds silent)
            let b = (checkTrailImpliesExplanation ctx trail db bvVal bounds vars c trailMustImplyC include_bounds silent)
            let c = (checkProblemImpliesExplanation ctx trail db bvVal bounds vars c silent)

            res <-  (trailMustImplyC && (a && b && c)) ||
                    ((not trailMustImplyC) && (a && c))

        try
            ctx.Dispose()
            System.GC.Collect()
            //System.GC.WaitForPendingFinalizers()
            //System.GC.WaitForFullGCComplete() |> ignore
            //System.GC.Collect()
        with
        | :? System.AccessViolationException as ex -> printfn("Context disposal exception ignored.")

        if not res then
            (!trail).forcePrint("Z3> At the failure, the trail was: ", bvVal, bounds)
            failwith "Explanation validation failed."

//        Log.Close()
        ()


let checkClauseValidity (ctx:Context) (db:Ref<Database>) (vars:Expr[]) (c:Clause) (silent:bool) =

    constants <- []
    let (cassmptns, ccnstrnts) = getClauseConstraints ctx db vars c

    let p = ctx.MkNot(ctx.MkOr(cassmptns))

    if not silent then
        verbose <| (lazy "Z3> constraints:")
        verbose <| (lazy "Z3> clause constraints:")
        for c in ccnstrnts do
            verbose <| (lazy ("Z3> " + (c.ToString())))
        verbose <| (lazy "Z3> clause assumptions:")
        for a in cassmptns do
            verbose <| (lazy ("Z3> " + (a.ToString())))
        verbose <| (lazy ("Z3> p = " + (p.ToString())))

    let body = ctx.MkAnd [| ctx.MkAnd ccnstrnts; p |]

    let cnstr = (if constants.Length > 0 then
                    // \forall constants ...
                    ctx.MkForall(List.toArray constants, body) :> BoolExpr
                else
                    body)

    let slvr = ctx.MkSolver()
    slvr.Add cnstr
    let rs = slvr.Check()

    match rs with
    | Status.UNSATISFIABLE -> verbose <| (lazy "Z3> Clause is UNSATISFIABLE (Constraints are VALID).")
    | Status.SATISFIABLE -> verbose <| (lazy "Z3> Clause is SATISFIABLE (Constraints are INVALID).")
    | _ -> printfn "Z3> Gave up; probably because of quantifiers."

    rs = Status.UNSATISFIABLE

let checkIsGeneralizedExplanationValid (db:Ref<Database>) (c:Clause) (silent:bool) =
    if DBG then printfn "Z3_VALIDITTY_CHECK> Checking validity of %s." (clauseToString c)

//    let logfn = Path.GetRandomFileName() + ".log"
//    (printfn "Writing Z3 interaction log to %s" logfn)
//    (Log.Open logfn) |> ignore

    let sttngs = Dictionary<string, string>()
    sttngs.Add("model", "true")
    sttngs.Add("unsat_core", "true")
    Global.SetParameter("pp.min_alias_size", "1000")

    let ctx = new Context(sttngs)
    let g = ctx.MkGoal(true, false, false)
    let vars = (mkZ3Vars ctx db)

    let mutable res = (checkClauseConsistency c)

    if res then
        res <- checkClauseValidity ctx db vars c silent

    try
        ctx.Dispose()
        System.GC.Collect()
        System.GC.WaitForPendingFinalizers()
        System.GC.WaitForFullGCComplete() |> ignore
        System.GC.Collect()
    with
    | :? System.AccessViolationException as ex -> printfn("Context disposal exception ignored.")

//    Log.Close()

    res


