module Preprocessing

open Microsoft.Z3
open System.Collections
open System.Collections.Generic
open GlobalOptions
open Util

let eliminateRelations (z3:Context) (e:Expr) (added_assertions : Ref< List<BoolExpr> >) =

// CMW: Z3 has already rewritten x > y into not y <= x. We may want to rewrite that further?
//    if e.FuncDecl.DeclKind = Z3_decl_kind.Z3_OP_NOT then
//        let c = e.Args.[0] :?> BoolExpr
//
//        if c.NumArgs > 1u && c.Args.[0].IsBV then
//            match c.FuncDecl.DeclKind with
//            | Z3_decl_kind.Z3_OP_ULEQ when c.Args.[0].IsBV  ->
//
//            | Z3_decl_kind.Z3_OP_SLEQ when c.Args.[0].IsBV  ->
//
//            | _ -> e
//        else
//            e

    if not (e.NumArgs = 2ul && e.Args.[0].IsBV && e.Args.[1].IsBV) then
        e
    else
        let x = e.Args.[0] :?> BitVecExpr
        let y = e.Args.[1] :?> BitVecExpr

        let size = x.SortSize
        let zero = z3.MkBV(0, size)
        let one  = z3.MkBV(1, size)
        let signflip_pattern = (if size > 1u then
                                     (z3.MkConcat(z3.MkBV(1, 1u), z3.MkBV(0, size - 1u)))
                                 else
                                     z3.MkBV(1, 1u) :> BitVecExpr)
        let signflip = (fun x -> z3.MkBVAdd(x, signflip_pattern))


        // We rewrite all comparison operators to unsigned less-than ULE
        match e.FuncDecl.DeclKind with
        | Z3_decl_kind.Z3_OP_ULEQ ->
            // OK, keep as is.
            e
        | Z3_decl_kind.Z3_OP_ULT ->
            // x < y  <==>  x <= y - 1 /\ y <> 0
            // CMW: I changed this from x < y  <==> x + 1 <= y /\ x <> 11...11 to avoid the large 2^size
            let y_minus_1 = z3.MkBVSub(y, one)
            let x_le_y_minus_1 = z3.MkBVULE (x, y_minus_1)
            let y_non_zero = z3.MkNot(z3.MkEq(y, z3.MkBV(0, size)))
            ((z3.MkAnd ([| x_le_y_minus_1; y_non_zero|])) :> Expr)
        | Z3_decl_kind.Z3_OP_UGT ->
            // x > y  <==> y <= x - 1 /\ x <> 0
            // CMW: I changed this from x + 1 <= y /\ x <> 11...11, to avoid the large 2^size
            let x_minus_1 = z3.MkBVSub(x, one)
            let y_le_x_minus_1 = z3.MkBVULE (y, x_minus_1)
            let x_non_zero = z3.MkNot(z3.MkEq(x, z3.MkBV(0, size)))
            ((z3.MkAnd ([| y_le_x_minus_1; x_non_zero |])) :> Expr)
        | Z3_decl_kind.Z3_OP_UGEQ ->
            // x >= y --> y <= x
            ((z3.MkBVULE (y, x)) :> Expr)

        | Z3_decl_kind.Z3_OP_SLEQ ->
            // x s<= y <==> xs u<= ys, where xs = (signflip x), ys = (signflip y)
            (z3.MkBVULE ((signflip x), (signflip y))) :> Expr
        | Z3_decl_kind.Z3_OP_SLT ->
            // x s< y <==> xs u<  ys, where xs = (signflip x), ys = (signflip y)
            //        <==> xs u<= ys - 1  /\  ys <> 00...0
            let x_flipped = (signflip x)
            let y_flipped = (signflip y)
            let y_minus_1 = z3.MkBVSub(y_flipped, one)
            let x_ule_y_minus_1 = z3.MkBVULE (x_flipped, y_minus_1)
            let y_non_zero = z3.MkNot(z3.MkEq(y_flipped, zero))
            (z3.MkAnd ([| x_ule_y_minus_1; y_non_zero|])) :> Expr
        | Z3_decl_kind.Z3_OP_SGT ->
            // x s> y <==> y s< x
            //        <==> ys u< xs, where xs = (signflip x), ys = (signflip y)
            //        <==> ys u<= xs - 1  /\  xs <> 00...0
            let x_flipped = (signflip x)
            let y_flipped = (signflip y)
            let x_minus_1 = z3.MkBVSub(x_flipped, one)
            let y_ule_x_minus_1 = z3.MkBVULE (y_flipped, x_minus_1)
            let x_non_zero = z3.MkNot(z3.MkEq(x_flipped, zero))
            (z3.MkAnd ([| y_ule_x_minus_1; x_non_zero |])) :> Expr
        | Z3_decl_kind.Z3_OP_SGEQ ->
            // x s>= y <==> (signflip ys) u<= (signflip xs)
            (z3.MkBVULE ((signflip y), (signflip x))) :> Expr

        | _ -> e


let naryToBinary (z3:Context) (expr:Expr) (added_assertions:Ref< List<BoolExpr> >) =
    if expr.IsBV && expr.NumArgs > 2u then
        let folder = match expr.FuncDecl.DeclKind with
                     | Z3_decl_kind.Z3_OP_BAND -> (fun x y -> z3.MkBVAND (x, y))
                     | Z3_decl_kind.Z3_OP_BOR -> (fun x y -> z3.MkBVOR (x, y))
                     | Z3_decl_kind.Z3_OP_BXOR -> (fun x y -> z3.MkBVXOR (x, y))
                     | Z3_decl_kind.Z3_OP_CONCAT -> (fun x y -> z3.MkConcat (x,y))
                     | Z3_decl_kind.Z3_OP_BADD -> (fun x y -> z3.MkBVAdd (x,y))
                     | Z3_decl_kind.Z3_OP_BMUL -> (fun x y -> z3.MkBVMul (x,y))
                     | _ -> NOT_YET_IMPLEMENTED(sprintf "nary->binary conversion for %s" (expr.FuncDecl.DeclKind.ToString()))

        let mutable current = expr.Args.[0] :?> BitVecExpr
        for i in 1 .. (int expr.NumArgs) - 1 do
            current <- folder current (expr.Args.[i] :?> BitVecExpr)
            let nn = z3.MkFreshConst("mcbv", current.FuncDecl.Range)
            (!added_assertions).Add(z3.MkEq(nn, current))
            current <- nn :?> BitVecExpr

        current :> Expr
    else
        expr


let eliminateDivI (z3:Context) (e:Expr) (added_assertions:Ref< List<BoolExpr> >) =
    // CMW: SDIV_I and UDIV_I are internal operations meaning BV division, where
    // div/0 has a fixed interpretation. That is the only division we support,
    // so we rewrite the DIV_I expressions to default B*DIV divisions.
    if (e.Args.Length = 2) then
        match (e.FuncDecl.Name.ToString()) with
        | "bvsdiv_i" -> z3.MkBVSDiv(e.Args.[0] :?> BitVecExpr, e.Args.[1] :?> BitVecExpr) :> Expr
        | "bvudiv_i" -> z3.MkBVUDiv(e.Args.[0] :?> BitVecExpr, e.Args.[1] :?> BitVecExpr) :> Expr
        | "bvsrem_i" -> z3.MkBVSRem(e.Args.[0] :?> BitVecExpr, e.Args.[1] :?> BitVecExpr) :> Expr
        | "bvurem_i" -> z3.MkBVURem(e.Args.[0] :?> BitVecExpr, e.Args.[1] :?> BitVecExpr) :> Expr
        | "bvsmod_i" -> z3.MkBVSMod(e.Args.[0] :?> BitVecExpr, e.Args.[1] :?> BitVecExpr) :> Expr
        | _ -> e
    else
        e


let normalize (ht:Dictionary<Expr, Expr>) (z3:Context) (e:Expr) (added_assertions:Ref< List<BoolExpr> >) =
    assert(e.IsBV || e.IsBool)

    let mk_new_args = fun args ->
        Array.map (fun (x:Expr) ->
            if x.IsConst || x.IsNumeral then x else
            match ht.TryGetValue x with
            | (true, y) -> y
            | (false, _) ->
                let y = z3.MkFreshConst("mcbv", x.FuncDecl.Range)
                ht.Add(x, y)
                (!added_assertions).Add(z3.MkEq(y, x))
                y
            ) args

    if e.IsConst || e.IsNumeral then
        e
    elif (e.IsBool) then
        let allBVArgs = not (Array.exists (fun (x:Expr) -> not x.IsBV) e.Args)
        match e.FuncDecl.DeclKind with
            | Z3_decl_kind.Z3_OP_EQ
            | Z3_decl_kind.Z3_OP_ULEQ
            | Z3_decl_kind.Z3_OP_SLEQ
            | Z3_decl_kind.Z3_OP_ULT
            | Z3_decl_kind.Z3_OP_SLT
            | Z3_decl_kind.Z3_OP_UGEQ
            | Z3_decl_kind.Z3_OP_SGEQ
            | Z3_decl_kind.Z3_OP_UGT
            | Z3_decl_kind.Z3_OP_SGT when allBVArgs -> e.FuncDecl.Apply (mk_new_args e.Args)
            | _ -> e
    elif e.IsBV then
        e.FuncDecl.Apply (mk_new_args e.Args)
    else
        NOT_YET_IMPLEMENTED("non-bv operator")
        e


let rewrite_f (z3:Context) (e:Expr) (added_assertions:Ref< List<BoolExpr> >) (f:Context -> Expr -> Ref< List<BoolExpr> > -> Expr) =
    let mutable stack = new Stack<Expr>()
    let mutable cache = ref (Hashtable())
    let caching_f = (fun (x:Expr) (s:Ref< Stack<Expr> >) (c:Ref< Hashtable >) (aa:Ref< List<BoolExpr> >) ->
                        let cached_value = if ((!c).ContainsKey(x)) then Some((!c).[x]) else None
                        match cached_value with
                        | Some(cv) -> c
                        | _ ->
                            let missing_args = (Array.fold
                                               (fun cnt y -> cnt + if not ((!c).ContainsKey(y)) then 1 else 0)
                                               0 x.Args)
                            if missing_args > 0 then
                                (!s).Push(x)
                                Array.map (fun y -> if not ((!c).ContainsKey(y)) then (!s).Push(y); ()) x.Args |> ignore
                                c
                            else
                                let rcs_f = (fun (y:Expr) -> if not ((!c).ContainsKey(y)) then assert(false)
                                                             let w = ((!c).[y]) :?> Expr
                                                             w)
                                let rcs = Array.map rcs_f x.Args
                                let nx = (x.FuncDecl.Apply rcs)
                                let rx = (f z3 nx aa)
                                (!c).Add(x, rx)
                                c
                                )
    stack.Push(e) |> ignore
    while stack.Count <> 0 do
        let ce = stack.Pop()
        cache <- (caching_f ce (ref stack) cache added_assertions)
    assert((!cache).ContainsKey(e))
    (!cache).[e]


let rewriteGoal (z3:Context) (g:Goal) (f:Context -> Expr -> Ref< List<BoolExpr> > -> Expr) =
    let newGoal = z3.MkGoal ()

    let added_assertions  = ref (List<BoolExpr>())
    let forms = g.Formulas;
    for i in 0 .. forms.Length - 1 do
        let ge = forms.[i]
        trace <| (lazy sprintf "Rewriting: %s" ((ge :> Expr).ToString()))
        let rewritten = (rewrite_f z3 ge added_assertions f) :?> BoolExpr
        if (rewritten <> ge) then trace <|  (lazy sprintf "Rewritten:\n %s\n to (goal index %d)\n %s" ((ge :> Expr).ToString()) i (rewritten.ToString()))
        newGoal.Assert(rewritten)
    for i in 0 .. (!added_assertions).Count - 1 do
        trace <| (lazy sprintf "Added assertion: %s" ((!added_assertions).[i].ToString()))
        newGoal.Assert((!added_assertions).[i])

    newGoal


let preprocess (z3:Context) (goal:Goal) =
    let solveEqsParams = z3.MkParams()
    solveEqsParams.Add("solve_eqs_max_occs", (uint32)2)
    let defaultParams = z3.MkParams()

    let mutable newGoal = goal

    verbose <| (lazy "Preprocessing/rewriting ...")

    if PREPROCESS then
        let simp2_p = z3.MkParams()
        simp2_p.Add("som", true)
        simp2_p.Add("pull_cheap_ite", true)
        simp2_p.Add("push_ite_bv", false)
        simp2_p.Add("local_ctx", true)
        simp2_p.Add("local_ctx_limit", (uint32)10000000)
        simp2_p.Add("flat", true)
        simp2_p.Add("hoist_mul", false)
        simp2_p.Add("hi_div0", true)


        let simpTac = z3.MkTactic("simplify")
        let preprocessing = [   z3.UsingParams(simpTac,simp2_p);
                                z3.MkTactic("elim-term-ite");
                                z3.MkTactic("propagate-values");
                                z3.UsingParams(z3.MkTactic("solve-eqs"),solveEqsParams);
                                simpTac;
                                z3.MkTactic("elim-uncnstr");
                                z3.UsingParams(simpTac,simp2_p);
                                z3.MkTactic("elim-term-ite");
                                z3.MkTactic("tseitin-cnf");
                                  ]
        for tac in preprocessing do
            newGoal <- tac.Apply(newGoal,defaultParams).Subgoals.[0]

    newGoal <- rewriteGoal z3 newGoal eliminateRelations
    newGoal <- rewriteGoal z3 newGoal eliminateDivI
    newGoal <- rewriteGoal z3 newGoal (normalize (new Dictionary<Expr, Expr>()))
    newGoal <- rewriteGoal z3 newGoal naryToBinary

    verbose <| (lazy "Preprocessing/rewriting done.")

    newGoal


