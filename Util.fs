module Util

open Microsoft.Z3
open System.Collections
open System.Collections.Generic
open System.Numerics
open GlobalOptions

let dbg (x:Lazy<string>) =
    if DBG then
        printfn "%s" (x.Force())

let trace (x:Lazy<string>) =
    if TRC then
        printfn "%s" (x.Force())

let verbose (x:Lazy<string>) =
    if VRB then
        printfn "%s" (x.Force())

let polite (x:Lazy<string>) =
    if POLITE then
        printf "%s" (x.Force())

let NOT_YET_IMPLEMENTED (s:string) =
    failwith ("NYI: " + s)

let UNREACHABLE (s:string) =
    failwith ("Unreachable code reached: " + s)

let UNSOUND (s:string) =
    failwith ("Unreachable code reached: " + s)

let rec collectCnsts (sortDic:Dictionary<string,Sort>) (fla:Expr)  =
    if fla.IsApp && fla.NumArgs = 0u then
        if not (sortDic.ContainsKey(fla.ToString())) then
            sortDic.Add(fla.ToString(),fla.FuncDecl.Range)
            [fla]
        else
            []
    else
       Array.map (collectCnsts sortDic) (fla.Args)
       |> Array.fold (fun x y -> x @ y) []

let isBoolRelation (f:Expr) =
    match f.FuncDecl.DeclKind with
    | Z3_decl_kind.Z3_OP_EQ
    | Z3_decl_kind.Z3_OP_SLEQ
    | Z3_decl_kind.Z3_OP_SLT
    | Z3_decl_kind.Z3_OP_SGEQ
    | Z3_decl_kind.Z3_OP_SGT
    | Z3_decl_kind.Z3_OP_ULEQ
    | Z3_decl_kind.Z3_OP_ULT
    | Z3_decl_kind.Z3_OP_UGEQ
    | Z3_decl_kind.Z3_OP_UGT
        -> true
    | _ -> false

let isBVsort (f:Expr) =
    match f.FuncDecl.Range.SortKind with
    | Z3_sort_kind.Z3_BV_SORT -> true
    | _ -> false


// CMW: `collectVars`: bad function name. It does much more than just to collect variables.
let rec collectVars (vars:HashSet<Expr>) (numerals:HashSet<Expr>) (flag:bool) (fla:Expr) =
    // CMW: Variable `flag`: bad name. What are the semantics?
    // CMW: Variable `fla`: bad name, hard to guess what it means; better: `frmla`, but there's
    // really no goood reason not to call it `formula`.
    if fla.FuncDecl.DeclKind = Z3_decl_kind.Z3_OP_BNUM then
        numerals.Add(fla) |> ignore
    else
        if isBoolRelation fla then
            Array.map (collectVars vars numerals false) fla.Args |> ignore

            if not (vars.Contains fla) && flag then
                vars.Add(fla) |> ignore
        else
            Array.map (collectVars vars numerals true) fla.Args |> ignore

            if  not (vars.Contains fla) &&
                fla.FuncDecl.DeclKind <> Z3_decl_kind.Z3_OP_NOT &&
                fla.FuncDecl.DeclKind <> Z3_decl_kind.Z3_OP_OR &&
                (flag || fla.NumArgs = 0u)  then
                vars.Add(fla) |> ignore


// CMW: `mapVars`: bad function name. It does much more than just to map variables.
let rec mapVars (g:Goal) (vars:HashSet<Expr>) (numerals:HashSet<Expr>)  =
    Array.map (collectVars vars numerals true) g.Formulas |> ignore
    let toBeIntroduced = Array.sum [|for v in vars do yield if v.IsBV && v.NumArgs > 0u then 1 else 0|]
    let expr2var = new Dictionary<Expr,int>()
    let num2id = new Dictionary<Expr,int>()
    let id2num = Array.create (numerals.Count + 1) null
    let var2expr = Array.create (vars.Count + 1 + toBeIntroduced) null
    let sorts = Array.create (vars.Count + 1 + toBeIntroduced) 0
    let mutable i = 1
    for e in vars do
        var2expr.[i] <- e
        expr2var.Add(e,i)
        if e.IsBV then
            match  e.FuncDecl.Range with
            | :? BitVecSort as bvSort -> sorts.[i] <- int bvSort.Size
            | _ -> UNREACHABLE("Error: Unable to obtain BV sort for a BV variable")
            if e.NumArgs > 0u then //Implicit equality, we need to introduce a boolean variable for it, it will have value var + 1
              i <- i + 1
              var2expr.[i] <- null //placeholder, sort is bool by initialization of the sort array
        i <- i + 1
    let mutable j = 1
    for e in numerals do
        id2num.[j] <- e
        num2id.Add(e, - j)
        j <- j + 1

    (i - 1, j - 1, var2expr, sorts, expr2var, num2id, id2num)


let collectConstants (g:Goal) (consts:Dictionary<string,Sort>)  =
    let exprList = Array.map (collectCnsts consts) g.Formulas
                   |> Array.fold (fun x y -> x @ y) []
    exprList

let collectLiterals (e:Expr) =
    if e.FuncDecl.DeclKind = Z3_decl_kind.Z3_OP_OR then
        [for c in e.Args -> c]
    else
        [e]

let removeNegation (e : Expr) =
    if e.FuncDecl.DeclKind = Z3_decl_kind.Z3_OP_NOT then
        e.Args.[0]
    else
        e

let makeZ3Lit (z3:Context) (l:int) =
    if l > 0 then
        (z3.MkConst(l.ToString(), z3.MkBoolSort()):?> BoolExpr)
    else
        z3.MkNot((z3.MkConst((abs l).ToString(), z3.MkBoolSort())) :?> BoolExpr)

let initVars (z3:Context) (v:int) =
    for i in 1 .. v do
        z3.MkFreshConst(i.ToString(),z3.BoolSort) |> ignore


let parseDimacs (z3:Context) (fn:string) =
    let lines = System.IO.File.ReadLines(fn)
    let mutable clsNum = 0
    let mutable varNum = 0
    let mutable vars = null
    let goal = z3.MkGoal(true,false,false)
    for  (l:string) in lines do
        if l.Length > 0 then
            match l.Chars 0 with
            | 'c' -> ()
            | '%' -> ()
            | '0' -> ()
            | 'p' -> let a = Array.filter (fun (x:string) -> x.Length > 0 && not (x.Equals("p")) && not (x.Equals("cnf"))) (l.Split([|' '|]))
                     varNum <- int a.[0]
                     clsNum <- int a.[1]
                     initVars z3 varNum
            |  _  -> let a = l.Split([|' '|]) |> Array.filter (fun (x:string) -> x.Length > 0)
                                |> Array.map (fun x -> int x)
                                |> Array.toSeq
                                |> Seq.takeWhile (fun x -> x <> 0)
                                |> Seq.toArray
                                |> Array.map (makeZ3Lit z3)
                     goal.Add(z3.MkOr((a)))
    goal

let parseInput (z3:Context) (fileName:string) =
    verbose <| (lazy "Parsing...")
    let r = if fileName.EndsWith(".smt2") then
                let g = z3.MkGoal(true,false,false)
                let p = z3.ParseSMTLIB2File(fileName, [||],[||],[||],[||])
                g.Add(p)
                g
            else
                parseDimacs z3 (fileName)
    verbose <| (lazy " done.")
    r


let BigIntegerToBinaryString (b:BigInteger) (ss:uint32) : string =
    assert(ss > 0ul)
    let mutable res = ""
    let mutable tmp = b;
    let two = BigInteger(2)
    for i in 1ul .. ss do
        res <- (tmp % two).ToString() + res
        tmp <- tmp / two
    res