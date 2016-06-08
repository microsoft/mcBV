module Literal

open Microsoft.Z3
open System.Collections.Generic
open Util

type VarType = int
// 0 - Boolean
// Otherwise, denotes BitVector length

//Variable are numbers from 1 .. maxVar
type Var = int

let isVar (v:int) = v > 0

//Literals are +- Vars
type Literal = int

let var2lit (v:Var) = (v:Literal) 
let lit2var (l:Literal) = (abs(l):Var)

let Negate (l:Literal) = - l
let isNegated (l:Literal) = l < 0
let isPositive (l:Literal) = l > 0

let mapVariables (g:Goal) (sorts:Dictionary<string, Sort>) (expr2Var:Dictionary<Expr,int>) =
    verbose <| (lazy "Mapping variables...")
    let varList = collectConstants g sorts
    let len = List.length varList
    let var2Expr = Array.create (len+1) null
    for p in (List.zip ([1 .. len ]) varList) do 
        expr2Var.Add( snd p, fst p)
        var2Expr.[fst p] <- snd p
    verbose <| (lazy " done.")
    var2Expr

let literalMapping (g:Goal) (maxLiteral:Literal)(lit2id:Dictionary<Expr,int>) (id2lit:Dictionary<int,Expr>) =
    verbose <| (lazy "Mapping literals...")
    let mutable lits = []
    for cls in g.Formulas do
        lits <- lits @ (collectLiterals cls)
    let posLits = Set.ofList (List.map removeNegation lits) |> Set.toList
    //let sortedLits = List.sortBy (fun (x:Expr) -> x.FuncDecl.Name.ToString()) posLits
    let nLen = (maxLiteral+ (List.length posLits)) 
    for e  in (List.zip ([(maxLiteral + 1) .. nLen])  posLits) do
        lit2id.Add(snd e, fst e)
        id2lit.Add(fst e, snd e)
    verbose <| (lazy " done.")
    nLen


let rec expr2Lit (dic:Dictionary<Expr,Var>) (e:Expr) = 
    let mutable l = 0
    if e.FuncDecl.DeclKind = Z3_decl_kind.Z3_OP_NOT then
            l <- (- (expr2Lit dic e.Args.[0]))
    else            
        if not (dic.TryGetValue(e,&l)) then
            printfn "Cannot find literal %s" (e.ToString())
            assert(false)    
    l