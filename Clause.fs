module Clause

open System.Collections.Generic
open Microsoft.Z3
open Literal

//|Size|l_1|...|l_size|

type Clause = Literal []

type ClauseStatus = 
| Sat
| Unsat
| Implication
| Unknown   

let emptyClause = [|0;|]

let getSize(c:Clause) = c.[0]
let isEmptyClause (c:Clause) = getSize c = 0
let getLiterals (c:Clause) = (Array.sub c 1 (getSize c))

let normalizeLiteralList (cls:Literal list) =
    List.sortWith (fun x y -> lit2var y - lit2var x) cls

let newClauseFromArray (ls:Literal []) :Clause = 
    let sz = Array.length ls
    Array.append [|sz|] ls


let newClauseFromList (ls:Literal list) :Clause = 
    let sz = List.length ls
    List.toArray  (sz :: ls)


let clauseToString(c:Clause) = 
    let mutable s = ['(';]
    for i in 1 .. getSize(c) do
        if i <> 1 then s <- s@[' ']
        s <- s@(Array.toList (c.[i].ToString().ToCharArray()))        
    s <- s@[')']
    let ss = s
    new string [|for c in ss -> c|]  


let expr2Clause lit2id (c:Expr) : Clause = 
    if c.FuncDecl.DeclKind = Z3_decl_kind.Z3_OP_OR then
        let lits = Array.map (expr2Lit lit2id) (c.Args)
        newClauseFromArray lits
    else 
        newClauseFromList [expr2Lit lit2id c]


let clauseContainsDuplicates (c:Clause) = 
    let mutable has_dupes = false
    for i in 1 .. getSize(c) do
        for j in i + 1 .. getSize(c) do
            if c.[i] = c.[j] then
                has_dupes <- true
    has_dupes


let collectLiterals (ls:Literal list) =
    let mutable cls = []
    for l in ls do
        if l <> 0 && not (List.exists (fun x -> x = l) cls) then 
            cls <- l :: cls
    cls


type ClauseComparer () = 
    interface IEqualityComparer<Clause> with        

        override r.GetHashCode(c) = 
            let mutable h = getSize c
            for i in 1 .. getSize c do
                h <- h ^^^ c.[i]
            h

        override r.Equals(c1:Clause, c2:Clause) =              
            if getSize c1 = getSize c2 then
                let s1 = Array.sort c1
                let s2 = Array.sort c2
                let mutable e = true
                for i in 1 .. getSize c1 do
                    if s1.[i] <> s2.[i] then
                        e <- false
                e                        
            else
                false
    
