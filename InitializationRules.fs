module InitializationRules

open System.Collections.Generic
open Microsoft.Z3
open GlobalOptions
open Util
open Literal
open BooleanValuation
open Clause
open Trail 
open State
open WatchManager
open VariableDB
open ClauseDB
open TheoryDB
open TheoryRelation
open BitVector
open BitVectorValuation

open RLEBVTheory
open BoundsTheory

let watchNewClause (s:State) (i:int) =     
    let trail = !s.trail
    let bval = !s.bVal
    let cDB = !s.clauseDB
    let w = !s.watchManager
    let pCls = (!s.clauseDB).getClauseRef i
           
    assert(getSize(!pCls) > 1)
    let (l, r) = findTwoWatches !pCls (s.bVal)
    w.watchBool (!pCls).[1] i
    w.watchBool (!pCls).[2] i
    match r with    
    | Clause.Unsat -> s.SetConflict (Some pCls)
    | Implication  -> s.Push (Imp (pCls, (!pCls).[1]))
    | _ -> ()


let pushUnit (s:State) (pCls:Ref<Clause>) = 
    assert(getSize(!pCls) = 1)
    match (!s.bVal).getValueB((!pCls).[1]) with
    | False     -> s.SetConflict (Some pCls)
    | Undefined -> s.Push (Imp (pCls, (!pCls).[1])) |> ignore
    | True      -> () // Already True, and therefore on the trail.


let pushUnits (s:State) =
    dbg <| (lazy "Pushing units: ")

    for c in (!s.clauseDB).units do
        let l = c.[1]
        let v = lit2var l

        // CMW: We should not need to do anything with model assignments
        // or bounds predicates here. This will all be done automatically
        // via pushUnit -> ... -> Trail.push

        pushUnit s (ref c)
    
    let mutable i = 0  
    while s.IsSearch && i < (!s.clauseDB).count do
        watchNewClause s i
        i <- i + 1 


let showWatches (s:State) (l:Literal) =    
    printfn "(%s): " (l.ToString())
    let lwl = ((!s.watchManager).getWatchList l)
    for w in lwl do
        printfn "| %s" (clauseToString ((!s.clauseDB).getClause w))