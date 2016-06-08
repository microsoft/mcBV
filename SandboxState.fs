module SandboxState 

open System.Collections.Generic
open Microsoft.Z3
open Literal
open State
open BooleanValuation
open BitVectorValuation
open BoundsValuation
open Trail
open Database
open TheoryDB
open WatchManager

let prepareSandbox (odb:Database) =
    
    let initSize = (!odb.Variables).highestVarInUse
    let initSorts = (!odb.Variables).sorts
    let fTrail = Trail(initSize)     
    let fBVal = BooleanValuation(initSize)
    let fPAssgnmnt = BitVectorValuation(initSize, initSorts)
    let fBounds = BoundsValuation(initSize, initSorts)
    //let fTheoryDB = TheoryDB(new Dictionary<Expr,Var>(),new Dictionary<Expr,int>(), odb.Numerals, odb.Clauses) 
    let fWatchMngr = WatchManager(initSize,10,odb.Theory)

    let mutable z3 : Context = new Context(new Dictionary<string,string>())
    let db = Database(odb.Numerals, odb.Variables, odb.Theory, ref fWatchMngr, z3.MkGoal(true,false,false))
    z3.Dispose()
    State(  initSize,
            ref fTrail,
            ref fBVal,
            ref fPAssgnmnt,
            ref fBounds,
            ref db)
                
    

