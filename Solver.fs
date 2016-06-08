module Solver

open System.Collections.Generic
open Microsoft.Z3

open Model
open GlobalOptions
open Util
open Preprocessing
open State
open BooleanValuation
open BitVectorValuation
open BoundsValuation
open Trail
open Database
open Rules
open Problem
open SandboxState
open Z3Check

[<NoComparison>]
type Solution = SAT of Model | UNKNOWN | UNSAT

type Solver = class
    new ( ) = { };

    member this.Load (z3opts:Dictionary<string,string>, filename:string ) =
        z3opts.Add("MODEL","true")
        let mutable z3 : Context = new Context(z3opts)

        let g = parseInput z3 filename

        trace <| (lazy sprintf "Unmodified goal: \n%s" (g.ToString()))

        let pg = (if filename.EndsWith ".smt2" then preprocess z3 g else g)
        let slvr = z3.MkSolver() in
        slvr.Add(pg.Formulas) ;
        trace <| (lazy sprintf "Preprocessed goal: \n%s" (slvr.ToString()))
        let vs = new HashSet<Expr>()
        let ns = new HashSet<Expr>()
        let (mv, mn, v2e, v2s, e2v, n2i, i2n) = mapVars pg vs ns

//        let z3Solver = this.z3.MkSolver("QF_BV")
//        z3Solver.Assert pg.Formulas
//        let res = z3Solver.Check ()
//        if res = Status.SATISFIABLE then
//            printfn "Z3 says SAT"
//        else if res = Status.UNSATISFIABLE then
//            printfn "Z3 says UNSAT"
//            for e in z3Solver.UnsatCore  do
//                printfn "%s" (e.ToString())
//        else
//            printfn "Z3 says UNKNOWN"

        //new Problem(pg, vs, ns, v2e, v2s, e2v, n2i, i2n, mv, mn)

        if TRC then
            printfn "Variable map: "
            for i  in 1 .. v2e.Length - 1 do
                if v2e.[i] = null then
                    printfn "%d := NULL" i
                else
                    if v2s.[i] = 0 then
                        printfn "[%d] := Z3's %s " i (v2e.[i].ToString())
                    else
                        printfn "%d:bv := Z3's %s " i (v2e.[i].ToString())

        if DBG then
            printfn "Sorts:"
            for i  in 1 .. v2s.Length - 1 do
                if v2s.[i] = 0 then
                    printfn "Sort(%d) == Boolean" i
                else
                    printfn "Sort(%d) == BitVec(%d)" i v2s.[i]

        if TRC then
            printfn "Numerals:"
            for i in 1 .. i2n.Length - 1 do
                let n = (i2n.[i] :?> BitVecNum)
                let sz = (n.Sort :?> BitVecSort).Size
                let nb = n.BigInteger
                printf "%d:num := #x%s" i (nb.ToString("X" + (sz/4ul).ToString()))
                if (sz % 4ul <> 0ul) then printf " (%s bit)" (sz.ToString())
                printfn ""

        try
            z3.Dispose()
            System.GC.Collect()
            // System.GC.WaitForPendingFinalizers()
            // System.GC.WaitForFullGCComplete() |> ignore
            // System.GC.Collect()
        with
        | :? System.AccessViolationException as ex -> printfn("Context disposal exception ignored.")


        new Problem(pg, vs, ns, v2e, v2s, e2v, n2i, i2n, mv, mn, g)


    member this.Solve (p : Problem) =
        if p.goal.Formulas.Length = 1 && p.goal.Formulas.[0].IsFalse then
            polite <| (lazy "Solved by preprocessor\n")
            Solution.UNSAT
        else
            let fTrail = Trail(p.maxVar)
            let fBVal = BooleanValuation(p.maxVar)
            let fPAssgnmnt = BitVectorValuation(p.maxVar, p.var2sort)
            let fBounds = BoundsValuation(p.maxVar, p.var2sort)
            let db = Database(p.maxVar, p.num2id, p.var2sort, p.expr2var, p.goal)


            if p.goal.Formulas.Length = 0 then
                polite <| (lazy "Solved by preprocessor\n")
                Solution.SAT(new Model(fPAssgnmnt, fBVal))
            else

                let initialState =
                    State(p.maxVar,
                          ref fTrail,
                          ref fBVal,
                          ref fPAssgnmnt,
                          ref fBounds,
                          ref db)

                let sbox = prepareSandbox db
                let s = checkSat initialState sbox


                if POLITE then
                    (!(!s.database).Statistics).Print()

                if s.IsSatisfiable then
                    Solution.SAT(new Model(!s.bvVal, !s.bVal))
                else if s.IsUnsatisfiable then
                    //checkUNSAT s.trail s.database s.bvVal s.bounds true 
                    Solution.UNSAT
                else
                    Solution.UNKNOWN

end

