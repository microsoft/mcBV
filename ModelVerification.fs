module ModelVerification

open Microsoft.Z3
open System.Collections.Generic
open GlobalOptions
open Util
open BooleanValuation
open Problem
open Model

let verifySat (p:Problem) (m:Model) =
    let mutable finalRes = true
    let z3 = new Context();
    let z3model = new Dictionary<Expr,Expr>()
    let g = p.goal.Translate(z3)
    let vgoal = g.Translate(z3)

    for i in 1..p.var2expr.Length - 1 do
        if (p.var2expr.[i] <> null &&
            p.var2expr.[i].IsConst) then
            if (p.var2expr.[i].IsBool) then
                let e = ((if ((m.getValueBool i) = True) then z3.MkTrue() else z3.MkFalse()) :> Expr)
                z3model.Add(p.var2expr.[i].Translate(z3), e.Translate(z3))
            else
                let mutable mv = (m.getValueBV i)
                if not mv.isConcreteValue then
                    mv <- mv.Minimum
                let e = mv.toZ3Expr z3
                z3model.Add(p.var2expr.[i].Translate(z3), e.Translate(z3))

    let vars : Expr[] = Array.create z3model.Count null
    let values : Expr[] = Array.create z3model.Count null

    let mutable i = 0
    for kv in z3model do
        vars.[i] <- kv.Key
        values.[i] <- kv.Value
        i <- i + 1

    if SHOWMODEL then
        for kv in z3model do
            printfn "%s := %s" (kv.Key.ToString()) (kv.Value.ToString())

    for i in 0 .. int(vgoal.Size) - 1 do
        let orig = vgoal.Formulas.[i]
        let subst = orig.Substitute(vars, values)
        let simple = subst.Simplify()
        if (simple.IsTrue) then
            if DBG then
                printfn "OK:    %s -> %s -> %s" (orig.ToString()) (subst.ToString()) (simple.ToString())
        else
            printfn "ERROR: %s -> %s -> %s" (orig.ToString()) (subst.ToString()) (simple.ToString())
            finalRes <- false

    finalRes


let Verify ( p : Problem ) ( m : Model ) =
    if not VERIFYMODEL then
        true
    else
        if not (verifySat p m) then
            false
        else
            polite <| (lazy "Ok, model verified.\n")
            true
