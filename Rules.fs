module Rules

open GlobalOptions
open Util
open BooleanValuation
open Clause
open Trail
open State
open RLEBVTheory
open BoundsTheory
open InitializationRules
open PropagationRules
open DecisionRules
open ConflictRules
open Explain


let CheckTDB (s:State) =
    let mutable res = true
    for i in 0 .. (!s.theoryDB).count - 1 do
        let tRel = (!s.theoryDB).getThRelationByIndex i
        let tHolds = tHolds tRel s.bvVal s.numeralDB
        let tbndsHolds = tbndsHolds tRel s.bounds s.numeralDB
        let valueB = (!s.bVal).getValueB tRel.getBoolVar
        let valueT = (!s.bVal).getValueT tRel.getBoolVar

        match (tHolds, tbndsHolds, valueB, valueT) with
        | (Undefined, Undefined, _, Undefined)
        | (False, False, False, False)
        | (False, Undefined, False, False)
        | (True, True, True, True)
        | (True, Undefined, True, True) ->
            // That's alright, ignore.
            ()
        | (True, _, False, _)
        | (True, _, _, False)
        | (False, _, True, _)
        | (False, _, _, True)
        | (_, _, True, False)
        | (_, _, False, True) ->
            let mutable is_propagated = false
            for c in (!s.trail).getTrailPtr .. (!s.trail).getCount - 1 do
                match (!s.trail).trail.[c] with
                | BoolDecision l
                | Imp (_,l) ->
                    if abs l = tRel.getBoolVar then
                        is_propagated <- true
                | MAssgnmnt (bv,_,_) -> if (List.exists (fun x -> x = bv) tRel.variableArguments) then
                                                is_propagated <- true
                | BAssgnmnt (bv,_,_) -> ()
            if not is_propagated then
                printfn "Invariant violation; disagreement: %s -> (RLE:%s,Bnds:%s) x (B:%s,T:%s)"
                    (tRel.ToString(s.numeralDB))
                    (tHolds.ToString())
                    (tbndsHolds.ToString())
                    (valueB.ToString())
                    (valueT.ToString())
                res <- false

        | (True, _, Undefined, _)
        | (False, _, Undefined, _) ->
            let mutable is_propagated = false
            for c in (!s.trail).getTrailPtr .. (!s.trail).getCount - 1 do
                match (!s.trail).trail.[c] with
                | BoolDecision l
                | Imp (_,l) ->
                    if abs l = tRel.getBoolVar then
                        is_propagated <- true
                | MAssgnmnt (bv,_,_) -> if (List.exists (fun x -> x = bv) tRel.variableArguments) then
                                                is_propagated <- true
                | BAssgnmnt (bv,_,_) -> ()
            if not is_propagated then
                // tRel holds, but that fact has not been propagated into the according
                // Boolean variable that represents tRel (tRel.getBoolVar)
                printfn "Not propagated to valueB %s" (tRel.ToString())
                res <- false
        | (True, _, _, Undefined)
        | (False, _, _, Undefined) ->
              () // OK
        | (Undefined, True, _, _)
        | (Undefined, False, _, _) ->
              () // OK, bounds can be stronger
        | (Undefined, _, _, False)
        | (Undefined, _, _, True) ->
            printfn "Theory value assigned, but %s does not evaluate" (tRel.ToString())
            res <- false
        | _ ->
            printfn "Theory DB check not implemented for tHolds=%s tbndsHolds=%s valueB=%s valueT=%s" (tHolds.ToString()) (tbndsHolds.ToString()) (valueB.ToString()) (valueT.ToString())
            NOT_YET_IMPLEMENTED("th-rel check")

    if not res then
        printfn "Trail at the failure: "
        let mutable lvl = 0
        printfn "L%d====================================" lvl
        for i in 0 .. (!s.trail).getCount - 1  do
            let e = (!s.trail).trail.[i]
            match e with
            | BoolDecision v ->
                lvl <- lvl + 1
                printfn "L%d====================================" lvl
                printf "BoolDecision %d :" v
            | Imp (c,l) ->
                printf "(%s) -> %d : " (clauseToString !c) l
            | _ -> ()

            printfn "%s" (s.trailElemToString e)
    res


let paranoia (s:State) =
    let mutable res = true
    if not s.IsConflicted then
        res <- res && ((!s.clauseDB).Check s.bVal)
        res <- res && (CheckTDB s)
    res


let PropagateWithLimitedBounds (s:State) (trail:Trail) =
    let mutable cnt = 0
    let limit = (!s.variableDB).highestVarInUse / 2
    while not s.IsConflicted && trail.hasPropagationsPending do
        Propagate s trail.nextPropagation
        cnt <- cnt + 1
        if cnt > limit then
            s.boundsEnabled <- false
    s.boundsEnabled <- true


let checkSat (s:State) (sandbox:State)  =
    let mutable trail = !s.trail

    // Initial propagation and watchlist construction
    pushUnits s

//    printfn "Stats: "
//    printfn "Vars    : %d" (!s.varDB).highestVarInUse
//    printfn "BoolVars: %d" ((Array.sumBy (fun x -> if x = 0 then 1 else 0) (!s.varDB).sorts) - 1)
//    printfn "BvVars  : %d" (Array.sumBy (fun x -> if x > 0 then 1 else 0) (!s.varDB).sorts)
//    printfn "Clauses : %d" (!s.clauseDB).count
//    printfn "Units   : %d" (Array.sumBy (fun x ->
//                                         match x with
//                                         |Imp (cls,_) -> if getSize !cls = 1 then 1 else 0
//                                         | _ -> 0 ) (!s.trail).trail)

    dbg <| (lazy sprintf "%s" ((!s.clauseDB).ToString()))

    if DBG then
        printfn "Occurrence & watchlists: "
        let wm = (!s.watchManager)
        for v in 1 .. (!s.variableDB).highestVarInUse do
            if ((!s.variableDB).isBoolean v) then
                (wm.printBoolWatch s.clauseDB v)
            else
                (wm.printThWatch s.numeralDB s.theoryDB v)

    if s.IsConflicted then
        dbg <| (lazy sprintf "Conflict in initial clause database; trivially unsat.")
        dbg <| (lazy sprintf "Conflict clause: %s" (clauseToString !(s.GetConflictClause)))
        s.MarkUNSAT

    verbose <| (lazy sprintf "L 00 ===========================================================================")

    while not s.IsSolved do

        if s.IsConflicted then
            if (!s.trail).getNumDecisions = 0 then
                s.MarkUNSAT
            elif GENERALIZE then
                let pre_cnflct = !s.GetConflictClause
                xTExplanationGeneralization s sandbox

                if s.IsConflicted then
                    let aft_cnflct = !s.GetConflictClause
                    if pre_cnflct <> aft_cnflct then
                        s.ShowFancyConflict(pre_cnflct, "[pre-generalization]")
                        s.ShowFancyConflict(aft_cnflct, "[generalized]")
                    else
                        s.ShowFancyConflict(pre_cnflct, "[no generalization]")
                    resolveConflict s
                //else
                    //Otherwise Backjump-Decide resolved a conflict.
            else
                s.ShowFancyConflict(!s.GetConflictClause, "")
                resolveConflict s
        else
            // Propagation
            PropagateWithLimitedBounds s trail
            if DBG then assert(paranoia s)

            if s.IsSearch then
                if s.IsComplete then
                    // Everything is assigned, so we're done.
                    if not DBG then
                        s.MarkSAT
                    else
                        if (paranoia s) then s.MarkSAT
                else
                    // Decision time <- no propagagtions but search is incomplete,
                    // i.e., at least one variable is still unassigned.
                    let nd = trail.getNumDecisions + 1
                    verbose <| (lazy sprintf "L %02d ===========================================================================" nd)
                    decide s

    verbose <| (lazy sprintf "== Done ========================================================================")

    if VRB then
        if s.IsSatisfiable then
            printfn "SATISFIABLE"
            printfn "------------------"
            printfn "FINAL TRAIL:"
            (!s.trail).forcePrint("", s.bvVal, s.bounds)
            printfn "------------------"
            printfn "Model:"
            for v in 1 .. (!s.variableDB).highestVarInUse do
                if (!s.variableDB).sorts.[v] = 0 then
                    printfn "%d -> %s" v (((!s.bVal).getValueB v).ToString())
                else
                    printfn "%d -> %s" v (((!s.bvVal).getValue v).ToString())
        else if s.IsUnsatisfiable then
            (!s.trail).print("", s.bvVal, s.bounds)
        else
            verbose <| (lazy "UNKNOWN")

    s