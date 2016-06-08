module PropagationRules

open GlobalOptions
open Util
open Literal
open BooleanValuation
open Clause
open Trail
open State
open WatchManager
open TheoryRelation
open BoundsTheory
open RLEBVTheory


let visitOccurrence (s:State) (tRel:Ref<TheoryRelation>) =
    let pVal = s.bVal
    let boolVar = (!tRel).getBoolVar

    let T = (!pVal).getValueT boolVar
    let B = (!pVal).getValueB boolVar
    match (T, B) with

    // Check for conflicts
    | (True, False)
    | (False, True) ->
        // Note that valueT of boolVar could be a consequence of contraints in
        // either theory, but we don't know which one it is. Also, it could be
        // a cross-theory implication, in which case we need to know about
        // both theories' reasons.
        // See also tbndsImplyNewInterval, which creates cross-theory implications
        // (and so does trail.pushMA once we re-enable the negative PA case.)
        let tAnts = (tGetAntecedents s tRel)
        let tbndsAnts = if USE_BOUNDS then (tbndsGetAntecedents s tRel) else []
        let c = newClauseFromList (tAnts @ tbndsAnts)
        // TODO: Cross-theory explanation generalization?
        // generalizeExplanation
        s.SetConflict (Some (ref c))

    // For everything else we need to evaluate tRel
    | (Undefined, _) ->
        if USE_BOUNDS && s.boundsEnabled then
            tbndsEvaluate s tRel
        if not s.IsConflicted then
            tEvaluate s tRel

    | (True, Undefined)
    | (False, Undefined) ->
        assert(false)
        ()

    | (True, True) -> ()
    | (False, False) -> ()


let visitOccurrences (s:State) (v:Var) =
    let occCount = (!s.watchManager).getCount v

    let mutable i = 0
    while i < occCount && s.IsSearch do
        let w = (!s.watchManager).getPointer v i
        let wRel = (!s.theoryDB).getThRelationByIndex w

        let boolVar = wRel.getBoolVar
        let valB = ((!s.bVal).getValueB (boolVar))
        let valT = ((!s.bVal).getValueT (boolVar))
        trace <| (lazy sprintf " | o-see %s%s (B: %s T: %s)"
                                (if valB = False then "not " else "")
                                (wRel.ToString(s.numeralDB))
                                (valB.ToString())
                                (valT.ToString()))

        visitOccurrence s (ref wRel)

        i <- i + 1


let bPropagate (s:State) (l:Literal) =
    let trail = !s.trail
    let cDB = !s.clauseDB
    let w = !s.watchManager
    let ind = w.getIndex(l)
    let mutable j = 0 //write ptr
    let mutable i = 0 //read ptr
    let cnt = w.getCount l

    // w.trcPrintWatch pCDB pTDB l true
    let mutable wcnt = 0
    while s.IsSearch && i < cnt do
        let clsPtr = w.getPtr ind i
        let c = (cDB.getClause clsPtr)
        let (newLit,wCnt) = findWatch l c s.bVal

        match wCnt with
        | Clause.Sat ->
            // Satisfied, just keep the clause
            trace <| (lazy sprintf " | b-see %d : %s (kept; %d is true)" clsPtr (clauseToString c) newLit)
            w.setPtr ind j (w.getPtr ind i)
            j <- j + 1
            wcnt <- wcnt + 1
        | Clause.Unknown ->
            // We have a new watch (on newLit, in position c.[2])
            assert ((!s.bVal).getValueB (newLit) <> False)
            trace <| (lazy sprintf " | b-see %d : %s (migrated) to %d" clsPtr (clauseToString c) newLit)
            w.watchBool newLit clsPtr  |> ignore
            wcnt <- wcnt + 1
        | Clause.Implication ->
            // Implication of newLit, which is in c.[1]; push onto trail
            trace <| (lazy sprintf " | b-see %d : %s (implication) of %d" clsPtr (clauseToString c) newLit)
            s.Push (Imp (cDB.getClauseRef clsPtr, newLit)) |> ignore
            // assert (not s.IsConflicted) // CMW: This is not true anymore; any Boolean variable can
            // be implied, but conflicting because of theory knowledge. But, I think this shouldn't
            // break anything.
            w.setPtr ind j (w.getPtr ind i)
            j <- j + 1
            wcnt <- wcnt + 17
        | Clause.Unsat ->
            // Conflict, but first compact the rest of this watch to maintain integrity
            trace <| (lazy sprintf " | b-see %d : %s unsatisfied" clsPtr (clauseToString c))
            for k in i .. (cnt - 1) do
                let cid = (w.getPtr ind k)
                trace <| (lazy sprintf " | b-see %d : %s (kept/compacting)" cid (clauseToString (cDB.getClause cid)))
                w.setPtr ind j cid
                j <- j + 1
            s.SetConflict (Some (cDB.getClauseRef clsPtr))
            wcnt <- wcnt + 1

        i <- i + 1

    w.setCount l j  |> ignore

    if wcnt <> 0 then
        if (w.getWatchList l).Length = 0 then
            trace <| (lazy sprintf " | Watches for %d is empty." l)
        else
            trace <| (lazy sprintf " | Watches for %d are now: " l)
            w.trcPrintWatch s.numeralDB s.clauseDB s.theoryDB l true


let PropagateTheories (s:State) (t:TrailElement) =
    match t with
    | MAssgnmnt (v,_, _) -> visitOccurrences s v
    | BAssgnmnt (v,_,_) -> visitOccurrences s v
    | _ -> () // Purely propositional Implication


let Propagate (s:State) (t:TrailElement) =

    verbose <| (lazy sprintf "\\ Propagate %s  :\n %s"

            (match t with
            | MAssgnmnt(v, _, _) -> "model assignment"//(sprintf "%d:bv = %s" v ((!s.bvVal).getValue(v).ToString()))
            | BAssgnmnt (v, _, _) -> "bounds"//(sprintf "%d:bv = %s" v ((!s.bounds).get(v).ToString()))
            | BoolDecision l -> "decision " + l.ToString()
            | Imp(e, l) -> "implication " + (clauseToString !e) + " -> "+ l.ToString())

            //((!s.trail).ElementToString t)
            ( s.trailElemToString t))

    // Propagate model assignments and theory relations
    PropagateTheories s t
    // Propagate Booleans and theory relation indicator variables
    if isBoolLiteral t && s.IsSearch then
        bPropagate s (getBoolLiteral t)
