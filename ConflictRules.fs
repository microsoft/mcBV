module ConflictRules

open GlobalOptions
open Util
open Stats
open Literal
open Clause
open BooleanValuation
open Learning
open Trail
open State
open Z3Check


let mutable private rc_seen : bool[] = [||]

let resolveConflict (s:State) =
    dbg <| (lazy sprintf "== Conflict ====================================================================")
    assert(s.IsConflicted)

    let trail = !s.trail
    let valuation = !s.bVal
    let mutable learnedLits = []
    let mutable lit = (0:Literal)
    let mutable cnflct = s.GetConflictClause
    let mutable pathC = 0
    let mutable guard = true

    (!(!s.database).Statistics).Conflict()

    let maxVar = (!s.variableDB).highestVarInUse
    if rc_seen.Length <= maxVar then
        rc_seen <- Array.append rc_seen (Array.create (maxVar + 1 - rc_seen.Length) false)

    let c = !cnflct
    for i in 1 .. getSize(c) do
        assert((trail.getLevelExpensive c.[i]) = (valuation.getBLvl c.[i]) || i = 1)
        // AZ: This exception is for the Tseitin variable which is not actually occuring on the trail.

    // CMW: Array.fold behaves weirdly sometimes, and I have no idea why.
    // let conflict_level = Array.fold (fun mxlvl lit -> max (valuation.getBLvl lit) mxlvl) 0 c
    let mutable conflict_level = 0
    for i in 1 .. getSize(c) do
        conflict_level <- max conflict_level (valuation.getBLvl c.[i])

    dbg <| (lazy sprintf "Conflict clause: %s" (clauseToString c))
    dbg <| (lazy sprintf "Conflict #: %d" (!(!(!s.database).Statistics).conflicts))
    dbg <| (lazy sprintf "# decisions: %d" trail.getNumDecisions)
    let cl = conflict_level
    dbg <| (lazy sprintf "Conflict level: %d" cl)
    dbg <| (lazy (let mutable str = "Literal levels: "
                  for i in 1 .. c.Length - 1 do
                      str <- str + (sprintf "%d - %d (%d)\t" c.[i] (valuation.getBLvl c.[i]) (trail.getLevelExpensive c.[i]))
                  str))

    // CMW: Some conflict clauses are created on the fly by the theories and
    // they can be incorrect, so we check them here, before anything is
    // derived from them.
    // trail.forcePrint("", s.bvVal, s.bounds)
//    if DBG then
//        dbg <| (lazy "Pre-conflict resolution check")
//        checkExplanation s.trail s.database s.partAssignment s.bounds c false true true
    assert(checkClauseIsFalse s.bVal !cnflct)

    if VRB then
        s.printConflict cnflct

    if conflict_level = 0 then
        s.MarkUNSAT
    else
//        // CMW: The following assertion can be violated, because empty domains
//        // are detected during decision making. Therefore, for a number of levels,
//        // the empty domain can go undetected and thus the decision level will be
//        // larger than the conflict level.
//        let mutable max_lvl = -1
//        for i in 1 .. (getSize c) do
//            max_lvl <- (max (trail.getLevel c.[i]) max_lvl)
//        assert(((getSize c) = 1 && max_lvl = 0) ||
//                max_lvl = (trail.getNumDecisions))

        while guard do
            assert (conflict_level > 0)
            let c = !cnflct
            let pc = pathC

            let start = if lit=0 then 1 else 2

            // CMW: This conflict resolution algorithm relies
            // on the fact that the implied literal is the
            // first literal in `cnflct'.
            if (lit <> 0 && (!cnflct).[1] <> lit) then
                printfn("Bug: Clause sorted incorrectly.") ;
                assert(false)

            for i in start .. getSize !cnflct do
                let lit = (!cnflct).[i]
                let lvl = valuation.getBLvl lit
                if not rc_seen.[lit2var lit] && lvl > 0 then
                    rc_seen.[lit2var ((!cnflct).[i])] <- true
                    if  lvl >= conflict_level then
                        pathC <- pathC + 1
                    else
                        learnedLits <- lit :: learnedLits

            if DBG then
                if (lit = 0) then
                    printfn "---------------------------------------------------"
                else
                    let v = (lit2var lit)
                    printf " |  /\ ("
                    let mutable first = true
                    for i in 1 .. (getSize c) do
                        let cl = c.[i]
                        if (cl <> lit) then
                            if first then
                                first <- false
                            else
                                printf " && "
                            printf "%d" (Negate cl)
                    printf ") => "
                    // printf " (pathC=%d)" pc
                    if (!s.theoryDB).isDefined v then
                        if (lit < 0) then printf "not "
                        printf "%s" (((!s.theoryDB).getThRelation v).ToString(s.numeralDB))
                    else
                        printf "%d" lit
                    printfn ""

            let mutable indx = trail.getCount - 1
            while indx > 0 && not rc_seen.[lit2var (trail.getLiteral indx)]  do //|| trail.getNumDecisions >= conflict_level)
                s.Pop
                indx <- indx - 1

            lit <- trail.getLiteral indx
            cnflct <- trail.getExplanation indx
            rc_seen.[lit2var lit] <- false
            pathC <- pathC - 1
            s.Pop

            if pathC <= 0 then
                guard <- false

        assert(lit<>0);
        let bt_lvl = List.fold (fun a x -> let l = (valuation.getBLvl x)
                                           if l > a then l else a) 0 learnedLits

        assert((valuation.getBLvl (lit2var lit)) = -1)
        assert(bt_lvl < conflict_level)

        learnedLits <- (Negate lit) :: learnedLits
        let learnedClause = newClauseFromList learnedLits

        while trail.getNumDecisions > bt_lvl do
            s.Pop

        assert(valuation.getValueB(lit) = Undefined)

        for i in 1 .. getSize learnedClause do
           rc_seen.[lit2var learnedClause.[i]] <- false
        if DBG then
            printfn  "---------------------------------------------------"
            printf  " |  -> ("
            let mutable first = true
            let alit = (Negate lit)
            for i in 1 .. getSize learnedClause do
                let cl = learnedClause.[i]
                if cl <> alit then
                    if first then
                        first <- false
                    else
                        printf " && "
                    printf "%d" (Negate cl)
            printf ") => "
            if (!s.theoryDB).isDefined (lit2var alit) then
                if (alit < 0) then printf "not "
                printf "%s " (((!s.theoryDB).getThRelation (lit2var alit)).ToString(s.numeralDB))
            else
                printf "%d " alit
            printfn ""
            printfn  "---------------------------------------------------"
        dbg <| (lazy sprintf "Decision level now: %d" trail.getNumDecisions)

        s.ClearConflict

        if (getSize learnedClause) > 1 then
            checkExplanation s.trail s.database s.bvVal s.bounds learnedClause false false true
            //AZ: There are cases when we can produce a known clause, because it
            //    can be propagated only in a certain order.
            //    E.g., x =/= a when x in [l,...,a,..., u] Nothing happens
            //          x <= a  when x in [l,...,a,..., u] yields [l,... a]
            //          x >= a  when x in [l,...,a] yields [a,a] which conflicts
            if not ((!s.clauseDB).isStored learnedClause) then
                s.Learn learnedClause |> ignore

        s.Push (Imp (ref learnedClause, Negate lit)) // Note: this may set a new (theory-dependant) conflict

    dbg <| (lazy sprintf "== Resolved ====================================================================")
    ()
