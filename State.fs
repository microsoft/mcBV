module State

open GlobalOptions
open Learning
open Util
open Literal
open Clause
open Trail
open Database
open WatchManager
open Z3Check
open BooleanValuation
open BitVectorValuation
open BoundsValuation
open VariableOrder
open Stats


type Answer =
| Sat
| Unsat
| Unknown

type State (maxVar:int,
            tr:Ref<Trail>,
            tBoolValuation:Ref<BooleanValuation>,
            tRLEValuation:Ref<BitVectorValuation>,
            tBndsValutation:Ref<BoundsValuation>,
            db:Ref<Database>) =

    member val trail = tr
    member val bVal = tBoolValuation
    member val bvVal = tRLEValuation
    member val bounds = tBndsValutation
    member val database = db
    member val numeralDB = (!db).Numerals
    member val variableDB = (!db).Variables
    member val clauseDB = (!db).Clauses
    member val theoryDB = (!db).Theory
    member val watchManager = (!db).Watches
    member val private inTempMode = false with get, set
    member val private answer = Unknown with get, set
    member val private conflict : Ref<Clause> Option = None with get, set
    member val private oldFlags = None with get, set

    member val boundsEnabled = true with get, set

    // AZ: Only to be used in sandbox
    member r.clearConflict () =
        r.conflict <- None

    member this.printConflict (conflict:Ref<Clause>) =
        printf " | >C< "
        this.printClause conflict

    member this.printClause (clause:Ref<Clause>)=
        (!this.trail).printClauseVerbose this.database clause
        // if DBG then printfn "--------------------------------------------------------------------------------"
        // if DBG then (!s.trail).forcePrint("", this.partAssignment, this.bounds)

    // AZ: The types mismatch, I know, but this is only for debugging purposes
    member this.printCube (cube:Ref<Clause>)=
        (!this.trail).printCubeVerbose this.database cube
        // if DBG then printfn "--------------------------------------------------------------------------------"
        // if DBG then (!s.trail).forcePrint("", this.partAssignment, this.bounds)


    member this.Push (e:TrailElement) =
        let c = (!this.trail).Push this.bVal this.bvVal this.bounds this.database (!db).Statistics e
        match c with
        | Some(cc) -> this.SetConflict (Some cc) //xTheory conflict, detected during a push attempt.
        | None -> ()

    member this.Pop =
        (!this.trail).Pop this.bVal this.bvVal this.bounds this.database

    member this.SetConflict (co:Ref<Clause> option) =
        match co with
        | Some(cc) -> checkExplanation this.trail this.database this.bvVal this.bounds !cc false false true
        | None -> ()
        this.conflict <- co

    member this.ClearConflict =
        this.conflict <- None

    member this.GetConflictClause =
        assert(this.conflict.IsSome)
        this.conflict.Value


    member this.IsComplete =
        let highest_var = (!this.variableDB).highestVarInUse
        let bool_vars_assigned = (!this.bVal).assignedVars
        let bv_vars_assigned = (!this.bvVal).assignedVars
        (highest_var = bool_vars_assigned + bv_vars_assigned)

    member this.IsConflicted =
        match this.conflict with
        | Some(_) -> true
        | None -> false

    member this.IsSearch = (not this.IsSolved) && this.conflict.IsNone
    member this.MarkSAT = this.answer <- Sat
    member this.MarkUNSAT = this.answer <- Unsat
    member this.MarkUNKNOWN = this.answer <- Unknown
    member this.IsSolved = this.answer = Sat || this.answer = Unsat
    member this.IsSatisfiable = this.answer = Sat
    member this.IsUnsatisfiable = this.answer = Unsat

    member this.Learn (c:Clause) =
        assert(not this.IsConflicted)
        let bVal = this.bVal
        if getSize(c) > 1 then
            dbg <| (lazy sprintf "* New clause: %s" (clauseToString c))
            (!this.database).addAndWatchClause bVal c |> ignore
        else if getSize(c) = 1 && (!bVal).getValueB (c.[1]) = Undefined then
            (!this.clauseDB).addUnit c.[1]
            this.Push (Imp (ref c, c.[1]))
            assert(not this.IsConflicted)
        else if (getSize(c) = 1 && (!bVal).getValueB (c.[1]) = False) then
            //this.conflict <- Some (ref c)
            assert(false)
        else
            assert(c.[0] > 0)
            printfn "Warning attempted to add a redundant clause"

    member this.defineTseitinVariable (lits: Literal list) =

        let cls = newClauseFromList lits
        match (!this.clauseDB).getTseitinDefinition cls with
        | Some t -> t
        | None   ->
            let tseitinVar = getTseitinVar this.database this.bVal this.bvVal this.bounds
            (!this.clauseDB).registerTseitin cls tseitinVar
            let tsVarImpliesGenLits = newClauseFromList ((Negate tseitinVar) :: lits)
            this.Learn tsVarImpliesGenLits
            for l in lits do
                this.Learn (newClauseFromList(Negate l :: tseitinVar :: []))
            if DBG then printfn "Defining  %d <--> %s" tseitinVar (clauseToString (newClauseFromList lits))
            tseitinVar

    member r.enterTempMode (s:State)=
        //Some of the sanbox data structures might be out of date.
        //The database is shared so that is fine,
        //But bVal, bvVal, bounds
        assert (not r.inTempMode)
        r.inTempMode <- true
        let sortsRef = (ref (!s.variableDB).sorts)
        (!r.bVal).enterTempMode s.bVal
        (!r.bvVal).enterTempMode s.bvVal sortsRef
        (!r.bounds).enterTempMode s.bounds sortsRef
        (!r.database).enterTempMode (s.database)
        (!r.watchManager).enterTempMode (!s.variableDB).highestVarInUse

    member r.leaveTempMode() =
        assert (r.inTempMode)
        r.inTempMode <- false
        (!r.bVal).leaveTempMode
        (!r.bvVal).leaveTempMode
        (!r.bounds).leaveTempMode
        (!r.database).leaveTempMode()
        (!r.watchManager).leaveTempMode ((!r.variableDB).highestVarInUse)

    member r.isInTempMode = r.inTempMode

    member r.trailElemToString (t:TrailElement) =
        match t with
        | BAssgnmnt (v,_,_) ->  let bnds = (!r.bounds).get v
                                v.ToString() + ":bv \in " + (bnds.ToString())
        | MAssgnmnt (v,_,_) ->  let pattern = (!r.bvVal).getValue v
                                v.ToString() + ":bv = " +  (pattern.ToString())
        | BoolDecision l
        | Imp (_,l) when (!r.theoryDB).isDefined (lit2var l) ->
            (if isNegated l then "not" else "")
            + ((!r.theoryDB).getThRelation (lit2var l)).ToString r.numeralDB
        | _ -> ""

    member r.ShowFancyConflict (cnflct:Clause, ?annotation:string) =
        if SHOW_CONFLICTS then
            assert (cnflct.Length > 0)
            assert (cnflct.Length = cnflct.[0] + 1)
            let nDB = (!r.database).Numerals
            let tDB = (!r.database).Theory

            printf "Conflict #%d: " !(!(!r.database).Statistics).conflicts
            match annotation with
            | None -> ()
            | Some(a) -> printf " %s" a
            printfn ""

            let mutable first = true
            for i in 1 .. cnflct.Length - 1 do
                let l = cnflct.[i]
                let v = lit2var l
                if not ((!tDB).isDefined v) then
                    if first then
                        printf "    "
                        first <- false
                    else
                        printf " || "
                    printf "%d" l
            if not first then printfn " || "

            first <- true
            for i in 1 .. cnflct.Length - 1 do
                let l = cnflct.[i]
                let v = (lit2var l)
                if (!tDB).isDefined v then
                    if first then
                        first <- false
                        printf "    "
                    else
                        printf " || "
                    if l < 0 then
                        printf "not "
                    printfn "%s" (((!tDB).getThRelation v).ToString(nDB, false))
            printfn ""