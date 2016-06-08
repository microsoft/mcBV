module TheoryDB

open Microsoft.Z3
open System.Collections.Generic
open Util
open Literal
open NumeralDB
open TheoryRelation
open ClauseDB


type TheoryDB private () =
    let reallocCoefficient = 0.5

    new (expr2var, num2id, n, c) as this =
        TheoryDB()
        then
            this.init expr2var num2id n c

    member val thRels = ([||]:TheoryRelation []) with get, set
    member val private allocatedSize = 0 with get, set
    member val count  = 0 with get, set
    member val private originalSize = 0 with get, set

    // member val introducedRelations = new Dictionary<TheoryRelation, Var>() with get, set
    member val introducedEQs = new Dictionary<TheoryRelation, Var>() with get, set
    member val introducedLEQs = new Dictionary<TheoryRelation, Var>() with get, set

    member val bool2ThRel = new Dictionary<int,int>() with get, set
    member val private inTempMode = false with get, set
    member val private snapshot = -1 with get, set

    member private r.init (expr2var:Dictionary<Expr,Var>) (num2id:Dictionary<Expr,int>) (nDB:ref<NumeralDB>) (cDB:ref<ClauseDB>) =
        let cnt = ref 0

        for e in expr2var.Keys do
            if isBoolRelation e || (e.IsBV && e.NumArgs > 0u) then
                incr cnt

        r.thRels <- Array.create !cnt EmptyThRel
        r.allocatedSize <- !cnt
        r.count <- 0
        r.originalSize <- !cnt

        dbg <| (lazy "Theory relations:")
        for e in expr2var.Keys do
            if isBoolRelation e then
                let t = thRelFromRel expr2var num2id nDB e
                if not (r.isIntroduced t) then
                     r.add t |> ignore
            else if e.IsBV && e.NumArgs > 0u then
                let t = newThRelFromBVOP expr2var num2id nDB e
                if not (r.isIntroduced t) then
                    r.add t |> ignore
                (!cDB).addUnit t.getBoolVar


    member private r.reallocate () =
        assert (r.allocatedSize > 0) //This ensures that init ran before first reallocation

        let desired = int (reallocCoefficient * (float r.allocatedSize))
        let sizeIncrement = if desired = 0 then 1 else desired
        r.thRels <- Array.append r.thRels (Array.create sizeIncrement EmptyThRel)
        r.allocatedSize <- r.allocatedSize + sizeIncrement

    member private r.isLegal (ind:int) =
        0 <= ind  && ind <= r.count

    member r.getThRelationByIndex(i:int) =
        assert (r.isLegal i)
        r.thRels.[i]

    member private r.getThRelationRefByIndex(i:int) =
        assert (r.isLegal i)
        ref r.thRels.[i]

    member r.getThRelRef(i:int) =
        assert (r.isLegal i)
        ref (r.thRels.[i])

    member r.getThRelation (boolVar:int) =
        assert (r.isDefined boolVar)
        let relInd = r.bool2ThRel.[boolVar]
        r.getThRelationByIndex relInd

    member r.getThRelationReference (boolVar:int) =
        assert (r.isDefined boolVar)
        let relInd = r.bool2ThRel.[boolVar]
        r.getThRelationRefByIndex relInd

    member r.getThRelationVar (t:TheoryRelation) =
        if t.getRelationOP = Z3_decl_kind.Z3_OP_EQ then
            match r.introducedEQs.TryGetValue t with
            | (true, boolVar) -> (true, boolVar)
            | (false, _) -> (false, 0)
        else
            match r.introducedLEQs.TryGetValue t with
            | (true, boolVar) -> (true, boolVar)
            | (false, _) -> (false, 0)

    member r.isDefined (b:Var) =
        r.bool2ThRel.ContainsKey b

    member r.mapBooleanToThRel (b:Var) (ind:int) =
        assert (not (r.isDefined b))
        r.bool2ThRel.Add(b, ind)

    member r.isIntroduced (t:TheoryRelation) =
        if (t.getRelationOP = Z3_decl_kind.Z3_OP_EQ) then
            (r.introducedEQs.ContainsKey t)
        else
            (r.introducedLEQs.ContainsKey t)

    //Intended use:
    // we have a new clause to add, either through learning or a generated explanation or w/e
    // 1. Add the clause, obtain its pointer in the DB
    // 2. Run getWatches over the reference and add the pointers where necessary
    member r.add (t:TheoryRelation) : int =
        assert(not (r.isIntroduced t))
        if r.count = r.allocatedSize then
            r.reallocate ()

        let index = r.count
        r.thRels.[index] <- t
        r.count <- r.count + 1
        r.mapBooleanToThRel t.getBoolVar index
        if t.getRelationOP = Z3_decl_kind.Z3_OP_EQ then
            r.introducedEQs.Add(t, t.getBoolVar)
        else
            assert(t.getRelationOP = Z3_decl_kind.Z3_OP_ULEQ)
            r.introducedLEQs.Add(t, t.getBoolVar)
        index

    member r.enterTempMode () =
        assert(not r.inTempMode)
        assert(r.snapshot = -1)
        r.inTempMode <- true
        r.snapshot <- r.count

    member r.leaveTempMode =
        assert(r.inTempMode)
        assert(r.snapshot >= 0)
        for i in r.snapshot .. r.count - 1 do
            let t = r.getThRelationByIndex i
            assert(r.isIntroduced t)
            if (t.getRelationOP = Z3_decl_kind.Z3_OP_EQ) then
                r.introducedEQs.Remove t |> ignore
            else
                r.introducedLEQs.Remove t |> ignore
            r.bool2ThRel.Remove t.getBoolVar |> ignore

        r.count <- r.snapshot
        r.snapshot <- -1
        r.inTempMode <- false