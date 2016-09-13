module Database

open System
open System.Collections.Generic

open Microsoft.Z3

open Util
open Stats
open Literal
open Clause
open BitVector
open TheoryRelation
open NumeralDB
open VariableDB
open ClauseDB
open TheoryDB
open WatchManager

open BooleanValuation
open BitVectorValuation
open BoundsValuation

type Database = class
    val Numerals : Ref<NumeralDB>
    val Variables : Ref<VariableDB>
    val Clauses : Ref<ClauseDB>
    val Theory : Ref<TheoryDB>
    val Watches : Ref<WatchManager>

    val Statistics : Ref<Statistics>

    val var2sort : int[]
    val expr2var : Dictionary<Expr, int>
    val num2id : Dictionary<Expr, int>

    val mutable private inTempMode : bool

    new (maxVariable, num2id, var2sort, expr2var, goal) =
        let n = ref (new NumeralDB(num2id))
        let v = ref (new VariableDB(var2sort))
        let c = ref (new ClauseDB(goal, expr2var))
        let t = ref (new TheoryDB(expr2var, num2id, n, c))
        let w = ref (new WatchManager(maxVariable, 10, t))
        let s = ref (new Statistics())
        {
            Statistics = s;
            Numerals = n;
            Variables = v;
            Clauses = c;
            Theory = t;
            Watches = w;
            var2sort = var2sort;
            expr2var = expr2var;
            num2id = num2id;
            inTempMode = false;
        }
    new (numDB, varDB, thDB, wMngr, goal) =
        let n = numDB
        let v = varDB
        let c = ref (new ClauseDB(goal,  new Dictionary<Expr,int>()))
        let t = thDB
        let w = wMngr//ref (new WatchManager(maxVariable, 10, t))
        let s = ref (new Statistics())
        {
            Statistics = s;
            Numerals = n;
            Variables = v;
            Clauses = c;
            Theory = t;
            Watches = w;
            var2sort = null;
            expr2var = null;
            num2id = null
            inTempMode = false;
        }

    member this.enterTempMode (orig:Ref<Database>) =
        assert(not this.inTempMode)
        assert (this.Variables = (!orig).Variables)
        assert (this.Numerals = (!orig).Numerals)
        assert (this.Theory = (!orig).Theory)
        this.inTempMode <- true
        (!this.Variables).enterTempMode()
        (!this.Numerals).enterTempMode()
        (!this.Theory).enterTempMode()
        //(!this.Watches).enterTempMode((!this.Variables).highestVarInUse)

    member this.leaveTempMode() =
        assert(this.inTempMode)
        (!this.Variables).leaveTempMode
        (!this.Theory).leaveTempMode
        (!this.Numerals).leaveTempMode
        //(!this.Watches).leaveTempMode
        this.inTempMode <- false


    member this.mkFreshBooleanVariable () =
        let res = (!this.Variables).newBooleanVariable ()
        (!this.Watches).newVarToWatch res
        res

    member this.mkFreshBitVectorVariable (size:int) =
        let res = (!this.Variables).newBitVectorVariable size
        (!this.Watches).newVarToWatch res
        res

    member this.mkNumeral (value:BitVector) =
       (!this.Numerals).newNumeral this.Statistics value


    member this.addTheoryRelation (t:TheoryRelation) =
        let tDB = (!this.Theory)
        assert(not (tDB.isIntroduced t))
        let index = tDB.add t
        (!this.Statistics).NewThLiteral()
        
        for v in t.variableArguments do
            (!this.Watches).watchBV v index
        verbose <|  (lazy (sprintf "X New theory relation: %s" (t.ToString(this.Numerals))))
        ()

    member this.addToOccurenceLists (t:TheoryRelation) =
        assert(this.inTempMode)
        let tDB = (!this.Theory)
        assert(tDB.isIntroduced t)

        let index = tDB.bool2ThRel.[t.getBoolVar]       

        for v in t.variableArguments do
            (!this.Watches).watchBVInTmpMode v index
        verbose <|  (lazy (sprintf "X Fresh watches on theory relation: %s" (t.ToString(this.Numerals))))
        ()

    member this.addAndWatchClause (bVal:Ref<BooleanValuation>)(c:Clause) =

        let ind = (!this.Clauses).addClause c

        match findWatch -c.[1] c bVal with
        | (_, Clause.Unknown) -> (!this.Watches).watchBool c.[1] ind |>ignore
                                 (!this.Watches).watchBool c.[2] ind |>ignore
                                 Clause.Unknown
        | _ -> match findWatch -c.[1] c bVal with
                | (_, Clause.Unsat) ->
                    //this.conflict <- Some (ref c)
                    assert(false)
                    Clause.Unsat
                | (_, Implication) ->
                    (!this.Watches).watchBool c.[1] ind |>ignore
                    (!this.Watches).watchBool c.[2] ind |>ignore
                    Clause.Implication
                | _ ->
                    (!this.Watches).watchBool c.[1] ind  |>ignore
                    (!this.Watches).watchBool c.[2] ind  |>ignore
                    Clause.Unknown //AZ: is this correct?

end