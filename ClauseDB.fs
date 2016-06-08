module ClauseDB

open Microsoft.Z3
open System.Collections.Generic
open GlobalOptions
open Util
open Literal
open Clause
open BooleanValuation


type ClauseDB private () =
    let reallocCoefficient = 0.5
    let minSize = 5

    new (g:Goal, expr2var:Dictionary<Expr,Var>) as this =
        ClauseDB()
        then
            this.init(g, expr2var)

    member val private clauses = [||] with get, set
    member val private allocatedSize = 0 with get, set    
    member val private originalSize = 0 with get, set
    member val private storedClauses = new HashSet<Clause>( new ClauseComparer());
    member val private tseitin = new Dictionary<Clause, Var>(new ClauseComparer());   

    member val count = 0 with get, set
    member val originalClauses = [||] with get, set
    member val units = [||] with get, set
    

    member r.addUnit (l:Literal) =
        r.units <- Array.append r.units [|(newClauseFromArray [|l|])|]
    
    member r.init (g:Goal, expr2var:Dictionary<Expr,Var>) =
        r.originalClauses <- (Array.map (expr2Clause expr2var) (g.Formulas))
        r.clauses <- Array.filter (fun (x:Clause) -> x.[0] <> 1) r.originalClauses
        r.units <- (Array.filter (fun (x:Clause) -> getSize(x) = 1) r.originalClauses)
        for c in r.originalClauses do
            if not (r.isStored c) then
                r.store c

        assert (r.allocatedSize = 0)
        let len = Array.length r.clauses
        if len > 0 then
            r.originalSize <- Array.length r.clauses
            r.count <- r.originalSize
            r.allocatedSize <- r.originalSize
        else
            r.clauses <- Array.create minSize [|0|]
            r.originalSize <- 0
            r.count <- 0
            r.allocatedSize <- minSize                        
    
    member private r.reallocate () = 
        assert (r.allocatedSize > 0) //This ensures that init ran before first reallocation
        let before = r.allocatedSize
        let si = int (reallocCoefficient * (float r.allocatedSize))
        let sizeIncrement = if si <= 0 then 1 else si
        r.clauses <- Array.append r.clauses (Array.create sizeIncrement emptyClause)
        r.allocatedSize <- r.allocatedSize + sizeIncrement        
        assert(r.allocatedSize > before)
    
    member private r.isLegal (ind:int) =
        0 <= ind  && ind <= r.count

    member r.getClause(i:int) = //clsDB.[i]
        assert (r.isLegal i)
        r.clauses.[i]
        
    member r.getClauseRef(i:int) = //ref  clsDB.[i]
        assert (r.isLegal i)
        ref (r.clauses.[i])
    
    member r.isLearned(i:int) =
        assert (r.isLegal i)
        i >= r.originalSize

    member r.isStored (c:Clause) = r.storedClauses.Contains c

    member r.store (c:Clause) = r.storedClauses.Add c |> ignore

    member r.getTseitinDefinition (c:Clause) = 
        if r.tseitin.ContainsKey c then
            Some (r.tseitin.Item c)
        else
            None

    member r.registerTseitin (c:Clause) (v:Var) = r.tseitin.Add (c, v)

    member r.isRegisteredTseitin (v:Var) = r.tseitin.ContainsValue v


    //Intended use:
    // we have a new clause to add, either through learning or a generated explanation or w/e
    // 1. Add the clause, obtain its pointer in the DB
    // 2. Run getWatches over the reference and add the pointers where necessary
    member r.addClause (c:Clause) = 
        assert (getSize c > 1)
        assert (not (r.isStored c))
        // dbg <| (lazy sprintf "Adding clause: %s" (clauseToString c))
        if r.count = r.allocatedSize then
            r.reallocate ()
        
        let index = r.count
        r.clauses.[index] <- c
        r.store c
        r.count <- r.count + 1
        index 
    
    member r.printClause (clause:Ref<Clause>) = 
        printf "["
        for j in 1 .. (!clause).[0] do
            printf " %d " (!clause).[j]       
        printf "]"

    member r.eval (bVal:Ref<BooleanValuation>) (clsR:Ref<Clause>) =
        let cls = !clsR
        let size = getSize(cls)
        let mutable res = false
    
        if size > 0 then
            let cnt = cls
                      |> Array.map (fun (x:Literal) -> (!bVal).getValueB x)
                      |> Array.sumBy (fun (x:Val) -> if x = False then 0 else 1)
            cnt > 0
        else
            printf "Zero size clause in the DB!"
            false

    member r.Check (bVal:Ref<BooleanValuation>) : bool =
        let mutable q = true
        for i in 0 .. r.count - 1 do
            let cls = r.getClause i  
            if not (r.eval bVal (ref cls)) then
                printf "Conflict:"
                r.printClause (ref cls)
                q <- false
        q

    override r.ToString() =
        if r.count = 0 then
            "ClauseDB: EMPTY"
        else
            let mutable res = "ClauseDB: (" + (r.count.ToString()) + " clauses)"  + System.Console.Out.NewLine
            for i in 0 .. r.count - 1 do
                let c = r.getClause i
                res <- res + (clauseToString(c)) + System.Console.Out.NewLine
            res