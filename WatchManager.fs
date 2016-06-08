module WatchManager

open GlobalOptions
open Literal
open Clause
open BooleanValuation
open NumeralDB
open TheoryDB
open ClauseDB

type WOList = int []
type WatchList = int []
type OccurenceList = int []


// Watch list/Occurence list structure:
//|Size|Count| p_0 | ... |p_{count-1}| trash |
//|  OFFSET  | p_0 | ... |p_{count-1}| trash |

//Returns a pair of (newWatch, clauseStatus)/numNonFalseWatches)/
let findWatch (pl:Literal) (c:Clause) (v:Ref<BooleanValuation>) =     
    let size = getSize(c)    
    let npl = -pl;

    assert (size >= 2)

    if (c.[1] = npl) then
        let tmp = c.[1]
        c.[1] <- c.[2]
        c.[2] <- tmp

    // at this point we know that c.[2] = npl, which just became false.

    match (!v).getValueB(c.[1]) with
    | True -> (c.[1], Sat) // Satisfied clause.
    // This is wrong:
    // | False -> (c.[1], 0) // Conflict, c.[1] is the "conflicting literal"
    | _ -> 
        let mutable i = 3
        let mutable found = false
        
        // [ U, F ] or [ F F ]

        while (not found && i <= size) do
            if (!v).getValueB(c.[i]) <> False then
                found <- true
            else
                i <- i + 1

        if (found) then // [ U, U ] or [ F, U ]
            let tmp = c.[i]
            c.[i] <- c.[2]
            c.[2] <- tmp
            (c.[2], Unknown) // All fine, c.[1] and c.[2] are valid watches
        else
            if (!v).getValueB(c.[1]) = False then
                (c.[1], Unsat) // Conflict, c.[1] is the "conflicting literal"
            else
                (c.[1], Implication) // Implication; invariant: implied literals is at c.[1]


let findTwoWatches (c:Clause) (v:Ref<BooleanValuation>) =     
    let size = getSize(c)
    assert (size >= 2)
    let mutable i = 0

    let v(l) = (!v).getValueB(l)

    if v(c.[1]) = False then
        i <- 2
        while i <= size do
            if v(c.[i]) <> False then
                let tmp = c.[1]
                c.[1] <- c.[i]
                c.[i] <- tmp
                i <- size + 1
            else
                i <- i + 1
    
    if v(c.[2]) = False then
        i <- 3
        while i <= size do
            if v(c.[i]) <> False then
                let tmp = c.[1]
                c.[1] <- c.[i]
                c.[i] <- tmp
                i <- size + 1
            else
                i <- i + 1

    if v(c.[1]) = True then
        (c.[1], Sat)
    else if v(c.[1]) = False then
        (c.[1], Unsat)
    elif v(c.[2]) = False  then
        (c.[1], Implication)
    else
        (c.[2], Unknown)


let sizeInd = 0
let countInd = 1
let snapCount = 2
let wolOffset = 3


type WatchManager private (numOfVariables:int, initWLSize:int) =     
    let reallocCoefficient = 2.0

    new (numOfVariables:int, initWLSize:int, tDB:Ref<TheoryDB>) as this =
        WatchManager(numOfVariables, initWLSize)
        then
            this.initializeWatchLists tDB ()
            

    member val private allocated = 2*numOfVariables with get, set
    member val private inUse = numOfVariables with get, set
    member val offset = 3 with get //Offset for the Size and Count and snapshot*)
    member val lists = [|([|0; 0|]:WatchList)|] with get, set
    member val private inTempMode = false with get, set
    member val private snapshot = -1 with get, set

    member r.emptyWatchList = [|0; 0|]        

    member r.initializeWatchLists (fThDB:Ref<TheoryDB>) () =
        r.lists <-  [| for i in 0 .. r.allocated - 1 do yield Array.create initWLSize -1 |]
        
        for i in 0 .. r.allocated - 1 do
            r.setSz i (initWLSize - r.offset) |> ignore
            r.setCnt i 0 |> ignore

        for i in 0 .. (!fThDB).count - 1 do            
            let t = ((!fThDB).getThRelationByIndex i)
            for varg in t.variableArguments do
                r.watchBV varg i


    member r.getIndex(l:Literal) :int =
        let ind =   if l > 0 then 
                        2*l - 1
                    elif l < 0 then 
                        2 * (-l - 1)
                    else 
                        -1
        assert (r.validIndex ind)
        ind

    member r.reallocate() = 
        let newSize = int (reallocCoefficient * float r.allocated)
        r.reallocate (newSize, initWLSize)
            
    member r.reallocate (newSize:int, wlSize:int)=
        assert(newSize > r.allocated)
        r.lists <- Array.append r.lists [|for i in 0 .. newSize - r.allocated - 1 do yield Array.create wlSize -1 |]
        let oldSize = r.allocated
        r.allocated <- newSize
        for i  in oldSize ..  r.allocated - 1 do
            r.setSz i (wlSize - r.offset) |> ignore
            r.setCnt i 0 |> ignore

    member r.newVarToWatch (var:Var) = 
        assert (not r.inTempMode ||var = r.inUse + 1)
        if r.inUse * 2 >= r.allocated then
            r.reallocate()
        r.inUse <- r.inUse + 1

    member r.validIndex ind = ind > -1 && ind < 2*r.inUse && r.inUse < r.allocated
    
    //To be stand alone functions over WatchList/OccurenceList
    member private r.getSz(ind:int) :int =
        
        r.lists.[ind].[sizeInd]
   
    member r.getSize(l:int) :int = 
        let ind = r.getIndex(l)
        r.getSz(ind)

    member r.setSz(ind:int) (s:int) :int = 
        assert ( ind > -1 && ind < r.allocated)
        r.lists.[ind].[sizeInd] <- s
        r.lists.[ind].[sizeInd]
    
    
    member private r.getCnt(ind:int)=
        assert (r.validIndex ind)
        r.lists.[ind].[countInd]
    
    member r.getCount(l:Literal) : int =
        let ind = r.getIndex(l)
        r.getCnt(ind)
    
    member private r.setCnt (ind:int) (c:int) : int =
        assert ( ind > -1 && ind < r.allocated)
        r.lists.[ind].[countInd] <- c
        r.lists.[ind].[countInd]

    member r.setCount (l:Literal) (c:int) =
        let ind = r.getIndex(l)
        r.setCnt ind c
        
    member private r.incrCnt (ind:int) : int =
        assert (r.validIndex ind)
        r.lists.[ind].[countInd] <- r.lists.[ind].[countInd] + 1
        r.lists.[ind].[countInd]

    member r.removeReference (bvVar:Var) (ptr:int) =
        assert (r.inTempMode)

        let idx = r.getIndex bvVar
        let mutable found = false
        let cnt = r.getCnt idx 

        for i in 0 .. cnt - 1 do
            if not found && r.getPtr idx i = ptr then
                found <- true
                if i < cnt - 1 then
                    r.setPtr idx i (r.getPtr idx (cnt - 1))
                
                r.setPtr idx (cnt - 1) -1
                r.setCnt idx (cnt - 1)    |> ignore
        
        assert(found)

    member  r.getPtr (ind:int) (i:int) :int =        
        assert ( r.validIndex ind && 0 <= i && i < r.getCnt ind)
        r.lists.[ind].[r.offset + i]

    member  r.setPtr (ind:int) (i:int) (ptr:int) : Unit =
        assert ( r.validIndex ind && 0 <= i && i <= r.getCnt ind)
        r.lists.[ind].[r.offset + i] <- ptr

    member r.getPointer (l:Literal) (i:int) :int = 
        let ind = r.getIndex l        
        r.getPtr ind i

    member r.setPointer (l:Literal) (ptr:int) = 
        let ind = r.getIndex(l)
        assert (ind > -1 && ind < r.allocated)//if  ind > -1 then
        let cnt = r.getCnt ind
        if cnt >= r.getSz ind then
            r.reallocateList ind |> ignore
        r.setPtr ind cnt ptr 
        r.incrCnt(ind) |> ignore

    //Initializing/Migrating the watches
    member r.watchBool (l:Literal) (c:int) : Unit = 
        assert (l<>0)
        r.setPointer -l c
         
    
    //Initializing the occurences
    member r.watchBV (v:Var) (t:int) : Unit = 
        assert (v <> 0)
        r.setPointer v t

    member r.watchBVInTmpMode (v:Var) (t:int) : Unit = 
        assert (v <> 0)
        assert (r.inTempMode)

        let idx = r.getIndex v
        let mutable found = false
        let cnt = r.getCnt idx 

        for i in 0 .. cnt - 1 do
            if not found && r.getPtr idx i = t then
                found <- true
        if not found then
            r.setPointer v t
        

    member r.getWatchList (l:Literal) :WatchList = 
        assert (l <> 0)
        let ind = r.getIndex(l)
        assert (ind > -1)//if  ind > -1 then
        r.lists.[ind]
        
        
    member r.reallocateList (ind:int) :int =
        assert (r.validIndex ind)
        let size = r.getSz(ind)
        assert(size > 0)
        let nSize = 2*size                       
        r.lists.[ind] <- Array.append r.lists.[ind] (Array.create size -1)
        r.setSz ind nSize

    member r.printThWatch (nDB:Ref<NumeralDB>) (thDB:Ref<TheoryDB>) (l:Literal) =
        let ind = r.getIndex(l)
        let cnt = r.getCnt(ind)        
        if cnt = 0 then
            printfn "%d:bv: None." l
        else
            printfn "%d:bv: " l
            for k in 0 .. cnt - 1 do
                let cPtr = r.getPtr ind k
                let tRel = !((!thDB).getThRelRef cPtr)
                printfn "  %d : %s " cPtr (tRel.ToString nDB) //(clauseToString (!(cDB.getClauseRef cPtr)))
   
    member r.printBoolWatch (cDB:Ref<ClauseDB>) (l:Literal) =
        let ind = r.getIndex(l)
        let cnt = r.getCnt(ind)
        // printfn "Currently watching clauses for literal %d: " l
        
        if cnt = 0 then
            printfn "%d: None." l
        else
            printfn "%d: " l    
            for k in 0 .. cnt - 1 do
                let cPtr = r.getPtr ind k
                printfn " %d : %s " cPtr (clauseToString (!((!cDB).getClauseRef cPtr)))

    member r.trcPrintWatch (nDB:Ref<NumeralDB>) (cDB:Ref<ClauseDB>) (tDB:Ref<TheoryDB>) (l:Literal) (isBool:bool) =
        if TRC then
            if isBool then
                r.printBoolWatch cDB l
            else
                r.printThWatch nDB tDB l
    
    member r.setSnapCnt (ind:int) = 
        assert (r.inTempMode)
        assert ( ind > -1 && ind < r.allocated)
        r.lists.[ind].[snapCount] <- r.getCnt ind

    member r.resetSnapCnt (ind:int) = 
        assert (r.inTempMode)
        assert ( r.validIndex ind)
        r.lists.[ind].[snapCount] <- - 1
    
    member r.getSnapCnt (ind:int) = 
        assert ( ind > -1 && ind < r.allocated)
        r.lists.[ind].[snapCount]

    member r.resetListToSnapCnt (ind:int) = 
        assert (r.inTempMode)
        assert ( ind > -1 && ind < r.allocated)
        let snap = r.getSnapCnt ind
        let cnt = r.getCnt ind
        if snap > -1 then
            for i  in snap + 1 .. cnt - 1 do
                r.setPtr ind i -1
            r.setCnt ind snap |> ignore
            r.resetSnapCnt ind

    member r.getInUse = r.inUse

    member r.enterTempModeOld () = 
        assert(not r.inTempMode)
        assert(r.snapshot = -1)
        r.inTempMode <- true        
        for i in 1 .. r.inUse do
            r.setSnapCnt (r.getIndex i)
            r.setSnapCnt (r.getIndex -i)

        r.snapshot <- r.inUse
    
    member r.enterTempMode (newMaxVar:Var) = 
        assert(not r.inTempMode)
        assert(r.snapshot = -1)
        r.inTempMode <- true
        while newMaxVar > r.inUse do
            r.newVarToWatch (r.inUse + 1)

        let initSz = (initWLSize/2)
        assert (initSz > r.offset)
        r.lists <- [|for i in 0 .. r.allocated - 1 do yield Array.create initSz -1 |]
        for i  in 0 ..  r.allocated - 1 do
            r.setSz i (initSz - r.offset) |> ignore
            r.setCnt i 0 |> ignore
    
    member r.leaveTempMode (highestVarInUse:Var) =
        assert(r.inTempMode)
        //assert(r.snapshot >= 0)
        r.inUse <- highestVarInUse
        r.inTempMode <- false

    member r.leaveTempModeOld =
        assert(r.inTempMode)
        assert(r.snapshot >= 0)
        for i in r.snapshot .. r.inUse - 1 do
            let indA = r.getIndex i
            r.lists.[indA] <- Array.create initWLSize -1
            r.setSz indA (initWLSize - r.offset) |> ignore
            r.setCnt indA 0 |> ignore
            let indB = r.getIndex i
            r.lists.[indB] <- Array.create initWLSize -1
            r.setSz indB (initWLSize - r.offset) |> ignore
            r.setCnt indB 0 |> ignore

        
        for i in 1 .. r.snapshot - 1 do
            r.resetListToSnapCnt (r.getIndex i)
            r.resetListToSnapCnt (r.getIndex -i)
                                           
        r.inUse <- r.snapshot
        r.snapshot <- -1
        r.inTempMode <- false

    member r.fastForward (orig:Ref<WatchManager>) = 
        let oInUse = (!orig).getInUse
        if r.inUse < oInUse then r.inUse <- oInUse
        if r.inUse >= r.allocated then r.reallocate (r.inUse, 3)
            
        assert (r.inUse = oInUse)             

//    member r.watchNewClause (pCls:Ref<Clause>) (pVal:Ref<Valuation>) (pT:Ref<Trail>)  = 
//        let mutable inConflict = false
//        let mutable newState = null
//        if getSize(!pCls) = 1 then
//            match (!pVal).getVal((!pCls).[1]) with
//            | False -> inConflict <- true
//                       newState <- Conflict (pT, pCDB, pCls)
//            | Undefined -> trail.push (cDB.getClauseRef i) (!pCls).[1] |> ignore                           
//            | True -> () //Already True, and therefore on the trail
//        else
//            match findWatch -(!pCls).[1] !pCls pVal with
//            | (_, Clause.Unknown) -> w.watchBool (!pCls).[1] i  |>ignore
//                                     w.watchBool (!pCls).[2] i |>ignore
//            | _ -> match findWatch -(!pCls).[1] !pCls pVal with
//                    | (_, Clause.Unsat) -> w.watchBool (!pCls).[1] i |>ignore
//                                           w.watchBool (!pCls).[2] i |>ignore           
//                                           inConflict <- true
//                                           newState <- Conflict (pT, pCDB, pCls)
//                    | (_, Implication) -> 
//                               w.watchBool (!pCls).[1] i  |>ignore
//                               w.watchBool (!pCls).[2] i  |>ignore
//                               if (!pVal).getVal((!pCls).[1]) = Undefined then //this should be the invariant
//                                    trail.push (cDB.getClauseRef i) (!pCls).[1]|> ignore                                    
//                    | _ ->     w.watchBool (!pCls).[1] i  |>ignore
//                               w.watchBool (!pCls).[2] i  |>ignore

    //Watch literal l in clause c
    

    
    
    
       
