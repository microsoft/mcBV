module BooleanValuation

open GlobalOptions
open Literal

type Val = 
    | True
    | False
    | Undefined 

    override r.ToString () : string = 
        match r with
        | True -> "True"
        | False -> "False"
        | Undefined -> "Undef"

    member r.not :Val =
        match r with
        | True -> False
        | False -> True
        | Undefined -> Undefined

    
    
let Not (v:Val) :Val =
    match v with
    | True -> False
    | False -> True
    | Undefined -> Undefined

let consistent (x:Val) (y:Val) = 
    match (x,y) with
    | (True, False) | (False, True) -> false
    | _ -> true

type BooleanValuation(size:int) = 
    
    let mutable allocated = size + 1 //1 to account for L 0 being reserved
    let mutable inUse = size + 1
    
    let mutable reallocCoefficient = 2.0

    member val valueB = Array.create allocated Undefined with get,set
    member val valueT = Array.create allocated Undefined with get,set
    member val booleanLevel = Array.create allocated -1 with get,set
    member val theoryLevel = Array.create allocated -1 with get,set

    member val private inTempMode = false with get, set
    member val private snapshot = -1 with get, set

    member r.getInUse = inUse

    member r.assignedVars = 
        Array.sum (Array.map (fun x -> if x <> Undefined then 1 else 0) r.valueB)

    member r.isConsistent = 
        Array.sum (Array.map2 (fun x y -> if consistent x y then 0 else 1) r.valueB r.valueT)

    member r.reallocate () =
        let newSize = int (reallocCoefficient * float allocated)
        r.reallocate newSize
    
    member r.reallocate (newSize:int) =
        assert (newSize >= allocated)
        r.valueB <- Array.append r.valueB (Array.create ((newSize + 1) - allocated) Undefined )
        r.valueT <- Array.append r.valueT (Array.create ((newSize + 1) - allocated) Undefined )
        r.booleanLevel <- Array.append r.booleanLevel (Array.create ((newSize + 1) - allocated) -1 )
        r.theoryLevel <- Array.append r.theoryLevel (Array.create ((newSize + 1) - allocated) -1 )
        allocated <- r.valueB.Length

    member r.newVar (var:Var)  =
        assert(var = inUse)
        if inUse = allocated then
            r.reallocate()
        
        inUse <- inUse + 1
        
                
    member r.getValueB(l:Literal) =         
        let v = lit2var l
        assert (v < inUse)
        if isNegated l then
            Not r.valueB.[v]
        else 
            r.valueB.[v]

    member r.getValueT(l:Literal) = 
        let v = lit2var l
        assert (v < inUse)
        if isNegated l then
           Not r.valueT.[v]
        else 
            r.valueT.[v]

    member r.getBLvl(l:Literal) = 
        let v = lit2var l
        assert (v < inUse)
        r.booleanLevel.[v]

    member r.getTLvl(l:Literal) = 
        let v = lit2var l
        assert (v < inUse)
        r.theoryLevel.[v]

    member r.resetVal(l:Literal) = 
        let v = lit2var l
        assert (v < inUse)
        r.valueB.[v] <- Undefined
        r.valueT.[v] <- Undefined
        r.booleanLevel.[v] <- -1
        //r.valueB.[v]
    
    member r.resetValueT (l:Literal) = 
        let v = lit2var l
        assert (v < inUse)        
        r.valueT.[v] <- Undefined
        r.theoryLevel.[v] <- -1

    member r.resetValueTAboveCurrentDecisionLevel (l:int) = 
        for i in 1 .. inUse - 1 do
            if r.getTLvl i > l then
                r.resetValueT i
                
                
    member r.setValueB (l:Literal) (lvl:int)=
        let v = lit2var l
        assert (v < inUse)
        
        r.booleanLevel.[v] <- lvl
        
        if isNegated l then
            r.valueB.[v] <- False            
            r.valueB.[v]
        else
            r.valueB.[v] <- True            
            r.valueB.[v]

    member r.setValueT (l:Literal) (lvl:int) =
        let v = lit2var l
        assert (v < inUse)
        
        r.theoryLevel.[v] <- lvl
        
        if isNegated l then
            r.valueT.[v] <- False                                    
            r.valueT.[v]
        else
            r.valueT.[v] <- True            
            r.valueT.[v]

    member r.getFirstUndefVar () = 
        let mutable i = 1
        while i < inUse && r.valueB.[i] <> Undefined do
            i <- i + 1
        
        if i < inUse then   
            i
        else
            0
    
    member r.enterTempMode (orig:Ref<BooleanValuation>) = 
        assert (not r.inTempMode )
        assert (r.snapshot = -1)
        r.inTempMode <- true
        r.snapshot <- (!orig).getInUse
        r.fastForward r.snapshot

        assert (r.getInUse = (!orig).getInUse)
        assert (Array.fold (fun s x -> s && (x = Undefined)) true r.valueB)
        assert (Array.fold (fun s x -> s && (x = Undefined)) true r.valueT)
        assert (Array.fold (fun s x -> s && (x = -1)) true r.booleanLevel)
        assert (Array.fold (fun s x -> s && (x = -1)) true r.theoryLevel)

    member r.leaveTempMode = 
        assert(r.inTempMode)
        assert(r.snapshot >= 0)       
        for i in r.snapshot .. inUse - 1 do
            r.resetVal i
            r.resetValueT i
            
        inUse <- r.snapshot
        r.snapshot <- -1
        r.inTempMode <- false
        
    member private r.fastForward (oInUse:int) =
        if oInUse > allocated then            
            r.reallocate oInUse
        if oInUse > inUse then
            inUse <- oInUse
             
    member r.getFirstUndefLit (sorts:Ref<int []>) = 
        let mutable i = 1
        while i < inUse && (r.valueB.[i] <> Undefined || (!sorts).[i] > 0) do
            i <- i + 1
        
        if i < inUse then   
            if DBG then
                i
            else         
//            if (System.Random().Next() % 2) = 0 then 
//                -i
//            else
                i
        else
            i <- 1
            while i < inUse && (!sorts).[i] = 0 do
                i <- i + 1 
            if i < inUse then
                i
            else
                0
        