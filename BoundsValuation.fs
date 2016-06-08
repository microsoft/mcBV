module BoundsValuation

open Literal
open BitVector
open Util
open Interval


type BoundsValuation (size:int, sorts:VarType[]) =  
    let mutable allocated = size + 1 
    let mutable reallocCoefficient = 2.0   

    member val private inUse = size + 1 with get, set

    member val bounds =  [|for s in sorts do                                                             
                            if s > 0 then 
                                yield Interval.Full (s)
                            else
                                yield Interval.Empty (1) |] with get, set

    member val L_explanation = Array.create (size + 1) (0:Literal) with get, set  
    member val U_explanation = Array.create (size + 1) (0:Literal) with get, set
    
    member val private inTempMode = false with get, set
    member val private snapshot = -1 with get, set  

    member r.getInUse = r.inUse
    member r.reallocate() = 
        let newSize = int (reallocCoefficient * float allocated)
        r.reallocate newSize

    member r.reallocate (newSize:int) =         
        r.bounds <- Array.append r.bounds (Array.create ((newSize + 1) - allocated) (Interval.Empty 1) )
        r.L_explanation <- Array.append r.L_explanation (Array.create ((newSize + 1) - allocated) 0)        
        r.U_explanation <- Array.append r.U_explanation (Array.create ((newSize + 1) - allocated) 0)
        allocated <- r.bounds.Length        
    
    member r.fastForward (oInUse: int) (sorts: Ref<int []>) = 
        if r.inUse < oInUse then
            if oInUse > allocated then
                r.reallocate oInUse 
            for i in r.inUse .. oInUse - 1 do
                r.newVar i (!sorts).[i]
        assert (r.inUse = oInUse)

    member r.newVar (var:Var) (s:VarType) = 
        assert(var = r.inUse)
        if r.inUse = allocated then
            r.reallocate()
        r.inUse <- r.inUse + 1
        if (s <> 0) then
            let bv = BitVector s
            r.bounds.[var] <- Interval(bv.Minimum, bv.Maximum)
            dbg <| (lazy sprintf  " | initial bound: %s <= %d:bv" (r.bounds.[var].ToString()) var)

    member r.set (i:Var) (bounds:Interval) =
        assert (sorts.[i] = bounds.Dimension)
        r.bounds.[i] <- bounds
    
    member r.getExplanations v = (r.L_explanation.[v], r.U_explanation.[v])    

    member r.get(i:Var) = 
        assert (r.bounds.[i].Dimension <> 0)        
        r.bounds.[i]
    
    member r.enterTempMode (orig:Ref<BoundsValuation>) (sorts:Ref<int[]>) = 
        assert (not r.inTempMode )
        assert (r.snapshot = -1)
        r.inTempMode <- true
        r.snapshot <- (!orig).getInUse
        r.fastForward r.snapshot sorts
        
        assert (r.inUse = (!orig).getInUse)        
        assert (Array.fold (fun s (x:int) -> s && x = 0) true r.L_explanation)
        assert (Array.fold (fun s (x:int) -> s && x = 0) true r.U_explanation)
        for i in 1 .. r.inUse - 1 do
            assert ( (!sorts).[i] = 0 &&  r.bounds.[i].isEmpty ||  r.bounds.[i].Dimension = (!sorts).[i] && r.bounds.[i].isFull)
            assert (r.bounds.[i].Dimension = (!orig).bounds.[i].Dimension)


    member r.leaveTempMode = 
        assert(r.inTempMode)
        assert(r.snapshot >= 0)       
        for i in r.snapshot .. r.inUse - 1 do
            r.bounds.[i] <- Interval.Empty 1
            r.L_explanation.[i] <- 0
            r.U_explanation.[i] <- 0
            
        r.inUse <- r.snapshot
        r.snapshot <- -1
        r.inTempMode <- false

//    member r.setLower (i:Var) (bv:BitVector)=
//        assert (r.isBVVar i)
//        assert (r.bounds.[i].Length <> 0)
//        
//        bv.CheckInvariant()
//        dbg <| (lazy sprintf  " | new bound: %s <= %d:bv" (bv.ToString()) i)
//        r.lower.[i] <- bv

        

//    member r.setUpper (i:Var) (bv:BitVector)=
//        assert (r.isBVVar i)
//        assert (r.upper.[i].Length <> 0)

//        bv.CheckInvariant()
//        dbg <| (lazy sprintf  " | new bound: %d:bv <= %s" i (bv.ToString()))
//        r.upper.[i] <- bv