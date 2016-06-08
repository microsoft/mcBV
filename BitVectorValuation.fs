module BitVectorValuation

open Literal
open BitVector

type BitVectorValuation (size:int, sorts:VarType[]) =  
    let mutable allocated = size + 1 
    let mutable reallocCoefficient = 2.0
    
    member val inUse = size + 1 with get, set
    member val vals = [| for s in sorts do yield if s > 0 then (BitVector s) else BitVector.Invalid |] with get, set    
    member val mAssignmntsExplanations = Array.create (size + 1) (0:Var) with get, set     
    
    member val private inTempMode = false with get, set
    member val private snapshot = -1 with get, set

    member r.getInUse = r.inUse

    member r.reallocate() =
        let newSize = int (reallocCoefficient * float allocated)
        r.reallocate newSize

    member r.reallocate (newSize:int) =
        r.vals <- Array.append r.vals (Array.create ((newSize + 1) - allocated) (BitVector.Invalid) )        
        r.mAssignmntsExplanations <- Array.append r.mAssignmntsExplanations (Array.create ((newSize + 1) - allocated) 0)        
        allocated <- r.vals.Length

    member r.fastForward (oInUse:int) (sorts: Ref<int []>) = 
        if r.inUse < oInUse then
            if oInUse >= allocated then
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
            r.vals.[var] <- bv                          

    member private r.isBVVar (v:Var) = 
        (v > 0 && v < r.inUse && r.vals.[v].Length <> 0)

    member private r.isBooleanVar (v:Var) =
        (v > 0 && v < r.inUse && r.vals.[v].Length = 0)

    member r.getValue (i:Var) = 
        assert (r.isBVVar i)
        r.vals.[i]

    member r.isAssigned (i:Var) = 
        if r.isBVVar i then
            r.vals.[i].isConcreteValue
        elif r.isBooleanVar i then
            false
        else
            true // Numerals have i < 0 and they are assigned by definition

    member r.isConcreteValue (i:Var) =
        assert (r.isBVVar i)
        r.vals.[i].isConcreteValue
  
    member r.setValue (i:Var) (bv:BitVector) =
        assert (r.isBVVar i)        
        bv.CheckInvariant()
        // dbg <| (lazy sprintf  " | new value: %d:bv = %s"  i (bv.ToString()))
        r.vals.[i] <- bv

    member r.assignedVars = 
         let mutable cnt = 0 
         for i in 0 .. r.inUse do
            if r.isBVVar i && r.isConcreteValue i then
                cnt <- cnt + 1 
         cnt

    member r.getExplanation (v:Var) =
        assert (0 <= v && v <= r.inUse) 
        r.mAssignmntsExplanations.[v]
    member r.getMAssignmentExplRef = 
        ref r.mAssignmntsExplanations
    
    member r.enterTempMode (orig:Ref<BitVectorValuation>) (sorts:Ref<int[]>) = 
        assert (not r.inTempMode )
        assert (r.snapshot = -1)
        r.inTempMode <- true        
        r.snapshot <- (!orig).getInUse
        r.fastForward r.snapshot sorts
        
        assert (r.inUse = (!orig).getInUse)
        assert (Array.fold (fun s (x:BitVector) -> s && (x.isFullyUndefined) ) true r.vals)
        assert (Array.fold (fun s (x:int) -> s && x = 0) true r.mAssignmntsExplanations )
        for i in 1 .. r.inUse - 1 do
            assert (r.vals.[i].Length = (!sorts).[i])
            assert (r.vals.[i].Length = (!orig).vals.[i].Length)

        
        
//        for i in 0 .. r.inUse do
//            assert (r.vals.[i].isFullyUndefined)


    member r.leaveTempMode = 
        assert(r.inTempMode)
        assert(r.snapshot >= 0)       
        for i in r.snapshot .. r.inUse - 1 do
            r.vals.[i] <- BitVector.Invalid
            r.mAssignmntsExplanations.[i] <- 0
            
        r.inUse <- r.snapshot
        r.snapshot <- -1
        r.inTempMode <- false