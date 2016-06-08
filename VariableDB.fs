module VariableDB

open Microsoft.Z3
open System.Collections.Generic
open GlobalOptions
open Util
open Literal
open VariableOrder



type VariableDB private (size:int) =
    //Handles variables that are currently in use
    //Boolean and BitVector variables are mixed up
    //Sorts will make the distinction between boolean and bv mvars

    let reallocCoefficient = 0.5

    new (var2sort:VarType[]) as this =
        let size = var2sort.Length - 1
        VariableDB (size)
        then
            this.sorts <- var2sort
            for i in 1 .. this.highestVarInUse do
                if var2sort.[i] > 0 then
                    this.varOrder.insert i false
                else
                    this.varOrder.insert i true

    member val originalSize = size + 1
    member val allocatedSize = size + 1 with get,set

    // Dictates the size of the sort array
    member val highestVarInUse = size with get, set
    member val private inTempMode = false with get, set
    member val private snapshot = -1 with get, set
    member val varOrder : VariableOrder =  new VariableOrder()
    member val sorts = [||] with get, set

    member private r.isLegal (v:int) = 0 < v && v <= r.highestVarInUse

    member private r.reallocate () =
        let sizeIncrement =  int (reallocCoefficient * (float r.allocatedSize))
        r.sorts <- Array.append r.sorts (Array.zeroCreate sizeIncrement)
        r.allocatedSize <- r.allocatedSize + sizeIncrement

    member r.isBoolean (v:int) =
        assert (r.isLegal v)
        r.sorts.[v] = 0

    member r.isBitVector (v:int) =
        assert (r.isLegal v)
        r.sorts.[v] > 0

    member r.getBitVectorLength (v:int) =
        assert (r.isLegal v)
        r.sorts.[v]

    member r.newBooleanVariable () =
        if r.highestVarInUse + 1 = r.allocatedSize then
            r.reallocate ()

        r.highestVarInUse <- r.highestVarInUse + 1
        r.varOrder.insert r.highestVarInUse true
        r.highestVarInUse

    member r.newBitVectorVariable (len:int) =
        if r.highestVarInUse + 1 = r.allocatedSize then
            r.reallocate ()

        r.highestVarInUse <- r.highestVarInUse + 1
        let v = r.highestVarInUse
        r.sorts.[v] <- len
        r.varOrder.insert v false
        v



    member r.getSnapshot = r.snapshot

    member r.enterTempMode () =
        assert(not r.inTempMode)
        assert(r.snapshot = -1)
        r.inTempMode <- true
        r.varOrder.enterTempMode()
        r.snapshot <- r.highestVarInUse

    member r.leaveTempMode =
        assert(r.inTempMode)
        assert(r.snapshot >= 0)
//        for i in r.snapshot + 1 .. r.highestVarInUse do
//            r.varOrder.remove i
        r.varOrder.leaveTempMode
        r.highestVarInUse <- r.snapshot
        r.snapshot <- -1
        r.inTempMode <- false


    member r.print () =
        if DBG then
            printfn ""
            printfn "-------------------"
            printfn "|Variable database|"
            printfn "-------------------"
            printfn "Allocated: %d   MaxVar: %d  " r.allocatedSize r.highestVarInUse
            for v in 1 .. r.highestVarInUse do
                if r.isBoolean v then
                    printfn "%d : Bool" v
                else
                    printfn "%d : BitVector %d" v r.sorts.[v]
