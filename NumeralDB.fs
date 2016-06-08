module NumeralDB

open System.Collections.Generic
open System.Numerics

open Microsoft.Z3
open Literal
open GlobalOptions
open BitVector
open Stats
open Stats

type Num = int

type NumeralDB private (size:int) =
    let mutable allocated = size
    let mutable reallocCoefficient = 2.0

    member val next_unused = 1 with get, set
    member val int2bv = Array.create allocated BitVector.Invalid with get, set
    member val bv2int = new Dictionary<BitVector, int>() with get, set

    new (expr2num:Dictionary<Expr, int>) as this =
        NumeralDB(expr2num.Count + 1)
        then
            for kvp in expr2num do
                let id = abs kvp.Value
                assert(id > 0)
                if id >= this.next_unused then
                    this.next_unused <- id + 1
                let num = BitVector.BitVectorFromExpr kvp.Key
                if this.int2bv.[id].isInvalid then
                    assert(not (this.bv2int.ContainsKey num))
                    this.ensureSize (id + 1)
                    this.bv2int.Add(num, id)
                    this.int2bv.[id] <- num
                else
                    assert(id <> 0)
                    assert(this.int2bv.[id] = num)
                    assert(this.bv2int.[num] = id)

    member r.ensureSize (minSize:int) =
        while allocated <= minSize do
            let newSize = int (reallocCoefficient * float allocated)
            r.int2bv <- Array.append r.int2bv (Array.create ((newSize + 1) - allocated) BitVector.Invalid)
            allocated <- newSize

    member r.newNumeral (stats:Ref<Statistics>) (num:BitVector) : Num =
        if r.bv2int.ContainsKey(num) then
            -r.bv2int.[num]
        else
            let id = r.next_unused
            r.next_unused <- id + 1
            r.ensureSize (id + 1)
            assert(r.int2bv.[id].isInvalid)
            r.int2bv.[id] <- num
            r.bv2int.Add(num, id)
            if TRC then
                printfn "X New numeral: %d:num := %s" id (num.ToString())
            (!stats).NewNumeral()
            -id

    member r.getNumeral (n:Num) =
        let id = abs n
        assert(id > 0 && id < r.int2bv.Length)
        let res = r.int2bv.[id]
        assert(res.isValid)
        res


    member val private inTempMode = false with get, set
    member val private snapshot = -1 with get, set

    member r.enterTempMode () =
        assert(not r.inTempMode)
        assert(r.snapshot = -1)
        r.inTempMode <- true
        r.snapshot <- r.int2bv.Length

    member r.leaveTempMode =
        assert(r.inTempMode)
        assert(r.snapshot >= 0)
        for i in r.snapshot .. r.int2bv.Length - 1 do            
            r.int2bv.[i].Length <- 0
            r.bv2int.Remove r.int2bv.[i] |> ignore
        r.next_unused <- r.snapshot
        r.snapshot <- -1
        r.inTempMode <- false