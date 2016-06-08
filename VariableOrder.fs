module VariableOrder

open System.Collections.Generic
open PriorityQueue
open Literal


type VariableOrder ()  = class
    let initBvValue = 100000
    let initBoolValue = 99900
    let resetValue = 100001
    let increment = 1

    let step = 500
    let mutable allocated = 11 // 1 to account for L 0 being reserved
    let mutable priorities = Array.create allocated resetValue
    let mutable queue = new PriorityQueue<int, Var> ()

    member val private inTempMode = false with get, set

    member r.enterTempMode () =
        assert(not r.inTempMode)
        r.inTempMode <- true

    member r.leaveTempMode =
        assert(r.inTempMode)
        r.inTempMode <- false

    member private this.insertPriority (v:Var) (p:int) =
        if v >= allocated then
            priorities <- Array.append priorities (Array.create step resetValue)
            allocated <- allocated + step

        priorities.[v] <- p

    member private this.getPriority (v:Var) =
        assert (v < allocated)
        priorities.[v]

    member private this.setPriority (v:Var) (p:int) =
        assert (v < allocated)
        priorities.[v] <- p

    member this.insert (v:Var) (isBool:bool) =
        if not this.inTempMode then
            assert (v <> 0)
            let iv = if isBool then initBoolValue else initBvValue
            assert (v >= allocated || this.getPriority v = resetValue)
            assert (not (queue.Contains iv v))
            this.insertPriority v iv
            queue.Enqueue iv v

    member this.boost (v:Var) =
        if not this.inTempMode then
            let p = this.getPriority v
            if (queue.Contains p v) then
                let newP = queue.Peek().Key - 1
                assert (newP > p)
                this.setPriority v newP
                let idx = queue.IndexOf p v
                queue.RemoveAt idx
                queue.Enqueue newP v

    member this.bump (v:Var) =
        if not this.inTempMode then
            let p = this.getPriority v
            let idx = queue.IndexOf p v
            if idx <> -1 then
                let newP = p - increment
                assert (newP < p)
                this.setPriority v newP

                queue.RemoveAt idx
                queue.Enqueue newP v

    member this.IsEmpty = queue.IsEmpty

    member this.suspend (v:Var) =
        if not this.inTempMode then
            let p = this.getPriority v // CMW: priority can stay in priorities.[v]
            let idx = queue.IndexOf p v
            if idx <> -1 then
                queue.RemoveAt idx

    member this.restore (v:Var)  =
        if not this.inTempMode then
            let p = this.getPriority v
            assert (not (queue.Contains p v))
            queue.Enqueue p v

    member this.next() =
        if not this.inTempMode then
            let mutable pair = queue.Dequeue()
            let p = pair.Key
            let v = pair.Value
            assert (p = this.getPriority v)
            this.setPriority v resetValue
            queue.Enqueue resetValue v // CMW: Is this necessary, or can we leave v unqueued?
            v
        else
            assert(false)
            -1

end
