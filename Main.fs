module Main

open System.Collections.Generic

open GlobalOptions
open Util
open Solver
open ModelVerification
open State

let showHelp () =
    printfn "mcBV 1.0 (C) Copyright 2016 Microsoft Corporation"
    printfn "Usage: mcbv.exe [options] <filename>"
    printfn "Options:"
    printfn "Capital letter sets the option ON, lower letter sets the option OFF [default]"
    printfn " -I/i Interactive mode (after solving waits for a key to be pressed) [on]"
    printfn " -D/d Debug mode [off]"
    printfn " -V/v Verbose mode [off]"
    printfn " -T/t Print traces [off]"
    printfn " -M/m Print model [off]"
    printfn " -Q/q Verify model [on]"
    printfn " -C/c Run z3 checks [off]"
    printfn " -J/j Just answer [off]"



let parseArguments (argv:array<string>) =

    for arg in argv do
        if arg.Chars 0 = '-' then
            for c in arg.ToCharArray() do
                match c with
                | 'I' -> INTERACTIVE <- true
                | 'i' -> INTERACTIVE <- false
                | 'V' -> VRB <- true
                | 'v' -> VRB <- false
                | 'D' -> DBG <- true
                | 'd' -> DBG <- false
                | 'T' -> TRC <- true
                | 't' -> TRC <- false
                | 'M' -> SHOWMODEL <- true
                | 'm' -> SHOWMODEL <- false
                | 'Q' -> VERIFYMODEL <- true
                | 'q' -> VERIFYMODEL <- false
                | 'C' -> RUNZ3CHECKS <- true
                | 'c' -> RUNZ3CHECKS <- false
                | 'J' -> POLITE <- true
                | 'j' -> POLITE <- false
                | 'N' -> PREPROCESS <- true
                | 'n' -> PREPROCESS <- false
                | 'G' -> GENERALIZE <- true
                | 'g' -> GENERALIZE <- false
                | 'B' -> USE_BOUNDS <- true
                | 'b' -> USE_BOUNDS <- false
                | 'K' -> SHOW_CONFLICTS <- true
                | _ -> ()

    Array.filter (fun (x:string) -> x.Chars 0 <> '-' ) argv

[<EntryPoint>]
let main argv =
    if argv.Length <= 0 then

        showHelp() ;
        30 // `Error'

    else
        let before = System.DateTime.Now
        let mutable exitStatus = 30 // = Error

        try
            let inputs = parseArguments argv

            if inputs.Length <= 0 then
                showHelp()
                exitStatus <- 30
            else
                let z3opts = new Dictionary<string,string>()
                let s = new Solver()
                let p = s.Load(z3opts, inputs.[0])

                // printfn "%s" inputs.[0]
                // dbg <| (lazy sprintf "%s" (p.ToString()))

                let solution = s.Solve p

                match solution with
                | SAT(m) ->
                    if not (Verify p m) then
                        printfn ("Error: Model verification failed.")
                        exitStatus <- 30
                    else
                        printfn("sat")
                        exitStatus <- 10
                | UNSAT ->
                        printfn ("unsat")
                        exitStatus <- 20
                | UNKNOWN ->
                        printfn ("unknown")
                        exitStatus <- 30
        with
        | :? System.StackOverflowException
        | :? System.OutOfMemoryException
        | :? Microsoft.Z3.Z3Exception as ex when ex.Message = "out of memory" ->
            // Ocassionally OutOfMemory exceptions are thrown from Z3, or from F#
            printfn "(error \"out of memory\")"
            exitStatus <- 30
        | :? System.AccessViolationException as ex ->
            // There is a rare case in which Z3 throws an access violation during
            // context destruction, could be a cleanup bug in Z3.
            // Unhandled Exception: System.AccessViolationException: Attempted to read or write protected memory. This is often an indication that other memory is corrupt.
            //    at Microsoft.Z3.Native.LIB.Z3_del_context(IntPtr a0)
            //    at Microsoft.Z3.Context.Finalize()
            if (ex.Message.Contains("Microsoft.Z3.Native.LIB.Z3_del_context") ||
                ex.StackTrace.Contains("Microsoft.Z3.Native.LIB.Z3_del_context")) then
                printfn "Z3 cleanup problem ignored."
                () // keep previous exit status
            else
                exitStatus <- 30
        | Failure msg ->
            printfn "EXCEPTION: %s" msg
            printfn "UNKNOWN"
            exitStatus <- 30
        | ex ->
            printfn "EXCEPTION: %s: %s" ((ex.GetType()).ToString()) (ex.StackTrace.ToString())
            printfn "UNKNOWN"
            exitStatus <- 30

        if INTERACTIVE then
            System.Console.ReadKey() |> ignore

        let time = System.DateTime.Now - before
        printfn "%f sec." time.TotalSeconds
        exitStatus  // All done.