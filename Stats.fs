module Stats

open System.Collections.Generic
open Microsoft.Z3

type Statistics () =
    member val propagations = ref 0
    member val conflicts = ref 0
    member val decisions = ref 0
    member val modelAssignments =  ref 0
    member val intrThLits =  ref 0
    member val intrNumerals =  ref 0

    member r.Implication() =
        incr r.propagations

    member r.Conflict() =
        incr r.conflicts

    member r.Decision() =
        incr r.decisions

    member r.ModelAssignment() =
        incr r.modelAssignments

    member r.NewThLiteral() =
        incr r.intrThLits

    member r.NewNumeral() =
        incr r.intrNumerals

    member r.Print() =
        printfn "+------- Statistics --------+"
        printfn "| Decisions    : % 10d |" (!r.decisions)
        printfn "| Propagations : % 10d |" (!r.propagations)
        printfn "| Conflicts    : % 10d |" (!r.conflicts)
        printfn "| MAssignments : % 10d |" (!r.modelAssignments)
        printfn "| Theory Lits  : % 10d |" (!r.intrThLits)
        printfn "| Numerals     : % 10d |" (!r.intrNumerals)
        printfn "+---------------------------+"
