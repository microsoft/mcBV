module BoundInference
open System.Collections.Generic
open Microsoft.Z3
open GlobalOptions
open Util
open Numeral
open Literal
open BooleanValuation
open Clause
open Trail 
open State
open WatchManager
open VariableDB
open ClauseDB
open TheoryDB
open ThRel
open BitVector
open BitVectorValuation
open Explain
open Learning

// 1 Determine the relation
// 2 Determine reverse operation
// 3 Evaluate

//
//let inferByRelations (s:State) (v:int) (tRel:internalThRel) = 
//    assert (List.exists (fun x -> x = v) tRel.distinctArgs)
//    
//    if tRel.getRhs 

// Assume" x_l,x_u <= op args_l args_u (rhs)
// We will evaluate the op args_l args_u
// And based on that update the x_l, x_u
// rhs_l <= x_l <= x_u <= rhs_u
//
//let inferBounds (s:State) (v:int) (tRel:internalThRel) =    
//    let (currentL, currentU) = (!s.partAssignment).getBounds v
//    if BitVector.bvEQ currentL currentU then
//        None
//    else 
//        let (inferredL,inferredU) = inferByRelations s v tRel
//
//        let resL = if not (BitVector.bvULEQ inferredL currentL) then
//                        inferredL
//                   else 
//                        currentL
//
//        let resU = if not (BitVector.bvULEQ currentU inferredU) then
//                        inferredU
//                   else 
//                        currentU
//        Some (relL,resU)    
//
//
