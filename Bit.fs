module Bit

open System.Numerics
open Util

type Bit = 
    | Zero
    | One
    | U
    | N // "Nothing" or "NotABit"
    
    override  r.ToString() =
        match r with
        | Zero -> "0"
        | One -> "1"
        | U -> "U"
        | N -> "N"

let bitFromInt (i:int64) = 
    match i with
    | 0L -> Zero
    | 1L -> One
    | _ -> U

let bitFromBigInt (i:BigInteger) = 
    if i = BigInteger.Zero then
        Zero
    elif i = BigInteger.One then
        One
    else
        U

let bitToString (b:Bit) = 
    match b with
    | Zero -> "0"
    | One -> "1"
    | U  -> "U"
    | N -> "N"

let And (b1:Bit) (b2:Bit) = 
    assert (b1 <> N && b2 <> N)
    if b1 = b2 then
        b1
    else if b1 = Zero || b2 = Zero then
        Zero
    else
        U

let Or (b1:Bit) (b2:Bit) = 
    assert (b1 <> N && b2 <> N)
    if b1 = b2 then
        b1
    else if b1 = One || b2 = One then
        One
    else
        U

let XOr (b1:Bit) (b2:Bit) = 
    assert (b1 <> N && b2 <> N)
    match (b1, b2) with
    | (Zero, Zero) 
    | (One, One)  -> Zero
    | (Zero, One) 
    | (One, Zero) -> One
    | _ -> U

let Add b1 b2 = XOr b1 b2

let Not (b1:Bit) = 
    assert (b1 <> N)
    match b1 with
    | One -> Zero
    | Zero -> One
    | U -> U
    | _ -> N

let Intersect (b1:Bit) (b2:Bit) =
    assert (b1 <> N && b2 <> N)

    match (b1,b2) with
    | (N, _)
    | (_, N)
    | (One, Zero) 
    | (Zero, One) -> //UNREACHABLE("CMW: Is Intersect really expected to return N bits?");
                     //AZ: Yes, that is how the outer function knows that it is not a valid bit-vector
                     N     
    | (U, _) -> b2
    | (_, U) -> b1
    | _ -> assert (b1=b2)
           b1

let isConcrete (b:Bit) =
    (b = One || b = Zero)    