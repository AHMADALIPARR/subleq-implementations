<!--
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only
-->

# SUBLEQ Microcode / Gate-Level Description

## Half Subtractor Logic (mapped to NAND gates)

INPUTS:
  Bit B_i, Bit A_i
  Borrow_In (Bin)

// Invert A for subtraction
NOT_A = A_i NAND A_i

// Half Subtractor logic mapped to Gates
XOR_1 = B_i XOR NOT_A
SUM_i = XOR_1 XOR Bin    // This routes back to mem[B]

// Borrow Out (Bout) generation
NAND_1 = B_i NAND NOT_A
NAND_2 = XOR_1 NAND Bin
Bout   = NAND_1 NAND NAND_2

## Flags for Branch

// 1. Check if Negative (Just read the Most Significant Bit)
Sign_Flag = SUM_31

// 2. Check if exactly Zero (NOR tree across all 32 output bits)
// If any bit is 1, the result is 0. If all are 0, result is 1.
Zero_Flag = NOT (SUM_0 OR SUM_1 OR ... OR SUM_31)

// 3. JLE Trigger
Branch_Enable = Sign_Flag OR Zero_Flag

## ATS2 Dependently Typed Primitive (Verified Bounds)

```ats
// ATS2: Dependently typed SUBLEQ primitive
// The {a,b:nat | a < 1000, b < 1000} constraint proves at compile-time 
// that pointers a and b are strictly within the tape bounds.

fun verified_subleq 
  {a,b:nat | a < 1000, b < 1000} 
  ( mem: &(@[int][1000])
  , a: int a
  , b: int b
  ) : int = let
  
  // Extract values, backed by machine-checked proofs
  val val_a = mem[a]
  val val_b = mem[b]
  val result = val_b - val_a
  
  // Mutate tape
  val () = mem[b] := result
in
  result
end
```
