\ Copyright (C) Ahmad <ahmedparr93@gmail.com>
\ SPDX-License-Identifier: AGPL-3.0-only

\ SUBLEQ Virtual Machine in Forth (ANS Forth / Gforth compliant)
\ Machine State:
\   - Memory tape: array of cells
\   - Instruction Pointer: IP
\   - Input stream: array of cells + head pointer + count
\   - Output stream: array of cells + count
\   - Halted flag: HALTED?
\   - Fault flag: FAULT-CODE (0=None, 1=InvalidFetch, 2=InvalidRead, 3=InvalidWrite, 4=InputExhausted, 5=FATrap, 6=Overflow)

10000 constant MAX-MEM
1000 constant MAX-IO

create SUBLEQ-MEM MAX-MEM cells allot
variable SUBLEQ-MEM-SIZE

variable SUBLEQ-IP

create SUBLEQ-IN MAX-IO cells allot
variable SUBLEQ-IN-HEAD
variable SUBLEQ-IN-COUNT

create SUBLEQ-OUT MAX-IO cells allot
variable SUBLEQ-OUT-COUNT

variable SUBLEQ-HALTED
variable SUBLEQ-FAULT

\ Variables to hold current instruction
variable CUR-A
variable CUR-B
variable CUR-C

\ Fault constants
0 constant FAULT-NONE
1 constant FAULT-INVALID-FETCH
2 constant FAULT-INVALID-READ
3 constant FAULT-INVALID-WRITE
4 constant FAULT-INPUT-EXHAUSTED
5 constant FAULT-FA-TRAP
\ M[b] - M[a] does not fit in a cell (the Racket, Factor and Lean engines are unbounded)
6 constant FAULT-OVERFLOW

: SUBLEQ-INIT ( -- )
  0 SUBLEQ-IP !
  0 SUBLEQ-IN-HEAD !
  0 SUBLEQ-IN-COUNT !
  0 SUBLEQ-OUT-COUNT !
  0 SUBLEQ-HALTED !
  FAULT-NONE SUBLEQ-FAULT ! ;

: SUBLEQ-LOAD-MEM ( addr u -- )
  dup 0 < over MAX-MEM > or if
    2drop 0 SUBLEQ-MEM-SIZE !
    1 SUBLEQ-HALTED !
    FAULT-INVALID-WRITE SUBLEQ-FAULT !
    exit
  then
  dup SUBLEQ-MEM-SIZE !
  0 ?do
    dup i cells + @
    SUBLEQ-MEM i cells + !
  loop
  drop ;

: SUBLEQ-LOAD-IN ( addr u -- )
  dup 0 < over MAX-IO > or if
    2drop 0 SUBLEQ-IN-COUNT !
    1 SUBLEQ-HALTED !
    FAULT-INVALID-WRITE SUBLEQ-FAULT !
    exit
  then
  dup SUBLEQ-IN-COUNT !
  0 SUBLEQ-IN-HEAD !
  0 ?do
    dup i cells + @
    SUBLEQ-IN i cells + !
  loop
  drop ;

: SUBLEQ-FETCH ( -- flag )
  SUBLEQ-IP @ dup 0 < if
    drop 1 SUBLEQ-HALTED !
    0
  else
    dup 3 + SUBLEQ-MEM-SIZE @ > if
      drop 1 SUBLEQ-HALTED !
      FAULT-INVALID-FETCH SUBLEQ-FAULT !
      0
    else
      dup cells SUBLEQ-MEM + @ CUR-A !
      dup 1+ cells SUBLEQ-MEM + @ CUR-B !
      2 + cells SUBLEQ-MEM + @ CUR-C !
      1
    then
  then ;

\ Standard arithmetic on CUR-A CUR-B CUR-C: a >= 0, b >= 0
\ (used by SUBLEQ-STEP and by the subleq primitive)
: SUBLEQ-ARITH ( -- )
  CUR-A @ 0 < CUR-A @ SUBLEQ-MEM-SIZE @ >= or if
    1 SUBLEQ-HALTED !
    FAULT-INVALID-READ SUBLEQ-FAULT !
    exit
  then
  CUR-B @ 0 < CUR-B @ SUBLEQ-MEM-SIZE @ >= or if
    1 SUBLEQ-HALTED !
    FAULT-INVALID-WRITE SUBLEQ-FAULT !
    exit
  then

  CUR-B @ cells SUBLEQ-MEM + @
  CUR-A @ cells SUBLEQ-MEM + @
  2dup - >r \ val_b - val_a
  \ overflow when val_b and val_a differ in sign and the result's sign differs from val_b
  over xor swap r@ xor and 0 < if
    r> drop
    1 SUBLEQ-HALTED !
    FAULT-OVERFLOW SUBLEQ-FAULT !
    exit
  then
  r>
  dup CUR-B @ cells SUBLEQ-MEM + !
  0 <= if
    CUR-C @ SUBLEQ-IP !
  else
    SUBLEQ-IP @ 3 + SUBLEQ-IP !
  then
  SUBLEQ-IP @ 0 < if 1 SUBLEQ-HALTED ! then ;

: SUBLEQ-STEP ( -- )
  SUBLEQ-HALTED @ if exit then
  SUBLEQ-FAULT @ if 1 SUBLEQ-HALTED ! exit then
  SUBLEQ-FETCH 0= if exit then

  \ Check halt sentinel: a < 0 and b < 0
  CUR-A @ 0 < CUR-B @ 0 < and if
    1 SUBLEQ-HALTED !
    exit
  then

  \ Check Flash-Attention Trap: a = -2
  CUR-A @ -2 = if
    CUR-C @ 0 < if
      1 SUBLEQ-HALTED !
    else
      CUR-C @ SUBLEQ-IP !
    then
    FAULT-FA-TRAP SUBLEQ-FAULT !
    exit
  then

  \ Check Input Extension: a = -1, b >= 0
  CUR-A @ -1 = if
    CUR-B @ 0 < CUR-B @ SUBLEQ-MEM-SIZE @ >= or if
      1 SUBLEQ-HALTED !
      FAULT-INVALID-WRITE SUBLEQ-FAULT !
      exit
    then
    SUBLEQ-IN-COUNT @ 0 <= if
      1 SUBLEQ-HALTED !
      FAULT-INPUT-EXHAUSTED SUBLEQ-FAULT !
      exit
    then
    SUBLEQ-IN SUBLEQ-IN-HEAD @ cells + @ \ in-val
    CUR-B @ cells SUBLEQ-MEM + !
    1 SUBLEQ-IN-HEAD +!
    -1 SUBLEQ-IN-COUNT +!
    CUR-B @ cells SUBLEQ-MEM + @ \ val
    0 <= if
      CUR-C @ SUBLEQ-IP !
    else
      SUBLEQ-IP @ 3 + SUBLEQ-IP !
    then
    SUBLEQ-IP @ 0 < if 1 SUBLEQ-HALTED ! then
    exit
  then

  \ Check Output Extension: b = -1, a >= 0
  CUR-B @ -1 = if
    CUR-A @ 0 < CUR-A @ SUBLEQ-MEM-SIZE @ >= or if
      1 SUBLEQ-HALTED !
      FAULT-INVALID-READ SUBLEQ-FAULT !
      exit
    then
    SUBLEQ-OUT-COUNT @ MAX-IO >= if
      1 SUBLEQ-HALTED !
      FAULT-INVALID-WRITE SUBLEQ-FAULT !
      exit
    then
    CUR-A @ cells SUBLEQ-MEM + @
    SUBLEQ-OUT SUBLEQ-OUT-COUNT @ cells + !
    1 SUBLEQ-OUT-COUNT +!
    SUBLEQ-IP @ 3 + SUBLEQ-IP !
    SUBLEQ-IP @ 0 < if 1 SUBLEQ-HALTED ! then
    exit
  then

  \ Standard arithmetic: a >= 0, b >= 0
  SUBLEQ-ARITH ;

: SUBLEQ-RUN ( fuel -- )
  0 ?do
    SUBLEQ-HALTED @ if unloop exit then
    SUBLEQ-STEP
  loop ;

: SUBLEQ-OBSERVE ( -- pc halted fault out-count )
  SUBLEQ-IP @
  SUBLEQ-HALTED @
  SUBLEQ-FAULT @
  SUBLEQ-OUT-COUNT @ ;

\ Backwards-compatible subleq primitive word
\ M[b] := M[b] - M[a]; IP := c if the result is <= 0, else IP + 3
: subleq ( a b c -- )
  SUBLEQ-HALTED @ if drop 2drop exit then
  SUBLEQ-FAULT @ if drop 2drop 1 SUBLEQ-HALTED ! exit then
  CUR-C ! CUR-B ! CUR-A !
  SUBLEQ-ARITH ;
