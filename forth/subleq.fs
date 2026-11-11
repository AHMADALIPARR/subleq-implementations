\ Copyright (C) Ahmad <ahmedparr93@gmail.com>
\ SPDX-License-Identifier: AGPL-3.0-only

\ SUBLEQ Virtual Machine in Forth (ANS Forth / Gforth compliant)
\ Machine State:
\   - Memory tape: array of cells
\   - Instruction Pointer: IP
\   - Input stream: array of cells + head pointer + count
\   - Output stream: array of cells + count
\   - Halted flag: HALTED?
\   - Fault flag: FAULT-CODE (0=None, 1=InvalidFetch, 2=InvalidRead, 3=InvalidWrite, 4=InputExhausted, 5=FATrap)

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

: SUBLEQ-INIT ( -- )
  0 SUBLEQ-IP !
  0 SUBLEQ-IN-HEAD !
  0 SUBLEQ-IN-COUNT !
  0 SUBLEQ-OUT-COUNT !
  0 SUBLEQ-HALTED !
  FAULT-NONE SUBLEQ-FAULT ! ;

: SUBLEQ-LOAD-MEM ( addr u -- )
  dup SUBLEQ-MEM-SIZE !
  0 ?do
    dup i cells + @
    SUBLEQ-MEM i cells + !
  loop
  drop ;

: SUBLEQ-LOAD-IN ( addr u -- )
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
    CUR-A @ cells SUBLEQ-MEM + @
    SUBLEQ-OUT SUBLEQ-OUT-COUNT @ cells + !
    1 SUBLEQ-OUT-COUNT +!
    SUBLEQ-IP @ 3 + SUBLEQ-IP !
    SUBLEQ-IP @ 0 < if 1 SUBLEQ-HALTED ! then
    exit
  then

  \ Standard arithmetic: a >= 0, b >= 0
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
  - \ val_b - val_a
  dup CUR-B @ cells SUBLEQ-MEM + !
  0 <= if
    CUR-C @ SUBLEQ-IP !
  else
    SUBLEQ-IP @ 3 + SUBLEQ-IP !
  then
  SUBLEQ-IP @ 0 < if 1 SUBLEQ-HALTED ! then ;

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
: subleq ( a b c -- )
  >r
  dup cells SUBLEQ-MEM + @
  over cells SUBLEQ-MEM + @
  swap -
  rot cells SUBLEQ-MEM + !
  dup 0 <= if r> SUBLEQ-IP ! else r> drop drop then ;
