\ Copyright (C) Ahmad <ahmedparr93@gmail.com>
\ SPDX-License-Identifier: AGPL-3.0-only

\ Forth SUBLEQ Test Suite
\ Tests all verification obligations in Forth
\ Run with: gforth forth/subleq.fs forth/test-subleq.fs

cr .( === Running Forth SUBLEQ Verification Obligations === ) cr

: ASSERT ( flag -- )
  if else ." ASSERTION FAILED" cr 1 throw then ;

\ 1. Positive subtraction (3 4 6  3 10 0)
create TEST1 3 , 4 , 6 , 3 , 10 , 0 ,
SUBLEQ-INIT
TEST1 6 SUBLEQ-LOAD-MEM
SUBLEQ-STEP
SUBLEQ-MEM 4 cells + @ 7 = ASSERT
SUBLEQ-IP @ 3 = ASSERT
SUBLEQ-HALTED @ 0= ASSERT
.( PASS: Positive subtraction ) cr

\ 2. Negative subtraction (3 4 6  5 2 0)
create TEST2 3 , 4 , 6 , 5 , 2 , 0 ,
SUBLEQ-INIT
TEST2 6 SUBLEQ-LOAD-MEM
SUBLEQ-STEP
SUBLEQ-MEM 4 cells + @ -3 = ASSERT
SUBLEQ-IP @ 6 = ASSERT
.( PASS: Negative subtraction ) cr

\ 3. Zero subtraction (3 4 6  5 5 0)
create TEST3 3 , 4 , 6 , 5 , 5 , 0 ,
SUBLEQ-INIT
TEST3 6 SUBLEQ-LOAD-MEM
SUBLEQ-STEP
SUBLEQ-MEM 4 cells + @ 0 = ASSERT
SUBLEQ-IP @ 6 = ASSERT
.( PASS: Zero subtraction ) cr

\ 4. Aliasing (3 3 6  42 0 0)
create TEST4 3 , 3 , 6 , 42 , 0 , 0 ,
SUBLEQ-INIT
TEST4 6 SUBLEQ-LOAD-MEM
SUBLEQ-STEP
SUBLEQ-MEM 3 cells + @ 0 = ASSERT
SUBLEQ-IP @ 6 = ASSERT
.( PASS: Aliasing ) cr

\ 5. Instruction modification (3 3 3  10 20 30)
create TEST5 3 , 3 , 3 , 10 , 20 , 30 ,
SUBLEQ-INIT
TEST5 6 SUBLEQ-LOAD-MEM
SUBLEQ-STEP
SUBLEQ-MEM 3 cells + @ 0 = ASSERT
SUBLEQ-IP @ 3 = ASSERT
.( PASS: Self-modification ) cr

\ 6. Invalid fetch
create TEST6 1 , 2 ,
SUBLEQ-INIT
TEST6 2 SUBLEQ-LOAD-MEM
SUBLEQ-STEP
SUBLEQ-HALTED @ 1 = ASSERT
SUBLEQ-FAULT @ FAULT-INVALID-FETCH = ASSERT
.( PASS: Invalid fetch ) cr

\ 7. Invalid read
create TEST7 99 , 1 , 0 , 0 , 0 , 0 ,
SUBLEQ-INIT
TEST7 6 SUBLEQ-LOAD-MEM
SUBLEQ-STEP
SUBLEQ-HALTED @ 1 = ASSERT
SUBLEQ-FAULT @ FAULT-INVALID-READ = ASSERT
.( PASS: Invalid read ) cr

\ 8. Invalid write
create TEST8 0 , 99 , 0 , 0 , 0 , 0 ,
SUBLEQ-INIT
TEST8 6 SUBLEQ-LOAD-MEM
SUBLEQ-STEP
SUBLEQ-HALTED @ 1 = ASSERT
SUBLEQ-FAULT @ FAULT-INVALID-WRITE = ASSERT
.( PASS: Invalid write ) cr

\ 9. Input extension & exhaustion
create TEST9 -1 , 3 , 6 , 0 , 0 , 0 ,
create IN9 42 ,
SUBLEQ-INIT
TEST9 6 SUBLEQ-LOAD-MEM
IN9 1 SUBLEQ-LOAD-IN
SUBLEQ-STEP
SUBLEQ-MEM 3 cells + @ 42 = ASSERT
SUBLEQ-IP @ 3 = ASSERT
.( PASS: Input val ) cr

SUBLEQ-INIT
TEST9 6 SUBLEQ-LOAD-MEM
SUBLEQ-STEP
SUBLEQ-HALTED @ 1 = ASSERT
SUBLEQ-FAULT @ FAULT-INPUT-EXHAUSTED = ASSERT
.( PASS: Input exhausted ) cr

\ 10. Output extension
create TEST10 3 , -1 , 6 , 99 , 0 , 0 ,
SUBLEQ-INIT
TEST10 6 SUBLEQ-LOAD-MEM
SUBLEQ-STEP
SUBLEQ-OUT-COUNT @ 1 = ASSERT
SUBLEQ-OUT @ 99 = ASSERT
SUBLEQ-IP @ 3 = ASSERT
.( PASS: Output extension ) cr

\ 11. Halt sentinel
create TEST11 -1 , -1 , -1 ,
SUBLEQ-INIT
TEST11 3 SUBLEQ-LOAD-MEM
SUBLEQ-STEP
SUBLEQ-HALTED @ 1 = ASSERT
.( PASS: Halt sentinel ) cr

\ 12. Countdown loop: 3 1 0  1 0 12  2 2 3  0 0 0  -1 -1 -1
create TEST12 3 , 1 , 0 ,  1 , 0 , 12 ,  2 , 2 , 3 ,  0 , 0 , 0 ,  -1 , -1 , -1 ,
SUBLEQ-INIT
TEST12 15 SUBLEQ-LOAD-MEM
3 SUBLEQ-IP !
100 SUBLEQ-RUN
SUBLEQ-HALTED @ 1 = ASSERT
SUBLEQ-MEM @ 0 = ASSERT
.( PASS: Countdown loop ) cr

\ 13. Flash-Attention trap
create TEST13 -2 , 0 , 6 , 0 , 0 , 0 ,
SUBLEQ-INIT
TEST13 6 SUBLEQ-LOAD-MEM
SUBLEQ-STEP
SUBLEQ-FAULT @ FAULT-FA-TRAP = ASSERT
SUBLEQ-IP @ 6 = ASSERT
.( PASS: FA trap ) cr

cr .( All Forth SUBLEQ verification obligations passed successfully! ) cr
bye
