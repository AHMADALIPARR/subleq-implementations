! SPDX-License-Identifier: AGPL-3.0-or-later
! Unit tests for factor/subleq.factor.
! Usage: factor factor/subleq-tests.factor   (exits 1 if any check fails)
USING: command-line namespaces io.pathnames parser kernel ;
<< script get parent-directory "subleq.factor" append-path run-file >>
USING: arrays subleq io kernel math math.parser namespaces prettyprint sequences
system ;
IN: subleq.tests

SYMBOLS: checks failures ;
0 checks set-global 0 failures set-global

: check ( actual expected name -- )
    checks [ 1 + ] change-global
    [ 2dup = ] dip swap
    [ 3drop ]
    [
        "FAIL " write print
        "  expected " write unparse print
        "  actual   " write unparse print
        failures [ 1 + ] change-global
    ] if ;

! wrap32
2147483648 wrap32 -2147483648 "wrap 2^31" check
-2147483649 wrap32 2147483647 "wrap -2^31-1" check
4294967295 wrap32 -1 "wrap 2^32-1" check

! subleq-step on its own: ( mem ip -- mem' ip' )
"running" status set 0 steps set
{ 3 0 7 5 } clone 0 subleq-step
7 "branch to absolute c = 7" check
{ -2 0 7 5 } "M[0] = 3 - 5" check

! run-subleq drives subleq-step until it returns f
{ 3 3 -1 7 } { } 100 run-subleq
status get "halted" "branch to c = -1 halts" check
last-pc get -1 "halt pc is -1" check
memory get { 3 3 -1 0 } "M[3] = 0" check

{ 4 3 -1 5 1 } { } 100 run-subleq
status get "halted" "no branch, c = -1 halts" check
last-pc get 3 "pc + 3" check

{ 4 3 -1 -2147483648 1 } { } 100 run-subleq
memory get { 4 3 -1 2147483647 1 } "wrapped subtraction" check
last-pc get 3 "wrapped result > 0 does not branch" check

{ -2 -7 5 } { } 100 run-subleq
status get "trap" "trap beats output" check
trap-code get -7 "trap code is b" check
steps get 1 "trap counts one step" check

{ -1 3 -1 0 } { 77 } 100 run-subleq
memory get { -1 3 -1 77 } "input stored in M[b]" check

{ -1 -5 -1 } { 1 } 100 run-subleq
outputs get length 0 "input beats output" check

{ -1 0 -1 } { } 100 run-subleq
status get "fault:input-exhausted" "input exhausted" check
steps get 0 "fault counts no step" check

{ 99 -1 -1 } { } 100 run-subleq
outputs get >array { 0 } "out-of-range read is 0" check

{ 3 200 -1 -5 } { } 100 run-subleq
memory get { 3 200 -1 -5 } "out-of-range write discarded" check

{ 0 0 } { } 100 run-subleq
status get "fault:pc-out-of-range" "pc out of range" check

{ 0 0 0 } { } 10 run-subleq
status get "step-limit" "step limit" check
steps get 10 "ten steps" check

"factor: " write checks get-global number>string write " checks, " write
failures get-global number>string write " failed" print
failures get-global zero? [ 0 ] [ 1 ] if exit
