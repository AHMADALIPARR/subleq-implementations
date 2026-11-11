\ Copyright (C) Ahmad <ahmedparr93@gmail.com>
\ SPDX-License-Identifier: AGPL-3.0-or-later
\ Unit tests for forth/subleq.fs. Usage: gforth forth/test-subleq.fs
\ Exits with status 1 if any check fails.

s" subleq.fs" included

variable checks  variable failures
: check ( f -- )
  1 checks +!  0= if 1 failures +! ." FAIL check #" checks @ 0 .r cr then ;
: image ( x0 .. xn-1 n -- )  \ load n cells, x0 deepest
  dup mem-size !  1- 0 swap ?do i mem ! -1 +loop ;
: no-input ( -- ) 0 in-count ! ;
: one-input ( v -- ) inbuf ! 1 in-count ! ;

\ wrap32
2147483648 wrap32 -2147483648 = check
-2147483649 wrap32 2147483647 = check
4294967295 wrap32 -1 = check
5 wrap32 5 = check

\ the subleq word alone: M[b] := M[b] - M[a], branch to c if <= 0
3 0 7 5 4 image  reset  3 2 9 subleq  2 mem @ 2 = check  ip @ 3 = check
3 0 7 5 4 image  reset  2 3 9 subleq  3 mem @ -2 = check  ip @ 9 = check

\ ordinary step, branch taken to c = -1 -> halted, pc -1
3 3 -1 7 4 image no-input reset 100 run
status @ halted = check  ip @ -1 = check  3 mem @ 0 = check  steps @ 1 = check
\ branch not taken, still halts on c = -1
4 3 -1 5 1 5 image no-input reset 100 run
status @ halted = check  ip @ 3 = check  3 mem @ 4 = check
\ wrapped overflow: -2^31 - 1 -> 2^31 - 1, no branch
4 3 -1 -2147483648 1 5 image no-input reset 100 run
3 mem @ 2147483647 = check  ip @ 3 = check
\ trap: priority over output, records b
-2 -7 5 3 image no-input reset 100 run
status @ trapped = check  trap-code @ -7 = check  ip @ 0 = check  steps @ 1 = check
\ input into M[3]
-1 3 -1 0 4 image 77 one-input reset 100 run
status @ halted = check  3 mem @ 77 = check  ip @ 3 = check
\ input beats output when b < 0 (value discarded)
-1 -5 -1 3 image 1 one-input reset 100 run
status @ halted = check  out-count @ 0 = check
\ input exhausted
-1 0 -1 3 image no-input reset 100 run
status @ fault-input = check  steps @ 0 = check
\ output, out-of-range read gives 0
99 -1 -1 3 image no-input reset 100 run
out-count @ 1 = check  outbuf @ 0 = check
\ out-of-range ordinary write is discarded
3 200 -1 -5 4 image no-input reset 100 run
3 mem @ -5 = check  ip @ 3 = check
\ pc out of range
0 0 2 image no-input reset 100 run
status @ fault-pc = check
\ step limit
0 0 0 3 image no-input reset 10 run
status @ step-limit = check  steps @ 10 = check

." forth: " checks @ 0 .r ."  checks, " failures @ 0 .r ."  failed" cr
failures @ 0<> 1 and (bye)
