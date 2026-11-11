\ SPDX-License-Identifier: AGPL-3.0-or-later
\ SUBLEQ Virtual Machine in Forth
\ Instruction: subleq a, b, c  (mem[b] = mem[b] - mem[a], branch to c if <= 0)
\ Semantics: semantics/subleq-spec.md (32-bit wrap, absolute c, halt on c = -1,
\ a = -2 trap > a = -1 input > b < 0 output > ordinary, out-of-range reads 0,
\ out-of-range writes discarded, PC out of range = fault).

variable ip  \ Instruction pointer
CREATE memory 1000 cells allot  \ 1000 cell memory space
variable mem-size  \ cells actually loaded (N); 0 <= N <= 1000

: mem ( n -- addr )  cells memory + ;
: in-range? ( n -- f )  0 mem-size @ within ;
: rd ( a -- v )  dup in-range? if mem @ else drop 0 then ;
: wr ( v a -- )  dup in-range? if mem ! else 2drop then ;
: wrap32 ( n -- n' )  $FFFFFFFF and dup $80000000 and if $100000000 - then ;

: subleq ( a b c -- )
  \ Fetch values, subtract, store, and conditional branch
  >r
  swap rd over rd swap - wrap32 ( b val_b-val_a )
  dup rot wr ( store result in b )
  0 <= if r> ip ! else r> drop 3 ip +! then ;

\ ---- machine status, I/O buffers and the run loop ----
0 constant running
1 constant halted
2 constant trapped
3 constant fault-pc
4 constant fault-input
5 constant step-limit
variable status
variable trap-code
variable steps

CREATE inbuf 1000 cells allot
variable in-count
variable in-pos
100000 constant out-max
CREATE outbuf out-max cells allot
variable out-count

: out, ( v -- )
  out-count @ out-max >= abort" subleq: output buffer full"
  out-count @ cells outbuf + !  1 out-count +! ;

: reset ( -- )
  0 ip !  running status !  0 trap-code !  0 steps !
  0 in-pos !  0 out-count ! ;

: fetch ( -- a b c )  ip @ mem @  ip @ 1+ mem @  ip @ 2 + mem @ ;

: halt-on-c ( c -- )  -1 = if halted status ! then ;

: step ( -- )
  ip @ 0< ip @ 2 + mem-size @ >= or if fault-pc status ! exit then
  fetch ( a b c )
  2 pick -2 = if drop trap-code ! drop trapped status ! 1 steps +! exit then
  2 pick -1 = if
    in-pos @ in-count @ >= if drop 2drop fault-input status ! exit then
    rot drop ( b c ) >r
    in-pos @ cells inbuf + @ wrap32 swap wr  1 in-pos +!
    3 ip +!  1 steps +!  r> halt-on-c exit
  then
  over 0< if
    nip ( a c ) >r  rd out,
    3 ip +!  1 steps +!  r> halt-on-c exit
  then
  dup >r subleq  1 steps +!  r> halt-on-c ;

: run ( fuel -- )
  begin
    status @ running = while
    steps @ over >= if step-limit status ! else step then
  repeat drop ;
