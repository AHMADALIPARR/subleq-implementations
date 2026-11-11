\ SPDX-License-Identifier: AGPL-3.0-or-later
\ Command-line driver for forth/subleq.fs.
\ Usage: gforth forth/main.fs INPUT-FILE
\ INPUT-FILE format and the printed result: semantics/subleq-spec.md §5-6.

s" subleq.fs" included

variable src  variable src-len  variable src-pos

: peek ( -- c|-1 )  src-pos @ src-len @ < if src @ src-pos @ + c@ else -1 then ;
: skip-ws ( -- )  begin peek dup 0 33 within swap -1 <> and while 1 src-pos +! repeat ;
: next-int ( -- n )
  skip-ws peek -1 = abort" subleq: unexpected end of input"
  peek [char] - = dup if 1 src-pos +! then ( neg? )
  0 false ( neg? n any? )
  begin peek dup [char] 0 [char] 9 1+ within while
    [char] 0 - rot 10 * + swap drop true 1 src-pos +!
  repeat drop
  0= abort" subleq: bad number"
  swap if negate then ;

: load-input ( addr u -- fuel )
  slurp-file src-len ! src !  0 src-pos !
  next-int dup 0 1001 within 0= abort" subleq: N must be 0..1000"
  dup mem-size !  0 ?do next-int wrap32 i mem ! loop
  next-int dup 0 1001 within 0= abort" subleq: K must be 0..1000"
  dup in-count !  0 ?do next-int i cells inbuf + ! loop
  next-int
  skip-ws peek -1 <> abort" subleq: trailing data after FUEL" ;

: .int ( n -- )  0 .r ;
: .machine-status ( -- )
  status @ case
    halted of ." halted" endof
    trapped of ." trap" endof
    fault-pc of ." fault:pc-out-of-range" endof
    fault-input of ." fault:input-exhausted" endof
    step-limit of ." step-limit" endof
    ." running" endcase ;
: print-result ( -- )
  ." STATUS " .machine-status cr
  ." PC " ip @ .int cr
  ." STEPS " steps @ .int cr
  ." CODE " trap-code @ .int cr
  ." OUTPUT" out-count @ 0 ?do space i cells outbuf + @ .int loop cr
  ." MEM" mem-size @ 0 ?do space i mem @ .int loop cr ;

: main ( -- )
  next-arg dup 0= abort" usage: gforth forth/main.fs INPUT-FILE"
  load-input reset run print-result ;

main bye
