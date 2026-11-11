! SPDX-License-Identifier: AGPL-3.0-or-later
! Command-line driver for factor/subleq.factor.
! Usage: factor factor/subleq-main.factor INPUT-FILE
! INPUT-FILE format and printed result: semantics/subleq-spec.md sections 5-6.
USING: command-line namespaces io.pathnames parser kernel ;
<< script get parent-directory "subleq.factor" append-path run-file >>
USING: subleq io io.files io.encodings.utf8 sequences splitting math
math.parser kernel namespaces command-line ;
IN: subleq.main

: parse-ints ( str -- seq )
    " \t\r\n" split harvest [ string>number ] map
    dup [ integer? ] all? [ "subleq: non-integer token" throw ] unless ;

: .ints ( label seq -- )
    [ number>string ] map swap prefix " " join print ;

: parse-input ( seq -- mem inputs fuel )
    unclip cut                     ! mem rest
    unclip cut                     ! mem inputs rest'
    dup length 1 = [ "subleq: expected exactly one FUEL value" throw ] unless
    first ;

command-line get first utf8 file-contents parse-ints
parse-input run-subleq
"STATUS " status get append print
"PC " last-pc get number>string append print
"STEPS " steps get number>string append print
"CODE " trap-code get number>string append print
"OUTPUT" outputs get .ints
"MEM" memory get .ints
