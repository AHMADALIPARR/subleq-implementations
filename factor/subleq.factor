! Copyright (C) Ahmad <ahmedparr93@gmail.com>
! SPDX-License-Identifier: AGPL-3.0-only

USING: kernel math namespaces sequences io prettyprint arrays vectors accessors locals ;
IN: subleq

TUPLE: subleq-state
    { memory vector }
    { pc integer }
    { input vector }
    { output vector }
    { halted boolean }
    { fault } ;

: <subleq-state> ( memory pc input output halted fault -- state )
    subleq-state boa ;

:: subleq-init ( program input -- state )
    program >vector
    0
    input >vector
    V{ } clone
    f
    f
    <subleq-state> ;

:: subleq-step ( state -- state' )
    state halted>> [
        state
    ] [
        state fault>> [
            state clone t >>halted
        ] [
            state pc>> 0 < [
                state clone t >>halted
            ] [
                state memory>> length :> mem-len
                state pc>> :> pc
                pc 3 + mem-len > [
                    state clone
                    t >>halted
                    "invalid-fetch" >>fault
                ] [
                    pc state memory>> nth :> a
                    pc 1 + state memory>> nth :> b
                    pc 2 + state memory>> nth :> c

                    ! Halt sentinel: a < 0 and b < 0
                    a 0 < b 0 < and [
                        state clone t >>halted
                    ] [
                        ! Flash-Attention Trap: a = -2
                        a -2 = [
                            c 0 < [
                                state clone t >>halted "flash-attention-trap" >>fault
                            ] [
                                state clone c >>pc "flash-attention-trap" >>fault
                            ] if
                        ] [
                            ! Input extension: a = -1, b >= 0
                            a -1 = [
                                b 0 < b mem-len >= or [
                                    state clone t >>halted "invalid-write" >>fault
                                ] [
                                    state input>> empty? [
                                        state clone t >>halted "input-exhausted" >>fault
                                    ] [
                                        state input>> first :> in-val
                                        state input>> rest-slice >vector :> new-input
                                        state memory>> clone :> new-mem
                                        in-val b new-mem set-nth
                                        in-val 0 <= [ c ] [ pc 3 + ] if :> next-pc
                                        state clone
                                        new-mem >>memory
                                        next-pc >>pc
                                        new-input >>input
                                        next-pc 0 < >>halted
                                    ] if
                                ] if
                            ] [
                                ! Output extension: b = -1, a >= 0
                                b -1 = [
                                    a 0 < a mem-len >= or [
                                        state clone t >>halted "invalid-read" >>fault
                                    ] [
                                        a state memory>> nth :> out-val
                                        state output>> clone :> new-output
                                        out-val new-output push
                                        pc 3 + :> next-pc
                                        state clone
                                        next-pc >>pc
                                        new-output >>output
                                        next-pc 0 < >>halted
                                    ] if
                                ] [
                                    ! Standard arithmetic: a >= 0, b >= 0
                                    a 0 < a mem-len >= or [
                                        state clone t >>halted "invalid-read" >>fault
                                    ] [
                                        b 0 < b mem-len >= or [
                                            state clone t >>halted "invalid-write" >>fault
                                        ] [
                                            a state memory>> nth :> val-a
                                            b state memory>> nth :> val-b
                                            val-b val-a - :> res
                                            state memory>> clone :> new-mem
                                            res b new-mem set-nth
                                            res 0 <= [ c ] [ pc 3 + ] if :> next-pc
                                            state clone
                                            new-mem >>memory
                                            next-pc >>pc
                                            next-pc 0 < >>halted
                                        ] if
                                    ] if
                                ] if
                            ] if
                        ] if
                    ] if
                ] if
            ] if
        ] if
    ] if ;

:: subleq-run ( state fuel -- result )
    state :> s!
    fuel :> f!
    [ f 0 > s halted>> not and ] [
        s subleq-step s!
        f 1 - f!
    ] while
    s ;

:: subleq-trace ( state fuel -- trace )
    V{ } clone :> acc
    state :> s!
    fuel :> f!
    s acc push
    [ f 0 > s halted>> not and ] [
        s subleq-step s!
        s acc push
        f 1 - f!
    ] while
    acc >array ;

:: subleq-observe ( state -- observation )
    {
        state memory>> >array
        state pc>>
        state output>> >array
        state halted>>
        state fault>>
    } ;
! SPDX-License-Identifier: AGPL-3.0-or-later
USING: arrays combinators io kernel math namespaces prettyprint
sequences vectors ;
IN: subleq

! SUBLEQ machine state: a sequence of integers acting as memory and code.
! Word takes memory and instruction pointer (ip), executes one cycle,
! and returns updated memory and new ip (or f if halted).
! Semantics: semantics/subleq-spec.md (32-bit wrap, absolute c, halt on
! c = -1, a = -2 trap > a = -1 input > b < 0 output > ordinary,
! out-of-range reads 0 / writes discarded, PC out of range = fault).

! Machine status and I/O live in dynamic variables.
SYMBOLS: memory status trap-code steps inputs outputs current-c last-pc fuel ;

: wrap32 ( n -- n' )
    0xFFFFFFFF bitand dup 0x80000000 bitand zero? [ 0x100000000 - ] unless ;

! Out-of-range reads give 0, out-of-range writes are discarded.
: rd ( a -- v ) memory get 2dup bounds-check? [ nth ] [ 2drop 0 ] if ;
: wr ( v a -- ) memory get 2dup bounds-check? [ set-nth ] [ 3drop ] if ;

: pc-ok? ( ip -- ? ) dup 0 >= swap 2 + memory get length < and ;

: count-step ( -- ) steps [ 1 + ] change ;

: trap ( ip a b c -- ip ) drop trap-code set drop "trap" status set count-step ;

: input ( ip a b c -- ip' )
    drop nip inputs get empty?
    [ drop "fault:input-exhausted" status set ]
    [ inputs get unclip swap inputs set wrap32 swap wr 3 + count-step ] if ;

: output ( ip a b c -- ip' ) 2drop rd outputs get push 3 + count-step ;

: subleq-step ( mem ip -- mem' ip' )
    swap memory set
    dup pc-ok? [
        ! Extract a, b, c from current ip
        dup memory get [ nth ] [ [ 1 + ] dip nth ] [ [ 2 + ] dip nth ] 2tri
        dup current-c set
        {
            { [ pick -2 = ] [ trap ] }
            { [ pick -1 = ] [ input ] }
            { [ over 0 < ] [ output ] }
            [
                ! Ordinary SUBLEQ: ( ip a b c -- ip' )
                [
                    ! Fetch values from memory (out-of-range reads give 0)
                    [ rd ] dip [ rd ] keep
                    ! result = val_b - val_a, wrapped to 32 bits
                    [ swap - wrap32 ] dip

                    ! Store result in mem[b]
                    over swap wr
                ] dip

                ! Check branch condition (wrapped result <= 0)
                swap 0 <= [
                    ! branch to c (absolute)
                    nip
                ] [
                    ! advance ip by 3
                    drop 3 +
                ] if count-step
            ]
        } cond
        ! Halt rule: after a completed non-trap step, c = -1 halts.
        status get "running" = current-c get -1 = and
        [ "halted" status set ] when
    ] [ "fault:pc-out-of-range" status set ] if
    status get "running" = [ last-pc set f ] unless
    memory get swap ;

! run-subleq ( mem inputs fuel -- ) runs until halt, trap, fault or the
! step limit; the result is left in the dynamic variables above.
: run-subleq ( mem inputs fuel -- )
    fuel set >array inputs set
    [ wrap32 ] map >array
    "running" status set 0 trap-code set 0 steps set
    V{ } clone outputs set f last-pc set
    0
    [
        dup [
            steps get fuel get < dup
            [ over last-pc set "step-limit" status set ] unless
        ] [ f ] if
    ] [ subleq-step ] while
    drop memory set ;
