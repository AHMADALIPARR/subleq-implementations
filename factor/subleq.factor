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
