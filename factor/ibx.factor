! IBX-1: integer-only Gaussian butterfly network, Factor language.
! Launch with the Factor LANGUAGE executable, not GNU coreutils /usr/bin/factor.
USING: arrays io kernel locals math math.functions prettyprint sequences ;
IN: ibx.factor

! Interleaved butterfly indices are a and b; component arrays are separate.
! Four integer additions/subtractions; no multiplication or floating point in kernel.
:: butterfly! ( re im a b -- )
    a re nth :> xr
    a im nth :> xi
    b re nth :> yr
    b im nth :> yi
    xr yi - a re set-nth
    xi yr + a im set-nth
    xr yi + b re set-nth
    xi yr - b im set-nth ;

! One radix-2 butterfly stage: blocks of length 2*d.
:: stage! ( re im d -- )
    re length d 2 * /i [| block |
        d [| j |
            block d 2 * * j + :> a
            a d + :> b
            re im a b butterfly!
        ] each-integer
    ] each-integer ;

! Recursive stage scheduler. d = 1, 2, 4, ..., N/2.
:: stages! ( re im d -- )
    d re length < [
        re im d stage!
        re im d 2 * stages!
    ] when ; recursive

: transform! ( re im -- ) 1 stages! ;

:: reset-input! ( re im -- )
    re length [| j |
        j 17 mod 8 - j re set-nth
        0 j im set-nth
    ] each-integer ;

:: make-input ( n -- re im )
    n 0 <array> :> re
    n 0 <array> :> im
    re im reset-input!
    re im ;

:: energy ( re im -- n )
    0 :> total!
    re length [| j |
        j re nth sq j im nth sq + total + total!
    ] each-integer
    total ;

:: require= ( actual expected -- )
    actual expected = [ ] [ "IBX-1 assertion failed" throw ] if ;

:: verify-small ( -- )
    { 1 2 3 4 } clone :> re
    4 0 <array> :> im
    re im transform!
    re { -3 5 5 -3 } require=
    im { 5 1 -1 -5 } require= ;

:: verify-1024 ( -- )
    1024 make-input :> ( re im )
    re im energy :> before
    re im transform!
    re im energy before 1024 * require= ;

! Report nanoseconds for the full timed loop, including reset costs.
! Do NOT compare this number directly with a native-C inner-kernel number.
:: bench ( reps -- )
    1024 make-input :> ( re im )
    nano-count :> t0
    reps [
        re im reset-input!
        re im transform!
    ] times
    nano-count t0 - :> elapsed
    "IBX-1 / Factor" print
    "N=1024 stages=10 butterflies/transform=5120" print
    "repetitions=" write reps .
    "total_butterflies=" write reps 5120 * .
    "elapsed_ns_including_reset=" write elapsed .
    "ns_per_butterfly_including_reset=" write
    elapsed reps 5120 * /f .
    "output_energy=" write re im energy . ;

: main ( -- )
    verify-small
    verify-1024
    "PASS: small vector and N=1024 energy invariant" print
    200 bench ;

main
