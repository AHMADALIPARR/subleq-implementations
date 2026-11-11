USING: kernel math namespaces sequences io prettyprint ;
IN: subleq

! SUBLEQ machine state: a sequence of integers acting as memory and code.
! Word takes memory and instruction pointer (ip), executes one cycle, 
! and returns updated memory and new ip (or f if halted).

: subleq-step ( mem ip -- mem' ip' )
    over over 3 head* 
    ! Extract a, b, c from current ip
    [ first ] [ 1 swap nth ] [ 2 swap nth ] tri*
    
    ! Fetch values from memory (treating negative addresses as 0)
    over 0 < [ 0 ] [ over swap nth ] if
    >r
    over 0 < [ 0 ] [ over swap nth ] if
    r> swap - 
    ! result = val_b - val_a
    
    ! Store result in mem[b]
    2 pick over 2 pick set-nth
    
    ! Check branch condition (result <= 0)
    dup 0 <= [
        ! branch to c
        nip 2 pick swap
    ] [
        ! advance ip by 3
        drop 2 drop 3 +
    ] if ;
