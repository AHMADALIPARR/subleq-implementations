\ SUBLEQ Virtual Machine in Forth
\ Instruction: subleq a, b, c  (mem[b] = mem[b] - mem[a], branch to c if <= 0)

variable ip  \ Instruction pointer
CREATE memory 1000 allot  \ 1000 cell memory space

: subleq ( a b c -- )
  \ Fetch values, subtract, store, and conditional branch
  >r 
  dup @ over @ over - ( a b val_b-val_a )
  rot ! ( store result in b )
  0 <= if r> ip ! else r> drop drop drop then ;

\ Note: This is a basic sketch; full interpreter would need a loop over instructions,
\ proper memory addressing, and halt conditions.
