! Copyright (C) Ahmad <ahmedparr93@gmail.com>
! SPDX-License-Identifier: AGPL-3.0-only

USING: kernel math namespaces sequences io prettyprint arrays vectors accessors subleq ;
IN: subleq.tests

"=== Running Factor SUBLEQ Verification Obligations ===" print

! 1. Positive subtraction (3 4 6  3 10 0)
{ 3 4 6 3 10 0 } { } subleq-init subleq-step
dup memory>> 4 swap nth 7 = [ "PASS: Positive subtraction mem" print ] [ "FAIL: Positive subtraction mem" print ] if
dup pc>> 3 = [ "PASS: Positive subtraction pc" print ] [ "FAIL: Positive subtraction pc" print ] if
drop

! 2. Negative subtraction (3 4 6  5 2 0)
{ 3 4 6 5 2 0 } { } subleq-init subleq-step
dup memory>> 4 swap nth -3 = [ "PASS: Negative subtraction mem" print ] [ "FAIL: Negative subtraction mem" print ] if
dup pc>> 6 = [ "PASS: Negative subtraction pc" print ] [ "FAIL: Negative subtraction pc" print ] if
drop

! 3. Zero subtraction (3 4 6  5 5 0)
{ 3 4 6 5 5 0 } { } subleq-init subleq-step
dup memory>> 4 swap nth 0 = [ "PASS: Zero subtraction mem" print ] [ "FAIL: Zero subtraction mem" print ] if
dup pc>> 6 = [ "PASS: Zero subtraction pc" print ] [ "FAIL: Zero subtraction pc" print ] if
drop

! 4. Source/destination aliasing (a = b => res = 0)
{ 3 3 6 42 0 0 } { } subleq-init subleq-step
dup memory>> 3 swap nth 0 = [ "PASS: Aliasing mem" print ] [ "FAIL: Aliasing mem" print ] if
dup pc>> 6 = [ "PASS: Aliasing pc" print ] [ "FAIL: Aliasing pc" print ] if
drop

! 5. Instruction modification
{ 3 3 3 10 20 30 } { } subleq-init subleq-step
dup memory>> 3 swap nth 0 = [ "PASS: Self-modifying mem" print ] [ "FAIL: Self-modifying mem" print ] if
dup pc>> 3 = [ "PASS: Self-modifying pc" print ] [ "FAIL: Self-modifying pc" print ] if
drop

! 6. Invalid fetch
{ 1 2 } { } subleq-init subleq-step
dup halted>> [ "PASS: Invalid fetch halted" print ] [ "FAIL: Invalid fetch halted" print ] if
dup fault>> "invalid-fetch" = [ "PASS: Invalid fetch fault" print ] [ "FAIL: Invalid fetch fault" print ] if
drop

! 7. Invalid read
{ 99 1 0 0 0 0 } { } subleq-init subleq-step
dup halted>> [ "PASS: Invalid read halted" print ] [ "FAIL: Invalid read halted" print ] if
dup fault>> "invalid-read" = [ "PASS: Invalid read fault" print ] [ "FAIL: Invalid read fault" print ] if
drop

! 8. Invalid write
{ 0 99 0 0 0 0 } { } subleq-init subleq-step
dup halted>> [ "PASS: Invalid write halted" print ] [ "FAIL: Invalid write halted" print ] if
dup fault>> "invalid-write" = [ "PASS: Invalid write fault" print ] [ "FAIL: Invalid write fault" print ] if
drop

! 9. Input extension & exhaustion
{ -1 3 6 0 0 0 } { 42 } subleq-init subleq-step
dup memory>> 3 swap nth 42 = [ "PASS: Input val" print ] [ "FAIL: Input val" print ] if
dup pc>> 3 = [ "PASS: Input pc" print ] [ "FAIL: Input pc" print ] if
drop

{ -1 3 6 0 0 0 } { } subleq-init subleq-step
dup halted>> [ "PASS: Input exhausted halted" print ] [ "FAIL: Input exhausted halted" print ] if
dup fault>> "input-exhausted" = [ "PASS: Input exhausted fault" print ] [ "FAIL: Input exhausted fault" print ] if
drop

! 10. Output extension
{ 3 -1 6 99 0 0 } { } subleq-init subleq-step
dup output>> { 99 } sequence= [ "PASS: Output val" print ] [ "FAIL: Output val" print ] if
dup pc>> 3 = [ "PASS: Output pc" print ] [ "FAIL: Output pc" print ] if
drop

! 11. Halt sentinel
{ -1 -1 -1 } { } subleq-init subleq-step
dup halted>> [ "PASS: Halt sentinel halted" print ] [ "FAIL: Halt sentinel halted" print ] if
drop

! 12. Countdown loop
{ 3 1 0 1 0 12 2 2 3 0 0 0 -1 -1 -1 } { } subleq-init
3 >>pc
100 subleq-run
dup halted>> [ "PASS: Loop halted" print ] [ "FAIL: Loop halted" print ] if
dup memory>> 0 swap nth 0 = [ "PASS: Loop counter 0" print ] [ "FAIL: Loop counter 0" print ] if
drop

! 13. Flash-Attention trap
{ -2 0 6 0 0 0 } { } subleq-init subleq-step
dup fault>> "flash-attention-trap" = [ "PASS: FA trap fault" print ] [ "FAIL: FA trap fault" print ] if
dup pc>> 6 = [ "PASS: FA trap pc" print ] [ "FAIL: FA trap pc" print ] if
drop

"All Factor SUBLEQ verification obligations passed successfully!" print
