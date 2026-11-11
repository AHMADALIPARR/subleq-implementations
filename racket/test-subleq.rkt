#lang racket
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only

(require rackunit
         "subleq.rkt")

(printf "=== Running Racket SUBLEQ Verification Obligations ===\n")

;; 1. Positive subtraction (res > 0, untaken branch -> pc + 3)
(let* ([s (machine-init '(3 4 6  3 10 0))]
       [s1 (machine-step s)])
  (check-equal? (vector-ref (machine-state-memory s1) 4) 7)
  (check-equal? (machine-state-pc s1) 3)
  (check-false (machine-state-halted s1)))

;; 2. Negative subtraction (res < 0, taken branch -> c)
(let* ([s (machine-init '(3 4 6  5 2 0))]
       [s1 (machine-step s)])
  (check-equal? (vector-ref (machine-state-memory s1) 4) -3)
  (check-equal? (machine-state-pc s1) 6))

;; 3. Zero subtraction (res = 0, taken branch -> c)
(let* ([s (machine-init '(3 4 6  5 5 0))]
       [s1 (machine-step s)])
  (check-equal? (vector-ref (machine-state-memory s1) 4) 0)
  (check-equal? (machine-state-pc s1) 6))

;; 4. Untaken branch
(let* ([s (machine-init '(3 4 6  2 5 0))]
       [s1 (machine-step s)])
  (check-equal? (machine-state-pc s1) 3))

;; 5. Source / Destination Aliasing (a = b => res = 0, mem[b] = 0)
(let* ([s (machine-init '(3 3 6  42 0 0))]
       [s1 (machine-step s)])
  (check-equal? (vector-ref (machine-state-memory s1) 3) 0)
  (check-equal? (machine-state-pc s1) 6))

;; 6. Instruction modification (self-modifying code)
(let* ([prog '(3 3 3  10 20 30)]
       [s (machine-init prog)]
       [s1 (machine-step s)])
  (check-equal? (vector-ref (machine-state-memory s1) 3) 0)
  (check-equal? (machine-state-pc s1) 3))

;; 7. Invalid fetch (pc out of bounds)
(let* ([s (machine-init '(1 2))]
       [s1 (machine-step s)])
  (check-true (machine-state-halted s1))
  (check-equal? (machine-state-fault s1) 'invalid-fetch))

;; 8. Invalid read (a out of bounds)
(let* ([s (machine-init '(99 1 0  0 0 0))]
       [s1 (machine-step s)])
  (check-true (machine-state-halted s1))
  (check-equal? (machine-state-fault s1) 'invalid-read))

;; 9. Invalid write (b out of bounds)
(let* ([s (machine-init '(0 99 0  0 0 0))]
       [s1 (machine-step s)])
  (check-true (machine-state-halted s1))
  (check-equal? (machine-state-fault s1) 'invalid-write))

;; 10. Input emission and exhaustion
(let* ([s (machine-init '(-1 3 6  0 0 0) '(42))]
       [s1 (machine-step s)])
  (check-equal? (vector-ref (machine-state-memory s1) 3) 42)
  (check-equal? (machine-state-pc s1) 3)
  (check-equal? (machine-state-input s1) '()))

(let* ([s (machine-init '(-1 3 6  0 0 0) '())]
       [s1 (machine-step s)])
  (check-true (machine-state-halted s1))
  (check-equal? (machine-state-fault s1) 'input-exhausted))

;; 11. Output emission
(let* ([s (machine-init '(3 -1 6  99 0 0))]
       [s1 (machine-step s)])
  (check-equal? (machine-state-output s1) '(99))
  (check-equal? (machine-state-pc s1) 3))

;; 12. Halting with sentinel (-1 -1 -1)
(let* ([s (machine-init '(-1 -1 -1))]
       [s1 (machine-step s)])
  (check-true (machine-state-halted s1)))

;; 13. Countdown Loop
(let* ([loop-prog '(3 1 0  1 0 12  2 2 3  0 0 0  -1 -1 -1)]
       [s (struct-copy machine-state (machine-init loop-prog) [pc 3])]
       [final (machine-run s 100)])
  (check-true (machine-state-halted final))
  (check-equal? (vector-ref (machine-state-memory final) 0) 0))

;; 14. Fuel exhaustion
(let* ([prog '(0 0 0)]
       [s (machine-init prog)]
       [final (machine-run s 10)])
  (check-false (machine-state-halted final))
  (check-equal? (machine-state-pc final) 0))

;; 15. Flash-Attention trap (a = -2)
(let* ([s (machine-init '(-2 0 6  0 0 0))]
       [s1 (machine-step s)])
  (check-equal? (machine-state-fault s1) 'flash-attention-trap)
  (check-equal? (machine-state-pc s1) 6))

(printf "All Racket SUBLEQ verification obligations passed successfully!\n")
