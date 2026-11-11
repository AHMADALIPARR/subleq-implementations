#lang racket
;; SPDX-License-Identifier: AGPL-3.0-or-later

;; ORIGINAL SUBLEQ baseline (kept for benchmarking).
;; This is the repository's original interpreter, moved here from
;; racket/subleq.rkt. Its semantics are unchanged: unbounded integers,
;; no I/O, halt when pc < 0, when pc + 2 >= length, or when a < 0 and b < 0.
;; It does NOT follow semantics/subleq-spec.md; racket/subleq.rkt does.
;;
;; Changes compared with the original file (documented, behaviour-preserving):
;;  * `provide` added so the baseline can be called from benchmarks/tests.
;;  * optional #:fuel keyword (default #f = unlimited, the original
;;    behaviour). With a number, execution stops after that many steps.
;;  * the commented-out `sample-prog` is kept as a definition and exported.

(provide execute-subleq sample-prog)

;; SUBLEQ Interpreter (One-Instruction Set Computer)
;; Instruction layout: [A, B, C]
;; Operation: mem[B] = mem[B] - mem[A], then if mem[B] <= 0 jump to C (else PC + 3)

(define (execute-subleq memory-list #:fuel [fuel #f])
  (let* ([mem (list->vector memory-list)]
         [len (vector-length mem)])
    (letrec ([step
              (lambda (pc n)
                (cond
                  [(and fuel (>= n fuel)) mem]
                  [(< pc 0) mem]
                  [(>= (+ pc 2) len) mem]
                  [else
                   (let* ([a (vector-ref mem pc)]
                          [b (vector-ref mem (+ pc 1))]
                          [c (vector-ref mem (+ pc 2))])
                     ;; Halt if A and B are negative, or standard sentinel
                     (if (and (< a 0) (< b 0))
                         mem
                         (let* ([val-a (if (< a 0) 0 (vector-ref mem a))]
                                [val-b (if (< b 0) 0 (vector-ref mem b))]
                                [res (- val-b val-a)])
                           (when (>= b 0)
                             (vector-set! mem b res))
                           (if (<= res 0)
                               (step c (+ n 1))
                               (step (+ pc 3) (+ n 1))))))]))])
      (step 0 0)
      mem)))

;; Example test: Subtract 1 from cell 0 until <= 0, then jump
;; Program: [0, 1, 0,  1, 1, 0] -> mem[1] = mem[1] - mem[0]
(define sample-prog '(1 0 3  1 0 3  -1 -1 -1))
;; (execute-subleq sample-prog)

(module+ test
  (require rackunit)
  ;; Baseline behaviour checks (original semantics).
  ;; a < 0 and b < 0 halts immediately; pc + 2 >= length halts.
  (check-equal? (vector->list (execute-subleq '(-1 -1 -1))) '(-1 -1 -1))
  (check-equal? (vector->list (execute-subleq '(3 4 -1 5 7))) '(3 4 -1 5 2))
  ;; sample-prog: two steps leave mem[0] = 1 - 0 = 1, then the -1 -1 sentinel halts.
  (check-equal? (vector->list (execute-subleq sample-prog)) sample-prog)
  ;; #:fuel stops a non-terminating program: 0 0 0 loops on itself.
  (check-equal? (vector->list (execute-subleq (list 0 0 0) #:fuel 5)) (list 0 0 0)))
