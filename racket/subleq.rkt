#lang racket

;; SUBLEQ Interpreter (One-Instruction Set Computer)
;; Instruction layout: [A, B, C]
;; Operation: mem[B] = mem[B] - mem[A], then if mem[B] <= 0 jump to C (else PC + 3)

(define (execute-subleq memory-list)
  (let* ([mem (list->vector memory-list)]
         [len (vector-length mem)])
    (letrec ([step
              (lambda (pc)
                (cond
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
                               (step c)
                               (step (+ pc 3))))))]))])
      (step 0)
      mem)))

;; Example test: Subtract 1 from cell 0 until <= 0, then jump
;; Program: [0, 1, 0,  1, 1, 0] -> mem[1] = mem[1] - mem[0]
(define sample-prog '(1 0 3  1 0 3  -1 -1 -1))
;; (execute-subleq sample-prog)
