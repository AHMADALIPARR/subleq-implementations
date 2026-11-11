#lang racket
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only

;; SUBLEQ Execution Engine (Canonical Operational Semantics)
;; State: S = (M, PC, I, O, H, E)
;; Supports:
;;   - Standard SUBLEQ (mem[b] = mem[b] - mem[a]; branch if <= 0)
;;   - Input stream (a = -1, b >= 0)
;;   - Output stream (b = -1, a >= 0)
;;   - Flash-Attention extension trap (a = -2)
;;   - Halting conditions (PC < 0 or negative sentinel)
;;   - Fault reporting for out-of-bounds memory accesses

(provide (struct-out machine-state)
         machine-init
         machine-step
         machine-run
         machine-trace
         machine-observe
         execute-subleq)

(struct machine-state
  (memory   ;; vector of exact integers
   pc       ;; exact integer (instruction pointer)
   input    ;; list of exact integers
   output   ;; list of exact integers (in emission order)
   halted   ;; boolean
   fault    ;; symbol or #f ('invalid-fetch, 'invalid-read, 'invalid-write, 'input-exhausted, 'flash-attention-trap, etc.)
   )
  #:transparent)

;; (machine-init program [input '()])
(define (machine-init program [input '()])
  (define mem-vec
    (cond
      [(vector? program) (vector-copy program)]
      [(list? program) (list->vector program)]
      [else (error 'machine-init "Expected vector or list for program")]))
  (machine-state mem-vec 0 input '() #f #f))

;; (machine-step state) -> state'
(define (machine-step state)
  (match-define (machine-state mem pc input output halted fault) state)
  (cond
    ;; Already terminated or faulted
    [halted state]
    [fault (struct-copy machine-state state [halted #t])]
    ;; Check halt condition on negative PC
    [(< pc 0)
     (struct-copy machine-state state [halted #t])]
    ;; Check instruction fetch bounds
    [(> (+ pc 3) (vector-length mem))
     (struct-copy machine-state state [halted #t] [fault 'invalid-fetch])]
    [else
     (define a (vector-ref mem pc))
     (define b (vector-ref mem (+ pc 1)))
     (define c (vector-ref mem (+ pc 2)))
     (cond
       ;; Halt Sentinel (-1 -1 -1 or both a < 0 and b < 0, preserving existing code)
       [(and (< a 0) (< b 0))
        (struct-copy machine-state state [halted #t])]

       ;; Flash-Attention Trap (a = -2)
       [(= a -2)
        (struct-copy machine-state state
                     [pc (if (< c 0) pc c)]
                     [halted (< c 0)]
                     [fault 'flash-attention-trap])]

       ;; Input Extension (a = -1, b >= 0)
       [(= a -1)
        (cond
          [(< b 0)
           (struct-copy machine-state state [halted #t] [fault 'invalid-write])]
          [(>= b (vector-length mem))
           (struct-copy machine-state state [halted #t] [fault 'invalid-write])]
          [(null? input)
           (struct-copy machine-state state [halted #t] [fault 'input-exhausted])]
          [else
           (define in-val (car input))
           (define new-mem (vector-copy mem))
           (vector-set! new-mem b in-val)
           (define next-pc (if (<= in-val 0) c (+ pc 3)))
           (struct-copy machine-state state
                        [memory new-mem]
                        [pc next-pc]
                        [input (cdr input)]
                        [halted (< next-pc 0)])])]

       ;; Output Extension (b = -1, a >= 0)
       [(= b -1)
        (cond
          [(or (< a 0) (>= a (vector-length mem)))
           (struct-copy machine-state state [halted #t] [fault 'invalid-read])]
          [else
           (define out-val (vector-ref mem a))
           (define next-pc (+ pc 3))
           (struct-copy machine-state state
                        [pc next-pc]
                        [output (append output (list out-val))]
                        [halted (< next-pc 0)])])]

       ;; Standard SUBLEQ arithmetic: a >= 0, b >= 0
       [else
        (cond
          [(or (< a 0) (>= a (vector-length mem)))
           (struct-copy machine-state state [halted #t] [fault 'invalid-read])]
          [(or (< b 0) (>= b (vector-length mem)))
           (struct-copy machine-state state [halted #t] [fault 'invalid-write])]
          [else
           (define val-a (vector-ref mem a))
           (define val-b (vector-ref mem b))
           (define res (- val-b val-a))
           (define new-mem (vector-copy mem))
           (vector-set! new-mem b res)
           (define next-pc (if (<= res 0) c (+ pc 3)))
           (struct-copy machine-state state
                        [memory new-mem]
                        [pc next-pc]
                        [halted (< next-pc 0)])])])]))

;; (machine-run state fuel) -> final-state
(define (machine-run state fuel)
  (let loop ([s state] [f fuel])
    (cond
      [(or (<= f 0) (machine-state-halted s)) s]
      [else (loop (machine-step s) (- f 1))])))

;; (machine-trace state fuel) -> list of state snapshots
(define (machine-trace state fuel)
  (let loop ([s state] [f fuel] [acc (list state)])
    (cond
      [(or (<= f 0) (machine-state-halted s)) (reverse acc)]
      [else
       (define s-next (machine-step s))
       (loop s-next (- f 1) (cons s-next acc))])))

;; (machine-observe state) -> hash of observations
(define (machine-observe state)
  (hash 'memory (vector->list (machine-state-memory state))
        'pc (machine-state-pc state)
        'output (machine-state-output state)
        'halted (machine-state-halted state)
        'fault (machine-state-fault state)))

;; Backwards-compatible execute-subleq
(define (execute-subleq memory-list)
  (define init-s (machine-init memory-list))
  (define final-s (machine-run init-s 100000))
  (machine-state-memory final-s))
