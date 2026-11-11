#lang rosette
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only

;; Post-conditions for the milestone 1 sequences.
;; Each predicate is the data post-condition conjoined with the frame
;; (every cell that is not an declared output or the scratch cell) and the
;; halting observation: status halted, PC = −1, STEPS = fuel, no output,
;; CODE = 0.
;;
;; `mutation` is #f or 'zero-spec-identity. The identity mutation replaces
;; only the Zero post-condition (the cell must stay unchanged), so a correct
;; Zero sequence fails the mutated spec.

(require "model.rkt" "sequences.rkt")

(provide postcondition
         preserved-indices)

(define (cell st i)
  (list-ref (machine-mem st) i))

(define (preserved-indices seq)
  (define n (image-length seq))
  (define written
    (case (mc-seq-name seq)
      [(zero) (list (operand-index seq 'X))]
      [(move) (list (operand-index seq 'Z) (operand-index seq 'B))]
      [(add) (list (operand-index seq 'Z) (operand-index seq 'B))]
      [(load) (list (operand-index seq 'Z) (operand-index seq 'RD))]
      [(store) (list (operand-index seq 'Z) (operand-index seq 'DST))]
      [else (error 'preserved-indices "unknown sequence ~a" (mc-seq-name seq))]))
  (filter (λ (i) (not (member i written))) (range n)))

(define (same-cells? initial final indices)
  (for/fold ([acc #t]) ([i (in-list indices)])
    (&& acc (bveq (cell initial i) (cell final i)))))

(define (halted-cleanly? final steps)
  (&& (eq? (machine-status final) 'halted)
      (= (machine-steps final) steps)
      (null? (machine-out final))
      (bveq (machine-code final) (bv 0 W))
      (bveq (machine-pc final) (bv -1 W))))

(define (data-post seq initial final mutation)
  (define (ix name) (operand-index seq name))
  (case (mc-seq-name seq)
    [(zero)
     (if (eq? mutation 'zero-spec-identity)
         (bveq (cell final (ix 'X)) (cell initial (ix 'X)))
         (bveq (cell final (ix 'X)) (bv 0 W)))]
    [(move)
     (&& (bveq (cell final (ix 'B)) (cell initial (ix 'A)))
         (bveq (cell final (ix 'Z)) (bv 0 W)))]
    [(add)
     (&& (bveq (cell final (ix 'B))
               (bvadd (cell initial (ix 'A)) (cell initial (ix 'B))))
         (bveq (cell final (ix 'Z)) (bv 0 W)))]
    [(load)
     (&& (bveq (cell final (ix 'RD)) (cell initial (ix 'SRC)))
         (bveq (cell final (ix 'Z)) (bv 0 W)))]
    [(store)
     (&& (bveq (cell final (ix 'DST)) (cell initial (ix 'RS)))
         (bveq (cell final (ix 'Z)) (bv 0 W)))]
    [else (error 'data-post "unknown sequence ~a" (mc-seq-name seq))]))

(define (postcondition seq initial final mutation)
  (&& (data-post seq initial final mutation)
      (same-cells? initial final (preserved-indices seq))
      (halted-cleanly? final (mc-seq-fuel seq))))
