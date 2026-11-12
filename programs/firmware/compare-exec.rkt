#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only
;;
;; Execute the original firmware image and the reconstructed image
;; independently, then compare observable behavior.

(require racket/list racket/format
         "subleq-firmware.rkt"
         "../../racket/subleq.rkt")

(define (code-triples image code-end)
  (for/list ([pc (in-range 0 code-end 3)])
    (list (list-ref image pc)
          (list-ref image (+ pc 1))
          (list-ref image (+ pc 2)))))

(define (flatten-triples triples)
  (apply append triples))

(define (run-and-observe image label)
  (define r (run-subleq image '() 10000))
  (define mem (result-mem r))
  (define status (result-status r))
  (define steps (result-steps r))
  (define output (result-output r))
  (define code (result-code r))
  (printf "~a:\n" label)
  (printf "  status=~a steps=~a output=~a code=~a\n" status steps output code)
  (values r mem status steps output code))

(define (main)
  (define-values (image syms code-end) (assemble-firmware))
  (define n (length image))
  (printf "Original image: ~a words, code-end=~a\n" n code-end)

  ;; Reconstruct: code triples + original data section
  (define triples (code-triples image code-end))
  (define rebuilt-code (flatten-triples triples))
  (define data (drop image code-end))
  (define rebuilt (append rebuilt-code data))
  (printf "Reconstructed image: ~a words (bit-exact code: ~a)\n"
          (length rebuilt) (equal? rebuilt-code (take image code-end)))

  (newline)
  (define-values (r1 mem1 status1 steps1 out1 code1)
    (run-and-observe image "Original"))
  (define-values (r2 mem2 status2 steps2 out2 code2)
    (run-and-observe rebuilt "Reconstructed"))

  (newline)
  (printf "=== Comparison ===\n")
  (printf "status match: ~a\n" (eq? status1 status2))
  (printf "steps match: ~a (~a vs ~a)\n" (= steps1 steps2) steps1 steps2)
  (printf "output match: ~a\n" (equal? out1 out2))
  (printf "code/trap match: ~a\n" (equal? code1 code2))
  (printf "final memory match: ~a\n" (equal? mem1 mem2))

  ;; Named cells
  (define (cell name)
    (vector-ref (list->vector mem1) (hash-ref syms name)))
  (define (cell2 name)
    (vector-ref (list->vector mem2) (hash-ref syms name)))
  (printf "\nNamed cells (original vs reconstructed):\n")
  (for ([name '(CR0 CR4 MSR_EFER CURRENT_EXC FAULT_ADDR)])
    (define v1 (cell name))
    (define v2 (cell2 name))
    (printf "  ~a: ~a vs ~a ~a\n" name v1 v2 (if (= v1 v2) "OK" "DIFF")))

  (printf "\nAll observables match: ~a\n"
          (and (eq? status1 status2)
               (= steps1 steps2)
               (equal? out1 out2)
               (equal? code1 code2)
               (equal? mem1 mem2))))

(module+ main
  (main))
