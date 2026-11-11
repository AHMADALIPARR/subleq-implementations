#lang rosette
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only AND MIT
;; SPDX-FileCopyrightText: 2022 Institute for Complex Systems (ICS), Johannes Kepler University Linz
;; Origin: adapted from verify.rkt from https://github.com/ics-jku/goldcrest-microcode-verification@55d3404
;; (MIT License, see LICENSES/MIT-goldcrest.txt).

(require "model.rkt")
(require "microcode.rkt")

;; Symbolic initial register state (matches memory layout in model.rkt)
(define-symbolic
  val-tmp0 val-rvpc val-src1 val-tmp1
  val-src2 val-tmp2 val-tmp3 val-tmp4
  val-immi val-tmp5 val-one val-word
  val-inc val-step val-tmp6 val-tmp7
  (bitvector XLEN))

(define test-mem
  (list val-tmp0 val-rvpc val-src1 val-tmp1
        val-src2 val-tmp2 val-tmp3 val-tmp4
        val-immi val-tmp5 val-one val-word
        val-inc val-step val-tmp6 val-tmp7))

;; Number of failed checks so far. A FAIL used to exit non-zero only with
;; --fail-fast, so `make verify` and CI passed even when every spec failed.
;; Now every FAIL is counted and rv-verify-finish exits 1 if any failed.
(define failure-count 0)
(define check-count 0)
(define (record-check!) (set! check-count (add1 check-count)))
(define (record-failure!) (set! failure-count (add1 failure-count)))

;; Core verification macro: runs microcode on symbolic state and checks spec
(define-syntax-rule (rv-verify #:name name #:init-pc pc #:fuel fuel
                               #:microcode microcode #:solver solver
                               #:spec spec #:assumptions assumptions)
  (begin
    (current-solver solver)
    (printf "~a with ~a (~a bits) for ~a steps " name (object-name solver) XLEN fuel)
    (flush-output)
    (when assumptions
      (assumptions test-mem))
    (define-values (results milli real-milli cpu-time)
      (time-apply
       (λ ()
         (verify
          (let ([res (execute fuel microcode test-mem pc)])
            (assert (spec res)))))
       '()))
    (define m (first results))
    (record-check!)
    (if (unsat? m)
        (printf "PASS ~as\n" (/ real-milli 1000.0))
        (begin
          (record-failure!)
          (printf "FAIL ~as\n" (/ real-milli 1000.0))
          (printf "Counterexample model: ~a\n" m)
          (define full-model (complete-solution m test-mem))
          (define full-mem (for/list ([c test-mem]) (full-model c)))
          (define concrete-res (execute fuel microcode full-mem pc))
          (printf "Execution of ~a with counterexample:\n" name)
          (for ([c test-mem] [v (list-ref concrete-res 0)])
            (printf "  ~a = ~a (~a)\n" c v (bitvector->natural v)))
          (printf "  result = ~a (~a)\n" (list-ref concrete-res 1)
                  (bitvector->natural (list-ref concrete-res 1)))
          (when (vector-member "--fail-fast" (current-command-line-arguments))
            (exit 1))))))

;; Print a summary and exit with status 1 if any check failed.
(define (rv-verify-finish)
  (printf "~a checks, ~a failed\n" check-count failure-count)
  (exit (if (zero? failure-count) 0 1)))

(provide rv-verify rv-verify-finish
         val-tmp0 val-rvpc val-src1 val-tmp1 val-src2 val-tmp2
         val-tmp3 val-tmp4 val-immi val-tmp5 val-one val-word
         val-inc val-step val-tmp6 val-tmp7
         test-mem)
