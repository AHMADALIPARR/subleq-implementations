#lang rosette

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
    (if (unsat? m)
        (printf "PASS ~as\n" (/ real-milli 1000.0))
        (begin
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

(provide rv-verify
         val-tmp0 val-rvpc val-src1 val-tmp1 val-src2 val-tmp2
         val-tmp3 val-tmp4 val-immi val-tmp5 val-one val-word
         val-inc val-step val-tmp6 val-tmp7
         test-mem)
