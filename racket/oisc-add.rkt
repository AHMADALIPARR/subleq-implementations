#lang rosette

;; Deliberately limited SUBLEQ machine for a first verification experiment.
;; Semantics (written down before implementation):
;;   result = data[b] - data[a]   (modulo 2^32)
;;   data[b] = result
;;   if signed(result) <= 0:
;;     micro_pc = target
;;   else:
;;     micro_pc = micro_pc + 1

(define W 32)
(define ZERO (bv 0 W))

;; Data-register layout for the ADD example:
;; 0 = source A, 1 = source B, 2 = temporary, 3 = output

(struct insn (a b target) #:transparent)
(struct machine (regs pc) #:transparent)

(define (reg-write regs index value)
  (for/list ([old regs] [i (in-naturals)])
    (if (= i index) value old)))

(define (step program state)
  (define regs (machine-regs state))
  (define pc (machine-pc state))
  (define instruction (list-ref program pc))

  (define a (insn-a instruction))
  (define b (insn-b instruction))

  (define result
    (bvsub (list-ref regs b)
           (list-ref regs a)))

  (machine
   (reg-write regs b result)
   (if (bvsle result ZERO)
       (insn-target instruction)
       (add1 pc))))

;; Four SUBLEQ instructions compute output = A + B.
;; Each branch target equals the next instruction,
;; so this first example has no data-dependent control flow.
(define add-program
  (list
   (insn 2 2 1)   ; temporary = 0
   (insn 0 2 2)   ; temporary = -A
   (insn 1 2 3)   ; temporary = -A - B
   (insn 2 3 4))) ; output = 0 - temporary

(define-symbolic a b (bitvector 32))
(define-symbolic scratch (bitvector 32))

(define initial
  (machine (list a b scratch ZERO) 0))

(define final
  (for/fold ([state initial])
            ([i (in-range 4)])
    (step add-program state)))

(define result
  (verify
   (begin
     (assert (= (machine-pc final) 4))
     (assert
      (equal? (list-ref (machine-regs final) 3)
              (bvadd a b)))
     (assert
      (equal? (list-ref (machine-regs final) 0) a))
     (assert
      (equal? (list-ref (machine-regs final) 1) b)))))

(cond
  [(unsat? result)
   (displayln "PASS: ADD result, exit PC, and source preservation")]
  [(sat? result)
   (displayln "FAIL: counterexample")
   (displayln
    (evaluate (list a b scratch) result))]
  [else
   (displayln "UNKNOWN: no proof or counterexample")])
