#lang rosette
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only

;; Fail-closed harness for the milestone 1 sequences.
;;
;; Exit status:
;;   0  every symbolic, concrete, and differential check passed
;;   1  at least one counterexample or concrete failure
;;   2  harness error (bad arguments, unknown mutation, solver missing,
;;      symbolic PC, malformed sequence, solver unknown/timeout)
;;
;; Symbolic checks call Rosette `verify`. `unsat` is pass, `sat` prints the
;; model and is a failure, `unknown` is a harness error.
;;
;; Mutations (sequence or spec deliberately wrong):
;;   racket racket/microcode/verify.rkt --mutation <id>
;;     exits 1 when the fault is observed
;;   racket racket/microcode/verify.rkt --mutation-self-test
;;     runs every mutation in a child process and exits 0 only if each child
;;     exits 1

(require racket/list
         racket/runtime-path
         racket/string
         rosette/solver/smt/z3
         "../subleq.rkt"
         "model.rkt"
         "sequences.rkt"
         "specs.rkt")

(output-smt #f)
(current-bitwidth 32)

(define-runtime-path harness-path "verify.rkt")

(define mutation-ids
  '(zero-wrong-target
    add-subtract
    move-skip-clear
    load-wrong-source
    store-clobber
    zero-spec-identity))

(define checks 0)
(define failures 0)
(define harness-errors 0)

(define (note-pass!) (set! checks (add1 checks)))
(define (note-fail!)
  (set! checks (add1 checks))
  (set! failures (add1 failures)))
(define (note-harness!)
  (set! checks (add1 checks))
  (set! harness-errors (add1 harness-errors)))

(define (replace-cells image pairs)
  (define v (list->vector image))
  (for ([p (in-list pairs)])
    (vector-set! v (car p) (cdr p)))
  (vector->list v))

;; Image faults. Spec fault is handled in postcondition, not here.
(define (mutated-image seq mutation)
  (define image (mc-seq-image seq))
  (cond
    [(not mutation) image]
    [(and (eq? mutation 'zero-wrong-target) (eq? (mc-seq-name seq) 'zero))
     ;; Zero FRAME instead of X.
     (replace-cells image '((0 . 4) (1 . 4)))]
    [(and (eq? mutation 'add-subtract) (eq? (mc-seq-name seq) 'add))
     ;; B ← B − A instead of B ← B − (−A).
     (replace-cells image '((6 . 13)))]
    [(and (eq? mutation 'move-skip-clear) (eq? (mc-seq-name seq) 'move))
     ;; Clear Z again instead of clearing B, so B ← B + A.
     (replace-cells image '((3 . 15) (4 . 15)))]
    [(and (eq? mutation 'load-wrong-source) (eq? (mc-seq-name seq) 'load))
     ;; RD ← MEM2 instead of RD ← SRC.
     (replace-cells image '((6 . 19)))]
    [(and (eq? mutation 'store-clobber) (eq? (mc-seq-name seq) 'store))
     ;; Halting instruction writes OTHER ← OTHER − RS and leaves Z = −RS.
     (replace-cells image '((12 . 16) (13 . 18)))]
    [else image]))

(define (active-spec-mutation seq mutation)
  (if (and (eq? mutation 'zero-spec-identity) (eq? (mc-seq-name seq) 'zero))
      'zero-spec-identity
      #f))

(define (validate-sequences!)
  (for ([seq (in-list all-sequences)])
    (define image (mc-seq-image seq))
    (define n (length image))
    (define idxs (map cadr (mc-seq-operands seq)))
    (unless (and (exact-nonnegative-integer? (mc-seq-entry-pc seq))
                 (exact-positive-integer? (mc-seq-fuel seq))
                 (boolean? (mc-seq-self-modifying? seq))
                 (andmap exact-integer? image)
                 (= (length idxs) (length (remove-duplicates idxs)))
                 (andmap (λ (i) (and (exact-nonnegative-integer? i) (< i n))) idxs)
                 (< (+ (mc-seq-entry-pc seq) 2) n))
      (error 'verify "malformed sequence ~a" (mc-seq-name seq)))))

(define (machine-from-image image assignment seq)
  (define mem
    (for/list ([word (in-list image)] [i (in-naturals)])
      (define op (findf (λ (p) (= (cadr p) i)) (mc-seq-operands seq)))
      (int->bv (if op (hash-ref assignment (car op)) word))))
  (define st (make-machine mem))
  (if (zero? (mc-seq-entry-pc seq))
      st
      (struct-copy machine st [pc (int->bv (mc-seq-entry-pc seq))])))

(define (fresh-assignment seq)
  (for/list ([op (in-list (mc-seq-operands seq))])
    (define-symbolic* cell (bitvector W))
    (list (car op) (cadr op) cell)))

(define (symbolic-machine seq syms mutation)
  (define image (mutated-image seq mutation))
  (define mem
    (for/list ([word (in-list image)] [i (in-naturals)])
      (define hit (findf (λ (s) (= (second s) i)) syms))
      (if hit (third hit) (int->bv word))))
  (define st (make-machine mem))
  (if (zero? (mc-seq-entry-pc seq))
      st
      (struct-copy machine st [pc (int->bv (mc-seq-entry-pc seq))])))

(define (install-solver!)
  (define smt (z3 #:options (hash ':timeout 60000)))
  (current-solver smt)
  smt)

(define (print-counterexample seq syms initial final cex)
  (define full (complete-solution cex (map third syms)))
  (printf "  counterexample model: ~a\n" full)
  (for ([s (in-list syms)])
    (printf "  ~a (cell ~a) = ~a\n"
            (first s) (second s)
            (bv->signed (evaluate (third s) full))))
  (printf "  initial ~a\n" (machine-summary (evaluate initial full)))
  (printf "  final   ~a\n" (machine-summary (evaluate final full))))

(define (check-symbolic seq mutation)
  (printf "~a symbolic  entry-pc ~a  fuel ~a  self-modifying ~a\n"
          (mc-seq-name seq)
          (mc-seq-entry-pc seq)
          (mc-seq-fuel seq)
          (if (mc-seq-self-modifying? seq) "yes" "no"))
  (printf "~a\n" (mc-seq-doc seq))
  (define syms (fresh-assignment seq))
  (define initial (symbolic-machine seq syms mutation))
  (define final (run (mc-seq-fuel seq) initial))
  (define formula
    (postcondition seq initial final (active-spec-mutation seq mutation)))
  (define-values (results ms real-ms cpu)
    (time-apply (λ () (verify (assert formula))) '()))
  (define cex (first results))
  (cond
    [(unsat? cex)
     (note-pass!)
     (printf "  symbolic unsat PASS (~a ms)\n" real-ms)]
    [(sat? cex)
     (note-fail!)
     (printf "  symbolic sat FAIL (~a ms)\n" real-ms)
     (print-counterexample seq syms initial final cex)]
    [else
     (note-harness!)
     (printf "  symbolic UNKNOWN FAIL-CLOSED (~a ms): ~a\n" real-ms cex)]))

(define concrete-value-sets
  (list
   '(0 0 0 0 0)
   '(1 1 1 1 1)
   '(-1 -1 -1 -1 -1)
   '(2147483647 -2147483648 1 42 -7)
   '(-2147483648 2147483647 -2147483648 0 123456)
   '(42 -7 0 1 -2147483648)
   '(5 9 -42 2147483647 -1)))

(define (assignment-for seq nums)
  (for/hash ([op (in-list (mc-seq-operands seq))]
             [n (in-list nums)])
    (values (car op) n)))

(define (holds-concretely? formula)
  (cond
    [(eq? formula #t) #t]
    [(eq? formula #f) #f]
    [(concrete? formula) (eq? formula #t)]
    [else (unsat? (verify (assert formula)))]))

(define (check-concrete-one seq mutation nums)
  (define asg (assignment-for seq nums))
  (define image (mutated-image seq mutation))
  (define initial (machine-from-image image asg seq))
  (define final (run (mc-seq-fuel seq) initial))
  (define formula
    (postcondition seq initial final (active-spec-mutation seq mutation)))
  (define ok? (holds-concretely? formula))
  (if ok?
      (note-pass!)
      (begin
        (note-fail!)
        (printf "  concrete FAIL ~a inputs ~a\n" (mc-seq-name seq) asg)
        (printf "  final ~a\n" (machine-summary final)))))

(define (check-concrete seq mutation)
  (for ([nums (in-list concrete-value-sets)])
    (check-concrete-one seq mutation (take nums (length (mc-seq-operands seq)))))
  (printf "  concrete ~a cases done\n" (length concrete-value-sets)))

(define (parts-machine st)
  (list (machine-status st)
        (bitvector->integer (machine-pc st))
        (machine-steps st)
        (bv->signed (machine-code st))
        (map bv->signed (machine-out st))
        (map bv->signed (machine-mem st))))

(define (parts-result r)
  (list (result-status r)
        (result-pc r)
        (result-steps r)
        (result-code r)
        (result-output r)
        (result-mem r)))

(define (check-differential image inputs fuel label)
  (define r (run-subleq image inputs fuel))
  (define st (run fuel (make-machine (map int->bv image) (map int->bv inputs))))
  (define got (parts-machine st))
  (define exp (parts-result r))
  (if (equal? got exp)
      (note-pass!)
      (begin
        (note-fail!)
        (printf "  differential FAIL ~a\n  model ~a\n  racket ~a\n" label got exp))))

(define edge-programs
  ;; label, image, inputs, fuel
  (list
   (list 'branch-taken '(3 3 -1 7) '() 2)
   (list 'branch-not-taken '(4 3 -1 5 1) '() 2)
   (list 'wrap '(4 3 -1 -2147483648 1) '() 2)
   (list 'trap-beats-halt '(-2 -5 -1) '() 1)
   (list 'input-then-output '(-1 9 3 9 -1 -1 0 0 0 0) '(77) 5)
   (list 'input-beats-output '(-1 -5 -1) '(1) 1)
   (list 'input-exhausted '(-1 0 -1) '() 5)
   (list 'input-wrap '(-1 3 -1 0) '(2147483648) 1)
   (list 'oob-read-write '(100 200 -1) '() 2)
   (list 'output-b-lt-minus-one '(5 -4 -1 0 0 42) '() 1)
   (list 'short-image '(0 0) '() 1)
   (list 'empty-image '() '() 1)
   (list 'step-limit '(0 0 0) '() 4)
   (list 'self-modify-c '(2 2 5 9 8 7) '() 2)))

(define (check-edges)
  (printf "differential vs racket/subleq.rkt\n")
  (for ([e (in-list edge-programs)])
    (check-differential (second e) (third e) (fourth e) (first e)))
  (printf "  edge programs ~a done\n" (length edge-programs)))

(define (check-wrap-agreement)
  (define samples
    '(0 1 -1 5 42 -42
      2147483647 -2147483648 2147483648 -2147483649
      4294967295 -4294967296 4294967296 -4294967297))
  (for ([n (in-list samples)])
    (if (= (bv->signed (int->bv n)) (wrap32 n))
        (note-pass!)
        (begin
          (note-fail!)
          (printf "  wrap32 FAIL n=~a model=~a racket=~a\n"
                  n (bv->signed (int->bv n)) (wrap32 n)))))
  (printf "  wrap32 samples ~a done\n" (length samples)))

(define (check-sequence-differential seq mutation)
  (for ([values (in-list concrete-value-sets)])
    (define asg (assignment-for seq (take values (length (mc-seq-operands seq)))))
    (define image
      (for/list ([word (in-list (mutated-image seq mutation))] [i (in-naturals)])
        (define op (findf (λ (p) (= (cadr p) i)) (mc-seq-operands seq)))
        (if op (hash-ref asg (car op)) word)))
    (check-differential image '() (mc-seq-fuel seq)
                        (format "~a ~a" (mc-seq-name seq) asg))))

(define (usage!)
  (eprintf "usage: racket racket/microcode/verify.rkt [--mutation <id> | --mutation-self-test]\n")
  (eprintf "mutations: ~a\n" (string-join (map symbol->string mutation-ids) " "))
  (exit 2))

(define (parse-args)
  (define args (vector->list (current-command-line-arguments)))
  (cond
    [(null? args) (cons 'run #f)]
    [(equal? args '("--mutation-self-test")) (cons 'self-test #f)]
    [(and (= (length args) 2) (equal? (first args) "--mutation"))
     (define id (string->symbol (second args)))
     (unless (memq id mutation-ids)
       (eprintf "harness error: unknown mutation ~a\n" (second args))
       (usage!))
     (cons 'mutation id)]
    [else (usage!)]))

(define (finish!)
  (printf "~a checks, ~a failed, ~a harness errors\n"
          checks failures harness-errors)
  (cond
    [(positive? harness-errors) (exit 2)]
    [(positive? failures) (exit 1)]
    [(zero? checks)
     (eprintf "harness error: no checks ran\n")
     (exit 2)]
    [else
     (printf "all checks passed\n")
     (exit 0)]))

(define (run-suite mutation)
  (install-solver!)
  (validate-sequences!)
  (printf "directive-machine microcode verification (milestone 1)\n")
  (printf "width: 32-bit two's-complement bitvectors (Lean wrap32)\n")
  (when mutation (printf "MUTATION active: ~a\n" mutation))
  (check-wrap-agreement)
  (check-edges)
  (for ([seq (in-list all-sequences)])
    (check-symbolic seq mutation)
    (check-concrete seq mutation)
    (check-sequence-differential seq mutation))
  (finish!))

(define (racket-executable)
  (or (find-executable-path (find-system-path 'exec-file))
      (find-executable-path "racket")
      (error 'verify "cannot find the racket executable on PATH")))

;; A fault is caught only when the child exits 1 and its report contains a
;; counterexample or a concrete failure. An exec failure is also exit 1 and
;; must not count.
(define (mutation-caught? code stdout stderr)
  (and (eqv? code 1)
       (or (string-contains? stdout "symbolic sat FAIL")
           (string-contains? stdout "concrete FAIL"))
       (not (string-contains? stderr "exec failed"))
       (not (string-contains? stdout "harness error:"))))

(define (run-self-test)
  (define exe (path->string (racket-executable)))
  (define script (path->string harness-path))
  (define missed 0)
  (printf "mutation self-test (~a faults) via ~a\n" (length mutation-ids) exe)
  (for ([id (in-list mutation-ids)])
    (define-values (sp out in err)
      (subprocess #f #f #f exe script "--mutation" (symbol->string id)))
    (close-output-port in)
    (define stdout (port->string out))
    (define stderr (port->string err))
    (close-input-port out)
    (close-input-port err)
    (subprocess-wait sp)
    (define code (subprocess-status sp))
    (define caught? (mutation-caught? code stdout stderr))
    (printf "----- mutation ~a exit ~a caught ~a -----\n"
            id code (if caught? "yes" "no"))
    (display stdout)
    (unless (string=? stderr "")
      (printf "----- stderr -----\n")
      (display stderr))
    (unless caught?
      (set! missed (add1 missed))
      (printf "mutation ~a was NOT caught (exit ~a)\n" id code)))
  (if (zero? missed)
      (begin
        (printf "mutation self-test: all ~a faults caught (each exited 1 with a counterexample)\n"
                (length mutation-ids))
        (exit 0))
      (begin
        (printf "mutation self-test: ~a of ~a faults were not caught\n"
                missed (length mutation-ids))
        (exit 1))))

(define (main)
  (define parsed (parse-args))
  (with-handlers ([exn:fail? (λ (e)
                               (eprintf "harness error: ~a\n" (exn-message e))
                               (exit 2))])
    (if (eq? (car parsed) 'self-test)
        (run-self-test)
        (run-suite (cdr parsed)))))

(main)
