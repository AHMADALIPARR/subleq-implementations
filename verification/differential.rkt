#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only

;; Differential runner (semantics/subleq-spec.md).
;; For every fixture in verification/fixtures/*.json and for a number of
;; seeded random programs, it writes the input file (spec §6), runs the
;; Racket, Factor, Forth and Lean command-line implementations as separate
;; processes, and compares their canonical output (spec §5):
;;   * fixtures: every implementation must print exactly the hand-written
;;     expected result;
;;   * random programs: every implementation must print the same result as
;;     the in-process Racket reference (racket/subleq.rkt).
;; Exit status is 0 only if every comparison matched and every process
;; exited with status 0.
;;
;; Usage: racket verification/differential.rkt [--random N] [--seed S] [--only IMPL,...]
;; Tool locations come from the environment: RACKET, FACTOR, GFORTH, SUBLEQ_LEAN.

(require racket/list racket/string racket/port racket/file racket/system
         racket/runtime-path json
         "../racket/subleq.rkt")

(define-runtime-path root "..")
(define (repo p) (path->string (simplify-path (build-path root p))))

(define (env name default) (or (getenv name) default))

(define impls
  (list
   (cons "racket" (λ (f) (list (env "RACKET" "racket") (repo "racket/subleq.rkt") f)))
   (cons "factor" (λ (f) (list (env "FACTOR" "factor") (repo "factor/subleq-main.factor") f)))
   (cons "forth"  (λ (f) (list (env "GFORTH" "gforth") (repo "forth/main.fs") f)))
   (cons "lean"   (λ (f) (list (env "SUBLEQ_LEAN" (repo "lean/.lake/build/bin/subleq-lean")) f)))))

(define random-count 200)
(define seed 20261110)
(define only #f)

(let loop ([args (vector->list (current-command-line-arguments))])
  (cond
    [(null? args) (void)]
    [(and (equal? (car args) "--random") (pair? (cdr args)))
     (set! random-count (string->number (cadr args))) (loop (cddr args))]
    [(and (equal? (car args) "--seed") (pair? (cdr args)))
     (set! seed (string->number (cadr args))) (loop (cddr args))]
    [(and (equal? (car args) "--only") (pair? (cdr args)))
     (set! only (string-split (cadr args) ",")) (loop (cddr args))]
    [else (eprintf "unknown argument: ~a\n" (car args)) (exit 2)]))

(define active
  (if only (filter (λ (p) (member (car p) only)) impls) impls))
(when (null? active) (eprintf "no implementations selected\n") (exit 2))

(define (input-text image inputs fuel)
  (string-join
   (map number->string (append (list (length image)) image
                               (list (length inputs)) inputs (list fuel)))
   " "))

;; run-impl : cmd-list -> (values exit-code stdout stderr)
(define (run-impl cmd)
  (define-values (sp out in err)
    (apply subprocess #f #f #f (find-exe (car cmd)) (cdr cmd)))
  (close-output-port in)
  (define o (port->string out))
  (define e (port->string err))
  (subprocess-wait sp)
  (close-input-port out) (close-input-port err)
  (values (subprocess-status sp) o e))

(define (find-exe p)
  (if (absolute-path? p) p (or (find-executable-path p) (error 'differential "not found: ~a" p))))

(define (expected->canonical h)
  (result->canonical
   (result (string->symbol (hash-ref h 'status)) (hash-ref h 'pc) (hash-ref h 'steps)
           (hash-ref h 'code) (hash-ref h 'output) (hash-ref h 'mem))))

(define tmp (make-temporary-file "subleq-diff-~a.txt"))
(define failures 0)
(define checks 0)

(define random-status (make-hash))

(define (check-case name image inputs fuel expected)
  (call-with-output-file tmp #:exists 'truncate
    (λ (o) (write-string (input-text image inputs fuel) o)))
  (for ([p active])
    (set! checks (add1 checks))
    (define-values (code out err) (run-impl ((cdr p) (path->string tmp))))
    (unless (and (eqv? code 0) (equal? out expected))
      (set! failures (add1 failures))
      (printf "MISMATCH ~a [~a] exit=~a\n--- expected\n~a--- got\n~a~a\n"
              name (car p) code expected out
              (if (string=? err "") "" (string-append "--- stderr\n" err))))))

;; 1. Fixtures
(define fixture-files
  (sort (map path->string
             (filter (λ (f) (regexp-match? #rx"[.]json$" (path->string f)))
                     (directory-list (build-path root "verification" "fixtures") #:build? #t)))
        string<?))
(define fixture-count 0)
(for ([f fixture-files])
  (define js (call-with-input-file f read-json))
  (for ([c (hash-ref js 'cases)])
    (set! fixture-count (add1 fixture-count))
    (check-case (hash-ref c 'name) (hash-ref c 'memory) (hash-ref c 'input)
                (hash-ref c 'fuel) (expected->canonical (hash-ref c 'expected)))
    ;; The in-process reference must agree with the hand-written expectation too.
    (define ref (result->canonical (run-subleq (hash-ref c 'memory) (hash-ref c 'input)
                                               (hash-ref c 'fuel))))
    (set! checks (add1 checks))
    (unless (equal? ref (expected->canonical (hash-ref c 'expected)))
      (set! failures (add1 failures))
      (printf "MISMATCH ~a [racket in-process]\n" (hash-ref c 'name)))))

;; 2. Seeded random programs
(random-seed seed)
(define specials '(-2147483648 -2147483647 -3 -2 -1 0 1 2 2147483646 2147483647))
(define (rand-cell n)
  (define k (random 100))
  (cond
    [(< k 55) (- (random (+ n 4)) 2)]            ; mostly addresses -2 .. n+1
    [(< k 70) -1]                                ; halt / input / output markers
    [(< k 75) -2]                                ; trap marker
    [(< k 90) (list-ref specials (random (length specials)))]
    [else (- (random 2000) 1000)]))
(for ([i random-count])
  (define n (+ 3 (random 40)))
  (define image (for/list ([_ n]) (rand-cell n)))
  (define inputs (for/list ([_ (random 6)]) (- (random 4000000) 2000000)))
  (define fuel (+ 1 (random 300)))
  (define ref (run-subleq image inputs fuel))
  (hash-update! random-status (result-status ref) add1 0)
  (check-case (format "random-~a" i) image inputs fuel (result->canonical ref)))

(delete-file tmp)
(printf "random program outcomes (reference): ~a\n"
        (sort (hash->list random-status) string<? #:key (λ (p) (symbol->string (car p)))))
(printf "differential: implementations=~a fixtures=~a random=~a seed=~a checks=~a failures=~a\n"
        (string-join (map car active) ",") fixture-count random-count seed checks failures)
(exit (if (zero? failures) 0 1))
