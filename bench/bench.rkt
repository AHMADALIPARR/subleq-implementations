#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only

;; Benchmarks: the directive machine (semantics/subleq-spec.md) against the original
;; SUBLEQ (racket/subleq-original.rkt).
;;
;;  A. SHA-256 instruction counts for messages of 1, 2, 3 and 4 blocks and
;;     the per-block (marginal) cost on both machines.
;;  B. Keystream (killer app) instruction counts per word on both machines.
;;  C. Wall-clock time per implementation (secondary data).
;;
;; Instruction counts are exact counts of executed instructions:
;; STEPS from racket/subleq.rkt (the directive machine; forth/factor/lean print the
;; same STEPS, checked by bench/sha256-vectors.rkt and bench/killer-app.rkt)
;; and the count from execute-subleq/steps (original machine).
;; Every digest / output is checked against a plain-Racket reference,
;; including in the wall-clock runs (in process and on every command line).
;;
;; Usage: racket bench/bench.rkt [--only racket,forth,factor,lean] [--repeat R]

(require racket/list racket/string racket/file racket/port racket/system file/sha1
         "common.rkt" "../programs/sha256.rkt" "../programs/keystream.rkt"
         (except-in "../racket/subleq.rkt" wrap32) "../racket/subleq-original.rkt")

(define only #f)
(define repeat 3)
(let loop ([args (vector->list (current-command-line-arguments))])
  (cond
    [(null? args) (void)]
    [(and (equal? (car args) "--only") (pair? (cdr args)))
     (set! only (string-split (cadr args) ",")) (loop (cddr args))]
    [(and (equal? (car args) "--repeat") (pair? (cdr args)))
     (set! repeat (string->number (cadr args))) (loop (cddr args))]
    [else (eprintf "unknown argument ~a\n" (car args)) (exit 2)]))
(define active (if only (filter (λ (p) (member (car p) only)) impls) impls))

(define SEED 20261110)
(define fuel 1000000000)
(define failures 0)
(define (check! ok what) (unless ok (set! failures (add1 failures)) (printf "FAIL: ~a\n" what)))
(define (pct a b) (real->decimal-string (* 100.0 (/ (- a b) b)) 2))
(define (ratio a b) (real->decimal-string (/ a b) 3))

(printf "# Benchmark run\n\n")
(printf "Date: ~a\n\n" (string-trim (with-output-to-string (λ () (system "date '+%Y-%m-%d %H:%M %Z'")))))
(printf "| Tool | Version |\n|---|---|\n")
(for ([v (toolchain-versions)]) (printf "| ~a | ~a |\n" (car v) (cdr v)))
(printf "\nSeed for random data: ~a. Wall-clock figures are medians of ~a runs.\n\n" SEED repeat)

;; ---------------------------------------------------------------------------
;; A. SHA-256
(random-seed SEED)
(define-values (sha-img _s) (sha256-image #:target 'directive))
(printf "## A. SHA-256 instruction counts\n\n")
(printf "Directive image: ~a cells for every message. Messages: the three NIST vectors and seeded random messages of 55, 119, 183, 247 bytes (the longest messages that fit in 1, 2, 3, 4 blocks).\n\n" (length sha-img))
(printf "| Message | Bytes | Blocks | Directive machine STEPS | Original STEPS | Original - directive | Difference | I/O part of the difference (exact) | Image cells: directive / original |\n|---|---|---|---|---|---|---|---|---|\n")
(define nist (list (cons "NIST \"\"" #"") (cons "NIST \"abc\"" #"abc")
                   (cons "NIST 448-bit" #"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")))
(define randoms (for/list ([len '(55 119 183 247)])
                  (cons (format "random ~a" len) (apply bytes (for/list ([_ len]) (random 256))))))
(define sha-rows
  (for/list ([m (append nist randoms)])
    (define msg (cdr m))
    (define expected (bytes->hex-string (sha256-bytes msg)))
    (define r (run-subleq sha-img (sha256-input msg) fuel))
    (check! (equal? (digest-words->hex (result-output r)) expected) (format "sha directive ~a" (car m)))
    (define-values (oimg osyms) (sha256-image #:target 'original #:message msg))
    (define-values (mem n) (execute-subleq/steps oimg))
    (check! (equal? (digest-words->hex (for/list ([j 8]) (vector-ref mem (+ (hash-ref osyms 'H) j)))) expected)
            (format "sha original ~a" (car m)))
    (define blocks (+ 1 (quotient (+ (bytes-length msg) 8) 64)))
    ;; I/O emulation, exact: the original reads each message byte with
    ;; LOAD-NEXT (9 instructions) where the directive program uses IN (1); it also executes
    ;; IN for the length and 8 OUT for the digest, which the original does not.
    (define io (- (* 8 (bytes-length msg)) 9))
    (printf "| ~a | ~a | ~a | ~a | ~a | ~a | +~a% | ~a | ~a / ~a |\n" (car m) (bytes-length msg) blocks
            (result-steps r) n (- n (result-steps r)) (pct n (result-steps r)) io (length sha-img) (length oimg))
    (list (car m) blocks (result-steps r) n)))
(define (steps-of name) (findf (λ (r) (equal? (car r) name)) sha-rows))
(define r1 (steps-of "random 55")) (define r4 (steps-of "random 247"))
(define dir-block (/ (- (caddr r4) (caddr r1)) 3))
(define orig-block (/ (- (cadddr r4) (cadddr r1)) 3))
(printf "\nThe I/O part is 8 per message byte (LOAD-NEXT is 9 instructions, IN is 1) minus the 9 I/O instructions only the directive program executes (IN for the length, 8 OUT for the digest). The rest of the difference is the wrap emulation (MOD32, original only) and the different bit-31 handling inside UNPACK32.\n")
(printf "\nMarginal cost per 64-byte block, (STEPS(247 bytes) - STEPS(55 bytes)) / 3: the directive machine ~a, original ~a; the original needs ~a times as many (+~a%).\n"
        (real->decimal-string dir-block 1) (real->decimal-string orig-block 1)
        (ratio orig-block dir-block) (pct orig-block dir-block))
(printf "Per-block costs vary slightly with the data because some macros (UNPACK32, ACC+PARITY, ACC+CH) take data-dependent paths.\n\n")

;; ---------------------------------------------------------------------------
;; B. keystream
(printf "## B. Keystream (killer app) instruction counts\n\n")
(define-values (ks-img _k) (keystream-image #:target 'directive))
(define (ks-words n) (for/list ([_ n]) (random 4294967087)))
(printf "| N words | Directive machine STEPS | Original STEPS | Original / directive | Image cells: directive / original |\n|---|---|---|---|---|\n")
(define ks-rows
  (for/list ([n '(0 1000 10000)])
    (define ws (ks-words n))
    (define expected (keystream-reference 1 12345 ws))
    (define r (run-subleq ks-img (keystream-input 1 12345 ws) fuel))
    (check! (equal? (map (λ (v) (modulo v (expt 2 32))) (result-output r)) expected) (format "ks dir ~a" n))
    (define-values (oimg syms) (keystream-image #:target 'original #:mode 1 #:seed 12345 #:words ws))
    (define-values (mem k) (execute-subleq/steps oimg))
    (check! (equal? (for/list ([i n]) (vector-ref mem (+ (hash-ref syms 'RESULT) i))) expected) (format "ks orig ~a" n))
    (printf "| ~a | ~a | ~a | ~a | ~a / ~a |\n" n (result-steps r) k (ratio k (result-steps r)) (length ks-img) (length oimg))
    (list n (result-steps r) k ws)))
(define ks1 (cadr ks-rows)) (define ks2 (caddr ks-rows))
(printf "\nMarginal cost per word, (STEPS(10000) - STEPS(1000)) / 9000: the directive machine ~a, original ~a, ratio ~a.\n\n"
        (real->decimal-string (/ (- (cadr ks2) (cadr ks1)) 9000) 3)
        (real->decimal-string (/ (- (caddr ks2) (caddr ks1)) 9000) 3)
        (ratio (- (caddr ks2) (caddr ks1)) (- (cadr ks2) (cadr ks1))))

;; ---------------------------------------------------------------------------
;; C. wall clock
(printf "## C. Wall-clock time (secondary data)\n\n")
(printf "Command-line implementations run as separate processes on one input file. \"Total\" is the whole process; \"load only\" is the same file with FUEL = 0 (parse, load, print, no instructions executed); \"execution\" is total minus load only. In-process rows time only the interpreter call, after the image is built. Times in milliseconds.\n\n")
(printf "| Program | Machine / implementation | STEPS | Total | Load only | Execution | Instructions per second (execution) |\n|---|---|---|---|---|---|---|\n")
(define tmp (make-temporary-file "subleq-bench-~a.txt"))
;; dir-ok? : directive output words -> boolean; orig-ok? : original memory -> boolean
(define (bench-program name image inputs orig-image dir-ok? orig-ok?)
  ;; the directive machine, in process
  (define runs (for/list ([_ repeat]) (let-values ([(ms vs) (time-ms (λ () (run-subleq image inputs fuel)))]) (cons ms (car vs)))))
  (define steps (result-steps (cdar runs)))
  (for ([r runs])
    (check! (and (eq? (result-status (cdr r)) 'halted) (dir-ok? (result-output (cdr r))))
            (format "~a in-process result" name)))
  (define t (median (map car runs)))
  (printf "| ~a | directive / racket in process (run-subleq) | ~a | ~a | - | ~a | ~a |\n" name steps
          (real->decimal-string t 1) (real->decimal-string t 1) (ips steps t))
  (write-input-file tmp image inputs fuel)
  (define tmp0 (make-temporary-file "subleq-bench0-~a.txt"))
  (write-input-file tmp0 image inputs 0)
  (for ([p active])
    (define (timed f)
      (median (for/list ([_ repeat])
                (define-values (code out err ms) (run-impl ((cdr p) (path->string f))))
                (check! (eqv? code 0) (format "~a ~a exit ~a ~a" name (car p) code err))
                (define c (parse-canonical out))
                (if (eq? f tmp)
                    (check! (and (equal? (hash-ref c 'status) "halted") (eqv? (hash-ref c 'steps) steps)
                                 (dir-ok? (hash-ref c 'output)))
                            (format "~a ~a result" name (car p)))
                    (check! (eqv? (hash-ref c 'steps) 0) (format "~a ~a FUEL=0 run" name (car p))))
                ms)))
    (define total (timed tmp))
    (define load (timed tmp0))
    (printf "| ~a | directive / ~a | ~a | ~a | ~a | ~a | ~a |\n" name (car p) steps
            (real->decimal-string total 1) (real->decimal-string load 1)
            (real->decimal-string (- total load) 1) (ips steps (- total load))))
  (delete-file tmp0)
  ;; original, in process
  (define oruns (for/list ([_ repeat]) (let-values ([(ms vs) (time-ms (λ () (execute-subleq/steps orig-image)))])
                                          (check! (orig-ok? (car vs)) (format "~a original result" name))
                                          (cons ms (cadr vs)))))
  (define ot (median (map car oruns)))
  (printf "| ~a | original / racket in process (execute-subleq/steps) | ~a | ~a | - | ~a | ~a |\n" name (cdar oruns)
          (real->decimal-string ot 1) (real->decimal-string ot 1) (ips (cdar oruns) ot)))
(define (ips steps ms) (if (> ms 0) (format "~a" (inexact->exact (round (/ steps (/ ms 1000.0))))) "-"))

;; A long message, so that execution is not lost in the time to load the
;; 434,000-cell image: 4087 bytes = 64 blocks.
(let* ([msg (apply bytes (for/list ([_ 4087]) (random 256)))]
       [expected (bytes->hex-string (sha256-bytes msg))])
  (define-values (oimg osyms) (sha256-image #:target 'original #:message msg))
  (bench-program "SHA-256, 4087-byte message (64 blocks)" sha-img (sha256-input msg) oimg
                 (λ (out) (equal? (digest-words->hex out) expected))
                 (λ (mem) (equal? (digest-words->hex (for/list ([j 8]) (vector-ref mem (+ (hash-ref osyms 'H) j))))
                                  expected))))
(let* ([ws (cadddr ks2)] [n (length ws)] [expected (keystream-reference 1 12345 ws)])
  (define-values (oimg syms) (keystream-image #:target 'original #:mode 1 #:seed 12345 #:words ws))
  (bench-program "Keystream, 10000 words" ks-img (keystream-input 1 12345 ws) oimg
                 (λ (out) (equal? (map (λ (v) (modulo v (expt 2 32))) out) expected))
                 (λ (mem) (equal? (for/list ([i n]) (vector-ref mem (+ (hash-ref syms 'RESULT) i))) expected))))
(delete-file tmp)
(printf "\nbench: failures=~a\n" failures)
(exit (if (zero? failures) 0 1))
