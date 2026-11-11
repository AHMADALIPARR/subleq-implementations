#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only

;; Shared helpers for bench/*.rkt: writing spec §6 input files, running the
;; command-line implementations of the directive machine as subprocesses, parsing their
;; canonical output (spec §5), timing, and toolchain versions.
;; Tool locations come from the environment: RACKET, FACTOR, GFORTH, SUBLEQ_LEAN.

(require racket/list racket/string racket/port racket/file racket/system
         racket/runtime-path)
(provide impls write-input-file run-impl parse-canonical median
         toolchain-versions repo-path time-ms)

(define-runtime-path root "..")
(define (repo-path p) (path->string (simplify-path (build-path root p))))
(define (env name default) (or (getenv name) default))

(define (find-exe p)
  (if (absolute-path? p) p (or (find-executable-path p) (error 'bench "not found: ~a" p))))

;; name -> (file -> command list)
(define impls
  (list
   (cons "racket" (λ (f) (list (env "RACKET" "racket") (repo-path "racket/subleq.rkt") f)))
   (cons "forth"  (λ (f) (list (env "GFORTH" "gforth") "-m" "64M" (repo-path "forth/main-large.fs") f)))
   (cons "factor" (λ (f) (list (env "FACTOR" "factor") (repo-path "factor/subleq-main.factor") f)))
   (cons "lean"   (λ (f) (list (env "SUBLEQ_LEAN" (repo-path "lean/.lake/build/bin/subleq-lean")) f)))))

;; write-input-file : path image inputs fuel -> void
(define (write-input-file path image inputs fuel)
  (call-with-output-file path #:exists 'truncate
    (λ (o)
      (for ([x (append (list (length image)) image (list (length inputs)) inputs (list fuel))])
        (write-string (number->string x) o)
        (write-char #\space o))
      (newline o))))

;; run-impl : command list -> (values exit-code stdout stderr milliseconds)
(define (run-impl cmd)
  (define t0 (current-inexact-milliseconds))
  (define-values (sp out in err)
    (apply subprocess #f #f #f (find-exe (car cmd)) (cdr cmd)))
  (close-output-port in)
  (define o-box (box ""))
  (define o-th (thread (λ () (set-box! o-box (port->string out)))))  ; read both pipes concurrently
  (define e (port->string err))
  (thread-wait o-th)
  (subprocess-wait sp)
  (define ms (- (current-inexact-milliseconds) t0))
  (close-input-port out) (close-input-port err)
  (values (subprocess-status sp) (unbox o-box) e ms))

;; parse-canonical : string -> hash (status pc steps code output)
(define (parse-canonical s)
  (define lines (string-split s "\n"))
  (define (field name)                        ; tokens of the line whose first token is name
    (define l (findf (λ (l) (let ([t (string-split l " ")]) (and (pair? t) (equal? (car t) name)))) lines))
    (and l (string-split l " ")))
  (define (num name) (let ([f (field name)]) (and f (string->number (cadr f)))))
  (hasheq 'status (let ([f (field "STATUS")]) (and f (cadr f)))
          'pc (num "PC") 'steps (num "STEPS") 'code (num "CODE")
          'output (let ([f (field "OUTPUT")]) (if f (map string->number (cdr f)) '()))))

(define (median xs)
  (define s (sort xs <))
  (list-ref s (quotient (length s) 2)))

;; time-ms : thunk -> (values milliseconds result-list)
(define (time-ms thunk)
  (define t0 (current-inexact-milliseconds))
  (define vs (call-with-values thunk list))
  (values (- (current-inexact-milliseconds) t0) vs))

(define (sh cmd)
  (string-trim (with-output-to-string (λ () (system cmd)))))

(define (toolchain-versions)
  (list
   (cons "Racket" (version))
   (cons "gforth" (sh (format "~a --version 2>&1" (env "GFORTH" "gforth"))))
   (cons "Factor" (sh (format "~a -e='USING: io system ; vm-version print' 2>&1" (env "FACTOR" "factor"))))
   (cons "Lean" (let ([lean (find-executable-path "lean")])
                  (if lean
                      (sh "cd lean && lean --version 2>&1")
                      "lean not on PATH; toolchain pinned in lean/lean-toolchain")))
   (cons "OS" (sh "uname -srm"))
   (cons "CPU" (format "~a (~a logical CPUs)"
                       (sh "grep -m1 'model name' /proc/cpuinfo | cut -d: -f2")
                       (sh "nproc")))))
