#lang racket/base
;; SPDX-License-Identifier: AGPL-3.0-or-later

;; Killer-app evidence for programs/keystream.rkt (a toy keystream cipher).
;;
;;  1. Directive machine: one fixed image encrypts streams of N = 1000 and 10000
;;     words on all four implementations (racket, forth, factor, lean as
;;     separate processes). Outputs must equal the plain-Racket reference,
;;     and all four must print identical canonical results.
;;  2. Bad headers stop the directive machine with a trap (CODE 1 / CODE 2) on all four.
;;  3. The original machine:
;;     a. the directive image, unchanged, on racket/subleq-original.rkt;
;;     b. the port with wrap emulation and preloaded data (correct, measured);
;;     c. the port WITHOUT wrap emulation (MOD32 removed), to show what the
;;        unbounded integers do to the result and to the run time.
;;
;; Usage: racket bench/killer-app.rkt [--only racket,forth,factor,lean]
;; Exit status 0 only if every correctness check passed.

(require racket/list racket/string racket/file
         "common.rkt" "../programs/keystream.rkt" "../asm/sasm.rkt"
         (except-in "../racket/subleq.rkt" wrap32) "../racket/subleq-original.rkt")

(define only
  (let ([a (current-command-line-arguments)])
    (if (and (= (vector-length a) 2) (equal? (vector-ref a 0) "--only"))
        (string-split (vector-ref a 1) ",")
        #f)))
(define active (if only (filter (λ (p) (member (car p) only)) impls) impls))

(define 2^32 (expt 2 32))
(define SEED 20261110)
(define KEY 987654321)
(define failures 0)
(define checks 0)
(define (check! ok what)
  (set! checks (add1 checks))
  (unless ok (set! failures (add1 failures)) (printf "FAIL: ~a\n" what)))

(random-seed SEED)
(define (stream n) (for/list ([_ n]) (random 4294967087)))
(define streams (for/list ([n '(1000 10000)]) (stream n)))
(define (u32 v) (modulo v 2^32))

(define-values (img img-syms) (keystream-image #:target 'directive))
(define tmp (make-temporary-file "subleq-keystream-~a.txt"))

;; 1. the directive machine
(printf "## 1. Directive machine: one image (~a cells) for every stream\n\n" (length img))
(printf "Random plaintext words from (random-seed ~a), key (SEED) ~a, MODE 1 (encrypt).\n\n" SEED KEY)
(printf "| N words | Implementation | STATUS | STEPS | Output = reference | Same canonical result as in-process reference |\n|---|---|---|---|---|---|\n")
(define dir-steps (make-hash))
(for ([ws streams])
  (define n (length ws))
  (define inputs (keystream-input 1 KEY ws))
  (define expected (keystream-reference 1 KEY ws))
  (define ref (run-subleq img inputs 1000000000))
  (define ref-ok (equal? (map u32 (result-output ref)) expected))
  (check! (and ref-ok (eq? (result-status ref) 'halted)) (format "in-process N=~a" n))
  (hash-set! dir-steps n (result-steps ref))
  (printf "| ~a | racket (in-process reference) | ~a | ~a | ~a | - |\n" n (result-status ref) (result-steps ref)
          (if ref-ok "yes" "NO"))
  ;; decryption round trip
  (define back (run-subleq img (keystream-input -1 KEY (result-output ref)) 1000000000))
  (check! (equal? (map u32 (result-output back)) ws) (format "round trip N=~a" n))
  (define canon (result->canonical ref))
  (write-input-file tmp img inputs 1000000000)
  (for ([p active])
    (define-values (code out err ms) (run-impl ((cdr p) (path->string tmp))))
    (define r (parse-canonical out))
    (define ok (equal? (map u32 (hash-ref r 'output)) expected))
    (check! (and (eqv? code 0) ok (equal? out canon)) (format "~a N=~a exit=~a ~a" (car p) n code err))
    (printf "| ~a | ~a | ~a | ~a | ~a | ~a |\n" n (car p) (hash-ref r 'status) (hash-ref r 'steps)
            (if ok "yes" "NO") (if (equal? out canon) "yes" "NO"))))
(printf "\nDecrypting each ciphertext with the same image (MODE -1) gave back the plaintext (checked in process).\n\n")

;; 2. traps
(printf "## 2. Bad headers stop the directive machine with a trap\n\n")
(printf "| Header (MODE SEED N) | Implementation | STATUS | CODE | STEPS |\n|---|---|---|---|---|\n")
(for ([hdr '((1 0 -1) (7 0 0))] [code '(1 2)])
  (define ref (run-subleq img hdr 1000))
  (check! (and (eq? (result-status ref) 'trap) (= (result-code ref) code)) (format "trap ~a in-process" hdr))
  (printf "| ~a | racket (in-process reference) | ~a | ~a | ~a |\n" hdr (result-status ref) (result-code ref) (result-steps ref))
  (write-input-file tmp img hdr 1000)
  (for ([p active])
    (define-values (ec out err ms) (run-impl ((cdr p) (path->string tmp))))
    (define r (parse-canonical out))
    (check! (and (eqv? ec 0) (equal? out (result->canonical ref))) (format "trap ~a ~a" hdr (car p)))
    (printf "| ~a | ~a | ~a | ~a | ~a |\n" hdr (car p) (hash-ref r 'status) (hash-ref r 'code) (hash-ref r 'steps))))
(delete-file tmp)

;; 3a. the directive image on the original machine
(printf "\n## 3a. Directive image, unchanged, on the original machine\n\n")
(let ()
  (define fuel 10000000)
  (define-values (mem n) (execute-subleq/steps img #:fuel fuel))
  (define (cell k) (vector-ref mem (hash-ref img-syms k)))
  (printf "racket/subleq-original.rkt executed ~a instructions: ~a.\n" n
          (if (= n fuel) (format "it was still running when the step limit of ~a was reached" fuel) "it halted"))
  (printf "The original machine has no input or output, so the stream cannot be given to it and it prints nothing. At the end the cells MODE, X (seed) and N hold ~a, ~a, ~a.\n"
          (cell 'MODE) (cell 'X) (cell 'N))
  (printf "Memory cells that differ from the loaded image: ~a of ~a.\n\n"
          (for/sum ([a (vector->list mem)] [b img]) (if (equal? a b) 0 1)) (length img)))

;; 3b. the port to the original machine
(printf "## 3b. The same algorithm written for the original machine (wrap emulated, data preloaded)\n\n")
(printf "| N words | Machine | Image cells | STEPS | Output = reference |\n|---|---|---|---|---|\n")
(define orig-steps (make-hash))
(define orig-cells (make-hash))
(for ([ws streams])
  (define n (length ws))
  (define-values (oimg syms) (keystream-image #:target 'original #:mode 1 #:seed KEY #:words ws))
  (define-values (mem k) (execute-subleq/steps oimg))
  (define out (for/list ([i n]) (vector-ref mem (+ (hash-ref syms 'RESULT) i))))
  (define ok (equal? out (keystream-reference 1 KEY ws)))
  (check! ok (format "original port N=~a" n))
  (hash-set! orig-steps n k) (hash-set! orig-cells n (length oimg))
  (printf "| ~a | directive image | ~a | ~a | yes |\n| ~a | original (port) | ~a | ~a | ~a |\n"
          n (length img) (hash-ref dir-steps n) n (length oimg) k (if ok "yes" "NO")))
(define (marg h) (/ (- (hash-ref h 10000) (hash-ref h 1000)) 9000))
(printf "\nMarginal instructions per word, (STEPS(10000) - STEPS(1000)) / 9000: the directive machine ~a, original ~a, ratio ~a.\n"
        (real->decimal-string (marg dir-steps) 3) (real->decimal-string (marg orig-steps) 3)
        (real->decimal-string (/ (marg orig-steps) (marg dir-steps)) 3))
(printf "The original image grows by ~a cells per word (input and output arrays); the directive image stays at ~a cells.\n\n"
        (/ (- (hash-ref orig-cells 10000) (hash-ref orig-cells 1000)) 9000) (length img))

;; 3c. the port without wrap emulation
(printf "## 3c. The original machine WITHOUT wrap emulation (MOD32 removed)\n\n")
(printf "| N words | STEPS | Run time (ms, in process, median of 3) | Output words equal to the reference | Bits in the LCG state cell at the end |\n|---|---|---|---|---|\n")
(define long-stream (cadr streams))   ; the 10000-word stream from section 1
(for ([n '(250 500 1000 2000 4000 8000)])
  (define ws (take long-stream n))
  (define-values (oimg syms)
    (parameterize ([emulate-wrap #f])
      (keystream-image #:target 'original #:mode 1 #:seed KEY #:words ws)))
  (define runs
    (for/list ([_ 3])
      (define-values (ms vs) (time-ms (λ () (execute-subleq/steps oimg))))
      (cons ms vs)))
  (define mem (car (cdar runs)))
  (define k (cadr (cdar runs)))
  (define out (for/list ([i n]) (vector-ref mem (+ (hash-ref syms 'RESULT) i))))
  (define ref (keystream-reference 1 KEY ws))
  (printf "| ~a | ~a | ~a | ~a of ~a | ~a |\n" n k (real->decimal-string (median (map car runs)) 1)
          (for/sum ([a out] [b ref]) (if (= a b) 1 0)) n
          (integer-length (vector-ref mem (hash-ref syms 'X)))))

(printf "\nkiller-app: checks=~a failures=~a\n" checks failures)
(exit (if (zero? failures) 0 1))
