#lang racket/base
;; SPDX-License-Identifier: AGPL-3.0-or-later

;; "Killer app": a streaming keystream filter (a TOY cipher, not secure).
;;
;;   x(0)   = seed
;;   x(i+1) = 1664525 * x(i) + 1013904223  mod 2^32   (Numerical Recipes LCG)
;;   encrypt: c(i) = p(i) + x(i+1) mod 2^32
;;   decrypt: p(i) = c(i) - x(i+1) mod 2^32
;;
;; It is built to use every part of the directive parameter set:
;;   * 32-bit wrap-around: the LCG and the keystream addition are plain
;;     DOUBLE/ADD/SUB with no reduction code;
;;   * streaming I/O: words are read with a = -1 and written with b < 0 one
;;     at a time, so the image has a fixed size whatever the stream length;
;;   * trap: a bad header stops the machine with status trap, CODE 1
;;     (negative count) or CODE 2 (mode not 1 / -1);
;;   * halt on c = -1 when the stream is done.
;;
;; Directive input stream: MODE (1 = encrypt, -1 = decrypt), SEED, N, then
;; N words. Output: N words.
;;
;; The 'original version runs the same algorithm on racket/subleq-original.rkt:
;; MODE, SEED, N and the N words are placed in the image, the results are
;; written to an output array in the image with STORE-NEXT, wrap-around is
;; emulated with MOD32, and a bad header writes 1 or 2 to the STATUS cell
;; before halting (there is no trap). Words are canonical (0 <= w < 2^32).

(require racket/list "../asm/sasm.rkt")
(provide keystream-image keystream-input keystream-reference
         lcg-a lcg-c)

(define lcg-a 1664525)
(define lcg-c 1013904223)

;; reference in plain Racket (used to check every SUBLEQ result)
(define (keystream-reference mode seed words)
  (let loop ([x (modulo seed (expt 2 32))] [ws words] [acc '()])
    (if (null? ws)
        (reverse acc)
        (let* ([x* (modulo (+ (* lcg-a x) lcg-c) (expt 2 32))]
               [y (modulo ((if (= mode 1) + -) (car ws) x*) (expt 2 32))])
          (loop x* (cdr ws) (cons y acc))))))

(define (program mode seed words)
  (define dir? (directive?))
  (define n (length words))
  (define MODE (var (if dir? 0 mode) 'MODE))
  (define X (var (if dir? 0 (modulo seed (expt 2 32))) 'X))
  (define N (var (if dir? 0 n) 'N))
  (define P (var 0 'P))
  (define XC (var 0 'XC))
  (define T (var 0 'T))
  (define STATUS (var 0 'STATUS))            ; original only: 0 ok, 1/2 bad header
  (define INPTR (and (not dir?) (var 'DATA 'INPTR)))
  (define OUTPTR (and (not dir?) (var 'RESULT 'OUTPTR)))
  (unless dir?
    (arr (max n 1) (if (zero? n) 0 (map (λ (w) (modulo w (expt 2 32))) words)) 'DATA)
    (arr (max n 1) 0 'RESULT))
  (define bad-n (fresh 'E)) (define bad-mode (fresh 'E))
  (define enc (fresh 'E)) (define dec (fresh 'E)) (define fin (fresh 'E))
  (define nonpos (fresh 'E)) (define maybe-dec (fresh 'E))

  (when dir? (IN MODE) (IN X) (IN N))
  ;; header checks
  (if dir?
      (JSIGN N bad-n)                        ; N < 0 (signed)
      (sq (K -1) N bad-n))                   ; original (unbounded): N + 1 <= 0 iff N < 0
  (unless dir? (DEC N))                      ; undo the +1 on the ok path
  (JLEZ MODE nonpos)
  (MOV MODE T) (DEC T) (JLEZ T enc)          ; MODE >= 1: T = MODE - 1 = 0 iff MODE = 1
  (JMP bad-mode)
  (label nonpos)
  (MOV MODE T) (INC T)                       ; MODE <= 0: T = MODE + 1, no wrap
  (JLEZ T maybe-dec)
  (JMP bad-mode)                             ; MODE = 0
  (label maybe-dec)
  (INC T) (JLEZ T bad-mode)                  ; T + 1 <= 0 iff MODE < -1
  (JMP dec)

  (define (body add?)
    (define top (fresh 'E))
    (label top)
    (JLEZ N fin)
    (if dir? (IN P) (LOAD-NEXT INPTR P))
    (MULK X lcg-a XC)
    (ADD (K lcg-c) X) (MOD32 X 1)
    (if add?
        (begin (ADD X P) (MOD32 P 1))
        (begin (SUB X P) (unless dir? (ADD (K (expt 2 32)) P) (MOD32 P 1))))
    (if dir? (OUT P) (STORE-NEXT P OUTPTR))
    (DEC N)
    (JMP top))
  (label enc) (body #t)
  (label dec) (body #f)
  (label fin) (HALT)
  (label bad-n)
  (if dir? (TRAP 1) (begin (ZERO STATUS) (INC STATUS) (HALT)))
  (label bad-mode)
  (if dir? (TRAP 2) (begin (ZERO STATUS) (INC STATUS) (INC STATUS) (HALT))))

;; keystream-image : #:target [#:mode #:seed #:words] -> (values image symtab)
;; On 'directive the image is the same for every stream (arguments ignored).
(define (keystream-image #:target [target 'directive] #:mode [mode 1] #:seed [seed 0] #:words [words '()])
  (assemble (λ () (program mode seed words)) #:target target))

(define (keystream-input mode seed words)
  (append (list mode seed (length words)) words))

;; Tests: both machines against keystream-reference, round trip, bad headers.
(module+ test
  (require rackunit (except-in "../racket/subleq.rkt" wrap32) "../racket/subleq-original.rkt")
  (define 2^32 (expt 2 32))
  (define-values (img _) (keystream-image))
  (define (dir mode seed ws)
    (define r (run-subleq img (keystream-input mode seed ws) 10000000))
    (check-equal? (result-status r) 'halted)
    (map (λ (v) (modulo v 2^32)) (result-output r)))
  (define (orig mode seed ws)
    (define-values (oimg syms) (keystream-image #:target 'original #:mode mode #:seed seed #:words ws))
    (define-values (mem n) (execute-subleq/steps oimg))
    (check-equal? (vector-ref mem (hash-ref syms 'STATUS)) 0)
    (for/list ([i (length ws)]) (vector-ref mem (+ (hash-ref syms 'RESULT) i))))
  (random-seed 20261110)
  (for ([n '(0 1 2 50)] [seed (list 0 1 #xffffffff 123456789)])
    (define ws (for/list ([_ n]) (random 4294967087)))
    (define c (keystream-reference 1 seed ws))
    (check-equal? (dir 1 seed ws) c)
    (check-equal? (orig 1 seed ws) c)
    (check-equal? (dir -1 seed c) ws)
    (check-equal? (orig -1 seed c) ws))
  ;; edge words
  (let ([ws (list 0 1 #x7fffffff #x80000000 #xffffffff)])
    (check-equal? (dir 1 42 ws) (keystream-reference 1 42 ws))
    (check-equal? (orig 1 42 ws) (keystream-reference 1 42 ws)))
  ;; bad headers: trap with CODE 1 (N < 0) or 2 (bad mode) on the directive machine
  (for ([hdr '((1 0 -1) (1 0 -2147483648) (0 0 0) (2 0 0) (-2 0 0) (2147483647 0 0) (-2147483648 0 0))]
        [code '(1 1 2 2 2 2 2)])
    (define r (run-subleq img hdr 1000))
    (check-equal? (result-status r) 'trap)
    (check-equal? (result-code r) code)))
