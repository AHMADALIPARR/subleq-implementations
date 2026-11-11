#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-or-later

;; SUBLEQ interpreter following semantics/subleq-spec.md (directive semantics):
;;  * 32-bit signed cells, subtraction wraps mod 2^32
;;  * branch when the wrapped result r <= 0, absolute target c
;;  * halt after executing any non-trap instruction whose c = -1
;;  * a = -2 trap (code b) > a = -1 input > b < 0 output > ordinary
;;  * out-of-range reads give 0, out-of-range writes are discarded
;;  * PC < 0 or PC + 2 >= N is fault pc-out-of-range
;; The original unbounded interpreter lives in racket/subleq-original.rkt.

(require racket/list racket/string racket/port)

(provide wrap32
         (struct-out result)
         run-subleq
         result->canonical
         parse-input-text)

;; wrap32 : integer -> integer in [-2^31, 2^31)
(define (wrap32 x)
  (- (modulo (+ x 2147483648) 4294967296) 2147483648))

;; status is one of: 'halted 'trap 'fault:pc-out-of-range
;;                   'fault:input-exhausted 'step-limit
(struct result (status pc steps code output mem) #:transparent)

;; run-subleq : (listof integer) (listof integer) natural -> result
(define (run-subleq image inputs fuel)
  (define mem (list->vector (map wrap32 image)))
  (define n (vector-length mem))
  (define (in? a) (and (>= a 0) (< a n)))
  (define (rd a) (if (in? a) (vector-ref mem a) 0))
  (define (wr! a v) (when (in? a) (vector-set! mem a v)))
  (define (done status pc steps code out)
    (result status pc steps code (reverse out) (vector->list mem)))
  (let loop ([pc 0] [steps 0] [in inputs] [out '()])
    (cond
      [(>= steps fuel) (done 'step-limit pc steps 0 out)]
      [(or (< pc 0) (>= (+ pc 2) n)) (done 'fault:pc-out-of-range pc steps 0 out)]
      [else
       (define a (vector-ref mem pc))
       (define b (vector-ref mem (+ pc 1)))
       (define c (vector-ref mem (+ pc 2)))
       ;; continue-or-halt applies the halt rule after the effect.
       (define (next pc* in* out*)
         (if (= c -1)
             (done 'halted pc* (+ steps 1) 0 out*)
             (loop pc* (+ steps 1) in* out*)))
       (cond
         [(= a -2) (done 'trap pc (+ steps 1) b out)]
         [(= a -1)
          (if (null? in)
              (done 'fault:input-exhausted pc steps 0 out)
              (begin (wr! b (wrap32 (car in)))
                     (next (+ pc 3) (cdr in) out)))]
         [(< b 0) (next (+ pc 3) in (cons (rd a) out))]
         [else
          (define r (wrap32 (- (rd b) (rd a))))
          (wr! b r)
          (next (if (<= r 0) c (+ pc 3)) in out)])])))

(define (nums->string label xs)
  (string-join (cons label (map number->string xs)) " "))

;; result->canonical : result -> string (six lines, trailing newline)
(define (result->canonical r)
  (string-append
   (format "STATUS ~a\n" (result-status r))
   (format "PC ~a\n" (result-pc r))
   (format "STEPS ~a\n" (result-steps r))
   (format "CODE ~a\n" (result-code r))
   (nums->string "OUTPUT" (result-output r)) "\n"
   (nums->string "MEM" (result-mem r)) "\n"))

;; parse-input-text : string -> (values image inputs fuel)
;; Format: N m0..mN-1 K i0..iK-1 FUEL
(define (parse-input-text s)
  (define xs (map string->number (string-split s)))
  (unless (andmap exact-integer? xs) (error 'parse-input-text "non-integer token"))
  (define n (first xs))
  (define image (take (drop xs 1) n))
  (define rest1 (drop xs (+ 1 n)))
  (define k (first rest1))
  (define inputs (take (drop rest1 1) k))
  (define rest2 (drop rest1 (+ 1 k)))
  (unless (= (length rest2) 1) (error 'parse-input-text "expected exactly one FUEL value"))
  (values image inputs (first rest2)))

(module+ main
  (define args (current-command-line-arguments))
  (unless (= (vector-length args) 1)
    (eprintf "usage: racket racket/subleq.rkt INPUT-FILE\n")
    (exit 2))
  (define-values (image inputs fuel)
    (parse-input-text (call-with-input-file (vector-ref args 0) port->string)))
  (display (result->canonical (run-subleq image inputs fuel))))

(module+ test
  (require rackunit racket/runtime-path)
  (define-runtime-path countdown-path "../examples/countdown.subleq")
  (define (st r) (result-status r))
  ;; wrap32
  (check-equal? (wrap32 2147483648) -2147483648)
  (check-equal? (wrap32 -2147483649) 2147483647)
  (check-equal? (wrap32 4294967295) -1)
  (check-equal? (wrap32 5) 5)
  ;; ordinary, branch taken to absolute c = -1 -> halt (pc reported -1)
  (let ([r (run-subleq '(3 3 -1 7) '() 100)])
    (check-equal? (st r) 'halted)
    (check-equal? (result-pc r) -1)
    (check-equal? (result-steps r) 1)
    (check-equal? (result-mem r) '(3 3 -1 0)))
  ;; ordinary, no branch, c = -1 still halts (pc reported 3)
  (let ([r (run-subleq '(4 3 -1 5 1) '() 100)])
    (check-equal? (st r) 'halted)
    (check-equal? (result-pc r) 3)
    (check-equal? (result-mem r) '(4 3 -1 4 1)))
  ;; wrapped overflow: -2^31 - 1 wraps to 2^31-1 > 0, so no branch
  (let ([r (run-subleq '(4 3 -1 -2147483648 1) '() 100)])
    (check-equal? (result-mem r) '(4 3 -1 2147483647 1))
    (check-equal? (result-pc r) 3))
  ;; trap has top priority, records b, ignores c
  (let ([r (run-subleq '(-2 42 -1) '() 100)])
    (check-equal? (st r) 'trap)
    (check-equal? (result-code r) 42)
    (check-equal? (result-pc r) 0)
    (check-equal? (result-steps r) 1))
  ;; input then output, then halt
  (let ([r (run-subleq '(-1 9 3  9 -1 -1  0 0 0 0) '(77) 100)])
    (check-equal? (st r) 'halted)
    (check-equal? (result-output r) '(77))
    (check-equal? (list-ref (result-mem r) 9) 77))
  ;; input beats output when b < 0 too: value is discarded
  (let ([r (run-subleq '(-1 -5 -1) '(1) 100)])
    (check-equal? (st r) 'halted)
    (check-equal? (result-output r) '())
    (check-equal? (result-mem r) '(-1 -5 -1)))
  ;; input exhausted
  (let ([r (run-subleq '(-1 0 -1) '() 100)])
    (check-equal? (st r) 'fault:input-exhausted)
    (check-equal? (result-steps r) 0))
  ;; out-of-range read gives 0, write discarded
  (let ([r (run-subleq '(100 200 -1) '() 100)])
    (check-equal? (st r) 'halted)
    (check-equal? (result-pc r) -1)
    (check-equal? (result-mem r) '(100 200 -1)))
  ;; pc out of range
  (check-equal? (st (run-subleq '(0 0) '() 100)) 'fault:pc-out-of-range)
  (check-equal? (st (run-subleq '() '() 100)) 'fault:pc-out-of-range)
  ;; step limit
  (let ([r (run-subleq '(0 0 0) '() 10)])
    (check-equal? (st r) 'step-limit)
    (check-equal? (result-steps r) 10))
  ;; examples/countdown.subleq terminates under the spec and prints 3 2 1
  (let* ([text (call-with-input-file countdown-path port->string)]
         [code (string-join (for/list ([l (string-split text "\n")])
                              (car (string-split (string-append l " ") ";" #:trim? #f)))
                            " ")]
         [image (map string->number (string-split code))]
         [r (run-subleq image '() 1000)])
    (check-equal? image '(12 -1 3 13 12 9 14 14 0 14 14 -1 3 1 0))
    (check-equal? (st r) 'halted)
    (check-equal? (result-output r) '(3 2 1))
    (check-equal? (result-steps r) 9))
  ;; canonical form
  (check-equal? (result->canonical (run-subleq '(-2 7 0) '() 5))
                "STATUS trap\nPC 0\nSTEPS 1\nCODE 7\nOUTPUT\nMEM -2 7 0\n"))
