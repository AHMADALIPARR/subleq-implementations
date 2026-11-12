#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only
;;
;; IBX-1 integer-only Gaussian butterfly network.
;; Pure Racket reference that matches factor/ibx.factor.
;; The butterfly kernel (4 integer add/sub) can be replaced by a
;; SUBLEQ sequence executed via racket/subleq.rkt (directive machine).
;; Expected expansion: ~24 SUBLEQ instructions per butterfly using the
;; existing macro table (ADD/SUB/MOV).

(require racket/vector)

(provide transform! energy make-input verify-ibx)

;; Native butterfly (4 integer operations).
;; re[a] = xr - yi; im[a] = xi + yr; re[b] = xr + yi; im[b] = xi - yr
;; For the SUBLEQ-backed kernel see programs/ibx-subleq.rkt
;; (uses the directive machine via run-subleq; ~24 instructions).
(define (butterfly! re im a b)
  (define xr (vector-ref re a))
  (define xi (vector-ref im a))
  (define yr (vector-ref re b))
  (define yi (vector-ref im b))
  (vector-set! re a (- xr yi))
  (vector-set! im a (+ xi yr))
  (vector-set! re b (+ xr yi))
  (vector-set! im b (- xi yr)))

(define (stage! re im d)
  (define n (vector-length re))
  (define block-size (* 2 d))
  (for ([block (in-range 0 (/ n block-size))])
    (for ([j (in-range d)])
      (define a (+ (* block block-size) j))
      (define b (+ a d))
      (butterfly! re im a b))))

(define (transform! re im)
  (define n (vector-length re))
  (let loop ([d 1])
    (when (< d n)
      (stage! re im d)
      (loop (* d 2)))))

(define (energy re im)
  (for/sum ([j (in-range (vector-length re))])
    (+ (sqr (vector-ref re j)) (sqr (vector-ref im j)))))

(define (make-input n)
  (define re (make-vector n))
  (define im (make-vector n))
  (for ([j (in-range n)])
    (vector-set! re j (- (modulo j 17) 8))
    (vector-set! im j 0))
  (values re im))

(define (verify-ibx)
  ;; small vector (matches Factor verify-small)
  (define re (vector 1 2 3 4))
  (define im (make-vector 4 0))
  (transform! re im)
  (unless (equal? (vector->list re) '(-3 5 5 -3))
    (error 'ibx "small re mismatch: ~s" (vector->list re)))
  (unless (equal? (vector->list im) '(5 1 -1 -5))
    (error 'ibx "small im mismatch: ~s" (vector->list im)))
  ;; N=1024 energy invariant (matches Factor verify-1024)
  (define-values (re1024 im1024) (make-input 1024))
  (define before (energy re1024 im1024))
  (transform! re1024 im1024)
  (define after (energy re1024 im1024))
  (unless (= after (* 1024 before))
    (error 'ibx "energy invariant failed: ~a != ~a * ~a" after 1024 before))
  (printf "IBX-1 / Racket: PASS (small vector + N=1024 energy invariant)\n")
  (printf "Energy before: ~a  after: ~a  (scale ~a)\n" before after 1024))

(module+ main
  (verify-ibx))
