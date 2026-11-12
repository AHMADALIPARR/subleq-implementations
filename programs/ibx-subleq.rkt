#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only
;;
;; IBX-1 butterfly kernel executed by the directive SUBLEQ machine.
;; Uses asm/sasm.rkt macros to assemble a sequence that implements:
;;   re[a] = xr - yi
;;   im[a] = xi + yr
;;   re[b] = xr + yi
;;   im[b] = xi - yr
;; then runs it via racket/subleq.rkt.
;; Expected ~24 executed instructions per butterfly.

 (require racket/vector
         "../asm/sasm.rkt"
         (except-in "../racket/subleq.rkt" wrap32))

(provide butterfly-steps run-butterfly-subleq)

;; Assemble a self-contained image that reads four inputs from cells
;; XR XI YR YI, computes the four results into RA IA RB IB, then halts.
;; Scratch cells are allocated by the assembler.
(define (assemble-butterfly)
  (define-values (image syms)
    (assemble
     (λ ()
       (define XR (var 0 'XR))
       (define XI (var 0 'XI))
       (define YR (var 0 'YR))
       (define YI (var 0 'YI))
       (define RA (var 0 'RA))
       (define IA (var 0 'IA))
       (define RB (var 0 'RB))
       (define IB (var 0 'IB))
       (define T  (var 0 'T))
       ;; RA = XR - YI
       (MOV XR T)
       (SUB YI T)          ; T = XR - YI
       (MOV T RA)
       ;; IA = XI + YR
       (MOV XI T)
       (ADD YR T)          ; T = XI + YR
       (MOV T IA)
       ;; RB = XR + YI
       (MOV XR T)
       (ADD YI T)          ; T = XR + YI
       (MOV T RB)
       ;; IB = XI - YR
       (MOV XI T)
       (SUB YR T)          ; T = XI - YR
       (MOV T IB)
       (HALT))
     #:target 'directive))
  (values image syms))

;; Run one butterfly on the directive machine.
;; Returns the four results and the step count.
(define (run-butterfly-subleq xr xi yr yi)
  (define-values (image syms) (assemble-butterfly))
  (define mem (list->vector image))
  (vector-set! mem (hash-ref syms 'XR) xr)
  (vector-set! mem (hash-ref syms 'XI) xi)
  (vector-set! mem (hash-ref syms 'YR) yr)
  (vector-set! mem (hash-ref syms 'YI) yi)
  (define r (run-subleq (vector->list mem) '() 1000))
  (values (vector-ref (list->vector (result-mem r)) (hash-ref syms 'RA))
          (vector-ref (list->vector (result-mem r)) (hash-ref syms 'IA))
          (vector-ref (list->vector (result-mem r)) (hash-ref syms 'RB))
          (vector-ref (list->vector (result-mem r)) (hash-ref syms 'IB))
          (result-steps r)))

;; Convenience: just the step count for a representative call.
(define (butterfly-steps)
  (define-values (_ra _ia _rb _ib steps)
    (run-butterfly-subleq 1 2 3 4))
  steps)

(module+ main
  (define-values (ra ia rb ib steps)
    (run-butterfly-subleq 1 2 3 4))
  (printf "SUBLEQ butterfly (1 2 3 4) -> (~a ~a ~a ~a) in ~a steps\n"
          ra ia rb ib steps)
  (printf "Expected native: (-1 5 5 -1)\n"))
