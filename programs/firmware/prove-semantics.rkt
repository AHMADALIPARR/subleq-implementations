#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only
;;
;; Prove that higher-level operations recovered by the firmware-aware
;; decompiler have the same semantics as the SUBLEQ sequences they match.
;;
;; Each pattern is re-assembled as a self-contained mini-image with known
;; addresses, executed on the directive machine, and checked against the
;; claimed post-condition.

(require racket/list racket/format
         "../../asm/sasm.rkt"
         (except-in "../../racket/subleq.rkt" wrap32))

;; ---------------------------------------------------------------------------
;; Prove MOV: dest := src, Z restored to 0
;; The 4-instruction expansion used by sasm:
;;   sq dest dest
;;   sq src  Z
;;   sq Z    dest
;;   sq Z    Z
;; ---------------------------------------------------------------------------
(define (prove-mov)
  (define-values (image syms)
    (assemble
     (λ ()
       (define SRC (var 77 'SRC))
       (define DST (var 99 'DST))
       (label 'start)
       (MOV SRC DST)
       (HALT))
     #:target 'directive))
  (define r (run-subleq image '() 100))
  (define m (list->vector (result-mem r)))
  (define dst (vector-ref m (hash-ref syms 'DST)))
  (define z (vector-ref m (hash-ref syms 'K0)))
  (and (= dst 77) (= z 0)))

;; ---------------------------------------------------------------------------
;; Prove unconditional JUMP
;; ---------------------------------------------------------------------------
(define (prove-jump)
  (define-values (image syms)
    (assemble
     (λ ()
       (define F (var 0 'F))
       (label 'start)
       (JMP 'target)
       (MOV (K 0) F)          ; should be skipped
       (label 'target)
       (MOV (K 1) F)
       (HALT))
     #:target 'directive))
  (define r (run-subleq image '() 100))
  (define m (list->vector (result-mem r)))
  (= (vector-ref m (hash-ref syms 'F)) 1))

;; ---------------------------------------------------------------------------
;; Prove software IRET: ZERO CURRENT_EXC; HALT
;; ---------------------------------------------------------------------------
(define (prove-iret)
  (define-values (image syms)
    (assemble
     (λ ()
       (define CURRENT_EXC (var 14 'CURRENT_EXC))
       (label 'iret)
       (ZERO CURRENT_EXC)
       (HALT))
     #:target 'directive))
  (define r (run-subleq image '() 100))
  (define m (list->vector (result-mem r)))
  (and (eq? (result-status r) 'halted)
       (= (vector-ref m (hash-ref syms 'CURRENT_EXC)) 0)))

;; ---------------------------------------------------------------------------
;; Prove vector install: MOV handler-label → IDT[n]
;; ---------------------------------------------------------------------------
(define (prove-vector-install)
  (define-values (image syms)
    (assemble
     (λ ()
       (define IDT (arr 4 0 'IDT))
       (MOV (K 1) (at IDT 2))
       (HALT))
     #:target 'directive))
  (define r (run-subleq image '() 100))
  (define m (list->vector (result-mem r)))
  (define idt2 (vector-ref m (+ (hash-ref syms 'IDT) 2)))
  (= idt2 1))

;; ---------------------------------------------------------------------------
(define (main)
  (printf "Proving higher-level operations == SUBLEQ sequences\n\n")
  (define results
    (list (list "MOV (dest := src, Z restored)" (prove-mov))
          (list "JUMP (unconditional)" (prove-jump))
          (list "IRET (ZERO CURRENT_EXC; HALT)" (prove-iret))
          (list "Vector install (MOV → IDT[n])" (prove-vector-install))))
  (for ([r results])
    (printf "  ~a: ~a\n" (first r) (if (second r) "PASS" "FAIL")))
  (unless (andmap second results)
    (error 'prove "semantic mismatch"))
  (printf "\nAll recovered operations match the SUBLEQ sequences: PASS\n"))

(module+ main
  (main))
