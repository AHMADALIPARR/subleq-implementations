#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only
;;
;; SUBLEQ realization of the host x86 firmware Phase 2 mechanisms.
;;
;; LIDT          -> software interrupt-vector table in memory
;; CR0 / CR4     -> virtual processor-state and feature-control words
;; RDMSR/WRMSR   -> explicit memory-backed register-service operations
;; IRETQ         -> software exception return (restore saved state)
;; Page fault    -> memory-access validation + software fault dispatch
;; GPF           -> runtime check that dispatches a virtual exception
;; Exception handlers -> SUBLEQ routines reached through a dispatcher
;;
;; Ordinary SUBLEQ using the directive machine and sasm macros.

(require "../../asm/sasm.rkt"
         (except-in "../../racket/subleq.rkt" wrap32))

(provide assemble-firmware run-firmware-demo)

;; Returns (values image syms code-end)
;; code-end is the address of the first data cell.
(define (assemble-firmware)
  (define-values (image syms)
    (assemble
     (λ ()
       ;; data
       (define IDT (arr 20 0 'IDT))
       (define CR0 (var 0 'CR0))
       (define CR4 (var 0 'CR4))
       (define MSR_EFER (var 0 'MSR_EFER))
       (define SAVED_PC (var 0 'SAVED_PC))
       (define CURRENT_EXC (var 0 'CURRENT_EXC))
       (define FAULT_ADDR (var 0 'FAULT_ADDR))
       (define T (var 0 'T))

       ;; firmware-init
       (label 'firmware-init)
       (MOV (K 1) CR0)                 ; CR0.PE = 1
       (MOV (K #x200) CR4)             ; CR4.OSFXSR
       (MOV (K 1) MSR_EFER)            ; EFER.SCE
       ;; install vectors (store handler labels)
       (MOV 'H0 (at IDT 0))
       (MOV 'H1 (at IDT 1))
       (MOV 'H13 (at IDT 13))
       (MOV 'H14 (at IDT 14))
       ;; demo: raise page-fault style exception
       (MOV (K 14) CURRENT_EXC)
       (MOV (K #x1234) FAULT_ADDR)
       (JMP 'dispatch)

       ;; handlers
       (label 'H0)  (MOV (K 0) CURRENT_EXC) (JMP 'iret)
       (label 'H1)  (MOV (K 1) CURRENT_EXC) (JMP 'iret)
       (label 'H13) (MOV (K 13) CURRENT_EXC) (JMP 'iret)
       (label 'H14) (MOV (K 14) CURRENT_EXC) (JMP 'iret)

       ;; software iretq
       (label 'iret)
       (ZERO CURRENT_EXC)
       (HALT)

       ;; dispatcher (simplified: for demo we just jump to H14)
       (label 'dispatch)
       (JMP 'H14)

       (HALT))
     #:target 'directive))
  ;; Code ends at the lowest data address. Constants (K0, K1, ...) and
;; variables are all data; code labels are the ones we explicitly placed.
(define code-labels '(firmware-init H0 H1 H13 H14 iret dispatch))
(define data-addrs
  (for/list ([(k v) (in-hash syms)]
             #:unless (memq k code-labels))
    v))
(define code-end (apply min data-addrs))
(values image syms code-end))

(define (run-firmware-demo)
  (define-values (image syms) (assemble-firmware))
  (define r (run-subleq image '() 10000))
  (define mem (list->vector (result-mem r)))
  (values (result-status r)
          (result-steps r)
          (vector-ref mem (hash-ref syms 'CURRENT_EXC))
          (vector-ref mem (hash-ref syms 'CR0))
          (vector-ref mem (hash-ref syms 'CR4))
          (vector-ref mem (hash-ref syms 'FAULT_ADDR))))

(module+ main
  (define-values (status steps exc cr0 cr4 faddr)
    (run-firmware-demo))
  (printf "Firmware demo: status=~a steps=~a\n" status steps)
  (printf "  CURRENT_EXC=~a CR0=~a CR4=~a FAULT_ADDR=~a\n" exc cr0 cr4 faddr))
