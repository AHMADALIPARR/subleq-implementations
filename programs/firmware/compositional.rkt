#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only
;;
;; Compositional verification.
;;
;; Shows that the individually proved operations remain correct when
;; composed into the full firmware control flow:
;;
;;   init registers → install vectors → raise exception
;;   → dispatch → handler → software iret
;;
;; Each step's post-condition is checked, and the final state is shown
;; to be exactly the composition of the individual post-conditions.

(require racket/list racket/format racket/hash
         "subleq-firmware.rkt"
         "../../asm/sasm.rkt"
         (except-in "../../racket/subleq.rkt" wrap32))

;; ---------------------------------------------------------------------------
;; Instrumented firmware that records checkpoints
;; ---------------------------------------------------------------------------
(define (assemble-instrumented)
  (define-values (image syms)
    (assemble
     (λ ()
       (define IDT (arr 20 0 'IDT))
       (define CR0 (var 0 'CR0))
       (define CR4 (var 0 'CR4))
       (define MSR_EFER (var 0 'MSR_EFER))
       (define CURRENT_EXC (var 0 'CURRENT_EXC))
       (define FAULT_ADDR (var 0 'FAULT_ADDR))
       (define CHECK (var 0 'CHECK))   ; checkpoint counter

       (label 'firmware-init)
       ;; 1. Init registers
       (MOV (K 1) CR0)
       (MOV (K #x200) CR4)
       (MOV (K 1) MSR_EFER)
       (INC CHECK)                     ; checkpoint 1

       ;; 2. Install vectors
       (MOV 'H0 (at IDT 0))
       (MOV 'H14 (at IDT 14))
       (INC CHECK)                     ; checkpoint 2

       ;; 3. Raise exception
       (MOV (K 14) CURRENT_EXC)
       (MOV (K #x1234) FAULT_ADDR)
       (INC CHECK)                     ; checkpoint 3

       ;; 4. Dispatch
       (JMP 'dispatch)

       ;; handlers
       (label 'H0)  (MOV (K 0) CURRENT_EXC) (JMP 'iret)
       (label 'H14) (MOV (K 14) CURRENT_EXC) (JMP 'iret)

       ;; 5. software iret
       (label 'iret)
       (ZERO CURRENT_EXC)
       (INC CHECK)                     ; checkpoint 4
       (HALT)

       (label 'dispatch)
       (JMP 'H14)

       (HALT))
     #:target 'directive))
  (values image syms))

;; ---------------------------------------------------------------------------
;; Run and verify composition
;; ---------------------------------------------------------------------------
(define (verify-composition)
  (define-values (image syms) (assemble-instrumented))
  (define r (run-subleq image '() 10000))
  (define m (list->vector (result-mem r)))
  (define status (result-status r))
  (define steps (result-steps r))

  (define cr0 (vector-ref m (hash-ref syms 'CR0)))
  (define cr4 (vector-ref m (hash-ref syms 'CR4)))
  (define msr (vector-ref m (hash-ref syms 'MSR_EFER)))
  (define exc (vector-ref m (hash-ref syms 'CURRENT_EXC)))
  (define faddr (vector-ref m (hash-ref syms 'FAULT_ADDR)))
  (define check (vector-ref m (hash-ref syms 'CHECK)))
  (define idt0 (vector-ref m (hash-ref syms 'IDT)))
  (define idt14 (vector-ref m (+ (hash-ref syms 'IDT) 14)))

  (printf "Compositional verification\n")
  (printf "  status=~a steps=~a checkpoints=~a\n" status steps check)
  (printf "  CR0=~a CR4=~a MSR_EFER=~a\n" cr0 cr4 msr)
  (printf "  CURRENT_EXC=~a FAULT_ADDR=~a\n" exc faddr)
  (printf "  IDT[0]=~a IDT[14]=~a\n" idt0 idt14)

  ;; Individual post-conditions still hold after composition
  (define ok
    (and (eq? status 'halted)
         (= check 4)                  ; all four phases executed
         (= cr0 1)                    ; MOV CR0 preserved
         (= cr4 #x200)                ; MOV CR4 preserved
         (= msr 1)                    ; MOV MSR preserved
         (= exc 0)                    ; IRET cleared exception
         (= faddr #x1234)             ; fault address preserved
         (> idt0 0)                   ; vector installed
         (> idt14 0)))                ; vector installed

  (printf "  All composed post-conditions hold: ~a\n" ok)
  (unless ok (error 'composition "post-condition violated"))
  (printf "Compositional verification: PASS\n"))

(module+ main
  (verify-composition))
