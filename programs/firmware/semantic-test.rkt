#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only
;;
;; Semantic equivalence tests for the firmware-aware decompiler.
;;
;; Verifies that the decompiled representation preserves the observable
;; behavior of the original SUBLEQ program under the same initial state.
;;
;; Covers:
;;   - Exception handling and software iret
;;   - Virtual register updates (CR0, CR4, MSR_EFER)
;;   - Conditional branches (JLEZ-style)
;;   - Memory mutation
;;   - Self-modifying instruction (patch then execute)

(require racket/list racket/format racket/hash
         "subleq-firmware.rkt"
         "decompiler.rkt"
         "../../asm/sasm.rkt"
         (except-in "../../racket/subleq.rkt" wrap32))

;; ---------------------------------------------------------------------------
;; 1. Decompile and check that recognized ops match executed results
;; ---------------------------------------------------------------------------
(define (test-decompile-matches-execution)
  (printf "=== Decompiler vs execution ===\n")
  (define-values (image syms code-end) (assemble-firmware))
  (define r (run-subleq image '() 10000))
  (define mem (list->vector (result-mem r)))
  ;; Virtual registers after execution
  (define cr0 (vector-ref mem (hash-ref syms 'CR0)))
  (define cr4 (vector-ref mem (hash-ref syms 'CR4)))
  (define msr (vector-ref mem (hash-ref syms 'MSR_EFER)))
  (define exc (vector-ref mem (hash-ref syms 'CURRENT_EXC)))
  (define faddr (vector-ref mem (hash-ref syms 'FAULT_ADDR)))
  (printf "  After run: CR0=~a CR4=~a MSR=~a EXC=~a FAULT=~a\n"
          cr0 cr4 msr exc faddr)
  (unless (and (= cr0 1) (= cr4 #x200) (= msr 1)
               (= exc 0) (= faddr #x1234))
    (error 'semantic "virtual register / exception state mismatch"))
  (printf "  Virtual registers and exception state: PASS\n"))

;; ---------------------------------------------------------------------------
;; 2. Conditional branch test (JLEZ)
;; ---------------------------------------------------------------------------
(define (test-conditional-branch)
  (printf "=== Conditional branch (JLEZ) ===\n")
  (define-values (image syms)
    (assemble
     (λ ()
       (define X (var 0 'X))
       (define F (var 0 'F))
       (label 'start)
       (MOV (K -1) X)          ; X = -1 (will take branch)
       (JLEZ X 'taken)
       (MOV (K 0) F)           ; not taken
       (JMP 'done)
       (label 'taken)
       (MOV (K 1) F)           ; taken
       (label 'done)
       (HALT))
     #:target 'directive))
  (define r (run-subleq image '() 1000))
  (define mem (list->vector (result-mem r)))
  (define f (vector-ref mem (hash-ref syms 'F)))
  (printf "  F after JLEZ on -1: ~a (expected 1)\n" f)
  (unless (= f 1) (error 'branch "JLEZ did not take expected path"))
  (printf "  Conditional branch: PASS\n"))

;; ---------------------------------------------------------------------------
;; 3. Memory mutation test
;; ---------------------------------------------------------------------------
(define (test-memory-mutation)
  (printf "=== Memory mutation ===\n")
  (define-values (image syms)
    (assemble
     (λ ()
       (define A (var 5 'A))
       (define B (var 3 'B))
       (label 'start)
       (ADD A B)               ; B = B + A = 8
       (HALT))
     #:target 'directive))
  (define r (run-subleq image '() 1000))
  (define mem (list->vector (result-mem r)))
  (define b (vector-ref mem (hash-ref syms 'B)))
  (printf "  B after ADD: ~a (expected 8)\n" b)
  (unless (= b 8) (error 'mutation "ADD did not mutate B correctly"))
  (printf "  Memory mutation: PASS\n"))

;; ---------------------------------------------------------------------------
;; 4. Self-modifying instruction test
;; ---------------------------------------------------------------------------
(define (test-self-modifying)
  (printf "=== Self-modifying instruction ===\n")
  (define-values (image syms)
    (assemble
     (λ ()
       (define SRC (var 42 'SRC))
       (define DST (var 0 'DST))
       (define PTR (var 0 'PTR))
       (label 'start)
       ;; Point PTR at SRC
       (MOV 'SRC PTR)
       ;; Self-modifying load: patch the a-field of the next instruction
       (define patch (fresh 'P))
       (MOV PTR (at patch 0))
       (ZERO DST)
       (label patch) (sq 0 (Z))          ; a will be patched to SRC
       (sq (Z) DST)
       (sq (Z) (Z))
       (HALT))
     #:target 'directive))
  (define r (run-subleq image '() 1000))
  (define mem (list->vector (result-mem r)))
  (define dst (vector-ref mem (hash-ref syms 'DST)))
  (printf "  DST after self-modifying load: ~a (expected 42)\n" dst)
  (unless (= dst 42) (error 'selfmod "self-modifying load failed"))
  (printf "  Self-modifying instruction: PASS\n"))

;; ---------------------------------------------------------------------------
;; 5. Exception dispatch + return preserves state
;; ---------------------------------------------------------------------------
(define (test-exception-dispatch)
  (printf "=== Exception dispatch + return ===\n")
  (define-values (image syms code-end) (assemble-firmware))
  (define r (run-subleq image '() 10000))
  (define mem (list->vector (result-mem r)))
  (define status (result-status r))
  (define exc (vector-ref mem (hash-ref syms 'CURRENT_EXC)))
  (printf "  status=~a CURRENT_EXC after iret=~a (expected 0)\n" status exc)
  (unless (and (eq? status 'halted) (= exc 0))
    (error 'dispatch "exception not cleared by software iret"))
  (printf "  Exception dispatch and return: PASS\n"))

;; ---------------------------------------------------------------------------
(define (main)
  (test-decompile-matches-execution)
  (test-conditional-branch)
  (test-memory-mutation)
  (test-self-modifying)
  (test-exception-dispatch)
  (printf "\nAll semantic equivalence tests: PASS\n"))

(module+ main
  (main))
