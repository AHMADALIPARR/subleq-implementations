#lang rosette
;; SPDX-License-Identifier: AGPL-3.0-or-later

(require "model.rkt")
(require "microcode.rkt")
(require "verify.rkt")

(output-smt #f)

;; Symbolic verification of core instructions of the SUBLEQ microcode in
;; microcode.rkt, run on the Harvard-style model in model.rkt.
;;
;; Register convention (taken from microcode.rkt and model.rkt, where
;; RSLT is defined as SRC2): operands are already in the OISC registers,
;; the microcode leaves the architectural result in RSLT (= SRC2) and the
;; next RISC-V PC in RVPC. The value `execute` returns as the "result" is
;; only the last micro-instruction's subtraction result (for these routines
;; the new RVPC), so the specs check registers, not that value.
;;
;; Earlier versions of these specs compared that returned value with
;; IMMI + SRC1 etc.; they disagreed with the microcode and all four failed.
;;
;; Verification boundary: LB/LH/LW/LBU/LHU/SB/SH/SW are stubs in
;; microcode.rkt (their *-PC entries point at the ADD routine) and are
;; NOT verified. Only the four routines below are checked here.
;; Uses Rosette's default solver (Z3).

(define default-solver (current-solver))

(define (reg res r) (list-ref (verify-memory res) (bitvector->natural r)))

(rv-verify
 #:name "ADD / ADDI / LUI"
 #:init-pc ADD-PC
 #:fuel 4
 #:microcode microcode
 #:solver default-solver
 #:spec (λ (res)
          (and (bveq (reg res RVPC) (bvadd val-rvpc (bv 4 XLEN)))
               (bveq (reg res RSLT) (bvadd val-src2 val-immi))))
 #:assumptions #f)

(rv-verify
 #:name "SUB"
 #:init-pc SUB-PC
 #:fuel 2
 #:microcode microcode
 #:solver default-solver
 #:spec (λ (res)
          (and (bveq (reg res RVPC) (bvadd val-rvpc (bv 4 XLEN)))
               (bveq (reg res RSLT) (bvsub val-src2 val-immi))))
 #:assumptions #f)

(rv-verify
 #:name "AUIPC"
 #:init-pc AUIPC-PC
 #:fuel 8
 #:microcode microcode
 #:solver default-solver
 #:spec (λ (res)
          (and (bveq (reg res RVPC) (bvadd val-rvpc (bv 4 XLEN)))
               (bveq (reg res RSLT) (bvadd val-rvpc val-immi))))
 #:assumptions #f)

(rv-verify
 #:name "JAL"
 #:init-pc JAL-PC
 #:fuel 8
 #:microcode microcode
 #:solver default-solver
 #:spec (λ (res)
          (and (bveq (reg res RVPC) (bvadd val-rvpc val-immi))
               (bveq (reg res RSLT) (bvadd val-rvpc (bv 4 XLEN)))))
 #:assumptions (λ (mem)
                 (assume (eq? (bv 0 2) (extract 1 0 (list-ref mem 1))))))

(printf "\nVerification suite finished.\n")
(rv-verify-finish)
