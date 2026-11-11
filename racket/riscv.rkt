#lang rosette
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-or-later AND MIT
;; SPDX-FileCopyrightText: 2022 Institute for Complex Systems (ICS), Johannes Kepler University Linz
;; Origin: adapted from riscv.rkt (specs rewritten in this repository) from https://github.com/ics-jku/goldcrest-microcode-verification@55d3404
;; (MIT License, see LICENSES/MIT-goldcrest.txt).

(require "model.rkt")
(require "microcode.rkt")
(require "verify.rkt")

(output-smt #f)

;; Symbolic checks of four routines of the SUBLEQ microcode in
;; microcode.rkt, run on the Harvard-style model in model.rkt.
;;
;; What is checked: the register effect of each routine. microcode.rkt is
;; upstream's compliant.rkt; it leaves its result in RSLT (= SRC2, as
;; model.rkt defines it) and the next RISC-V PC in RVPC. The value `execute`
;; returns as the "result" is only the last micro-instruction's subtraction
;; (for these routines, the new RVPC), so the specs check registers.
;;
;; Why the specs changed: the previous specs came from upstream riscv.rkt,
;; which verifies upstream's *other* microcode file (microcode.rkt there),
;; not compliant.rkt. Against this microcode they all failed, and the
;; program still exited 0.
;;
;; What is NOT checked: conformance to RV32I. That depends on how the
;; Goldcrest VP loads rs1/rs2/imm into SRC2/IMMI before the routine runs,
;; which is outside this repository. SUBLEQ_AUDIT_REPORT.md (SUBLEQ-02)
;; states that under Goldcrest's convention SUB computes rs2 - rs1; that
;; claim was not re-checked here and the microcode was not changed.
;;
;; Verification boundary: LB/LH/LW/LBU/LHU/SB/SH/SW are stubs in
;; microcode.rkt (their *-PC entries point at the ADD routine) and are
;; NOT verified. Only the four routines below are checked.
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
