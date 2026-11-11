#lang rosette
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only


(require "model.rkt")
(require "microcode.rkt")
(require "verify.rkt")

(output-smt #f)

;; Example verifications for core instructions using symbolic inputs.
;; Specs match the RISC-V architectural behavior after the microcode has run.
;; (Assumes operands are already loaded into the OISC registers.)
;; Uses Rosette's default solver (Z3).

(define default-solver (current-solver))

(rv-verify
 #:name "ADD / ADDI / LUI"
 #:init-pc ADD-PC
 #:fuel 4
 #:microcode microcode
 #:solver default-solver
 #:spec (λ (res)
          (and (eq? (list-ref (list-ref res 0) 1) (bvadd val-rvpc (bv 4 XLEN)))
               (eq? (list-ref res 1) (bvadd val-immi val-src1))))
 #:assumptions #f)

(rv-verify
 #:name "SUB"
 #:init-pc SUB-PC
 #:fuel 2
 #:microcode microcode
 #:solver default-solver
 #:spec (λ (res)
          (and (eq? (list-ref (list-ref res 0) 1) (bvadd val-rvpc (bv 4 XLEN)))
               (eq? (list-ref res 1) (bvsub val-src1 val-immi))))
 #:assumptions #f)

(rv-verify
 #:name "AUIPC"
 #:init-pc AUIPC-PC
 #:fuel 8
 #:microcode microcode
 #:solver default-solver
 #:spec (λ (res)
          (and (eq? (list-ref (list-ref res 0) 1) (bvadd val-rvpc (bv 4 XLEN)))
               (eq? (list-ref res 1) (bvadd val-rvpc val-immi))))
 #:assumptions #f)

(rv-verify
 #:name "JAL"
 #:init-pc JAL-PC
 #:fuel 8
 #:microcode microcode
 #:solver default-solver
 #:spec (λ (res)
          (and (eq? (list-ref (list-ref res 0) 1) (bvadd val-rvpc val-immi))
               (eq? (list-ref res 1) (bvadd val-rvpc (bv 4 XLEN)))))
 #:assumptions (λ (mem)
                 (assume (eq? (bv 0 2) (extract 1 0 (list-ref mem 1))))))

(printf "\nVerification suite finished.\n")
