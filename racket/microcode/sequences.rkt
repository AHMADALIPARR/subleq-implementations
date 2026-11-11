#lang rosette
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only

;; Milestone 1 SUBLEQ sequences on the flat directive-machine memory.
;; Addresses are absolute cell indices (there is no register file distinct
;; from memory). Load and Store are moves between a named register cell and
;; a fixed memory cell. None of the sequences is self-modifying: the write
;; targets are data cells, and a branch target equals the fall-through PC
;; (c = PC + 3) except for the last instruction, whose c = −1 halts.
;;
;; Scratch Z is cleared on entry, so the post-condition does not assume a
;; pre-zeroed constant cell the way the sasm `K0` macros do. Z is cleared
;; again before the halt. That is the directive MOV/ADD idiom from
;; docs/macro-expansions.md, plus the initial clear.
;;
;; Each value is an exact integer. Operand cells are overwritten with the
;; symbolic or concrete inputs; the zeros in those positions are placeholders.

(provide (struct-out mc-seq)
         all-sequences
         seq-by-name
         operand-index
         image-length)

(struct mc-seq (name entry-pc fuel self-modifying? image operands doc)
  #:transparent)

;; operands is a list of (name index), index into image.

(define zero
  (mc-seq
   'zero
   0
   1
   #f
   ;;        X  FRAME
   '(3 3 -1  0  0)
   '((X 3) (FRAME 4))
   (string-append
    "Zero. One ordinary instruction: M[X] ← M[X] − M[X], then halt.\n"
    "  entry PC: 0\n"
    "  contract: cell X is the input and the output; FRAME and the instruction\n"
    "            cells are unchanged; M[X] = 0; status halted; PC = −1\n"
    "  fuel: 1 (necessary and sufficient)\n"
    "  self-modifying: no")))

(define move
  (mc-seq
   'move
   0
   5
   #f
   ;; clear Z, clear B, Z ← −A, B ← −Z, clear Z and halt
   '(15 15 3
     17 17 6
     16 15 9
     15 17 12
     15 15 -1
     ;; Z A B FRAME
     0 0 0 0)
   '((Z 15) (A 16) (B 17) (FRAME 18))
   (string-append
    "Move. M[B] ← M[A] via scratch Z (clear, negate, subtract, clear).\n"
    "  entry PC: 0\n"
    "  contract: A is the source; B is the destination; Z is scratch\n"
    "            (arbitrary on entry, 0 on exit); FRAME and the instruction\n"
    "            cells are unchanged; M[B] = M[A] (32-bit wrap, including −2^31)\n"
    "  fuel: 5 (necessary and sufficient)\n"
    "  self-modifying: no")))

(define add
  (mc-seq
   'add
   0
   4
   #f
   ;; clear Z, Z ← −A, B ← B − Z, clear Z and halt
   '(12 12 3
     13 12 6
     12 14 9
     12 12 -1
     ;; Z A B FRAME
     0 0 0 0)
   '((Z 12) (A 13) (B 14) (FRAME 15))
   (string-append
    "Add. M[B] ← wrap32(M[B] + M[A]) via scratch Z.\n"
    "  entry PC: 0\n"
    "  contract: A and B are inputs; B is the output; Z is scratch\n"
    "            (arbitrary on entry, 0 on exit); FRAME and the instruction\n"
    "            cells are unchanged\n"
    "  fuel: 4 (necessary and sufficient)\n"
    "  self-modifying: no")))

(define load
  (mc-seq
   'load
   0
   5
   #f
   ;; clear Z, clear RD, Z ← −SRC, RD ← −Z, clear Z and halt
   '(15 15 3
     16 16 6
     17 15 9
     15 16 12
     15 15 -1
     ;; Z RD SRC RC MEM2
     0 0 0 0 0)
   '((Z 15) (RD 16) (SRC 17) (RC 18) (MEM2 19))
   (string-append
    "Load-word (fixed absolute address). Register cell RD ← M[SRC].\n"
    "  entry PC: 0\n"
    "  contract: SRC is the memory operand (preserved); RD is the destination\n"
    "            register; RC is a register that must be preserved; MEM2 is a\n"
    "            second memory cell that must be preserved; Z is scratch\n"
    "            (arbitrary on entry, 0 on exit). Not register-indirect.\n"
    "  fuel: 5 (necessary and sufficient)\n"
    "  self-modifying: no")))

(define store
  (mc-seq
   'store
   0
   5
   #f
   ;; clear Z, clear DST, Z ← −RS, DST ← −Z, clear Z and halt
   '(15 15 3
     17 17 6
     16 15 9
     15 17 12
     15 15 -1
     ;; Z RS DST OTHER
     0 0 0 0)
   '((Z 15) (RS 16) (DST 17) (OTHER 18))
   (string-append
    "Store-word (fixed absolute address). M[DST] ← register cell RS.\n"
    "  entry PC: 0\n"
    "  contract: RS is the source register (preserved); DST is the memory cell\n"
    "            written; OTHER is a memory cell that must be preserved; Z is\n"
    "            scratch (arbitrary on entry, 0 on exit). Not register-indirect.\n"
    "  fuel: 5 (necessary and sufficient)\n"
    "  self-modifying: no")))

(define all-sequences (list zero move add load store))

(define (seq-by-name name)
  (findf (λ (s) (eq? (mc-seq-name s) name)) all-sequences))

(define (operand-index seq name)
  (define hit (assq name (mc-seq-operands seq)))
  (unless hit (error 'operand-index "no operand ~a in ~a" name (mc-seq-name seq)))
  (cadr hit))

(define (image-length seq)
  (length (mc-seq-image seq)))
