#lang rosette
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only

;; Rosette model of the directive SUBLEQ machine.
;;
;; The semantics are semantics/subleq-spec.md, the same rules
;; lean/Subleq/Machine.lean, racket/subleq.rkt, factor/subleq.factor and
;; forth/subleq.fs execute. This is a re-implementation, not an adapter:
;; racket/subleq.rkt decides control with Racket `cond` and mutates a vector,
;; which does not merge symbolic branches. verify.rkt checks concrete
;; agreement with run-subleq.
;;
;; Width. Every memory cell is a 32-bit two's-complement bitvector. `bvsub`
;; is Lean's wrap32(b − a) for every pair of 32-bit values, and `bvsle` is
;; the signed `r ≤ 0` test. The PC is the same width. PC arithmetic in this
;; milestone stays inside a few small addresses or the sentinel −1, where
;; bitvector addition matches Lean's integer addition. Cells are wrapped when
;; an image is loaded, matching `init`.
;;
;; Precedence, matching Lean `step` (not a separate halt-sentinel opcode):
;;   1. status ≠ running → state is unchanged
;;   2. PC < 0 or PC + 2 ≥ N → fault:pc-out-of-range, STEPS unchanged
;;   3. a = −2 → trap, CODE = b, STEPS + 1, PC and memory unchanged (c ignored)
;;   4. a = −1 → input, or fault:input-exhausted if IN is empty (STEPS unchanged)
;;   5. b < 0 → output of read(a), PC + 3, STEPS + 1
;;   6. otherwise r = wrap32(read(b) − read(a)), write b, branch to absolute c
;;      iff r ≤ 0, else PC + 3, STEPS + 1
;;   Halt rule: after input, output, or ordinary, c = −1 sets status halted.
;; Fetch reads a, b and c before any write.
;;
;; Symbolic execution is fail-closed at a symbolic PC: milestone 1 sequences
;; keep the PC concrete by using a fall-through branch target (c = PC + 3)
;; until the halting instruction. A symbolic fetch raises an error instead of
;; returning a guessed state.

(require racket/list)

(provide W
         int->bv
         bv->signed
         (struct-out machine)
         make-machine
         machine-summary
         step
         run)

(define W 32)
(define MOD32 4294967296)
(define BIAS 2147483648) ; 2^31

(define (wrap32-int x)
  (- (modulo (+ x BIAS) MOD32) BIAS))

;; Exact integer → wrapped 32-bit bitvector. Same map as Lean `wrap32`.
(define (int->bv x)
  (integer->bitvector (wrap32-int x) (bitvector W)))

;; Bitvector → signed exact integer in [−2^31, 2^31).
(define (bv->signed v)
  (bitvector->integer v))

(struct machine (mem pc in out status code steps) #:transparent)

(define (make-machine mem [inputs '()])
  (machine mem (bv 0 W) inputs '() 'running (bv 0 W) 0))

(define (machine-summary m)
  (define (show v)
    (if (concrete? v) (bv->signed v) v))
  (format "status ~a pc ~a steps ~a code ~a out ~a mem ~a"
          (machine-status m)
          (if (concrete? (machine-pc m)) (bitvector->integer (machine-pc m)) (machine-pc m))
          (machine-steps m)
          (show (machine-code m))
          (map show (machine-out m))
          (map show (machine-mem m))))

(define (mem-ref mem addr)
  (cond
    [(concrete? addr)
     (define i (bitvector->integer addr))
     (if (and (<= 0 i) (< i (length mem)))
         (list-ref mem i)
         (bv 0 W))]
    [else
     (for/fold ([acc (bv 0 W)]) ([cell (in-list mem)] [i (in-naturals)])
       (if (bveq addr (integer->bitvector i (bitvector W))) cell acc))]))

(define (mem-set mem addr val)
  (cond
    [(concrete? addr)
     (define i (bitvector->integer addr))
     (if (and (<= 0 i) (< i (length mem)))
         (list-set mem i val)
         mem)]
    [else
     (for/list ([cell (in-list mem)] [i (in-naturals)])
       (if (bveq addr (integer->bitvector i (bitvector W))) val cell))]))

(define (fetch-fault? pc n)
  (unless (concrete? pc)
    (error 'machine "symbolic PC at fetch; refusing to guess a state"))
  (define i (bitvector->integer pc))
  (or (< i 0) (>= (+ i 2) n)))

;; Fall-through targets stay a concrete PC so the next fetch is well-defined
;; even when the branch condition is a symbolic bitvector.
(define (pc-next r c pc)
  (define fall (bvadd pc (bv 3 W)))
  (if (and (concrete? c) (concrete? fall)
           (= (bitvector->integer c) (bitvector->integer fall)))
      fall
      (if (bvsle r (bv 0 W)) c fall)))

(define (apply-halt c st)
  (cond
    [(not (concrete? c))
     (if (bveq c (bv -1 W))
         (struct-copy machine st [status 'halted])
         st)]
    [(bveq c (bv -1 W)) (struct-copy machine st [status 'halted])]
    [else st]))

(define (do-trap st b)
  (struct-copy machine st
               [status 'trap]
               [code b]
               [steps (add1 (machine-steps st))]))

(define (do-input st mem b c)
  (define in (machine-in st))
  (if (null? in)
      (struct-copy machine st [status 'fault:input-exhausted])
      (apply-halt
       c
       (struct-copy machine st
                    [mem (mem-set mem b (car in))]
                    [in (cdr in)]
                    [pc (bvadd (machine-pc st) (bv 3 W))]
                    [steps (add1 (machine-steps st))]))))

(define (do-output st mem a c)
  (apply-halt
   c
   (struct-copy machine st
                [out (append (machine-out st) (list (mem-ref mem a)))]
                [pc (bvadd (machine-pc st) (bv 3 W))]
                [steps (add1 (machine-steps st))])))

(define (do-ordinary st mem pc a b c)
  (define r (bvsub (mem-ref mem b) (mem-ref mem a)))
  (apply-halt
   c
   (struct-copy machine st
                [mem (mem-set mem b r)]
                [pc (pc-next r c pc)]
                [steps (add1 (machine-steps st))])))

(define (step st)
  (cond
    [(not (eq? (machine-status st) 'running)) st]
    [(fetch-fault? (machine-pc st) (length (machine-mem st)))
     (struct-copy machine st [status 'fault:pc-out-of-range])]
    [else
     (define mem (machine-mem st))
     (define pc (machine-pc st))
     ;; Read all three operands before any write.
     (define a (mem-ref mem pc))
     (define b (mem-ref mem (bvadd pc (bv 1 W))))
     (define c (mem-ref mem (bvadd pc (bv 2 W))))
     (cond
       [(not (and (concrete? a) (concrete? b)))
        (error 'machine "symbolic opcode; milestone 1 sequences use a concrete instruction stream")]
       [(bveq a (bv -2 W)) (do-trap st b)]
       [(bveq a (bv -1 W)) (do-input st mem b c)]
       [(bvslt b (bv 0 W)) (do-output st mem a c)]
       [else (do-ordinary st mem pc a b c)])]))

;; `run fuel` attempts at most `fuel` steps. A non-running state is final.
;; Fuel exhausted while still running becomes step-limit (the runner, not the
;; instruction). Matches Lean `run` and racket/subleq.rkt.
(define (run fuel st)
  (cond
    [(not (eq? (machine-status st) 'running)) st]
    [(<= fuel 0) (struct-copy machine st [status 'step-limit])]
    [else (run (sub1 fuel) (step st))]))
