#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only
;;
;; Firmware-aware decompiler.
;; Recognizes multi-instruction SUBLEQ sequences as higher-level
;; firmware operations (virtual register writes, vector installs,
;; exception dispatch, software iret).

(require racket/list racket/format racket/hash
         "subleq-firmware.rkt")

(provide decompile-firmware)

(define (addr->name syms addr)
  (or (for/first ([(k v) (in-hash syms)] #:when (= v addr))
        (if (symbol? k) k #f))
      ;; IDT is an array; report IDT+n for offsets
      (let ([idt (hash-ref syms 'IDT #f)])
        (and idt (<= idt addr) (< addr (+ idt 20))
             (string->symbol (format "IDT+~a" (- addr idt)))))
      addr))

;; Look ahead up to n triples
(define (peek triples i n)
  (for/list ([j (in-range n)]
             #:when (< (+ i j) (length triples)))
    (list-ref triples (+ i j))))

;; Try to match a MOV (4 instructions): ZERO dest; sq src Z; sq Z dest; sq Z Z
(define (match-mov triples i syms)
  (define seq (peek triples i 4))
  (and (= (length seq) 4)
       (let ([t0 (list-ref seq 0)]
             [t1 (list-ref seq 1)]
             [t2 (list-ref seq 2)]
             [t3 (list-ref seq 3)])
         (and (= (list-ref t0 0) (list-ref t0 1))          ; ZERO dest
              (= (list-ref t1 1) (hash-ref syms 'K0))     ; sq src Z
              (= (list-ref t2 0) (hash-ref syms 'K0))     ; sq Z dest
              (= (list-ref t2 1) (list-ref t0 0))
              (= (list-ref t3 0) (hash-ref syms 'K0))     ; sq Z Z
              (= (list-ref t3 1) (hash-ref syms 'K0))
              (let ([dest (addr->name syms (list-ref t0 0))]
                    [src  (addr->name syms (list-ref t1 0))])
                (and dest src
                     (list 'mov dest src)))))))

;; Try to match ZERO + HALT as software iret
(define (match-iret triples i syms)
  (define seq (peek triples i 2))
  (and (= (length seq) 2)
       (let ([t0 (list-ref seq 0)]
             [t1 (list-ref seq 1)])
         (and (= (list-ref t0 0) (list-ref t0 1))
              (eq? (addr->name syms (list-ref t0 0)) 'CURRENT_EXC)
              (< (list-ref t1 0) 0)
              (< (list-ref t1 1) 0)
              (list 'iret)))))

;; Unconditional jump
(define (match-jump triples i syms)
  (define t (list-ref triples i))
  (and (= (list-ref t 0) (list-ref t 1))
       (>= (list-ref t 2) 0)
       (not (= (list-ref t 2) (+ (* i 3) 3)))
       (list 'jump (addr->name syms (list-ref t 2)))))

(define (decompile-firmware)
  (define-values (image syms code-end) (assemble-firmware))
  (define triples
    (for/list ([pc (in-range 0 code-end 3)])
      (list (list-ref image pc)
            (list-ref image (+ pc 1))
            (list-ref image (+ pc 2)))))
  (printf "; Firmware-aware decompilation\n")
  (printf "; ~a code words, ~a instructions, ~a data cells\n\n"
          code-end (length triples) (- (length image) code-end))
  (define i 0)
  (define ops '())
  (let loop ()
    (when (< i (length triples))
      (define pc (* i 3))
      (define matched
        (or (match-mov triples i syms)
            (match-iret triples i syms)
            (match-jump triples i syms)))
      (cond
        [matched
         (printf "~a: ~a\n" (~a pc #:min-width 4 #:align 'right #:pad-string "0") matched)
         (set! ops (cons matched ops))
         (set! i (+ i (if (eq? (car matched) 'mov) 4
                          (if (eq? (car matched) 'iret) 2 1))))]
        [else
         (define t (list-ref triples i))
         (printf "~a: raw ~a ~a ~a\n"
                 (~a pc #:min-width 4 #:align 'right #:pad-string "0")
                 (list-ref t 0) (list-ref t 1) (list-ref t 2))
         (set! i (add1 i))])
      (loop)))
  (newline)
  (printf "; Higher-level operations recovered: ~a\n" (length ops))
  (for ([op (reverse ops)])
    (printf "  ~a\n" op)))

(module+ main
  (decompile-firmware))
