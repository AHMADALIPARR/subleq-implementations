#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only
;;
;; SUBLEQ raw image disassembler with control-flow analysis.
;;
;; Reads space-separated integers and prints:
;;   - one instruction per triple with pattern hints
;;   - reachable set from PC=0
;;   - basic blocks and their successors
;;
;; Control-flow model (conservative):
;;   - Fall-through edge to pc+3 always exists unless the instruction
;;     is a forced halt/trap (a<0 and b<0, or a=-2).
;;   - Branch edge to c exists when c >= 0 and c != pc+3.
;;   - Both edges are marked possible; we do not yet solve for the
;;     sign of the subtraction result.

(require racket/port racket/string racket/file racket/format
         racket/list racket/set racket/hash)

(define (read-image path)
  (define text (if path (file->string path) (port->string (current-input-port))))
  (filter number? (map string->number (string-split text))))

(define (hint pc a b c)
  (cond
    [(and (< a 0) (< b 0)) "  ; halt"]
    [(= a -2) "  ; FlashAttention / coprocessor trap"]
    [(= a -1) "  ; input stream"]
    [(= b -1) "  ; output stream"]
    [(and (= a b) (= c (+ pc 3))) "  ; zero cell"]
    [(and (= a b) (>= c 0) (not (= c (+ pc 3)))) "  ; unconditional jump"]
    [(and (>= a 0) (>= b 0) (< c 0)) "  ; branch-to-halt"]
    [else ""]))

;; Build instruction map: pc -> (a b c)
(define (instructions image)
  (for/hash ([pc (in-range 0 (- (length image) 2) 3)])
    (values pc (list (list-ref image pc)
                     (list-ref image (+ pc 1))
                     (list-ref image (+ pc 2))))))

;; Successors of an instruction (conservative)
(define (successors pc a b c n)
  (define forced-stop? (or (and (< a 0) (< b 0)) (= a -2)))
  (define fall (and (not forced-stop?)
                    (< (+ pc 3) n)
                    (+ pc 3)))
  (define branch (and (>= c 0) (< c n) (not (= c (+ pc 3))) c))
  (filter values (list fall branch)))

;; Reachable PCs from 0
(define (reachable instrs n)
  (define seen (mutable-set))
  (define work (list 0))
  (let loop ()
    (unless (null? work)
      (define pc (car work))
      (set! work (cdr work))
      (when (and (not (set-member? seen pc)) (hash-has-key? instrs pc))
        (set-add! seen pc)
        (define-values (a b c) (apply values (hash-ref instrs pc)))
        (for ([s (successors pc a b c n)])
          (set! work (cons s work))))
      (loop)))
  (sort (set->list seen) <))

;; Basic blocks: maximal straight-line sequences
(define (basic-blocks instrs n reachable)
  (define leaders (mutable-set 0))
  (for ([pc reachable])
    (define-values (a b c) (apply values (hash-ref instrs pc)))
    (for ([s (successors pc a b c n)])
      (set-add! leaders s)))
  (define blocks '())
  (define seen (mutable-set))
  (for ([start (sort (set->list leaders) <)]
        #:when (set-member? reachable start)
        #:when (not (set-member? seen start)))
    (define block (list start))
    (let loop ([pc start])
      (set-add! seen pc)
      (define-values (a b c) (apply values (hash-ref instrs pc)))
      (define succs (successors pc a b c n))
      (cond
        [(and (= (length succs) 1)
              (= (first succs) (+ pc 3))
              (set-member? reachable (+ pc 3))
              (not (set-member? leaders (+ pc 3))))
         (set! block (append block (list (+ pc 3))))
         (loop (+ pc 3))]
        [else
         (set! blocks (cons (list block succs) blocks))])))
  (reverse blocks))

(define (disassemble image [code-end #f])
  (define n (length image))
  (define end (or code-end n))
  (define instrs (instructions (take image end)))
  (printf "; SUBLEQ image, ~a words total, ~a code words (~a instructions), ~a data cells\n" n end (/ end 3) (- n end))
  (for ([pc (sort (hash-keys instrs) <)])
    (define-values (a b c) (apply values (hash-ref instrs pc)))
    (printf "~a: subleq ~a, ~a, ~a~a\n"
            (~a pc #:min-width 4 #:align 'right #:pad-string "0")
            a b c (hint pc a b c)))
  (newline)
  (define reach (reachable instrs n))
  (printf "; reachable from 0: ~a\n" reach)
  (newline)
  (printf "; basic blocks\n")
  (for ([blk (basic-blocks instrs n reach)])
    (define body (first blk))
    (define succs (second blk))
    (printf "  ~a -> ~a\n" body succs)))

(module+ main
  (define args (current-command-line-arguments))
  (define path (if (zero? (vector-length args)) #f (vector-ref args 0)))
  (define code-end (if (> (vector-length args) 1)
                       (string->number (vector-ref args 1))
                       #f))
  (disassemble (read-image path) code-end))
