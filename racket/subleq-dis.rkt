#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only
;;
;; SUBLEQ raw image disassembler.
;; Reads space-separated integers from stdin or a file and prints
;; one instruction per triple, with light pattern hints.

(require racket/port racket/string racket/file racket/format)

(define (read-image path)
  (define text (if path (file->string path) (port->string (current-input-port))))
  (map string->number (string-split text)))

(define (hint pc a b c)
  (cond
    [(and (< a 0) (< b 0)) "  ; halt"]
    [(= a -2) "  ; trap"]
    [(= a -1) "  ; input"]
    [(= b -1) "  ; output"]
    [(and (= a b) (= c (+ pc 3))) "  ; zero"]
    [(and (= a b) (>= c 0) (not (= c (+ pc 3)))) "  ; jump"]
    [else ""]))

(define (disassemble image)
  (printf "; SUBLEQ image, ~a words\n" (length image))
  (for ([pc (in-range 0 (- (length image) 2) 3)])
    (define a (list-ref image pc))
    (define b (list-ref image (+ pc 1)))
    (define c (list-ref image (+ pc 2)))
    (printf "~a: subleq ~a, ~a, ~a~a\n"
            (~a pc #:min-width 4 #:align 'right #:pad-string "0")
            a b c (hint pc a b c))))

(module+ main
  (define args (current-command-line-arguments))
  (define path (if (zero? (vector-length args)) #f (vector-ref args 0)))
  (disassemble (read-image path)))
