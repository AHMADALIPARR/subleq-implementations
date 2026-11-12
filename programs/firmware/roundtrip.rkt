#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only
;;
;; Round-trip binary equivalence for the SUBLEQ firmware.
;;
;; source → assemble → image
;;        → extract code triples (stop at code/data boundary)
;;        → re-emit as flat words
;;        → bit-exact comparison against original code portion
;;
;; Also checks the post-condition invariants of the demo run.

(require racket/list racket/format
         "subleq-firmware.rkt"
         "../../racket/subleq.rkt")

(define (code-triples image code-end)
  (for/list ([pc (in-range 0 code-end 3)])
    (list (list-ref image pc)
          (list-ref image (+ pc 1))
          (list-ref image (+ pc 2)))))

(define (flatten-triples triples)
  (apply append triples))

(define (run-roundtrip)
  (define-values (image syms code-end) (assemble-firmware))
  (define n (length image))
  (printf "Image: ~a words\n" n)
  (printf "Code ends at: ~a (~a instructions)\n" code-end (/ code-end 3))
  (printf "Data cells: ~a\n" (- n code-end))

  ;; Round-trip the code portion
  (define triples (code-triples image code-end))
  (define rebuilt (flatten-triples triples))
  (define original-code (take image code-end))
  (define match? (equal? rebuilt original-code))
  (printf "Code round-trip bit-exact: ~a\n" match?)
  (unless match?
    (error 'roundtrip "code portion mismatch"))

  ;; Full image round-trip (code + data preserved)
  (define rebuilt-full (append rebuilt (drop image code-end)))
  (define full-match? (equal? rebuilt-full image))
  (printf "Full image round-trip bit-exact: ~a\n" full-match?)
  (unless full-match?
    (error 'roundtrip "full image mismatch"))

  ;; Execute and check invariants
  (define r (run-subleq image '() 10000))
  (define mem (list->vector (result-mem r)))
  (define status (result-status r))
  (define steps (result-steps r))
  (define exc (vector-ref mem (hash-ref syms 'CURRENT_EXC)))
  (define cr0 (vector-ref mem (hash-ref syms 'CR0)))
  (define cr4 (vector-ref mem (hash-ref syms 'CR4)))
  (define faddr (vector-ref mem (hash-ref syms 'FAULT_ADDR)))

  (printf "Execution: status=~a steps=~a\n" status steps)
  (printf "  CURRENT_EXC=~a (expected 0 after iret)\n" exc)
  (printf "  CR0=~a (expected 1)\n" cr0)
  (printf "  CR4=~a (expected 512)\n" cr4)
  (printf "  FAULT_ADDR=~a (expected 4660)\n" faddr)

  (unless (eq? status 'halted) (error 'invariants "not halted"))
  (unless (= exc 0) (error 'invariants "exception not cleared"))
  (unless (= cr0 1) (error 'invariants "CR0 wrong"))
  (unless (= cr4 #x200) (error 'invariants "CR4 wrong"))
  (unless (= faddr #x1234) (error 'invariants "FAULT_ADDR wrong"))

  (printf "All invariants hold.\n")
  (printf "Round-trip + invariants: PASS\n"))

(module+ main
  (run-roundtrip))
