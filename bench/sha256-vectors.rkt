#lang racket/base
;; Copyright (C) Ahmad <ahmedparr93@gmail.com>
;; SPDX-License-Identifier: AGPL-3.0-only

;; SHA-256 in SUBLEQ against NIST test vectors: "abc" and the 448-bit
;; message are the examples of FIPS 180-2 Appendix B.1 and B.2; the empty
;; message is the Len = 0 entry of NIST CAVP SHA256ShortMsg.rsp. (All three
;; digests also agree with GNU coreutils sha256sum on the box used here.)
;;   ""          e3b0c442 98fc1c14 9afbf4c8 996fb924 27ae41e4 649b934c a495991b 7852b855
;;   "abc"       ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad
;;   448-bit     248d6a61 d20638b8 e5c02693 0c3e6039 a33ce459 64ff2167 f6ecedd4 19db06c1
;;   ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", two blocks)
;;
;; Directive machine: the same image (programs/sha256.rkt, 'directive) is run by
;;   racket racket/subleq.rkt, gforth forth/main-large.fs,
;;   factor factor/subleq-main.factor, and the Lean executable
;; (each a separate process). Each must exit 0, halt, print the expected
;; digest as its 8 output words, and print exactly the same canonical result
;; (all six lines, including the whole memory) as the in-process reference.
;; The original machine runs the 'original image in process
;; (racket/subleq-original.rkt); its digest is read from the H cells.
;;
;; Usage: racket bench/sha256-vectors.rkt [--only racket,forth,factor,lean]
;; Exit status 0 only if every check passed.

(require racket/list racket/string racket/file
         "common.rkt" "../programs/sha256.rkt"
         "../racket/subleq.rkt" "../racket/subleq-original.rkt")

(define vectors
  (list (list "empty string" #""
              "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
        (list "\"abc\"" #"abc"
              "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
        (list "448-bit \"abcdbcdecdefdefg...nopq\"" #"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
              "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")))

(define only
  (let ([a (current-command-line-arguments)])
    (if (and (= (vector-length a) 2) (equal? (vector-ref a 0) "--only"))
        (string-split (vector-ref a 1) ",")
        #f)))
(define active (if only (filter (λ (p) (member (car p) only)) impls) impls))

(define fuel 1000000000)
(define failures 0)
(define checks 0)
(define (check! ok what)
  (set! checks (add1 checks))
  (unless ok (set! failures (add1 failures)) (printf "FAIL: ~a\n" what)))

(define-values (dir-image _syms) (sha256-image #:target 'directive))
(printf "SHA-256 image for the directive machine: ~a cells (same image for every message)\n\n" (length dir-image))
(printf "| Vector | Machine / implementation | Digest printed | Matches NIST | STEPS |\n|---|---|---|---|---|\n")
(define tmp (make-temporary-file "subleq-sha256-~a.txt"))
(for ([v vectors])
  (define-values (name msg expected) (apply values v))
  (define inputs (sha256-input msg))
  ;; in-process reference
  (define ref (run-subleq dir-image inputs fuel))
  (define ref-hex (digest-words->hex (result-output ref)))
  (check! (and (eq? (result-status ref) 'halted) (equal? ref-hex expected)) (format "~a racket in-process" name))
  (printf "| ~a | directive / racket (in-process reference) | `~a` | ~a | ~a |\n"
          name ref-hex (if (equal? ref-hex expected) "yes" "NO") (result-steps ref))
  (define canon (result->canonical ref))
  (write-input-file tmp dir-image inputs fuel)
  (for ([p active])
    (define-values (code out err ms) (run-impl ((cdr p) (path->string tmp))))
    (define parsed (parse-canonical out))
    (define hex (digest-words->hex (hash-ref parsed 'output)))
    (define same? (equal? out canon))
    (check! (and (eqv? code 0) (equal? (hash-ref parsed 'status) "halted") (equal? hex expected) same?)
            (format "~a ~a exit=~a status=~a same-as-reference=~a ~a" name (car p) code
                    (hash-ref parsed 'status) same? err))
    (printf "| ~a | directive / ~a | `~a` | ~a | ~a |\n" name (car p) hex
            (if (equal? hex expected) "yes" "NO") (hash-ref parsed 'steps)))
  ;; original machine
  (define-values (oimg osyms) (sha256-image #:target 'original #:message msg))
  (define-values (mem n) (execute-subleq/steps oimg))
  (define h (hash-ref osyms 'H))
  (define ohex (digest-words->hex (for/list ([j 8]) (vector-ref mem (+ h j)))))
  (check! (equal? ohex expected) (format "~a original" name))
  (printf "| ~a | original / racket/subleq-original.rkt (in-process) | `~a` | ~a | ~a |\n"
          name ohex (if (equal? ohex expected) "yes" "NO") n))
(delete-file tmp)
(printf "\nsha256-vectors: implementations=directive:racket-in-process,~a,original checks=~a failures=~a\n"
        (string-join (map car active) ",") checks failures)
(exit (if (zero? failures) 0 1))
