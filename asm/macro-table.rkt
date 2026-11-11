#lang racket/base
;; SPDX-License-Identifier: AGPL-3.0-or-later

;; Measures and checks every macro of asm/sasm.rkt on both machines.
;;
;; For each macro and each test case it assembles a small program
;; (JMP to the body, the macro, HALT), runs it on
;;   directive: racket/subleq.rkt          (run-subleq)
;;   original:  racket/subleq-original.rkt (execute-subleq/steps)
;; checks the resulting cells against an independent Racket computation, and
;; records how many instructions the macro executed (total minus the JMP,
;; the HALT and, for branch macros, the one instruction that records
;; whether the branch was taken).
;;
;;   racket asm/macro-table.rkt        prints the markdown table, exit 1 on any failure
;;   racket asm/macro-table.rkt --expansions   prints each macro's expansion
;;   raco test asm/macro-table.rkt     runs the same checks as rackunit tests

(require racket/list racket/sequence racket/string
         "sasm.rkt" (except-in "../racket/subleq.rkt" wrap32) "../racket/subleq-original.rkt")
(provide measure-all)

(define 2^32 (expt 2 32))

;; A test case.
;;  init     : hash name -> value (a number, a label symbol, or a list = an array)
;;             numbers are unsigned 32-bit words converted with `rep` unless raw?
;;  emit     : (hash name -> label) -> void, emits the macro under test
;;  expected : target -> hash name -> expected final value (list for arrays)
;;  inputs   : input words (directive)
;;  overhead : harness instructions executed inside the measured region
;;  static-overhead : harness instructions emitted inside the measured region
(struct tcase (name init emit expected inputs raw? overhead static-overhead))
(define (mk name init emit expected #:inputs [inputs '()] #:raw [raw? #f]
            #:overhead [ov 0] #:static-overhead [sov 0])
  (tcase name init emit expected inputs raw? ov sov))

;; the word representation on each machine
(define (rep target v) (if (eq? target 'directive) (wrap32 v) (modulo v 2^32)))

(define (run-case target c)
  (define-values (image syms)
    (assemble
     (λ ()
       (define body (fresh 'T))
       (define labels (make-hasheq))
       (JMP body)
       (label body)
       (for ([(k v) (in-hash (tcase-init c))])
         (define (cv x) (if (or (tcase-raw? c) (symbol? x)) x (rep target x)))
         (hash-set! labels k (if (list? v) (arr (length v) (map cv v) k) (var (cv v) k))))
       ((tcase-emit c) labels)
       (HALT))
     #:target target))
  (define-values (n mem r)
    (cond
      [(eq? target 'directive)
       (define r (run-subleq image (tcase-inputs c) 100000))
       (values (result-steps r) (list->vector (result-mem r)) r)]
      [else
       (define-values (mem n) (execute-subleq/steps image #:fuel 100000))
       (values n mem #f)]))
  (define cells
    (for/hasheq ([(k v) (in-hash (tcase-init c))])
      (define a (hash-ref syms k))
      (values k (if (list? v)
                    (for/list ([i (length v)]) (vector-ref mem (+ a i)))
                    (vector-ref mem a)))))
  (values (- n 2 (tcase-overhead c)) cells r))

(define (static-size target c)
  (- (length (filter (λ (s) (regexp-match? #rx"^  sq" s))
                     (listing (λ ()
                                (define labels (for/hasheq ([k (in-hash-keys (tcase-init c))]) (values k k)))
                                ((tcase-emit c) labels))
                              #:target target)))
     (tcase-static-overhead c)))

;; ---------------------------------------------------------------------------
(define words '(0 1 2 3 5 #x7fffffff #x80000000 #x80000001 #xfffffffe #xffffffff #x12345678 #xdeadbeef))
(define (pairs) (for*/list ([a words] [b words]) (list a b)))
(define (h . kvs) (for/hasheq ([p (in-slice 2 kvs)]) (values (car p) (cadr p))))
(define (rotl x n) (modulo (bitwise-ior (arithmetic-shift x n) (arithmetic-shift x (- n 32))) 2^32))

;; word-cases: inputs are words for cells a, b, ...
;;  mode 'wrap : expected results are taken mod 2^32 on both machines
;;  mode 'raw  : on original the expected result is the exact integer
;;               (these macros do not emulate wrap-around there)
(define (word-cases name xs emit f [mode 'wrap])
  (for/list ([x xs])
    (define init (for/hasheq ([v x] [k '(a b c d)]) (values k v)))
    (mk name init emit
        (λ (target)
          (for/hasheq ([(k v) (in-hash (f x))])
            (values k (if (and (eq? mode 'raw) (eq? target 'original)) v (rep target v))))))))

;; branch macros: emit (mac L yes); F := 1 if the branch was taken.
;; The harness adds two instructions (JMP done, INC F); one of them runs.
(define (branch-case name x mac taken?)
  (mk name (h 'a x 'F 0)
      (λ (L)
        (define yes (fresh 'Y)) (define done (fresh 'Y))
        (mac L yes)
        (JMP done)
        (label yes) (INC (hash-ref L 'F))
        (label done))
      (λ (target) (h 'a (rep target x) 'F (if taken? 1 0)))
      #:overhead 1 #:static-overhead 2))

(define both '(directive original))

(define specs
  (list
   (list "ZERO x" both
         (word-cases "ZERO" (map list words) (λ (L) (ZERO (hash-ref L 'a))) (λ (x) (h 'a 0))))
   (list "SUB a b" both
         (word-cases "SUB" (pairs) (λ (L) (SUB (hash-ref L 'a) (hash-ref L 'b)))
                     (λ (x) (h 'a (car x) 'b (- (cadr x) (car x)))) 'raw))
   (list "ADD a b" both
         (word-cases "ADD" (pairs) (λ (L) (ADD (hash-ref L 'a) (hash-ref L 'b)))
                     (λ (x) (h 'a (car x) 'b (+ (cadr x) (car x)))) 'raw))
   (list "MOV a b" both
         (word-cases "MOV" (pairs) (λ (L) (MOV (hash-ref L 'a) (hash-ref L 'b)))
                     (λ (x) (h 'a (car x) 'b (car x)))))
   (list "NEG-INTO a b" both
         (word-cases "NEG" (pairs) (λ (L) (NEG-INTO (hash-ref L 'a) (hash-ref L 'b)))
                     (λ (x) (h 'a (car x) 'b (- (car x)))) 'raw))
   (list "INC x" both
         (word-cases "INC" (map list words) (λ (L) (INC (hash-ref L 'a))) (λ (x) (h 'a (+ (car x) 1))) 'raw))
   (list "DEC x" both
         (word-cases "DEC" (map list words) (λ (L) (DEC (hash-ref L 'a))) (λ (x) (h 'a (- (car x) 1))) 'raw))
   (list "DOUBLE x" both
         (word-cases "DOUBLE" (map list words) (λ (L) (DOUBLE (hash-ref L 'a))) (λ (x) (h 'a (* 2 (car x)))) 'raw))
   (list "JLEZ x l" '(directive)        ; signed test on the directive machine
         (for/list ([x words])
           (branch-case "JLEZ" x (λ (L yes) (JLEZ (hash-ref L 'a) yes))
                        (<= (wrap32 x) 0))))
   (list "JLEZ x l" '(original)         ; canonical words are >= 0: taken only for 0
         (for/list ([x words])
           (branch-case "JLEZ" x (λ (L yes) (JLEZ (hash-ref L 'a) yes)) (= x 0))))
   (list "JSIGN x l" both
         (for/list ([x words])
           (branch-case "JSIGN" x (λ (L yes) (JSIGN (hash-ref L 'a) yes)) (>= x #x80000000))))
   (list "MOD32 x 3" '(original)
         (for/list ([x (list 0 1 #xffffffff #x100000000 #x1ffffffff #x200000000 (- (* 8 2^32) 1) (* 5 2^32))])
           (mk "MOD32" (h 'a x) (λ (L) (MOD32 (hash-ref L 'a) 3))
               (λ (target) (h 'a (modulo x 2^32))) #:raw #t)))
   (list "ADD32 a b" both
         (word-cases "ADD32" (pairs) (λ (L) (ADD32 (hash-ref L 'a) (hash-ref L 'b)))
                     (λ (x) (h 'a (car x) 'b (+ (cadr x) (car x))))))
   (list "SHL1 x" both
         (word-cases "SHL1" (map list words) (λ (L) (SHL1 (hash-ref L 'a))) (λ (x) (h 'a (* 2 (car x))))))
   (list "ROTL1 x" both
         (word-cases "ROTL1" (map list words) (λ (L) (ROTL1 (hash-ref L 'a))) (λ (x) (h 'a (rotl (car x) 1)))))
   (list "ROTR x 7" both
         (word-cases "ROTR7" (map list words) (λ (L) (ROTR (hash-ref L 'a) 7)) (λ (x) (h 'a (rotl (car x) 25)))))
   (list "MULK x 1664525" both
         (word-cases "MULK" (map (λ (w) (list w 0)) words)
                     (λ (L) (MULK (hash-ref L 'a) 1664525 (hash-ref L 'b)))
                     (λ (x) (h 'a (* 1664525 (car x)) 'b (car x)))))
   (list "UNPACK32 w bits v" both
         (for/list ([x words])
           (mk "UNPACK32" (h 'w x 'v 0 'bits (make-list 32 7))
               (λ (L) (UNPACK32 (hash-ref L 'w) (hash-ref L 'bits) (hash-ref L 'v)))
               (λ (target) (h 'w (rep target x)
                              'bits (for/list ([i 32]) (if (bitwise-bit-set? x i) 1 0)))))))
   (list "ACC+PARITY acc s (x y z)" both
         (for*/list ([x 2] [y 2] [z 2])
           (mk "PARITY3" (h 'acc 5 's 0 'x x 'y y 'z z)
               (λ (L) (ACC+PARITY (hash-ref L 'acc) (hash-ref L 's)
                                  (list (hash-ref L 'x) (hash-ref L 'y) (hash-ref L 'z))))
               (λ (target) (h 'acc (+ 5 (bitwise-xor x y z)) 's 0 'x x 'y y 'z z)))))
   (list "ACC+PARITY acc s (x y)" both
         (for*/list ([x 2] [y 2])
           (mk "PARITY2" (h 'acc 5 's 0 'x x 'y y)
               (λ (L) (ACC+PARITY (hash-ref L 'acc) (hash-ref L 's) (list (hash-ref L 'x) (hash-ref L 'y))))
               (λ (target) (h 'acc (+ 5 (bitwise-xor x y)) 's 0 'x x 'y y)))))
   (list "ACC+CH acc e f g" both
         (for*/list ([e 2] [f 2] [g 2])
           (mk "CH" (h 'acc 5 'e e 'f f 'g g)
               (λ (L) (ACC+CH (hash-ref L 'acc) (hash-ref L 'e) (hash-ref L 'f) (hash-ref L 'g)))
               (λ (target) (h 'acc (+ 5 (if (= e 1) f g)) 'e e 'f f 'g g)))))
   (list "ACC+MAJ acc s a b c" both
         (for*/list ([a 2] [b 2] [c 2])
           (mk "MAJ" (h 'acc 5 's 0 'a a 'b b 'c c)
               (λ (L) (ACC+MAJ (hash-ref L 'acc) (hash-ref L 's) (hash-ref L 'a) (hash-ref L 'b) (hash-ref L 'c)))
               (λ (target) (h 'acc (+ 5 (if (>= (+ a b c) 2) 1 0)) 'a a 'b b 'c c)))))
   (list "IN x" '(directive)
         (list (mk "IN" (h 'a 0) (λ (L) (IN (hash-ref L 'a))) (λ (t) (h 'a 42)) #:inputs '(42))))
   (list "OUT x" '(directive)
         (list (mk "OUT" (h 'a 9) (λ (L) (OUT (hash-ref L 'a))) (λ (t) (h 'a 9)))))
   (list "TRAP code" '(directive)
         (list (mk "TRAP" (h 'a 0) (λ (L) (TRAP 5)) (λ (t) (h 'a 0)))))
   (list "HALT" both
         (list (mk "HALT" (h 'a 0) (λ (L) (HALT)) (λ (t) (h 'a 0)))))
   (list "LOAD-NEXT ptr dst" both
         (list (mk "LOAD" (h 'p 'src 'd 0 'src 77)
                   (λ (L) (LOAD-NEXT (hash-ref L 'p) (hash-ref L 'd)))
                   (λ (t) (h 'd 77 'src 77)) #:raw #t)))
   (list "STORE-NEXT src ptr" both
         (list (mk "STORE" (h 'p 'd 'd 0 'src 77)
                   (λ (L) (STORE-NEXT (hash-ref L 'src) (hash-ref L 'p)))
                   (λ (t) (h 'd 77 'src 77)) #:raw #t)))))

;; Extra checks for the I/O cases, which are about status and output.
(define (io-ok? c r)
  (cond [(not r) #t]
        [(equal? (tcase-name c) "OUT") (equal? (result-output r) '(9))]
        [(equal? (tcase-name c) "IN") (eq? (result-status r) 'halted)]
        [(equal? (tcase-name c) "TRAP") (and (eq? (result-status r) 'trap) (= (result-code r) 5))]
        [else (eq? (result-status r) 'halted)]))

;; measure-all : -> list of (name target static min max ncases failures)
(define (measure-all)
  (for*/list ([s specs] [target (cadr s)])
    (define cases (caddr s))
    (define-values (costs fails)
      (for/fold ([costs '()] [fails '()]) ([c cases])
        (define-values (n0 cells r) (run-case target c))
        ;; TRAP and HALT stop the machine themselves: the harness HALT does not run
        (define n (if (member (tcase-name c) '("TRAP" "HALT")) (+ n0 1) n0))
        (define e ((tcase-expected c) target))
        (define ok (and (for/and ([(k v) (in-hash e)]) (equal? (hash-ref cells k) v)) (io-ok? c r)))
        (values (cons n costs) (if ok fails (cons (list (tcase-name c) (tcase-init c) cells) fails)))))
    (list (car s) target (static-size target (car cases))
          (apply min costs) (apply max costs) (length cases) fails)))

;; Expansions with symbolic operands, for docs/whitepaper.md.
;; K-1 is the constant cell -1, K0 is Z, Lnn/Hnn/... are generated labels.
(define expansion-specs
  (list (list "ADD a b" both (λ () (ADD 'a 'b)))
        (list "MOV a b" both (λ () (MOV 'a 'b)))
        (list "ADD32 a b" both (λ () (ADD32 'a 'b)))
        (list "MOD32 x 2" '(original) (λ () (MOD32 'x 2)))
        (list "SHL1 x" both (λ () (SHL1 'x)))
        (list "JSIGN x l" both (λ () (JSIGN 'x 'l)))
        (list "ROTL1 x" both (λ () (ROTL1 'x)))
        (list "MULK x 5 t" both (λ () (MULK 'x 5 't)))
        (list "IN x" '(directive) (λ () (IN 'x)))
        (list "OUT x" '(directive) (λ () (OUT 'x)))
        (list "TRAP 1" '(directive) (λ () (TRAP 1)))
        (list "HALT" both (λ () (HALT)))
        (list "LOAD-NEXT p d" both (λ () (LOAD-NEXT 'p 'd)))
        (list "STORE-NEXT s p" both (λ () (STORE-NEXT 's 'p)))
        (list "ACC+PARITY acc s (x y z)" both (λ () (ACC+PARITY 'acc 's '(x y z))))
        (list "ACC+CH acc e f g" both (λ () (ACC+CH 'acc 'e 'f 'g)))
        (list "ACC+MAJ acc s a b c" both (λ () (ACC+MAJ 'acc 's 'a 'b 'c)))
        (list "UNPACK32 w bits v (first lines)" both (λ () (UNPACK32 'w 'bits 'v)))))

(define (print-expansions)
  (printf "<!-- SPDX-License-Identifier: AGPL-3.0-or-later -->\n")
  (printf "# sasm macro expansions\n\n")
  (printf "Generated by `racket asm/macro-table.rkt --expansions > docs/macro-expansions.md`.\n")
  (printf "Each line `sq a b c` is one SUBLEQ instruction (M[b] -= M[a]; if M[b] <= 0 goto c).\n")
  (printf "`next` is the following instruction, `Kv` is the constant cell holding v (`K0` is Z),\n")
  (printf "names such as `M1`, `P3`, `U7` are labels generated by the assembler, and `x+5` is cell x + 5.\n")
  (printf "Costs are in docs/whitepaper.md, section 4.\n")
  (for* ([e expansion-specs] [target (cadr e)])
    (define lines (listing (caddr e) #:target target))
    (define shown (if (> (length lines) 24) (append (take lines 24) (list "  ...")) lines))
    (printf "\n`~a` on ~a:\n\n```\n~a\n```\n" (car e) target (string-join shown "\n"))))

(module+ main
  (when (member "--expansions" (vector->list (current-command-line-arguments)))
    (print-expansions)
    (exit 0))
  (define rows (measure-all))
  (printf "| Macro | Machine | Static size (instructions) | Executed instructions (min-max) | Cases checked |\n")
  (printf "|---|---|---|---|---|\n")
  (for ([r rows])
    (printf "| `~a` | ~a | ~a | ~a | ~a~a |\n" (list-ref r 0) (list-ref r 1) (list-ref r 2)
            (if (= (list-ref r 3) (list-ref r 4)) (list-ref r 3) (format "~a-~a" (list-ref r 3) (list-ref r 4)))
            (list-ref r 5) (if (null? (list-ref r 6)) ", all correct" (format " FAILED: ~s" (list-ref r 6)))))
  (unless (andmap (λ (r) (null? (list-ref r 6))) rows) (exit 1)))

(module+ test
  (require rackunit)
  (for ([r (measure-all)])
    (check-equal? (list-ref r 6) '() (format "~a on ~a" (list-ref r 0) (list-ref r 1)))))
