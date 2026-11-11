#lang racket/base
;; SPDX-License-Identifier: AGPL-3.0-or-later

;; SHA-256 (FIPS 180-4) as a SUBLEQ program, generated with asm/sasm.rkt
;; for both machines:
;;
;;  'directive (semantics/subleq-spec.md)
;;     The image does not depend on the message. The input stream is
;;     L, b0, ..., b(L-1)   (message length in bytes, then one byte per word).
;;     The program pads the message itself, processes 64-byte blocks one at
;;     a time, writes the digest as 8 output words (H0..H7, as signed 32-bit
;;     values) and halts with c = -1.
;;
;;  'original (racket/subleq-original.rkt)
;;     No I/O, so the message is placed in the image (a length cell and one
;;     cell per byte) and read with the self-modifying LOAD-NEXT macro. The
;;     digest is left in memory at the cells labelled H (canonical unsigned
;;     values). 32-bit wrap-around is emulated with MOD32 after additions.
;;
;; Apart from those two points (I/O and wrap emulation) both images run the
;; same algorithm with the same code structure:
;;  * words are unpacked into bit-sliced form (32 cells of 0/1) with
;;    UNPACK32, so ROTR/SHR cost nothing (they are index remappings);
;;  * Sigma0/Sigma1/sigma0/sigma1/Ch/Maj are computed bit by bit and summed
;;    straight into a word with Horner's rule (acc := 2*acc + bit);
;;  * the 48 schedule steps and the 64 rounds are fully unrolled; the block
;;    loop is the only loop.
;; Limit: messages shorter than 2^28 bytes (the bit length must fit in the
;; low length word and in a positive 32-bit cell).

(require racket/list "../asm/sasm.rkt")

(provide sha256-image sha256-input digest-words->hex
         H-init K-table)

;; --- constants, computed rather than typed in -------------------------------
(define (iroot n k)                 ; floor of the k-th root of n, exact
  (let loop ([lo 0] [hi (add1 (arithmetic-shift 1 (add1 (quotient (integer-length n) k))))])
    (if (> (- hi lo) 1)
        (let ([mid (quotient (+ lo hi) 2)])
          (if (<= (expt mid k) n) (loop mid hi) (loop lo mid)))
        lo)))
(define (primes n)
  (let loop ([p 2] [acc '()])
    (cond [(= (length acc) n) (reverse acc)]
          [(for/and ([q acc]) (positive? (remainder p q))) (loop (add1 p) (cons p acc))]
          [else (loop (add1 p) acc)])))
;; first 32 bits of the fractional parts of square / cube roots
(define H-init (for/list ([p (primes 8)])  (modulo (iroot (* p (expt 2 64)) 2) (expt 2 32))))
(define K-table (for/list ([p (primes 64)]) (modulo (iroot (* p (expt 2 96)) 3) (expt 2 32))))
(unless (and (= (first H-init) #x6a09e667) (= (last H-init) #x5be0cd19)
             (= (first K-table) #x428a2f98) (= (last K-table) #xc67178f2))
  (error 'sha256 "constant derivation is wrong"))

;; --- the program ------------------------------------------------------------
;; message : bytes, only used on 'original (placed in the image)
(define (program message)
  (define dir? (directive?))
  ;; data
  (define H (arr 8 H-init 'H))
  (define Kc (arr 64 K-table 'KT))
  (define W (arr 64 0 'W))
  (define WB (for/vector ([t 62]) (arr 32)))            ; bits of W[t], t = 0..61
  (define A-bits (for/vector ([t 66]) (arr 32)))        ; A_t, t = -2..63
  (define E-bits (for/vector ([t 66]) (arr 32)))        ; E_t, t = -2..63
  (define (AB t) (vector-ref A-bits (+ t 2)))
  (define (EB t) (vector-ref E-bits (+ t 2)))
  (define AWs (arr 64 0 'AW))                           ; AW_t, t = 1..64
  (define EWs (arr 64 0 'EW))                           ; EW_t, t = 1..64
  ;; a,e words: for t <= 0 they are the H cells themselves
  (define (AW t) (if (<= t 0) (at H (- t)) (at AWs (- t 1))))
  (define (EW t) (if (<= t 0) (at H (- 4 t)) (at EWs (- t 1))))
  (define LEN (var (if dir? 0 (bytes-length message)) 'LEN))
  (define REM (var 0 'REM))
  (define BITLEN (var 0 'BITLEN))
  (define FLAG (var 0 'FLAG))        ; 1 once the 0x80 byte has been produced
  (define ISFINAL (var 0 'ISFINAL))
  (define BYTE (var 0 'BYTE))
  (define S (var 0 'S))              ; parity scratch, kept 0
  (define S2 (var 0 'S2))            ; majority scratch
  (define V (var 0 'V))              ; unpack scratch
  (define T1 (var 0 'T1))
  (define PTR (and (not dir?) (var 'MSG 'PTR)))
  (unless dir?
    (arr (max 1 (bytes-length message)) (if (zero? (bytes-length message)) 0 (bytes->list message)) 'MSG))
  (define (bit base i) (at base (modulo i 32)))

  (define (get-byte)
    (define nomsg (fresh 'B)) (define emit80 (fresh 'B)) (define got (fresh 'B))
    (JLEZ REM nomsg)
    (if dir? (IN BYTE) (LOAD-NEXT PTR BYTE))
    (DEC REM)
    (JMP got)
    (label nomsg)
    (ZERO BYTE)
    (JLEZ FLAG emit80)
    (JMP got)
    (label emit80)
    (sq (K -128) BYTE)               ; BYTE := 128 (0x80)
    (INC FLAG)
    (label got))

  (define (word-from-bytes w)
    (ZERO w)
    (for ([k 4])
      (unless (zero? k) (for ([_ 8]) (DOUBLE w)))
      (get-byte)
      (ADD BYTE w)))

  ;; start
  (when dir? (IN LEN))
  (MOV LEN REM)
  (MOV LEN BITLEN) (DOUBLE BITLEN) (DOUBLE BITLEN) (DOUBLE BITLEN)
  (define block (label 'BLOCK))
  (for ([j 14]) (word-from-bytes (at W j)))
  (define notfinal (fresh 'F)) (define words-done (fresh 'F))
  (JLEZ FLAG notfinal)
  ;; final block: length words
  (ZERO (at W 14)) (MOV BITLEN (at W 15))
  (ZERO ISFINAL) (INC ISFINAL)
  (JMP words-done)
  (label notfinal)
  (word-from-bytes (at W 14)) (word-from-bytes (at W 15))
  (ZERO ISFINAL)
  (label words-done)

  ;; message schedule
  (for ([t 16]) (UNPACK32 (at W t) (vector-ref WB t) V))
  (for ([t (in-range 16 64)])
    (define wt (at W t))
    (define x2 (vector-ref WB (- t 2)))
    (define x15 (vector-ref WB (- t 15)))
    (ZERO wt)
    (for ([i (in-range 31 -1 -1)])
      (unless (= i 31) (DOUBLE wt))
      ;; sigma1(W[t-2]) = ROTR17 ^ ROTR19 ^ SHR10
      (ACC+PARITY wt S (append (list (bit x2 (+ i 17)) (bit x2 (+ i 19)))
                               (if (< (+ i 10) 32) (list (at x2 (+ i 10))) '())))
      ;; sigma0(W[t-15]) = ROTR7 ^ ROTR18 ^ SHR3
      (ACC+PARITY wt S (append (list (bit x15 (+ i 7)) (bit x15 (+ i 18)))
                               (if (< (+ i 3) 32) (list (at x15 (+ i 3))) '()))))
    (ADD (at W (- t 7)) wt) (ADD (at W (- t 16)) wt)
    (MOD32 wt 2)                                      ; < 4 * 2^32
    (when (<= t 61) (UNPACK32 wt (vector-ref WB t) V)))

  ;; working variables from H
  (UNPACK32 (at H 0) (AB 0) V) (UNPACK32 (at H 1) (AB -1) V) (UNPACK32 (at H 2) (AB -2) V)
  (UNPACK32 (at H 4) (EB 0) V) (UNPACK32 (at H 5) (EB -1) V) (UNPACK32 (at H 6) (EB -2) V)

  ;; 64 rounds
  (for ([t 64])
    (define e (EB t)) (define f (EB (- t 1))) (define g (EB (- t 2)))
    (define a (AB t)) (define b (AB (- t 1))) (define c (AB (- t 2)))
    ;; T1 = h + Sigma1(e) + Ch(e,f,g) + K[t] + W[t]
    (ZERO T1)
    (for ([i (in-range 31 -1 -1)])
      (unless (= i 31) (DOUBLE T1))
      (ACC+PARITY T1 S (list (bit e (+ i 6)) (bit e (+ i 11)) (bit e (+ i 25))))
      (ACC+CH T1 (at e i) (at f i) (at g i)))
    (ADD (EW (- t 3)) T1) (ADD (at Kc t) T1) (ADD (at W t) T1)
    (MOD32 T1 3)                                      ; < 5 * 2^32
    ;; new a = T1 + Sigma0(a) + Maj(a,b,c)
    (define an (AW (+ t 1)))
    (ZERO an)
    (for ([i (in-range 31 -1 -1)])
      (unless (= i 31) (DOUBLE an))
      (ACC+PARITY an S (list (bit a (+ i 2)) (bit a (+ i 13)) (bit a (+ i 22))))
      (ACC+MAJ an S2 (at a i) (at b i) (at c i)))
    (ADD T1 an)
    (MOD32 an 2)                                      ; < 3 * 2^32
    ;; new e = d + T1
    (define en (EW (+ t 1)))
    (MOV (AW (- t 3)) en) (ADD T1 en)
    (MOD32 en 1)                                      ; < 2 * 2^32
    (when (< t 63)
      (UNPACK32 en (EB (+ t 1)) V)
      (UNPACK32 an (AB (+ t 1)) V)))

  ;; H += working variables
  (for ([j 4])
    (ADD (AW (- 64 j)) (at H j)) (MOD32 (at H j) 1)
    (ADD (EW (- 64 j)) (at H (+ 4 j))) (MOD32 (at H (+ 4 j)) 1))
  (JLEZ ISFINAL block)
  (when dir? (for ([j 8]) (OUT (at H j))))
  (HALT))

;; sha256-image : #:target ['directive|'original] [#:message bytes]
;;   -> (values image symtab)
(define (sha256-image #:target [target 'directive] #:message [message #""])
  (when (>= (bytes-length message) (expt 2 28)) (error 'sha256 "message too long"))
  (assemble (λ () (program message)) #:target target))

;; input stream for 'directive
(define (sha256-input message)
  (when (>= (bytes-length message) (expt 2 28)) (error 'sha256 "message too long"))
  (cons (bytes-length message) (bytes->list message)))

;; 8 words (signed or unsigned) -> 64 hex digits
(define (digest-words->hex ws)
  (apply string-append
         (for/list ([w ws])
           (define u (modulo w (expt 2 32)))
           (define s (number->string u 16))
           (string-append (make-string (- 8 (string-length s)) #\0) s))))

;; Tests: NIST vectors on both machines, plus seeded random messages around
;; the padding boundaries checked against Racket's built-in sha256-bytes.
(module+ test
  (require rackunit file/sha1 (except-in "../racket/subleq.rkt" wrap32) "../racket/subleq-original.rkt")
  (define-values (img _) (sha256-image #:target 'directive))
  (define (dir-hex msg)
    (define r (run-subleq img (sha256-input msg) 100000000))
    (check-equal? (result-status r) 'halted)
    (digest-words->hex (result-output r)))
  (define (orig-hex msg)
    (define-values (oimg syms) (sha256-image #:target 'original #:message msg))
    (define-values (mem n) (execute-subleq/steps oimg))
    (digest-words->hex (for/list ([j 8]) (vector-ref mem (+ (hash-ref syms 'H) j)))))
  (for ([v (list (cons #"" "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
                 (cons #"abc" "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
                 (cons #"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
                       "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"))])
    (check-equal? (dir-hex (car v)) (cdr v))
    (check-equal? (orig-hex (car v)) (cdr v)))
  (random-seed 20261110)
  (for ([len '(1 54 55 56 57 63 64 65 119 120 128 200)])
    (define msg (apply bytes (for/list ([_ len]) (random 256))))
    (define expected (bytes->hex-string (sha256-bytes msg)))
    (check-equal? (dir-hex msg) expected (format "directive, length ~a" len))
    (check-equal? (orig-hex msg) expected (format "original, length ~a" len))))

;; Command line: write a spec §6 input file for the directive machine.
;;   racket programs/sha256.rkt OUT-FILE MESSAGE
;; MESSAGE is taken as UTF-8 bytes. FUEL is 10^9.
(module+ main
  (require racket/string)
  (define args (current-command-line-arguments))
  (unless (= (vector-length args) 2)
    (eprintf "usage: racket programs/sha256.rkt OUT-FILE MESSAGE\n") (exit 2))
  (define msg (string->bytes/utf-8 (vector-ref args 1)))
  (define-values (img _) (sha256-image #:target 'directive))
  (define in (sha256-input msg))
  (call-with-output-file (vector-ref args 0) #:exists 'truncate
    (λ (o)
      (write-string
       (string-join (map number->string (append (list (length img)) img
                                                (list (length in)) in (list 1000000000)))
                    " ")
       o)
      (newline o))))
