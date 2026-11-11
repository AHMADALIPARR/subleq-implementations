#lang racket/base
;; SPDX-License-Identifier: AGPL-3.0-or-later

;; sasm: a macro assembler for SUBLEQ, written in Racket.
;;
;; It emits memory images for two machines:
;;   'directive  the directive machine (semantics/subleq-spec.md):
;;               32-bit signed cells with wrap-around, a = -1 input,
;;               b < 0 output, a = -2 trap, halt when c = -1.
;;   'original   the original SUBLEQ (racket/subleq-original.rkt):
;;               unbounded integers, no I/O, halt when PC < 0.
;;
;; Every macro below documents its expansion and its cost in executed
;; instructions. Where the two machines need different code (wrap-around,
;; I/O), the macro checks (current-target) and the cost is given for both.
;; asm/macro-table.rkt measures the costs by running each macro on both
;; interpreters; docs/whitepaper.md publishes that table.
;;
;; Conventions
;;  * (sq a b [c]) is one SUBLEQ instruction: M[b] -= M[a]; if M[b] <= 0 goto c.
;;    c defaults to the next instruction.
;;  * Operands are integers (absolute addresses or the special values -1/-2),
;;    label symbols, or (list '+ label k).
;;  * Z is a cell that is 0 between macros. Macros that use Z restore it.
;;  * Code is laid out from address 0; data cells (variables, arrays,
;;    constants) follow the code.
;;  * On 'original the macros keep words in canonical form 0 <= x < 2^32.
;;    On 'directive words are 32-bit signed (the machine's own representation).

(require racket/list)

(provide current-target directive? original? emulate-wrap
         assemble listing
         sq label fresh
         var arr at K Z scratch
         ZERO JMP SUB ADD MOV NEG-INTO INC DEC JLEZ DOUBLE HALT
         IN OUT TRAP
         LOAD-NEXT STORE-NEXT
         MOD32 ADD32 SHL1 ROTL1 ROTR JSIGN MULK
         UNPACK32 ACC+PARITY ACC+CH ACC+MAJ
         macro-docs
         wrap32)

;; ---------------------------------------------------------------------------
;; Target

(define current-target (make-parameter 'directive))
(define (directive?) (eq? (current-target) 'directive))
(define (original?) (eq? (current-target) 'original))

;; emulate-wrap: when #f, MOD32 emits nothing on 'original either. Only used
;; to measure what happens if the original machine is NOT given wrap
;; emulation (wrong results, growing integers); see bench/killer-app.rkt.
(define emulate-wrap (make-parameter #t))

(define (wrap32 x)
  (- (modulo (+ x 2147483648) 4294967296) 2147483648))

;; ---------------------------------------------------------------------------
;; Assembler state (fresh for every call to assemble)

(define current-state (make-parameter #f))
(struct state ([code #:mutable]      ; reversed list of items
               [data #:mutable]      ; reversed list of items
               consts                ; hash value -> label
               scratches             ; hash name -> label
               [counter #:mutable]))

(define (st) (or (current-state) (error 'sasm "not inside assemble")))

(define (fresh [prefix 'L])
  (define s (st))
  (set-state-counter! s (add1 (state-counter s)))
  (string->symbol (format "~a~a" prefix (state-counter s))))

(define (emit-code! item) (set-state-code! (st) (cons item (state-code (st)))))
(define (emit-data! item) (set-state-data! (st) (cons item (state-data (st)))))

;; (sq a b [c]) : one instruction. c = 'next means the following instruction.
(define (sq a b [c 'next]) (emit-code! (list 'ins a b c)))

;; (label sym) : define sym as the address of the next instruction.
(define (label sym) (emit-code! (list 'label sym)) sym)

;; (var [init 0] [name]) : one data cell; returns its label. init may be a
;; number or a label (the cell then holds that address).
(define (var [init 0] [name #f])
  (define l (or name (fresh 'V)))
  (emit-data! (list 'label l))
  (emit-data! (list 'cell init))
  l)

;; (arr n [init 0]) : n consecutive data cells; returns the label of cell 0.
;; init may be a number or a list of n numbers.
(define (arr n [init 0] [name #f])
  (define l (or name (fresh 'A)))
  (emit-data! (list 'label l))
  (for ([i n])
    (emit-data! (list 'cell (if (list? init) (list-ref init i) init))))
  l)

;; (at base i) : operand for cell base + i.
(define (at base i) (if (zero? i) base (list '+ base i)))

;; (K v) : the label of a read-only constant cell holding v (shared).
(define (K v)
  (define v* (if (directive?) (wrap32 v) v))
  (define h (state-consts (st)))
  (or (hash-ref h v* #f)
      (let ([l (string->symbol (format "K~a" v*))])
        (hash-set! h v* l)
        (emit-data! (list 'label l))
        (emit-data! (list 'cell v*))
        l)))

(define (Z) (K 0))

;; (scratch name) : a shared scratch data cell, allocated on first use.
(define (scratch name)
  (define h (state-scratches (st)))
  (or (hash-ref h name #f)
      (let ([l (var 0 (string->symbol (format "S.~a" name)))])
        (hash-set! h name l)
        l)))

;; assemble : (-> any) #:target -> (values image symtab)
;; image is a list of integers (memory from address 0), symtab a hash.
(define (assemble thunk #:target [target 'directive])
  (parameterize ([current-target target]
                 [current-state (state '() '() (make-hash) (make-hasheq) 0)])
    (K 0)                                  ; Z is always allocated
    (thunk)
    (define code (reverse (state-code (st))))
    (define data (reverse (state-data (st))))
    (define syms (make-hasheq))
    (define (def! l a)
      (when (hash-ref syms l #f) (error 'sasm "duplicate label ~a" l))
      (hash-set! syms l a))
    ;; pass 1: addresses
    (define end-of-code
      (for/fold ([a 0]) ([it code])
        (case (car it)
          [(label) (def! (cadr it) a) a]
          [(ins) (+ a 3)])))
    (for/fold ([a end-of-code]) ([it data])
      (case (car it)
        [(label) (def! (cadr it) a) a]
        [(cell) (+ a 1)]))
    ;; pass 2: resolve
    (define (res x pc)
      (cond
        [(exact-integer? x) x]
        [(eq? x 'next) (+ pc 3)]
        [(symbol? x) (or (hash-ref syms x #f) (error 'sasm "undefined label ~a" x))]
        [(and (pair? x) (eq? (car x) '+)) (+ (res (cadr x) pc) (caddr x))]
        [else (error 'sasm "bad operand ~a" x)]))
    (define-values (rev-image _pc)
      (for/fold ([acc '()] [pc 0]) ([it code])
        (case (car it)
          [(label) (values acc pc)]
          [(ins) (values (list* (res (cadddr it) pc) (res (caddr it) pc) (res (cadr it) pc) acc)
                         (+ pc 3))])))
    (define data-cells
      (for/list ([it data] #:when (eq? (car it) 'cell))
        (define v (res (cadr it) 0))       ; a cell may hold a label (an address)
        (if (directive?) (wrap32 v) v)))
    (values (append (reverse rev-image) data-cells) syms)))

;; listing : (-> any) #:target -> list of strings, one per code item, with
;; symbolic operands (used to print macro expansions).
(define (listing thunk #:target [target 'directive])
  (parameterize ([current-target target]
                 [current-state (state '() '() (make-hash) (make-hasheq) 0)])
    (thunk)
    (for/list ([it (reverse (state-code (st)))])
      (case (car it)
        [(label) (format "~a:" (cadr it))]
        [(ins) (format "  sq ~a ~a ~a" (show (cadr it)) (show (caddr it)) (show (cadddr it)))]))))

(define (show x)
  (cond [(and (pair? x) (eq? (car x) '+)) (format "~a+~a" (cadr x) (caddr x))]
        [else (format "~a" x)]))

;; ---------------------------------------------------------------------------
;; Macro documentation registry: macro-docs is a list of (name . doc string)

(define macro-docs '())
(define-syntax-rule (defmacro (name arg ...) doc body ...)
  (begin
    (define (name arg ...) body ...)
    (set! macro-docs (append macro-docs (list (cons 'name doc))))))

;; ---------------------------------------------------------------------------
;; Basic macros (identical on both machines)

(defmacro (ZERO x)
  "x := 0.  sq x x.  1 instruction."
  (sq x x))

(defmacro (JMP l)
  "goto l.  sq Z Z l.  1 instruction."
  (sq (Z) (Z) l))

(defmacro (SUB a b)
  "b := b - a.  sq a b.  1 instruction (wraps on directive)."
  (sq a b))

(defmacro (ADD a b)
  "b := b + a.  sq a Z; sq Z b; sq Z Z.  3 instructions. Wraps mod 2^32 on directive; unbounded on original (see ADD32)."
  (sq a (Z)) (sq (Z) b) (sq (Z) (Z)))

(defmacro (MOV a b)
  "b := a.  sq b b; sq a Z; sq Z b; sq Z Z.  4 instructions. a and b must differ."
  (sq b b) (sq a (Z)) (sq (Z) b) (sq (Z) (Z)))

(defmacro (NEG-INTO a b)
  "b := -a.  sq b b; sq a b.  2 instructions."
  (sq b b) (sq a b))

(defmacro (INC x)
  "x := x + 1.  sq K(-1) x.  1 instruction."
  (sq (K -1) x))

(defmacro (DEC x)
  "x := x - 1.  sq K(1) x.  1 instruction."
  (sq (K 1) x))

(defmacro (JLEZ x l)
  "if x <= 0 goto l (x unchanged).  sq Z x l.  1 instruction."
  (sq (Z) x l))

(defmacro (DOUBLE x)
  "x := x + x.  = ADD x x.  3 instructions (wraps on directive)."
  (ADD x x))

(defmacro (HALT)
  "stop.  sq Z Z -1.  1 instruction. Directive: c = -1 halts. Original: the branch is taken to -1 and PC < 0 halts."
  (sq (Z) (Z) -1))

;; ---------------------------------------------------------------------------
;; I/O and trap (directive only)

(defmacro (IN x)
  "x := next input word.  -1 x next.  1 instruction. Directive only."
  (unless (directive?) (error 'IN "the original machine has no input"))
  (sq -1 x))

(defmacro (OUT x)
  "append M[x] to the output.  x -1 next.  1 instruction. Directive only."
  (unless (directive?) (error 'OUT "the original machine has no output"))
  (sq x -1))

(defmacro (TRAP code)
  "stop with status trap and CODE = code (an integer literal).  -2 code 0.  1 instruction. Directive only."
  (unless (directive?) (error 'TRAP "the original machine has no trap"))
  (unless (exact-integer? code) (error 'TRAP "code must be an integer literal"))
  (sq -2 code 0))

;; ---------------------------------------------------------------------------
;; Memory streaming on the original machine (its replacement for IN/OUT)

(defmacro (LOAD-NEXT ptr dst)
  "dst := M[M[ptr]]; M[ptr] += 1.  Self-modifying: MOV ptr into the a field of a later instruction, then copy through it.  9 instructions. Used on original where directive uses IN (1)."
  (define x (fresh 'LD))
  (MOV ptr (at x 0))                 ; 4: patch the a operand of instruction x
  (ZERO dst)                         ; 1
  (label x) (sq 0 (Z))               ; 1: Z := -M[ptr]   (a patched above)
  (sq (Z) dst) (sq (Z) (Z))          ; 2
  (INC ptr))                         ; 1

(defmacro (STORE-NEXT src ptr)
  "M[M[ptr]] := src; M[ptr] += 1.  Self-modifying: t := -ptr, patch the a and b fields of instruction x and the b field of instruction y, then x: zero M[p]; Z := -src; y: M[p] -= Z; clear Z.  2 + 3*2 + 4 + 1 = 13 instructions. Used on original where directive uses OUT (1)."
  (define x (fresh (quote ST))) (define y (fresh (quote ST))) (define t (scratch (quote store-t)))
  (NEG-INTO ptr t)                           ; 2: t = -ptr
  (ZERO (at x 0)) (sq t (at x 0))            ; 2: x.a = ptr
  (ZERO (at x 1)) (sq t (at x 1))            ; 2: x.b = ptr
  (ZERO (at y 1)) (sq t (at y 1))            ; 2: y.b = ptr
  (label x) (sq 0 0)                         ; 1: M[p] := 0
  (sq src (Z))                               ; 1: Z := -src
  (label y) (sq (Z) 0)                       ; 1: M[p] := src
  (sq (Z) (Z))                               ; 1
  (INC ptr))                                 ; 1

;; ---------------------------------------------------------------------------
;; Emulating 32-bit wrap-around on the original machine

;; One reduction step for 2^(32+j): if x >= 2^(32+j) then x -= 2^(32+j).
(define (mod-step x j)
  (define c (- (expt 2 (+ 32 j)) 1))
  (define l0 (fresh 'M))
  (define d (fresh 'M))
  (sq (K c) x l0)                    ; x -= 2^(32+j)-1; <= 0 means x was < 2^(32+j)
  (sq (K 1) x d)                     ; x -= 1   (total -2^(32+j))
  (sq (Z) (Z) d)
  (label l0) (sq (K (- c)) x d)      ; undo
  (label d))

(defmacro (MOD32 x k)
  "Original only: reduce 0 <= x < 2^k * 2^32 to x mod 2^32, using k compare-subtract steps of 2 or 3 instructions (2k..3k). Directive: no code (0)."
  (when (and (original?) (emulate-wrap))
    (for ([j (in-range (- k 1) -1 -1)]) (mod-step x j))))

(defmacro (ADD32 a b)
  "b := (b + a) mod 2^32.  Directive: ADD (3). Original: ADD + MOD32 b 1 (5 or 6)."
  (ADD a b)
  (MOD32 b 1))

(defmacro (SHL1 x)
  "x := (2x) mod 2^32.  Directive: DOUBLE (3). Original: DOUBLE + MOD32 x 1 (5 or 6)."
  (DOUBLE x)
  (MOD32 x 1))

;; JSIGN: jump if bit 31 of the word is set.
(defmacro (JSIGN x l)
  "if bit 31 of x is set goto l (x unchanged).  Directive: x < 0, tested as x <= 0 and then x + 1 <= 0 (no overflow because x <= 0), 2-3 instructions. Original: x >= 2^31, a compare-subtract, 2-3 instructions."
  (cond
    [(directive?)
     (define le (fresh 'J)) (define neg (fresh 'J)) (define done (fresh 'J))
     (sq (Z) x le)                   ; x <= 0 ?
     (sq (Z) (Z) done)               ; x > 0: bit clear
     (label le) (sq (K -1) x neg)    ; x + 1 <= 0 iff x < 0 (no overflow, x <= 0)
     (sq (K 1) x done)               ; x was 0: undo, result 0 <= 0 -> done
     (label neg) (sq (K 1) x l)      ; undo; x < 0 so the branch is taken
     (label done)]
    [else
     (define c (- (expt 2 31) 1))
     (define lo (fresh 'J)) (define done (fresh 'J))
     (sq (K c) x lo)                 ; x -= 2^31-1; <= 0 means x < 2^31
     (sq (K (- c)) x l)              ; undo; x >= 2^31 > 0 so no branch...
     (sq (Z) (Z) l)                  ; ...jump to l
     (label lo) (sq (K (- c)) x done) ; undo
     (label done)]))

(defmacro (ROTL1 x)
  "x := rotate-left-1(x) as a 32-bit word.  Directive: JSIGN, DOUBLE, INC if the top bit was set, 6-7 instructions. Original: DOUBLE, then if x >= 2^32 subtract 2^32 - 1, 5 instructions."
  (cond
    [(directive?)
     (define top (fresh 'R)) (define done (fresh 'R))
     (JSIGN x top)
     (DOUBLE x) (JMP done)
     (label top) (DOUBLE x) (INC x)
     (label done)]
    [else
     (define c (- (expt 2 32) 1))
     (define lo (fresh 'R)) (define done (fresh 'R))
     (DOUBLE x)
     (sq (K c) x lo)                 ; x - (2^32-1) <= 0 means 2x < 2^32 (top bit was clear)
     (sq (Z) (Z) done)               ; else x = 2x - 2^32 + 1: done
     (label lo) (sq (K (- c)) x done)
     (label done)]))

(defmacro (MULK x k tmp)
  "x := (x * k) mod 2^32 for an integer literal k >= 1 (tmp is a scratch cell). Horner over the bits of k: MOV x tmp, then per remaining bit DOUBLE x and, if the bit is 1, ADD tmp x: 4 + 3*(bits-1) + 3*(ones-1) instructions. Original: the same, then MOD32 x bits (x * k < 2^bits * 2^32), 2*bits..3*bits more."
  (unless (and (exact-integer? k) (>= k 1)) (error (quote MULK) "k must be a positive integer literal"))
  (define bits (integer-length k))
  (MOV x tmp)
  (for ([j (in-range (- bits 2) -1 -1)])
    (DOUBLE x)
    (when (bitwise-bit-set? k j) (ADD tmp x)))
  (MOD32 x bits))

(defmacro (ROTR x n)
  "x := rotate-right-n(x) as a 32-bit word, done as 32-n ROTL1 (word-level; programs/sha256.rkt uses bit-sliced words instead, where rotation costs 0)."
  (for ([_ (modulo (- 32 n) 32)]) (ROTL1 x)))

;; ---------------------------------------------------------------------------
;; Bit-sliced words (used by SHA-256). A bit-sliced word is 32 cells,
;; cell base+i holding bit i (0 or 1). Rotations and shifts are index
;; remappings at assembly time and cost 0 instructions.

;; One bit of UNPACK32 working on v = -(remaining value), 0 <= remaining < 2^(i+1).
(define (unpack-bit v b i)
  (define one (fresh 'U)) (define nxt (fresh 'U))
  (ZERO b)                                   ; 1
  (sq (K (- (expt 2 i))) v one)              ; v += 2^i ; <= 0 iff remaining >= 2^i
  (sq (K (expt 2 i)) v nxt)                  ; undo; v <= 0 so this always branches
  (label one) (sq (K -1) b nxt)              ; bit := 1 (falls through to nxt)
  (label nxt))

(defmacro (UNPACK32 w base v)
  "Write the 32 bits of word w into cells base..base+31 (w unchanged; v is a scratch cell). Original: v := -w, then per bit i (31..0) a compare-subtract with 2^i: 2 + 32*3 = 98 instructions. Directive: bit 31 from the sign of w (no wrap needed), then bits 30..0 the same way: 97-101 instructions."
  (cond
    [(original?)
     (NEG-INTO w v)                          ; 2
     (for ([i (in-range 31 -1 -1)]) (unpack-bit v (at base i) i))]
    [else
     (define nonpos (fresh 'U)) (define neg (fresh 'U)) (define bits (fresh 'U))
     (ZERO (at base 31)) (ZERO v)            ; 2
     (sq (Z) w nonpos)                       ; w <= 0 ?
     (sq w v bits)                           ; w > 0: v = -w < 0, always branches
     (label nonpos) (sq (K -1) w neg)        ; w + 1 <= 0 iff w < 0 (no overflow)
     (sq (K 1) w bits)                       ; w was 0: undo; 0 <= 0 -> bits (v = 0)
     (label neg)
     (sq w v)                                ; v = -(w+1), 0 <= v < 2^31
     (sq (K 1) w)                            ; undo w (w < 0, branch target is next)
     (sq (K (- (expt 2 31) 1)) v)            ; v = -(w + 2^31) exactly, no wrap
     (sq (K -1) (at base 31) bits)           ; bit 31 := 1
     (label bits)
     (for ([i (in-range 30 -1 -1)]) (unpack-bit v (at base i) i))]))

(defmacro (ACC+PARITY acc s bits)
  "acc += (b1 xor ... xor bk) for bit cells bits. s is a scratch cell that must be 0 and is left 0. k subtractions, then up to k decrement-tests that restore s. k=3: 5-7 instructions; k=2: 4-6."
  (define k (length bits))
  (define inc (fresh 'P)) (define done (fresh 'P))
  (for ([b bits]) (sq b s))                  ; s = -(sum)
  (define tests (for/list ([j k]) (fresh 'P)))
  (for ([j (in-range 1 (+ k 1))])
    (define next-test (if (< j k) (list-ref tests j) (if (odd? k) inc done)))
    (label (list-ref tests (- j 1)))
    (sq (K -1) s next-test)                  ; s = j - sum; <= 0 iff sum >= j
    (sq (K 1) s (if (odd? (- j 1)) inc done))) ; sum = j-1: s 1 -> 0
  (label inc) (sq (K -1) acc done)           ; acc += 1
  (label done))

(defmacro (ACC+CH acc e f g)
  "acc += (e ? f : g) for bit cells e, f, g. 2-4 instructions."
  (define g-path (fresh 'C)) (define done (fresh 'C))
  (sq (Z) e g-path)                          ; e = 0 -> g
  (sq (Z) f done)                            ; f = 0 -> done
  (sq (K -1) acc done)
  (sq (Z) (Z) done)
  (label g-path) (sq (Z) g done)
  (sq (K -1) acc done)
  (label done))

(defmacro (ACC+MAJ acc s a b c)
  "acc += majority(a, b, c) for bit cells. s is a scratch cell (any value). 6 instructions."
  (define inc (fresh 'J)) (define done (fresh 'J))
  (ZERO s) (sq a s) (sq b s) (sq c s)        ; s = -(a+b+c)
  (sq (K -2) s inc)                          ; 2 - sum <= 0 iff sum >= 2
  (sq (Z) (Z) done)
  (label inc) (sq (K -1) acc done)
  (label done))
