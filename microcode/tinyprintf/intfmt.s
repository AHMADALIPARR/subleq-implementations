; 16-bit SUBLEQ integer formatting microcode (Howe / eForth).
; Canonical decimal u16toa / i16toa, unsigned compares, unsigned magnitude
; for negatives (including -32768), snprintf-style bounded buffer:
;   LEN = required length (independent of truncation)
;   if CAP>0: write at most CAP-1 chars, NUL at min(LEN, CAP-1)
;   if CAP==0: write nothing
; Optional left space-pad when WIDTH > raw length; LEN = max(raw, WIDTH).
;
; Cell 0 is Z (always re-zeroed). Boot instruction at 0 is JMP START
; (SUB Z,Z,START), so a reset PC=0 is safe.
;
; Copyright (C) Ahmad <ahmedparr93@gmail.com>
; SPDX-License-Identifier: AGPL-3.0-only

Z:
        JMP START

ONE:    .word 1
TEN:    .word 10
C100:   .word 100
C1000:  .word 1000
C10000: .word 10000
K48:    .word 48
K45:    .word 45
K32:    .word 32          ; space
K32768: .word 32768       ; 0x8000 sign bit / unsigned 32768

INPUT:  .word 0           ; value to format (unsigned bits)
CAP:    .word 8           ; buffer capacity
WIDTH:  .word 0           ; 0 = no pad
MODE:   .word 0           ; 0 = u16toa, 1 = i16toa
LEN:    .word 0           ; required length (result)
N:      .word 0
T:      .word 0
SIGN:   .word 0           ; 1 if leading '-'
Q0:     .word 0           ; 10000s
Q1:     .word 0           ; 1000s
Q2:     .word 0           ; 100s
Q3:     .word 0           ; 10s
Q4:     .word 0           ; 1s
NDIG:   .word 0
RAW:    .word 0
PAD:    .word 0
ROOM:   .word 0
IDX:    .word 0
CH:     .word 0
TMP:    .word 0

; Output buffer: 16 cells (enough for padded short fields in tests).
BUF:    .word 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
.equ BUFEND 0              ; patched below if needed; unused

; ---------- program ----------
START:
        ZERO SIGN
        ZERO LEN
        ZERO PAD
        ZERO NDIG
        MOV INPUT N

        ; if MODE==0, unsigned path
        MOV MODE T
        JLEZ T U_PATH          ; MODE is 0 (or negative, we only store 0/1)
        JMP I_PATH
U_PATH:
        JMP DIGITS
I_PATH:
        ; signed: if N has bit 15 set, SIGN=1 and N = unsigned 0-N
        MOV N T
        SUB K32768 T           ; T = N - 32768
        ; T<=0 when N<=32768. We need N>=32768 (unsigned) i.e. signed N<0 or N==32768.
        ; N in 0..32767: T = N-32768 is 0x8000..0xFFFF, <=0, but N is non-negative.
        ; N==32768: T=0, <=0.
        ; N>32768: T>0.
        ;
        ; Better sign test: JLEZ N is true for N==0 or N>=32768.
        ; Distinguish 0 with INC.
        MOV N T
        JLEZ T maybe_neg
        JMP DIGITS             ; 1..32767: positive
maybe_neg:
        INC T
        JLEZ T do_neg          ; still <=0 after INC => original was 0x8000..0xFFFF
        JMP DIGITS             ; original was 0
do_neg:
        MOV ONE SIGN
        ; unsigned magnitude: N = 0 - N (wrap)
        ZERO T
        SUB N T                ; T = 0-N
        MOV T N
        JMP DIGITS

; Extract 5 decimal digits, most significant first, using unsigned >=
; and repeated subtraction of 10000,1000,100,10,1.
DIGITS:
        ZERO Q0
        ZERO Q1
        ZERO Q2
        ZERO Q3
        ZERO Q4

; --- place 10000 ---
P0_LOOP:
        ; unsigned N >= 10000?
        MOV N T
        JLEZ T P0_LE0
        JMP P0_POS
P0_LE0:
        INC T
        JLEZ T P0_GE             ; N >= 32768 => >= 10000
        JMP P0_DONE              ; N == 0
P0_POS:
        MOV N T
        SUB C10000 T
        JLEZ T P0_LE
        JMP P0_GE                ; N > 10000
P0_LE:
        INC T
        JLEZ T P0_DONE           ; N < 10000
        ; T was 0 => N == 10000, fall through to GE
P0_GE:
        SUB C10000 N
        INC Q0
        JMP P0_LOOP
P0_DONE:

; --- place 1000 ---
P1_LOOP:
        MOV N T
        JLEZ T P1_LE0
        JMP P1_POS
P1_LE0:
        INC T
        JLEZ T P1_GE
        JMP P1_DONE
P1_POS:
        MOV N T
        SUB C1000 T
        JLEZ T P1_LE
        JMP P1_GE
P1_LE:
        INC T
        JLEZ T P1_DONE
P1_GE:
        SUB C1000 N
        INC Q1
        JMP P1_LOOP
P1_DONE:

; --- place 100 ---
P2_LOOP:
        MOV N T
        JLEZ T P2_LE0
        JMP P2_POS
P2_LE0:
        INC T
        JLEZ T P2_GE
        JMP P2_DONE
P2_POS:
        MOV N T
        SUB C100 T
        JLEZ T P2_LE
        JMP P2_GE
P2_LE:
        INC T
        JLEZ T P2_DONE
P2_GE:
        SUB C100 N
        INC Q2
        JMP P2_LOOP
P2_DONE:

; --- place 10 ---
P3_LOOP:
        MOV N T
        JLEZ T P3_LE0
        JMP P3_POS
P3_LE0:
        INC T
        JLEZ T P3_GE
        JMP P3_DONE
P3_POS:
        MOV N T
        SUB TEN T
        JLEZ T P3_LE
        JMP P3_GE
P3_LE:
        INC T
        JLEZ T P3_DONE
P3_GE:
        SUB TEN N
        INC Q3
        JMP P3_LOOP
P3_DONE:

        ; ones: remainder is N (0..9)
        MOV N Q4

        ; convert quotients to ASCII
        ADD K48 Q0
        ADD K48 Q1
        ADD K48 Q2
        ADD K48 Q3
        ADD K48 Q4

        ; NDIG = number of significant digits (at least 1)
        ; skip leading '0's from Q0..Q3; Q4 always included if all zero.
        MOV Q0 T
        SUB K48 T                ; T = Q0-'0'
        JLEZ T S1                ; Q0=='0' (T==0); Q0 can't be < '0'
        JMP FIVE
S1:     MOV Q1 T
        SUB K48 T
        JLEZ T S2
        JMP FOUR
S2:     MOV Q2 T
        SUB K48 T
        JLEZ T S3
        JMP THREE
S3:     MOV Q3 T
        SUB K48 T
        JLEZ T S4
        JMP TWO
S4:     JMP ONE_DIG

FIVE:   MOV ONE TMP
        ADD ONE TMP
        ADD ONE TMP
        ADD ONE TMP
        ADD ONE TMP              ; TMP=5
        MOV TMP NDIG
        JMP HAVE_DIG
FOUR:   MOV ONE TMP
        ADD ONE TMP
        ADD ONE TMP
        ADD ONE TMP              ; 4
        MOV TMP NDIG
        JMP HAVE_DIG
THREE:  MOV ONE TMP
        ADD ONE TMP
        ADD ONE TMP
        MOV TMP NDIG
        JMP HAVE_DIG
TWO:    MOV ONE TMP
        ADD ONE TMP
        MOV TMP NDIG
        JMP HAVE_DIG
ONE_DIG:
        MOV ONE NDIG
HAVE_DIG:
        ; RAW = NDIG + SIGN
        MOV NDIG RAW
        MOV SIGN T
        JLEZ T RAW_OK            ; SIGN==0
        INC RAW
RAW_OK:
        ; PAD / LEN: if WIDTH > RAW then PAD=WIDTH-RAW, LEN=WIDTH else LEN=RAW
        ZERO PAD
        MOV WIDTH T
        JLEZ T NO_PAD            ; WIDTH==0 (or negative, we do not store negative)
        MOV WIDTH T
        SUB RAW T                ; T = WIDTH-RAW
        JLEZ T NO_PAD            ; WIDTH<=RAW
        MOV T PAD
        MOV WIDTH LEN
        JMP LEN_OK
NO_PAD:
        MOV RAW LEN
LEN_OK:

        ; if CAP==0, do not write, halt
        MOV CAP T
        JLEZ T DONE

        ; ROOM = CAP-1
        MOV CAP ROOM
        DEC ROOM

        ZERO IDX

        ; write PAD spaces (bounded by ROOM)
SP_LOOP:
        MOV PAD T
        JLEZ T AFTER_PAD
        MOV IDX T
        SUB ROOM T               ; T = IDX-ROOM; if IDX>=ROOM stop padding
        ; if IDX >= ROOM goto AFTER_PAD (no more room, including for further chars)
        ; unsigned? IDX and ROOM are small (<=65535 but we keep them <=16)
        JLEZ T SP_EQCHK          ; IDX<=ROOM
        JMP AFTER_PAD            ; IDX>ROOM, no room
SP_EQCHK:
        ; T==0 => IDX==ROOM, no room to write (NUL lives at ROOM)
        INC T
        JLEZ T SP_WRITE          ; T was <0, IDX<ROOM
        JMP AFTER_PAD
SP_WRITE:
        ; BUF[IDX] = ' '
        ; compute address BUF+IDX in TMP, then we cannot do indirect easily!
        ; Unrolled buffer writes: IDX is 0..15, use a jump table, or
        ; write by probing IDX against 0,1,2,...
        MOV ONE RETID
        JMP WRITE_SPACE

AFTER_PAD:
        ; optional '-'
        MOV SIGN T
        JLEZ T AFTER_SIGN
        MOV IDX T
        SUB ROOM T
        JLEZ T SG_EQ
        JMP AFTER_SIGN
SG_EQ:
        INC T
        JLEZ T SG_WRITE
        JMP AFTER_SIGN
SG_WRITE:
        MOV ONE RETID
        INC RETID
        JMP WRITE_MINUS

AFTER_SIGN:
        ; emit NDIG digits from Q0..Q4 skipping leading zeros, already
        ; encoded by starting point. Use a cursor SK = 5-NDIG (0..4).
        ; We'll walk Q0..Q4 and emit when we reach the first significant.
        JMP EMIT_DIGS

; ---- helpers for BUF[IDX]=CH; IDX++ ----
; Because the machine has no indirect addressing, writes are unrolled
; for IDX=0..15.

WRITE_SPACE:
        MOV K32 CH
        JMP STORE_CH
WRITE_MINUS:
        MOV K45 CH
        JMP STORE_CH

STORE_CH:
        MOV IDX T
        JLEZ T ST0
        DEC T
        JLEZ T ST1
        DEC T
        JLEZ T ST2
        DEC T
        JLEZ T ST3
        DEC T
        JLEZ T ST4
        DEC T
        JLEZ T ST5
        DEC T
        JLEZ T ST6
        DEC T
        JLEZ T ST7
        DEC T
        JLEZ T ST8
        DEC T
        JLEZ T ST9
        DEC T
        JLEZ T ST10
        DEC T
        JLEZ T ST11
        DEC T
        JLEZ T ST12
        DEC T
        JLEZ T ST13
        DEC T
        JLEZ T ST14
        JMP ST15
ST0:    MOV CH BUF
        JMP STORED
ST1:    MOV CH BUF+1
        JMP STORED
ST2:    MOV CH BUF+2
        JMP STORED
ST3:    MOV CH BUF+3
        JMP STORED
ST4:    MOV CH BUF+4
        JMP STORED
ST5:    MOV CH BUF+5
        JMP STORED
ST6:    MOV CH BUF+6
        JMP STORED
ST7:    MOV CH BUF+7
        JMP STORED
ST8:    MOV CH BUF+8
        JMP STORED
ST9:    MOV CH BUF+9
        JMP STORED
ST10:   MOV CH BUF+10
        JMP STORED
ST11:   MOV CH BUF+11
        JMP STORED
ST12:   MOV CH BUF+12
        JMP STORED
ST13:   MOV CH BUF+13
        JMP STORED
ST14:   MOV CH BUF+14
        JMP STORED
ST15:   MOV CH BUF+15
        JMP STORED
STORED:
        INC IDX
        ; who called us? We need a return. Use TMP2 as return id? We didn't set one.
        ; This is a problem. Use two store entry points? Better: a RET cell
        ; holding a label. Without indirect jump, use a STATE flag.
        ; STATE: 1=from pad, 2=from sign, 3=from digits, 4=from nul (not used)
        MOV RETID T
        DEC T
        JLEZ T RET_PAD       ; RETID==1
        DEC T
        JLEZ T RET_SIGN      ; RETID==2
        JMP RET_DIG          ; RETID==3

; We need to set RETID before jumping to WRITE_*. Patch the earlier jumps.
; (See RETID cell below; the bootstrapping JMP WRITE_SPACE must set RETID first.)

RET_PAD:
        DEC PAD
        JMP SP_LOOP
RET_SIGN:
        JMP AFTER_SIGN
RET_DIG:
        JMP DIG_NEXT

; ---- emit digits ----
EMIT_DIGS:
        ; SK = 5 - NDIG: skip first SK of Q0..Q4
        MOV ONE TMP
        ADD ONE TMP
        ADD ONE TMP
        ADD ONE TMP
        ADD ONE TMP              ; TMP=5
        SUB NDIG TMP             ; TMP = 5-NDIG (0..4)
        MOV TMP SK
        ; walk I = 0..4
        ZERO DI
DIG_LOOP:
        ; if DI==5 done
        MOV DI T
        SUB K5 T
        JLEZ T DIG_EQ5
        JMP DIG_BODY
DIG_EQ5:
        ; T==0 => DI==5 done; T<0 => DI<5 body
        INC T
        JLEZ T DIG_BODY
        JMP AFTER_DIGS
DIG_BODY:
        ; if DI < SK, skip this place
        MOV DI T
        SUB SK T                 ; T=DI-SK
        JLEZ T MAYBE_SKIP
        JMP TAKE_DIG             ; DI>SK
MAYBE_SKIP:
        INC T
        JLEZ T SKIP_DIG          ; DI<SK
        JMP TAKE_DIG             ; DI==SK
SKIP_DIG:
        JMP DIG_NEXT
TAKE_DIG:
        ; CH = Qi, then if room, store
        ; select Qi by DI
        MOV DI T
        JLEZ T TQ0
        DEC T
        JLEZ T TQ1
        DEC T
        JLEZ T TQ2
        DEC T
        JLEZ T TQ3
        JMP TQ4
TQ0:    MOV Q0 CH
        JMP HAVE_CH
TQ1:    MOV Q1 CH
        JMP HAVE_CH
TQ2:    MOV Q2 CH
        JMP HAVE_CH
TQ3:    MOV Q3 CH
        JMP HAVE_CH
TQ4:    MOV Q4 CH
HAVE_CH:
        ; if IDX >= ROOM, skip store
        MOV IDX T
        SUB ROOM T
        JLEZ T DG_EQ
        JMP DIG_NEXT
DG_EQ:
        INC T
        JLEZ T DG_STORE
        JMP DIG_NEXT
DG_STORE:
        MOV ONE RETID
        INC RETID
        INC RETID                ; RETID=3
        JMP STORE_CH
DIG_NEXT:
        INC DI
        JMP DIG_LOOP

AFTER_DIGS:
        ; NUL at min(LEN, CAP-1) = min(LEN, ROOM) wait:
        ; C snprintf: if LEN < CAP, NUL at LEN; else NUL at CAP-1 (=ROOM).
        ; So nul_index = LEN if LEN < CAP else ROOM.
        MOV LEN T
        SUB CAP T                ; T=LEN-CAP
        JLEZ T NUL_AT_LEN        ; LEN<=CAP. If LEN==CAP, nul at CAP-1=ROOM. If LEN<CAP, nul at LEN.
        JMP NUL_AT_ROOM          ; LEN>CAP
NUL_AT_LEN:
        ; T==0 => LEN==CAP => use ROOM; T<0 => LEN<CAP => use LEN
        INC T
        JLEZ T NUL_USE_LEN
        JMP NUL_AT_ROOM
NUL_USE_LEN:
        MOV LEN IDX
        JMP WRITE_NUL
NUL_AT_ROOM:
        MOV ROOM IDX
        JMP WRITE_NUL

WRITE_NUL:
        ZERO CH
        ; store CH at IDX but do not INC, and halt after
        MOV IDX T
        JLEZ T N0
        DEC T
        JLEZ T N1
        DEC T
        JLEZ T N2
        DEC T
        JLEZ T N3
        DEC T
        JLEZ T N4
        DEC T
        JLEZ T N5
        DEC T
        JLEZ T N6
        DEC T
        JLEZ T N7
        DEC T
        JLEZ T N8
        DEC T
        JLEZ T N9
        DEC T
        JLEZ T N10
        DEC T
        JLEZ T N11
        DEC T
        JLEZ T N12
        DEC T
        JLEZ T N13
        DEC T
        JLEZ T N14
        JMP N15
N0:     MOV CH BUF
        JMP DONE
N1:     MOV CH BUF+1
        JMP DONE
N2:     MOV CH BUF+2
        JMP DONE
N3:     MOV CH BUF+3
        JMP DONE
N4:     MOV CH BUF+4
        JMP DONE
N5:     MOV CH BUF+5
        JMP DONE
N6:     MOV CH BUF+6
        JMP DONE
N7:     MOV CH BUF+7
        JMP DONE
N8:     MOV CH BUF+8
        JMP DONE
N9:     MOV CH BUF+9
        JMP DONE
N10:    MOV CH BUF+10
        JMP DONE
N11:    MOV CH BUF+11
        JMP DONE
N12:    MOV CH BUF+12
        JMP DONE
N13:    MOV CH BUF+13
        JMP DONE
N14:    MOV CH BUF+14
        JMP DONE
N15:    MOV CH BUF+15
        JMP DONE

DONE:
        HALT

; cells used by the control flags (must be defined)
RETID:  .word 0
SK:     .word 0
DI:     .word 0
K5:     .word 5
