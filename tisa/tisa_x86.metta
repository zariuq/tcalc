; tisa_x86.metta -- t-ISA profile p1 to x86-64, by fixed templates (CeTTa, PeTTa lane).
;
; The MeTTa realization of tisa_x86.c, byte for byte. Every statement becomes
; one template: a fixed list of x86-64 instructions whose only parameters are
; registers, immediates and jump targets. Three layers, each usable alone:
;
;   encoder     (tisa-x86:encode INSTRUCTION)      section 2
;               one x86 instruction form -> its bytes, or its opcode bytes and a
;               rel32 to a label
;   templates   (tisa-x86:template NAME PARAMS)    section 4
;               a template's instruction list: instructions and macros
;               (section 3), flattened by (tisa-x86:code NAME PARAMS)
;   assembler   (tisa-x86:emit PROGRAM)            sections 5-6
;               walks the statement tree into a listing of spans and labels,
;               lays it out, and resolves every rel32 as the C does
;
; (tisa-x86:emit (TProg DECLS INITS ROOT)) is (Image BYTES SPANS LABELS):
;   BYTES   the image, a list of numbers 0..255; the entry is offset 0
;   SPANS   (SpanAt OFFSET LENGTH TEMPLATE SOURCE CODE) in image order, where
;           SOURCE is the statement realized (the instruction, or a control
;           statement without its sub-statements; Wrapper for the prologue,
;           failure handlers and epilogue) and CODE its instruction list
;   LABELS  ((LABEL OFFSET) ...) for every placed label
;
; Registers: v0..v11 are rdi rsi rdx rcx r8 r9 r10 r11 rax rbx r12 r13, the
; scratch registers s0 s1 are r14 r15. v0 holds the frame throughout.
; Programs are assumed admitted (SEMANTICS.txt, section 4); input outside the
; emitter's assumptions stops the run with a message and exit status 3.

!(import! &self str)
!(import! &self system)

; ---- 1. Registers, frame words, failure -------------------------------------

(= (vreg $v)
   (case $v
     ((0 rdi) (1 rsi) (2 rdx) (3 rcx) (4 r8) (5 r9) (6 r10) (7 r11)
      (8 rax) (9 rbx) (10 r12) (11 r13)
      ($other (tisa-x86:reject (register $other))))))

(= (reg-num rax) 0) (= (reg-num rcx) 1) (= (reg-num rdx) 2) (= (reg-num rbx) 3)
(= (reg-num rsp) 4) (= (reg-num rbp) 5) (= (reg-num rsi) 6) (= (reg-num rdi) 7)
(= (reg-num r8) 8) (= (reg-num r9) 9) (= (reg-num r10) 10) (= (reg-num r11) 11)
(= (reg-num r12) 12) (= (reg-num r13) 13) (= (reg-num r14) 14) (= (reg-num r15) 15)

; Frame words (tisa.h): region r's base and length, then the run's own words.
(= (region-base $r) (* 16 $r))
(= (region-len $r) (+ (* 16 $r) 8))
(= (frame-word STATUS) 144)
(= (frame-word RET-VAL) 152)
(= (frame-word BUDGET) 160)
(= (frame-word USED) 168)

; Outcome codes the failure handlers write (SEMANTICS.txt, section 7).
(= (outcome UNSUPPORTED) 2)
(= (outcome INVALID) 3)
(= (outcome EXHAUSTED) 4)

(= (tisa-x86:reject $why)
   (let $shown (system:write stderr
                  (str:concat "tisa_x86.metta: input outside the emitter's assumptions: "
                              (str:concat (repr $why) "\n")))
     (system:exit 3)))

; ---- 2. The encoder ------------------------------------------------------------
;
; Exactly the instruction forms tisa_x86.c uses. Operands are register names,
; widths Q (64-bit) or D (32-bit), immediates as the unsigned value of their
; field, displacements as signed numbers. Every memory operand is
; [base + disp32] (ModRM mod 10; base r12 adds the SIB byte 24), as modrm_mem
; writes it.
;
;   (OpRR op w rm reg)     op rm, reg         [REX] opcode ModRM(11 reg rm)
;                          op: ADD 01, OR 09, AND 21, SUB 29, XOR 31, CMP 39,
;                              TEST 85, MOV 89
;   (Movsxd d s)           movsxd d, s32      REX.W 63 /r
;   (Imul d s)             imul d, s          REX.W 0F AF /r
;   (Cmov cc d s)          cmovcc d, s        REX.W 0F 40+cc /r
;   (Setcc cc d)           setcc d8           REX 0F 90+cc /0 (REX always)
;   (Movzx8 d s)           movzx d32, s8      REX 0F B6 /r (REX always)
;   (ShiftImm op w d n)    op d, n            [REX] C1 /ext ib; SHL 4, SHR 5, SAR 7
;   (OpImm32 op w d k)     op d, imm32        [REX] 81 /ext id; ADD 0, AND 4, SUB 5,
;                                             CMP 7 (sign-extended when w is Q)
;   (OpImm8 op w d k)      op d, imm8         [REX] 83 /ext ib
;   (MovImm32 d k)         mov d32, imm32     [REX] B8+d id (zero-extends)
;   (MovImmSx d k)         mov d, simm32      REX.W C7 /0 id (sign-extends)
;   (MovImm64 d k)         mov d, imm64       REX.W B8+d io
;   (Load w d b o)         w 1: movzx d32, byte [b+o]   0F B6 /r
;                          w 4: mov d32, [b+o]          8B /r
;                          w 8: mov d, [b+o]            REX.W 8B /r
;   (Store w s b o)        mov [b+o], s (w bytes)       w 1: REX 88 /r (REX
;                          always); w 4: 89 /r; w 8: REX.W 89 /r
;   (OpRM op r b o)        op r, [b+o]        REX.W op /r; ADD 03, SUB 2B, CMP 3B
;   (AddToMem b o s)       add [b+o], s       REX.W 01 /r
;   (StoreImm32 b o k)     mov qword [b+o], simm32      REX.W C7 /0 id
;   (Jcc cc l)             jcc l              0F 80+cc rel32
;                          cc: B 2, AE 3, E 4, NE 5, BE 6, A 7, L 12, LE 14
;   (Jmp l)                jmp l              E9 rel32
;   (Push r) (Pop r)       push r / pop r     [REX] 50+r / [REX] 58+r
;   (Ret)                  ret                C3
;   (Place l)              defines label l here; no bytes (assembler only)
;
; (tisa-x86:encode I) is (Bytes (b ...)), or (Rel32 (b ...) LABEL) for a jump:
; its opcode bytes, then a rel32 the assembler resolves to LABEL.

(= (w-bit Q) 1)
(= (w-bit D) 0)

(= (op-rr-code ADD) 1)                  ; 01
(= (op-rr-code OR) 9)                   ; 09
(= (op-rr-code AND) 33)                 ; 21
(= (op-rr-code SUB) 41)                 ; 29
(= (op-rr-code XOR) 49)                 ; 31
(= (op-rr-code CMP) 57)                 ; 39
(= (op-rr-code TEST) 133)               ; 85
(= (op-rr-code MOV) 137)                ; 89

(= (op-rm-code ADD) 3)                  ; 03
(= (op-rm-code SUB) 43)                 ; 2B
(= (op-rm-code CMP) 59)                 ; 3B

(= (group1-ext ADD) 0)
(= (group1-ext AND) 4)
(= (group1-ext SUB) 5)
(= (group1-ext CMP) 7)

(= (shift-ext SHL) 4)
(= (shift-ext SHR) 5)
(= (shift-ext SAR) 7)

(= (cc-code B) 2) (= (cc-code AE) 3) (= (cc-code E) 4) (= (cc-code NE) 5)
(= (cc-code BE) 6) (= (cc-code A) 7) (= (cc-code L) 12) (= (cc-code LE) 14)

(= (load-opcode 1) (15 182))            ; 0F B6
(= (load-opcode 4) (139))               ; 8B
(= (load-opcode 8) (139))               ; 8B
(= (store-opcode 1) 136)                ; 88
(= (store-opcode 4) 137)                ; 89
(= (store-opcode 8) 137)                ; 89

(= (high-bit $n) (if (> $n 7) 1 0))
(= (low3 $n) (% $n 8))

; REX: W for 64-bit operands, R and B extending reg and base; force for the
; byte registers spl bpl sil dil.
(= (rex $w $reg $base $force)
   (let $x (+ (+ 64 (* 8 $w)) (+ (* 4 (high-bit $reg)) (high-bit $base)))
     (if (== $x 64) (if $force (64) ()) ($x))))

(= (modrm-rr $reg $rm) (+ 192 (+ (* 8 (low3 $reg)) (low3 $rm))))

; [base + disp32]; r12 as a base needs a SIB byte.
(= (modrm-mem $reg $base $disp)
   (let $m (+ 128 (+ (* 8 (low3 $reg)) (low3 $base)))
     (if (== (low3 $base) 4)
         (cons-atom $m (cons-atom 36 (le32 $disp)))
         (cons-atom $m (le32 $disp)))))

; Little-endian fields. A value that does not fit its field is rejected:
; 32-bit fields take a signed displacement or an unsigned immediate.
(= (le-bytes $u $n)
   (if (== $n 0) ()
       (let $b (% $u 256) (cons-atom $b (le-bytes (/ (- $u $b) 256) (- $n 1))))))
(= (le32 $x)
   (if (and (>= $x -2147483648) (< $x 4294967296))
       (le-bytes (% $x 4294967296) 4)
       (tisa-x86:reject (field-32 $x))))
(= (le64 $x)
   (if (and (>= $x 0) (< $x 18446744073709551616))
       (le-bytes $x 8)
       (tisa-x86:reject (field-64 $x))))
(= (imm8 $x) (if (and (>= $x 0) (< $x 256)) $x (tisa-x86:reject (field-8 $x))))

(= (tisa-x86:encode (OpRR $op $w $rm $reg))
   (let* (($g (reg-num $reg)) ($m (reg-num $rm)))
     (Bytes (append (rex (w-bit $w) $g $m False) ((op-rr-code $op) (modrm-rr $g $m))))))
(= (tisa-x86:encode (Movsxd $d $s))
   (let* (($dn (reg-num $d)) ($sn (reg-num $s)))
     (Bytes (append (rex 1 $dn $sn False) (99 (modrm-rr $dn $sn))))))
(= (tisa-x86:encode (Imul $d $s))
   (let* (($dn (reg-num $d)) ($sn (reg-num $s)))
     (Bytes (append (rex 1 $dn $sn False) (15 175 (modrm-rr $dn $sn))))))
(= (tisa-x86:encode (Cmov $cc $d $s))
   (let* (($dn (reg-num $d)) ($sn (reg-num $s)))
     (Bytes (append (rex 1 $dn $sn False) (15 (+ 64 (cc-code $cc)) (modrm-rr $dn $sn))))))
(= (tisa-x86:encode (Setcc $cc $d))
   (let $dn (reg-num $d)
     (Bytes (append (rex 0 0 $dn True) (15 (+ 144 (cc-code $cc)) (modrm-rr 0 $dn))))))
(= (tisa-x86:encode (Movzx8 $d $s))
   (let* (($dn (reg-num $d)) ($sn (reg-num $s)))
     (Bytes (append (rex 0 $dn $sn True) (15 182 (modrm-rr $dn $sn))))))
(= (tisa-x86:encode (ShiftImm $op $w $d $n))
   (let $dn (reg-num $d)
     (Bytes (append (rex (w-bit $w) 0 $dn False) (193 (modrm-rr (shift-ext $op) $dn) (imm8 $n))))))
(= (tisa-x86:encode (OpImm32 $op $w $d $k))
   (let $dn (reg-num $d)
     (Bytes (append (rex (w-bit $w) 0 $dn False)
                    (cons-atom 129 (cons-atom (modrm-rr (group1-ext $op) $dn) (le32 $k)))))))
(= (tisa-x86:encode (OpImm8 $op $w $d $k))
   (let $dn (reg-num $d)
     (Bytes (append (rex (w-bit $w) 0 $dn False) (131 (modrm-rr (group1-ext $op) $dn) (imm8 $k))))))
(= (tisa-x86:encode (MovImm32 $d $k))
   (let $dn (reg-num $d)
     (Bytes (append (rex 0 0 $dn False) (cons-atom (+ 184 (low3 $dn)) (le32 $k))))))
(= (tisa-x86:encode (MovImmSx $d $k))
   (let $dn (reg-num $d)
     (Bytes (append (rex 1 0 $dn False) (cons-atom 199 (cons-atom (modrm-rr 0 $dn) (le32 $k)))))))
(= (tisa-x86:encode (MovImm64 $d $k))
   (let $dn (reg-num $d)
     (Bytes (append (rex 1 0 $dn False) (cons-atom (+ 184 (low3 $dn)) (le64 $k))))))
(= (tisa-x86:encode (Load $w $d $b $o))
   (let* (($dn (reg-num $d)) ($bn (reg-num $b)))
     (Bytes (append (rex (if (== $w 8) 1 0) $dn $bn False)
                    (append (load-opcode $w) (modrm-mem $dn $bn $o))))))
(= (tisa-x86:encode (Store $w $s $b $o))
   (let* (($sn (reg-num $s)) ($bn (reg-num $b)))
     (Bytes (append (rex (if (== $w 8) 1 0) $sn $bn (== $w 1))
                    (cons-atom (store-opcode $w) (modrm-mem $sn $bn $o))))))
(= (tisa-x86:encode (OpRM $op $r $b $o))
   (let* (($rn (reg-num $r)) ($bn (reg-num $b)))
     (Bytes (append (rex 1 $rn $bn False) (cons-atom (op-rm-code $op) (modrm-mem $rn $bn $o))))))
(= (tisa-x86:encode (AddToMem $b $o $s))
   (let* (($sn (reg-num $s)) ($bn (reg-num $b)))
     (Bytes (append (rex 1 $sn $bn False) (cons-atom 1 (modrm-mem $sn $bn $o))))))
(= (tisa-x86:encode (StoreImm32 $b $o $k))
   (let $bn (reg-num $b)
     (Bytes (append (rex 1 0 $bn False) (cons-atom 199 (append (modrm-mem 0 $bn $o) (le32 $k)))))))
(= (tisa-x86:encode (Jcc $cc $l)) (Rel32 (15 (+ 128 (cc-code $cc))) $l))
(= (tisa-x86:encode (Jmp $l)) (Rel32 (233) $l))
(= (tisa-x86:encode (Push $r))
   (let $rn (reg-num $r) (Bytes (append (rex 0 0 $rn False) ((+ 80 (low3 $rn)))))))
(= (tisa-x86:encode (Pop $r))
   (let $rn (reg-num $r) (Bytes (append (rex 0 0 $rn False) ((+ 88 (low3 $rn)))))))
(= (tisa-x86:encode (Ret)) (Bytes (195)))

(= (encoded-length (Bytes $bs)) (length $bs))
(= (encoded-length (Rel32 $bs $l)) (+ (length $bs) 4))

; ---- 3. Macros -----------------------------------------------------------------
;
; A template is (Seq ITEM ...), each item an instruction or a macro call. A
; macro is a (Seq ...) of instructions and macros; it chooses among
; instruction forms by its arguments, exactly as the C helper it is named
; after does.

(= (mov64 $d $s) (if (== $d $s) (Seq) (Seq (OpRR MOV Q $d $s))))
(= (mov32 $d $s) (Seq (OpRR MOV D $d $s)))         ; zero-extends

(= (mov-imm $d $k)
   (if (<= $k 4294967295)
       (Seq (MovImm32 $d $k))
       (if (>= $k 18446744071562067968)             ; sign-extends from 32 bits
           (Seq (MovImmSx $d (% $k 4294967296)))
           (Seq (MovImm64 $d $k)))))

(= (normalize TyU64 $d) (Seq))
(= (normalize TyU32Z $d) (mov32 $d $d))
(= (normalize TyI32S $d) (Seq (Movsxd $d $d)))
(= (normalize TyBool $d) (Seq))
(= (normalize TyPtr $d) (Seq))

(= (op-width TyU64) Q)
(= (op-width TyU32Z) D)
(= (op-width TyI32S) D)
(= (op-width TyBool) Q)
(= (op-width TyPtr) Q)

(= (imm-value TyU64 $k) $k)
(= (imm-value TyU32Z $k) (% $k 4294967296))
(= (imm-value TyI32S $k) (sign-extend-32 (% $k 4294967296)))
(= (imm-value TyBool $k) $k)
(= (imm-value TyPtr $k) $k)
(= (sign-extend-32 $u) (if (>= $u 2147483648) (+ $u 18446744069414584320) $u))
(= (fits-simm32 $k) (or (< $k 2147483648) (>= $k 18446744071562067968)))

(= (pow2 $n) (if (== $n 0) 1 (* 2 (pow2 (- $n 1)))))

(= (condition CondEq) E)
(= (condition CondNe) NE)
(= (condition CondUlt) B)
(= (condition CondUle) BE)
(= (condition CondSlt) L)
(= (condition CondSle) LE)

(= (shift-op ShiftLeft) SHL)
(= (shift-op ShiftRightU) SHR)
(= (shift-op ShiftRightS) SAR)

(= (bin-instr BinAdd $into $other) (OpRR ADD Q $into $other))
(= (bin-instr BinSub $into $other) (OpRR SUB Q $into $other))
(= (bin-instr BinAnd $into $other) (OpRR AND Q $into $other))
(= (bin-instr BinOr $into $other) (OpRR OR Q $into $other))
(= (bin-instr BinXor $into $other) (OpRR XOR Q $into $other))
(= (bin-instr BinMulLo $into $other) (Imul $into $other))

; d := a op b. The operation runs in place on d, or on s0 when d is b and the
; operation does not commute.
(= (bin-operands $op $d $a $b)
   (if (== $d $a)
       (bin-core $op $d $d $b)
       (if (and (== $d $b) (!= $op BinSub))
           (bin-core $op $d $d $a)
           (if (== $d $b)
               (Seq (mov64 r14 $a) (bin-core $op $d r14 $b))
               (Seq (mov64 $d $a) (bin-core $op $d $d $b))))))
(= (bin-core $op $d $into $other) (Seq (bin-instr $op $into $other) (mov64 $d $into)))

; EXTRACT: d >>= l, then keep the low w bits.
(= (shift-down $d $l) (if (== $l 0) (Seq) (Seq (ShiftImm SHR Q $d $l))))
(= (keep-low $d $w)
   (if (<= $w 31)
       (Seq (OpImm32 AND D $d (- (pow2 $w) 1)))
       (if (== $w 32)
           (mov32 $d $d)
           (if (< $w 64)
               (Seq (ShiftImm SHL Q $d (- 64 $w)) (ShiftImm SHR Q $d (- 64 $w)))
               (Seq)))))

; CMP: flags from a and the right operand.
(= (compare $ty $a (OpReg $b)) (Seq (OpRR CMP (op-width $ty) $a $b)))
(= (compare $ty $a (OpImm $k))
   (if (== (op-width $ty) D)
       (Seq (OpImm32 CMP D $a (% $k 4294967296)))
       (if (fits-simm32 $k)
           (Seq (OpImm32 CMP Q $a (% $k 4294967296)))
           (Seq (mov-imm r14 $k) (OpRR CMP Q $a r14)))))

; s0 := s0 + o for a signed displacement, INVALID on carry or borrow.
(= (add-offset $o)
   (if (> $o 0)
       (Seq (OpImm32 ADD Q r14 $o) (Jcc B INVALID))
       (if (< $o 0)
           (Seq (mov-imm r15 (- 0 $o)) (OpRR SUB Q r14 r15) (Jcc B INVALID))
           (Seq))))

; INVALID unless [p + o, p + o + w) lies in region r. The pointer p is in r
; (its type says so), so q = p - base(r) is in [0, len(r)].
(= (bounds $r $p $o $w)
   (Seq (mov64 r14 $p)
        (OpRM SUB r14 rdi (region-base $r))         ; s0 = q
        (add-offset $o)                             ; s0 = q + o
        (Load 8 r15 rdi (region-len $r))            ; s1 = len
        (OpImm8 SUB Q r15 $w)                       ; s1 = len - w
        (Jcc B INVALID)
        (OpRR CMP Q r14 r15)                        ; q + o > len - w
        (Jcc A INVALID)))

; ADDR: the scaled index must not overflow, and q + index stays in the region.
(= (addr-index $r NONE $s) (Seq))
(= (addr-index $r (SOME $i) $s)
   (Seq (if (== $s 0) (Seq) (Seq (mov64 r15 $i) (ShiftImm SHR Q r15 (- 64 $s)) (Jcc NE INVALID)))
        (mov64 r15 $i)
        (if (== $s 0) (Seq) (Seq (ShiftImm SHL Q r15 $s)))
        (OpRR ADD Q r14 r15)
        (Jcc B INVALID)
        (OpRM CMP r14 rdi (region-len $r))          ; q + t <= len
        (Jcc A INVALID)))
(= (addr-disp $r $o)
   (if (== $o 0)
       (Seq)
       (Seq (add-offset $o)
            (if (> $o 0) (Seq (OpRM CMP r14 rdi (region-len $r)) (Jcc A INVALID)) (Seq)))))

; LOAD: a BOOL must be 0 or 1; a 32-bit type is normalized unless the load
; already produced its canonical form (frame loads are 8 bytes wide).
(= (load-check $ty $w $d)
   (Seq (if (== $ty TyBool) (Seq (OpImm8 CMP Q $d 1) (Jcc A INVALID)) (Seq))
        (if (and (== $ty TyU32Z) (== $w 8)) (mov32 $d $d) (Seq))
        (if (and (== $ty TyI32S) (!= $w 1)) (Seq (Movsxd $d $d)) (Seq))))

; ---- 4. The template table ----------------------------------------------------
;
; One entry per template: (tisa-x86:template NAME PARAMS) -> (Seq ITEM ...).
; Registers in PARAMS are hardware register names; labels are INVALID,
; UNSUPPORTED, EXHAUSTED, FAIL, EPILOGUE or a statement's (Local n).

; The public wrapper: save rbx r12 r13 r14 r15, restore them, return.
(= (tisa-x86:template PROLOGUE ())
   (Seq (Push rbx) (Push r12) (Push r13) (Push r14) (Push r15)))
; The shared failure handlers: the outcome code in eax becomes status and
; ret_val.
(= (tisa-x86:template FAILURE ())
   (Seq (Place UNSUPPORTED) (mov-imm rax (outcome UNSUPPORTED)) (Jmp FAIL)
        (Place INVALID) (mov-imm rax (outcome INVALID)) (Jmp FAIL)
        (Place EXHAUSTED) (mov-imm rax (outcome EXHAUSTED))
        (Place FAIL)
        (Store 8 rax rdi (frame-word STATUS))
        (Store 8 rax rdi (frame-word RET-VAL))))
(= (tisa-x86:template EPILOGUE ())
   (Seq (Place EPILOGUE) (Pop r15) (Pop r14) (Pop r13) (Pop r12) (Pop rbx) (Ret)))

; Instructions.
(= (tisa-x86:template IMM ($ty $d $k))
   (Seq (mov-imm $d (imm-value $ty $k))))
(= (tisa-x86:template MOV ($ty $d $a))
   (Seq (mov64 $d $a) (normalize $ty $d)))
(= (tisa-x86:template BIN ($op $ty $d $a $b))
   (Seq (bin-operands $op $d $a $b) (normalize $ty $d)))
(= (tisa-x86:template SHIFT ($op $ty $d $a $s))
   (Seq (mov64 $d $a) (ShiftImm (shift-op $op) (op-width $ty) $d $s) (normalize $ty $d)))
(= (tisa-x86:template EXTRACT ($ty $d $a $l $w))
   (Seq (mov64 $d $a) (shift-down $d $l) (keep-low $d $w) (normalize $ty $d)))
(= (tisa-x86:template CMP ($c $ty $d $a $rhs))
   (Seq (compare $ty $a $rhs) (Setcc (condition $c) $d) (Movzx8 $d $d)))
(= (tisa-x86:template SELECT ($ty $d $k $a $b))
   (Seq (mov64 r14 $b) (OpRR TEST Q $k $k) (Cmov NE r14 $a) (mov64 $d r14) (normalize $ty $d)))
(= (tisa-x86:template ADDR ($r $d $p $i $s $o))
   (Seq (mov64 r14 $p)
        (OpRM SUB r14 rdi (region-base $r))         ; s0 = q
        (addr-index $r $i $s)
        (addr-disp $r $o)
        (OpRM ADD r14 rdi (region-base $r))         ; back to an address
        (mov64 $d r14)))
(= (tisa-x86:template LOAD ($ty $w $r $d $p $o))
   (Seq (bounds $r $p $o $w) (Load $w $d $p $o) (load-check $ty $w $d)))
(= (tisa-x86:template LOAD-FRAME ($ty $d $j))
   (Seq (Load 8 $d rdi (* 8 $j)) (load-check $ty 8 $d)))
(= (tisa-x86:template STORE ($w $r $p $o $v))
   (Seq (bounds $r $p $o $w) (Store $w $v $p $o)))

; Control.
(= (tisa-x86:template IF ($c $no))
   (Seq (OpRR TEST Q $c $c) (Jcc E $no)))
(= (tisa-x86:template IF-ELSE ($end))
   (Seq (Jmp $end)))
(= (tisa-x86:template LOOP-ENTRY ($x $n $cap))
   (Seq (mov-imm r14 $cap)
        (OpRR CMP Q $n r14) (Jcc A UNSUPPORTED)     ; n > cap: UNSUPPORTED
        (OpRR XOR D $x $x)))                        ; x := 0
(= (tisa-x86:template LOOP-HEAD ($x $n $end))
   (Seq (OpRR CMP Q $x $n) (Jcc AE $end)))
(= (tisa-x86:template EARLY-LOOP-HEAD ($x $n $k $end))
   (Seq (OpRR CMP Q $x $n) (Jcc AE $end) (OpRR TEST Q $k $k) (Jcc E $end)))
(= (tisa-x86:template LOOP-LATCH ($x $top))
   (Seq (OpImm8 ADD Q $x 1) (Jmp $top)))
(= (tisa-x86:template EARLY-LOOP-LATCH ($x $k $top $end))
   (Seq (OpRR TEST Q $k $k) (Jcc E $end) (OpImm8 ADD Q $x 1) (Jmp $top)))
(= (tisa-x86:template RETURN ($o $r))
   (Seq (mov64 rax $r)
        (StoreImm32 rdi (frame-word STATUS) $o)
        (Store 8 rax rdi (frame-word RET-VAL))
        (Jmp EPILOGUE)))
(= (tisa-x86:template FUND ($u))
   (Seq (mov-imm r15 $u)
        (Load 8 r14 rdi (frame-word BUDGET))
        (OpRM SUB r14 rdi (frame-word USED))        ; allowance - receipt
        (OpRR CMP Q r14 r15)
        (Jcc B EXHAUSTED)
        (AddToMem rdi (frame-word USED) r15)))

; A template's instruction list: its items with every (Seq ...) spliced in.
(= (tisa-x86:code $name $params)
   (flat (tisa-x86:template $name $params) ()))
(= (flat $item $tail)
   (if (== (car-atom $item) Seq)
       (flat-list (cdr-atom $item) $tail)
       (cons-atom $item $tail)))
(= (flat-list $items $tail)
   (if (== $items ())
       $tail
       (let ($first $rest) (decons-atom $items) (flat $first (flat-list $rest $tail)))))

; ---- 5. Statements to a listing ----------------------------------------------
;
; The listing is the program's spans and label placements in image order:
; (Span TEMPLATE SOURCE CODE) and (Place LABEL). The walk prepends a statement
; to the listing of what follows it; n numbers the statements' own labels.

(= (span $name $source $params) (Span $name $source (tisa-x86:code $name $params)))

; Every number must fit the C field it was printed from (tisa.h): registers
; are v0..v11; region, scale, lsb, width and shift fields are uint8_t,
; displacements int32_t, caps, units and outcomes uint32_t, immediates
; uint64_t. A frame load's word index w has disp32 = 8w >= 0. A LOAD of region
; FRAME (255) is printed as TLoadFrame, never as TLoad.
(= (in-range $x $lo $hi $field) (if (and (>= $x $lo) (< $x $hi)) $x (tisa-x86:reject ($field $x))))
(= (u8 $x) (in-range $x 0 256 uint8))
(= (s32 $x) (in-range $x -2147483648 2147483648 int32))
(= (u32 $x) (in-range $x 0 4294967296 uint32))
(= (u64 $x) (in-range $x 0 18446744073709551616 uint64))
(= (load-region $r) (in-range $r 0 255 TLoad-region))
(= (frame-index $j) (in-range $j 0 268435456 TLoadFrame-word-index))

(= (instr-span $i)
   (case $i
     (((TImm $ty1 $d1 $k1)
       (span IMM $i ($ty1 (vreg $d1) (u64 $k1))))
      ((TMov $ty2 $d2 $a2)
       (span MOV $i ($ty2 (vreg $d2) (vreg $a2))))
      ((TBin $op3 $ty3 $d3 $a3 $b3)
       (span BIN $i ($op3 $ty3 (vreg $d3) (vreg $a3) (vreg $b3))))
      ((TShift $op4 $ty4 $d4 $a4 $s4)
       (span SHIFT $i ($op4 $ty4 (vreg $d4) (vreg $a4) (u8 $s4))))
      ((TExtract $ty5 $d5 $a5 $l5 $w5)
       (span EXTRACT $i ($ty5 (vreg $d5) (vreg $a5) (u8 $l5) (u8 $w5))))
      ((TCmp $c6 $ty6 $d6 $a6 (OpReg $b6))
       (span CMP $i ($c6 $ty6 (vreg $d6) (vreg $a6) (OpReg (vreg $b6)))))
      ((TCmp $c7 $ty7 $d7 $a7 (OpImm $k7))
       (span CMP $i ($c7 $ty7 (vreg $d7) (vreg $a7) (OpImm (u64 $k7)))))
      ((TSelect $ty8 $d8 $k8 $a8 $b8)
       (span SELECT $i ($ty8 (vreg $d8) (vreg $k8) (vreg $a8) (vreg $b8))))
      ((TAddr $r9 $d9 $p9 NONE $s9 $o9)
       (span ADDR $i ((u8 $r9) (vreg $d9) (vreg $p9) NONE (u8 $s9) (s32 $o9))))
      ((TAddr $r10 $d10 $p10 (SOME $x10) $s10 $o10)
       (span ADDR $i ((u8 $r10) (vreg $d10) (vreg $p10) (SOME (vreg $x10)) (u8 $s10) (s32 $o10))))
      ((TLoad $ty11 $w11 $r11 $d11 $p11 $o11)
       (span LOAD $i ($ty11 $w11 (load-region $r11) (vreg $d11) (vreg $p11) (s32 $o11))))
      ((TLoadFrame $ty12 $d12 $j12)
       (span LOAD-FRAME $i ($ty12 (vreg $d12) (frame-index $j12))))
      ((TStore $w13 $r13 $p13 $o13 $v13)
       (span STORE $i ($w13 (u8 $r13) (vreg $p13) (s32 $o13) (vreg $v13))))
      ($other (tisa-x86:reject (instruction $other))))))

(= (walk $s $rest $n)
   (case $s
     ((TSkip (Walk $rest $n))
      ((TInstr $i1) (Walk (cons-atom (instr-span $i1) $rest) $n))
      ((TSeq $a2 $b2)
       (let (Walk $after2 $n2) (walk $b2 $rest $n) (walk $a2 $after2 $n2)))
      ((TIf $c3 $a3 $b3) (walk-if $c3 $a3 $b3 $rest $n))
      ((TCountLoop $x4 $m4 $cap4 $body4)
       (walk-loop (TCountLoop $x4 $m4 $cap4) $body4 $rest $n))
      ((TEarlyLoop $x5 $m5 $k5 $cap5 $body5)
       (walk-loop (TEarlyLoop $x5 $m5 $k5 $cap5) $body5 $rest $n))
      ((TReturn $o6 $r6)
       (Walk (cons-atom (span RETURN $s ((u32 $o6) (vreg $r6))) $rest) $n))
      ((TFund $u7)
       (Walk (cons-atom (span FUND $s ((u32 $u7))) $rest) $n))
      ($other (tisa-x86:reject (statement $other))))))

; IF: test c, skip the then-branch when c is 0; an else-branch adds a jump
; over itself.
(= (walk-if $c $then $else $rest $n)
   (let* (($cr (vreg $c))
          ($no (Local $n))
          ($end (Local (+ $n 1)))
          ($n1 (+ $n 2)))
     (if (== $else TSkip)
         (let (Walk $listing $n2) (walk $then (cons-atom (Place $no) $rest) $n1)
           (Walk (cons-atom (span IF (TIf $c) ($cr $no)) $listing) $n2))
         (let* (((Walk $else-listing $n3) (walk $else (cons-atom (Place $end) $rest) $n1))
                ((Walk $then-listing $n4)
                 (walk $then (cons-atom (span IF-ELSE (TIf $c) ($end))
                                        (cons-atom (Place $no) $else-listing))
                       $n3)))
           (Walk (cons-atom (span IF (TIf $c) ($cr $no)) $then-listing) $n4)))))

; Loops: entry (cap check, x := 0), head at label top, body, latch jumping
; back to top; the exits go to end. SOURCE is the loop without its body.
(= (walk-loop $source $body $rest $n)
   (let* (($top (Local $n))
          ($end (Local (+ $n 1)))
          ((Walk $body-listing $n1)
           (walk $body
                 (cons-atom (loop-latch $source $top $end) (cons-atom (Place $end) $rest))
                 (+ $n 2))))
     (Walk (cons-atom (loop-entry $source)
             (cons-atom (Place $top) (cons-atom (loop-head $source $end) $body-listing)))
           $n1)))

(= (loop-entry (TCountLoop $x $m $cap))
   (span LOOP-ENTRY (TCountLoop $x $m $cap) ((vreg $x) (vreg $m) (u32 $cap))))
(= (loop-entry (TEarlyLoop $x $m $k $cap))
   (span LOOP-ENTRY (TEarlyLoop $x $m $k $cap) ((vreg $x) (vreg $m) (u32 $cap))))
(= (loop-head (TCountLoop $x $m $cap) $end)
   (span LOOP-HEAD (TCountLoop $x $m $cap) ((vreg $x) (vreg $m) $end)))
(= (loop-head (TEarlyLoop $x $m $k $cap) $end)
   (span EARLY-LOOP-HEAD (TEarlyLoop $x $m $k $cap) ((vreg $x) (vreg $m) (vreg $k) $end)))
(= (loop-latch (TCountLoop $x $m $cap) $top $end)
   (span LOOP-LATCH (TCountLoop $x $m $cap) ((vreg $x) $top)))
(= (loop-latch (TEarlyLoop $x $m $k $cap) $top $end)
   (span EARLY-LOOP-LATCH (TEarlyLoop $x $m $k $cap) ((vreg $x) (vreg $k) $top $end)))

(= (tisa-x86:listing (TProg $decls $inits $root))
   (let (Walk $body $n)
        (walk $root ((span FAILURE Wrapper ()) (span EPILOGUE Wrapper ())) 0)
     (cons-atom (span PROLOGUE Wrapper ()) $body)))

; ---- 6. The assembler ----------------------------------------------------------
;
; Layout encodes every instruction once, placing labels and recording spans;
; then every rel32 becomes target - (end of its instruction), as tisa_x86.c
; resolves its fixes.

(= (lay-listing $listing $off $encs $labels $spans)
   (if (== $listing ())
       (Laid (reverse $encs) $labels (reverse $spans))
       (let ($entry $more) (decons-atom $listing)
         (case $entry
           (((Place $l1)
             (lay-listing $more $off $encs (cons-atom ($l1 $off) $labels) $spans))
            ((Span $name $source $code)
             (let (Coded $end $encs2 $labels2) (lay-code $code $off $encs $labels)
               (lay-listing $more $end $encs2 $labels2
                            (cons-atom (SpanAt $off (- $end $off) $name $source $code) $spans))))
            ($other (tisa-x86:reject (listing-entry $other))))))))

(= (lay-code $code $off $encs $labels)
   (if (== $code ())
       (Coded $off $encs $labels)
       (let ($instr $more) (decons-atom $code)
         (case $instr
           (((Place $l2) (lay-code $more $off $encs (cons-atom ($l2 $off) $labels)))
            ($other
             (let $enc (tisa-x86:encode $other)
               (lay-code $more (+ $off (encoded-length $enc)) (cons-atom $enc $encs) $labels))))))))

(= (label-offset $l $labels)
   (if (== $labels ())
       (tisa-x86:reject (unplaced-label $l))
       (let (($name $at) $more) (decons-atom $labels)
         (if (== $name $l) $at (label-offset $l $more)))))

(= (resolve $encs $off $labels)
   (if (== $encs ())
       ()
       (let ($enc $more) (decons-atom $encs)
         (let $end (+ $off (encoded-length $enc))
           (append (resolved-bytes $enc $end $labels) (resolve $more $end $labels))))))
(= (resolved-bytes (Bytes $bs) $end $labels) $bs)
(= (resolved-bytes (Rel32 $bs $l) $end $labels)
   (append $bs (le32 (- (label-offset $l $labels) $end))))

(= (tisa-x86:assemble $listing)
   (let (Laid $encs $labels $spans) (lay-listing $listing 0 () () ())
     (Image (resolve $encs 0 $labels) $spans $labels)))

; Exactly one image per program, or a loud stop.
(= (tisa-x86:emit $program)
   (let $images (collapse (tisa-x86:assemble (tisa-x86:listing $program)))
     (if (== (length $images) 1)
         (car-atom $images)
         (tisa-x86:reject (images (length $images) $program)))))
