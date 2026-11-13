; leb128.metta -- the HOLR reader's unsigned LEB128 decoder, authored with
; p1.metta: one t-ISA p1 program, proved on its own (NATIVE-CHECKER.txt,
; section 6; tcalc/native/hol/reader_leb128.ml).
;
;   cetta --no-results leb128.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Regions: 0 input (RO), the stream's bytes; 1 out (RW, 16 bytes).
; Argument: arg0, the offset of the integer's first byte in the input.
;
; The integer is minimal unsigned LEB128 below 2^62 (so at most 9 bytes), read
; as CeTTa's reader reads it (hol_stream.c, cur_uv): byte i adds its seven low
; bits at 7i; a byte without its high bit ends the integer; at the end, a
; final byte 0 after a continuation, or a value of 2^62 or more, is malformed;
; a continuation on the ninth byte is malformed; no byte where one is needed
; is the end of the input. Outcomes:
;   FIRED     ret_val = the value; out word 0 = the value, word 1 = the number
;             of bytes it took
;   REFUSED 1 a malformed integer
;   REFUSED 2 the input ends first (also when the offset lies past the end)
; A refused run writes no memory. t-ISA shifts by immediates only, so byte i's
; bits are scaled by a multiplier, 128^i, kept in a register (scale) and
; shifted by 7 after each continuation byte.
;
; Registers: off the offset (then ix, the byte index's copy); avail the bytes
; from the offset to the input's end; at the address of the integer's first
; byte; acc the value so far; scale 128^i; idx the byte index i; nine the loop
; bound; byte the byte; t, u, ptr working registers.

!(import! &self "../p1/p1.metta")

; 2^62, the bound on values.
(= (leb128:limit) 4611686018427387904)

; The entry: the offset, and the bytes available from it.
(= (leb128:prologue)
   (Block leb128_prologue
     (Arg0 off)
     (Len avail input)
     (Cmp Ult t avail off)
     (If t (Seq (Imm u 2) (Return REFUSED u)))
     (Sub avail avail off)
     (Base at input)
     (Addr input at at off 0 0)
     (Imm acc 0) (Imm scale 1) (Imm nine 9)))

; Byte idx ends the integer: refuse a non-minimal form or a value too large,
; else write the value and its length, and fire.
(= (leb128:final)
   (Seq
     (CmpI Ne t ix 0) (CmpI Eq u byte 0) (Bin BinAnd TyBool t t u)
     (If t (Seq (Imm u 1) (Return REFUSED u)))
     (Mul byte byte scale) (Add acc acc byte)
     (Imm u (leb128:limit)) (Cmp Ule t u acc)
     (If t (Seq (Imm u 1) (Return REFUSED u)))
     (Base ptr out) (Store out ptr 0 acc)
     (Imm u 1) (Add u ix u) (Store out ptr 8 u)
     (Return FIRED acc)))

; Byte idx has its high bit: its seven bits, and the next scale.
(= (leb128:continue)
   (Seq (Imm u 128) (Sub byte byte u) (Mul byte byte scale) (Add acc acc byte)
        (Shl scale scale 7)))

; One byte: none left is the end of the input. The comparisons read ix, a
; copy of the loop index: t-ISA's image prover does not yet decide a
; comparison that sets ZF on the count loop's own index register (it names
; that register word j0, and its compare finish rewrites val (word j0) to
; j0 MOD 2^64 in the facts but not in the goal), so the index is copied into
; a register the loop does not name.
(= (leb128:body)
   (Block leb128_body
     (Mov ix idx)
     (Cmp Ule t avail ix)
     (If t (Seq (Imm u 2) (Return REFUSED u)))
     (Addr input ptr at idx 0 0)
     (Load 1 TyU64 input byte ptr 0)
     (CmpI Ult t byte 128)
     (If t (leb128:final) (leb128:continue))))

(= (leb128:program)
   (p1:program leb128
     (Regions (Region input RO 0 1) (Region out RW 16 8))
     (Registers (As off v1) (As ix v1) (As avail v2) (As at v3) (As acc v4) (As scale v5) (As idx v6)
                (As nine v7) (As byte v8) (As t v9) (As u v10) (As ptr v11))
     (Init)
     (Seq (leb128:prologue)
          (Invariant leb128_inv
            "\\N i s. tregs s 0 = tregs st 0 /\\ tmem s = tmem st /\\ N = 9 /\\ val(tisa_fword st 22) <= val(tisa_len st 0) /\\ tregs s 2 = word_sub (tisa_len st 0) (tisa_fword st 22) /\\ tregs s 3 = word_add (tisa_base st 0) (word (1 * val (tisa_fword st 22))) /\\ tregs s 4 = word (leb_dec (list_of_seq (\\j. region_byte st 0 (val(tisa_fword st 22) + j)) i)) /\\ tregs s 5 = word (128 EXP i) /\\ i <= val(tisa_len st 0) - val(tisa_fword st 22) /\\ (!j. j < i ==> 128 <= region_byte st 0 (val(tisa_fword st 22) + j))"
            (Loop idx nine 9 (leb128:body)))
          ; nine bytes with the high bit
          (Imm u 1) (Return REFUSED u))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write leb128:program $text $notes))
