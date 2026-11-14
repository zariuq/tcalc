; leb_next.metta -- the reader's leaf 26 (tcalc/native/PLANS.txt, sections 2
; and 10): the minimal unsigned LEB128 at the reader's cursor, authored with
; p1.metta as one standalone t-ISA p1 program; leb128's decoder with the
; offset kept in the reader's state. Its specification is pl_leb_next_spec
; (tcalc/native/hol/plans_leaves.ml); the proof is leb_next.ml.
;
;   cetta --no-results leb_next.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Regions: 0 input (RO), the stream's bytes; 1 the reader's state (RW, 16
; bytes; word 0 the cursor, word 1 work). No arguments.
;
; The integer at the cursor is read as leb128 reads it at its offset. Outcomes:
;   FIRED     ret_val = the value; state word 0 = the cursor plus the number
;             of bytes it took, word 1 = the value
;   REFUSED 1 a malformed integer
;   REFUSED 2 the input ends first (also when the cursor lies past the end)
; A refused run writes no memory.

!(import! &self "../../p1/p1.metta")

; 2^62, the bound on values.
(= (leb_next:limit) 4611686018427387904)

; The entry: the offset, and the bytes available from it.
(= (leb_next:prologue)
   (Block leb_next_prologue
     (Base ptr state) (Load state off ptr 0)
     (Len avail input)
     (Cmp Ult t avail off)
     (If t (Seq (Imm u 2) (Return REFUSED u)))
     (Sub avail avail off)
     (Base at input)
     (Addr input at at off 0 0)
     (Imm acc 0) (Imm scale 1) (Imm nine 9)))

; Byte idx ends the integer: refuse a non-minimal form or a value too large,
; else advance the cursor past it, keep the value, and fire.
(= (leb_next:final)
   (Seq
     (CmpI Ne t ix 0) (CmpI Eq u byte 0) (Bin BinAnd TyBool t t u)
     (If t (Seq (Imm u 1) (Return REFUSED u)))
     (Mul byte byte scale) (Add acc acc byte)
     (Imm u (leb_next:limit)) (Cmp Ule t u acc)
     (If t (Seq (Imm u 1) (Return REFUSED u)))
     (Base ptr state) (Load state u ptr 0) (Add u u ix) (Imm t 1) (Add u u t)
     (Store state ptr 0 u) (Store state ptr 8 acc)
     (Return FIRED acc)))

; Byte idx has its high bit: its seven bits, and the next scale.
(= (leb_next:continue)
   (Seq (Imm u 128) (Sub byte byte u) (Mul byte byte scale) (Add acc acc byte)
        (Shl scale scale 7)))

; One byte: none left is the end of the input. The comparisons read ix, a
; copy of the loop index: t-ISA's image prover does not yet decide a
; comparison that sets ZF on the count loop's own index register (it names
; that register word j0, and its compare finish rewrites val (word j0) to
; j0 MOD 2^64 in the facts but not in the goal), so the index is copied into
; a register the loop does not name.
(= (leb_next:body)
   (Block leb_next_body
     (Mov ix idx)
     (Cmp Ule t avail ix)
     (If t (Seq (Imm u 2) (Return REFUSED u)))
     (Addr input ptr at idx 0 0)
     (Load 1 TyU64 input byte ptr 0)
     (CmpI Ult t byte 128)
     (If t (leb_next:final) (leb_next:continue))))

(= (leb_next:program)
   (p1:program leb_next
     (Regions (Region input RO 0 1) (Region state RW 16 8))
     (Registers (As off v1) (As ix v1) (As avail v2) (As at v3) (As acc v4) (As scale v5) (As idx v6)
                (As nine v7) (As byte v8) (As t v9) (As u v10) (As ptr v11))
     (Init)
     (Seq (leb_next:prologue)
          (Invariant leb_next_inv
            "\\N i s. tregs s 0 = tregs st 0 /\\ tmem s = tmem st /\\ N = 9 /\\ val(tisa_read st (tisa_base st 1) 8) <= val(tisa_len st 0) /\\ tregs s 2 = word_sub (tisa_len st 0) (tisa_read st (tisa_base st 1) 8) /\\ tregs s 3 = word_add (tisa_base st 0) (word (1 * val (tisa_read st (tisa_base st 1) 8))) /\\ tregs s 4 = word (leb_dec (list_of_seq (\\j. region_byte st 0 (val(tisa_read st (tisa_base st 1) 8) + j)) i)) /\\ tregs s 5 = word (128 EXP i) /\\ i <= val(tisa_len st 0) - val(tisa_read st (tisa_base st 1) 8) /\\ (!j. j < i ==> 128 <= region_byte st 0 (val(tisa_read st (tisa_base st 1) 8) + j))"
            (Loop idx nine 9 (leb_next:body)))
          ; nine bytes with the high bit
          (Imm u 1) (Return REFUSED u))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write leb_next:program $text $notes))
