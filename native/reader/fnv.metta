; fnv.metta -- FNV-1a 64 over a byte range of a region, authored with
; p1.metta: one t-ISA p1 program, proved on its own (NATIVE-CHECKER.txt,
; section 6; tcalc/native/hol/reader_fnv.ml). The HOLR reader keeps END's
; checksum with it: the state so far, continued over each record's bytes.
;
;   cetta --no-results fnv.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Region 0 input (RO). Arguments: arg0 the range's offset, arg1 its length;
; the initial state is the entry register v1 (p1 has two frame arguments,
; and the range takes both). Each byte b turns the state h into
; (h xor b) * 1099511628211, mod 2^64. Outcomes:
;   FIRED        ret_val = the state after the range's bytes
;   REFUSED 1    the range does not lie inside the input
;   UNSUPPORTED  a range longer than the loop's cap, 2^32 - 1 bytes
; No run writes memory outside the frame's status and return words.
;
; Registers: h the state; off and n the range; avail the bytes from off to
; the input's end; at the address of the range's first byte; idx the byte
; index; byte the byte; ptr its address; t a working register; prime the
; FNV-1a 64 prime.

!(import! &self "../p1/p1.metta")

(= (fnv:prime) 1099511628211)

; The range, checked against the input.
(= (fnv:prologue)
   (Block fnv_prologue
     (Arg0 off) (Arg1 n)
     (Len avail input)
     (Cmp Ult t avail off)
     (If t (Seq (Imm ptr 1) (Return REFUSED ptr)))
     (Sub avail avail off)
     (Cmp Ult t avail n)
     (If t (Seq (Imm ptr 1) (Return REFUSED ptr)))
     (Base at input)
     (Addr input at at off 0 0)
     (Imm prime (fnv:prime))))

; One byte.
(= (fnv:body)
   (Block fnv_body
     (Addr input ptr at idx 0 0)
     (Load 1 TyU64 input byte ptr 0)
     (Xor h h byte)
     (Mul h h prime)))

(= (fnv:program)
   (p1:program fnv
     (Regions (Region input RO 0 1))
     (Registers (As h v1) (As off v2) (As n v3) (As avail v4) (As at v5) (As idx v6)
                (As byte v7) (As ptr v8) (As t v9) (As prime v10))
     (Init (Entry h TyU64))
     (Seq (fnv:prologue)
          (Invariant fnv_inv
            "\\N i s. tregs s 0 = tregs st 0 /\\ tmem s = tmem st /\\ N = val(tisa_fword st 23) /\\ val(tisa_fword st 22) + val(tisa_fword st 23) <= val(tisa_len st 0) /\\ tregs s 5 = word_add (tisa_base st 0) (word (1 * val (tisa_fword st 22))) /\\ tregs s 10 = word 1099511628211 /\\ tregs s 1 = fnv1a (tregs st 1) (list_of_seq (\\j. region_byte st 0 (val(tisa_fword st 22) + j)) i)"
            (Loop idx n 4294967295 (fnv:body)))
          (Return FIRED h))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write fnv:program $text $notes))
