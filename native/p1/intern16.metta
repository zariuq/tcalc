; intern16.metta -- intern16 authored with p1.metta: find-or-make of the
; 16-byte key (arg0, arg1) among rows of 16 bytes, through a table of
; 8-byte slots (0 empty, id + 1 occupied) probed linearly from a hash.
; A FIRED run returns an id whose row is the key: an existing row below the
; count, or a row appended at the count. Nothing about the table is
; trusted: a slot's id is checked against the count, and the count against
; the rows' capacity. (The C original is tcalc/native/intern/intern_p1.c;
; its proofs are tcalc/native/hol/intern16.ml.)
;
;   cetta --no-results intern16.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Registers, by role. The templates below use these names; a program binds
; them to machine registers (Registers), or a caller renames them (With):
;   k0 k1   the key            count  the row count     mask  slots - 1
;   hash    the key's hash     slots  the table's slots  probe the probe index
;   t8..t11 temporaries, given role names inside each block

!(import! &self "p1.metta")

; The key, the count (UNSUPPORTED above the rows' capacity), the mask, the hash.
(= (intern16:prologue $rows $table $header)
   (Block intern16_prologue
     (Spec intern16_prologue
       "\\st. st = st0"
       "\\s. tregs s 0 = tregs st0 0 /\\ tmem s = tmem st0 /\\ tregs s 1 = tisa_fword st0 22 /\\ tregs s 2 = tisa_fword st0 23 /\\ tregs s 3 = intern_count st0 /\\ val(intern_count st0) <= val(tisa_len st0 0) DIV 16"
       "\\k s. ~(k = 1)"
       (With (As header-at t8) (As capacity t9) (As too-many t10) (As one t9) (As golden t9) (As high t9)
         (Arg0 k0) (Arg1 k1)
         (Base header-at $header) (Load $header count header-at 0)
         (Len capacity $rows) (Shr capacity capacity 4)
         (Cmp Ult too-many capacity count)
         (If too-many (Return UNSUPPORTED count))
         (Len slots $table) (Shr slots slots 3)
         (Imm one 1) (Sub mask slots one)
         (Xor hash k0 k1) (Imm golden 11400714819323198485) (Mul hash hash golden)
         (Shr high hash 29) (Xor hash hash high)))))

; One probe: the slot at (hash + probe) & mask.
(= (intern16:body $rows $table $header)
   (Block intern16_body
     (Spec intern16_body
       "\\st. intern16_regions st0 /\\ tregs st 0 = tregs st0 0 /\\ tmem st = tmem st0 /\\ tregs st 1 = tisa_fword st0 22 /\\ tregs st 2 = tisa_fword st0 23 /\\ tregs st 3 = intern_count st0"
       "\\s. tregs s 0 = tregs st0 0 /\\ tmem s = tmem st0 /\\ tregs s 1 = tisa_fword st0 22 /\\ tregs s 2 = tisa_fword st0 23 /\\ tregs s 3 = intern_count st0"
       "\\k s. k = 1 ==> intern16_post st0 s"
       (With (As slot t8) (As slot-at t9) (As entry t10) (As empty t11)
         (Add slot hash probe) (And slot slot mask)
         (Base slot-at $table) (Addr $table slot-at slot-at slot 3 0)
         (Load $table entry slot-at 0)
         (CmpI Eq empty entry 0)
         (If empty
             (intern16:append-if-room $rows $table $header)
             (intern16:check-occupied $rows))))))

; An empty slot: append the key at the count if a row is free.
(= (intern16:append-if-room $rows $table $header)
   (With (As capacity t10) (As room t11) (As offset t10) (As row-at t11) (As next t10) (As slot-at t9) (As header-at t11)
     (Len capacity $rows) (Shr capacity capacity 4)
     (Cmp Ult room count capacity)
     (If room
         (Seq (Shl offset count 1)
              (Base row-at $rows) (Addr $rows row-at row-at offset 3 0)
              (Store $rows row-at 0 k0) (Store $rows row-at 8 k1)
              (Imm next 1) (Add next count next)
              (Store $table slot-at 0 next)
              (Base header-at $header) (Store $header header-at 0 next)
              (Return FIRED count))
         (Return UNSUPPORTED count))))

; An occupied slot holds id + 1; an id below the count whose row is the key is
; the answer.
(= (intern16:check-occupied $rows)
   (With (As one t11) (As entry t10) (As id t10) (As below t11) (As offset t11) (As row-at t8) (As word t11)
     (Imm one 1) (Sub id entry one)
     (Cmp Ult below id count)
     (If below
         (Seq (Shl offset id 1)
              (Base row-at $rows) (Addr $rows row-at row-at offset 3 0)
              (Load $rows word row-at 0) (Cmp Eq word word k0)
              (If word
                  (Seq (Load $rows word row-at 8) (Cmp Eq word word k1)
                       (If word (Return FIRED id))))))))

; Find-or-make with the probe loop capped at CAP slots.
(= (intern16:find-or-make $rows $table $header $cap)
   (Seq (intern16:prologue $rows $table $header)
        (Invariant intern16_probe
          "\\s. tregs s 0 = tregs st 0 /\\ tmem s = tmem st /\\ tregs s 1 = tisa_fword st 22 /\\ tregs s 2 = tisa_fword st 23 /\\ tregs s 3 = intern_count st"
          (Loop probe slots $cap (intern16:body $rows $table $header)))
        (Return UNSUPPORTED count)))

(= (intern16:program)
   (p1:program intern16
     (Regions (Region rows RW 16 8) (Region table RW 8 8) (Region header RW 8 8))
     (Registers (As k0 v1) (As k1 v2) (As count v3) (As mask v4) (As hash v5) (As slots v6)
                (As probe v7) (As t8 v8) (As t9 v9) (As t10 v10) (As t11 v11))
     (Init)
     (intern16:find-or-make rows table header 16777216)))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write intern16:program $text $notes))
