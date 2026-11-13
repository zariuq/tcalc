; intern_name.metta -- interning of names (byte strings), authored with
; p1.metta: one t-ISA p1 program, proved on its own (NATIVE-CHECKER.txt,
; sections 4 and 6; tcalc/native/hol/intern_name.ml). HOLR's NAME record
; carries a byte string; the checker interns it, so that equal names get
; equal name ids.
;
;   cetta --no-results intern_name.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Regions:
;   0 input   RO  the stream's bytes; the name is arg1 bytes from offset arg0
;   1 rows    RW  name rows, 16 bytes each: (offset into the arena, length)
;   2 arena   RW  the name bytes, packed
;   3 table   RW  8-byte slots: 0 empty, id + 1 used
;   4 header  RW  word 0 the row count, word 1 the arena bytes used
; Entry register v1 is the name's hash. The plan computes it with the fnv
; leaf; nothing here trusts it: a slot is a hint, re-checked against the
; count and, byte for byte, against the name.
;
; The table is probed linearly from the hash: position (hash + x) and
; (slots - 1) for x = 0, 1, ... A used slot whose id is below the count
; names a row; a row of the name's length is compared with the name byte
; for byte, and a match is the answer. An empty slot ends the search: the
; name's bytes are copied to the arena at the bytes used, the row (used,
; length) is written at the count, the slot is set to count + 1, and the
; two header words are written last: the publication. Outcomes:
;   FIRED         ret_val = the name's id
;   REFUSED 1     the name does not lie inside the input
;   UNSUPPORTED 1 rows full     3 every slot probed (table full)
;               4 arena full    5 a header word above its region's capacity
;               6 a row of the name's length lying outside the used arena
;               2 a loop above its cap (more slots, or a longer name, than
;                 2^32 - 1)
; Every refusal and every UNSUPPORTED outcome writes no region.
;
; Registers: hash is v1; probe and slots, the probe loop's index and bound,
; are v2 and v3. Inside a probe, v4 .. v11 take the roles each block names.
;
; The invariants are HOL texts over st, the state on entry, and, for the
; comparison and the copy, sq, the state on entry to the inner loop; they are
; defined in tcalc/native/hol/intern_name.ml.

!(import! &self "../p1/p1.metta")

(= (name:cap) 4294967295)

; The name lies inside the input; the header words lie inside their
; regions; the table's slots.
(= (name:prologue)
   (Block name_prologue
     (With (As off v4) (As n v5) (As ilen v6) (As bad v7) (As code v8) (As hdr v8) (As word v9)
           (As cap v10)
       (Arg0 off) (Arg1 n)
       (Len ilen input)
       (Cmp Ult bad ilen off)
       (If bad (Seq (Imm code 1) (Return REFUSED code)))
       (Sub ilen ilen off)
       (Cmp Ult bad ilen n)
       (If bad (Seq (Imm code 1) (Return REFUSED code)))
       (Base hdr header) (Load header word hdr 0)
       (Len cap rows) (Shr cap cap 4)
       (Cmp Ult bad cap word)
       (If bad (Seq (Imm word 5) (Return UNSUPPORTED word)))
       (Load header word hdr 8)
       (Len cap arena)
       (Cmp Ult bad cap word)
       (If bad (Seq (Imm word 5) (Return UNSUPPORTED word)))
       (Len slots table) (Shr slots slots 3))))

; One byte of the comparison: eq := eq and (arena byte i = name byte i).
(= (name:cmp-body)
   (Block name_cmp_body
     (With (As i v6) (As at v7) (As from v8) (As eq v9) (As a v10) (As b v11)
       (Addr arena a at i 0 0) (Load 1 TyU64 arena a a 0)
       (Addr input b from i 0 0) (Load 1 TyU64 input b b 0)
       (Cmp Eq a a b)
       (Bin BinAnd TyBool eq eq a))))

; A row of the name's length: its bytes must lie inside the used arena;
; compared with the name byte for byte, a match is the answer.
(= (name:compare)
   (Block name_compare
     (With (As id v4) (As n v5) (As i v6) (As bad v7) (As hdr v8) (As used v9) (As roff v10)
           (As row v11) (As at v7) (As from v8) (As ibase v9) (As eq v9)
       (Load rows roff row 0)
       (Load header used hdr 8)
       (Cmp Ult bad used roff)
       (If bad (Seq (Imm bad 6) (Return UNSUPPORTED bad)))
       (Sub used used roff)
       (Cmp Ult bad used n)
       (If bad (Seq (Imm bad 6) (Return UNSUPPORTED bad)))
       (Base at arena) (Addr arena at at roff 0 0)
       (Arg0 from) (Base ibase input) (Addr input from ibase from 0 0)
       (Imm TyBool eq 1)
       (Invariant name_cmp_inv "\\N i s. name_cmp_inv st sq N i s"
         (Loop i n (name:cap) (name:cmp-body)))
       (If eq (Return FIRED id)))))

; The slot's row, when its id is below the count: a row of the name's
; length is compared.
(= (name:row)
   (Block name_row
     (With (As id v4) (As n v5) (As same v7) (As twice v10) (As rlen v10) (As row v11)
       (Shl twice id 1) (Base row rows) (Addr rows row row twice 3 0)
       (Load rows rlen row 8)
       (Arg1 n)
       (Cmp Eq same rlen n)
       (If same (name:compare)))))

; A used slot holds id + 1.
(= (name:occupied)
   (Block name_occupied
     (With (As e v7) (As one v4) (As id v4) (As hdr v8) (As count v9) (As below v10)
       (Imm one 1) (Sub id e one)
       (Base hdr header) (Load header count hdr 0)
       (Cmp Ult below id count)
       (If below (name:row)))))

; One byte of the copy: arena byte i := name byte i.
(= (name:copy-body)
   (Block name_copy_body
     (With (As i v4) (As at v7) (As p v8) (As byte v9) (As from v11)
       (Addr input p from i 0 0) (Load 1 TyU64 input byte p 0)
       (Addr arena p at i 0 0) (Store 1 arena p 0 byte))))

; Room for the row and the bytes: copy the bytes, write the row and the
; slot, then publish: the two header words, last.
(= (name:append-room)
   (Block name_append_room
     (With (As i v4) (As bad v4) (As off v4) (As twice v4) (As next v4) (As n v5) (As slot-at v6)
           (As at v7) (As row v7) (As hdr v8) (As count v9) (As used v10) (As avail v11) (As from v11)
       (Load header used hdr 8)
       (Arg1 n)
       (Len avail arena) (Sub avail avail used)
       (Cmp Ult bad avail n)
       (If bad (Seq (Imm bad 4) (Return UNSUPPORTED bad)))
       (Base at arena) (Addr arena at at used 0 0)
       (Arg0 off) (Base from input) (Addr input from from off 0 0)
       (Invariant name_copy_inv "\\N i s. name_copy_inv st sq N i s"
         (Loop i n (name:cap) (name:copy-body)))
       (Base hdr header) (Load header count hdr 0)
       (Shl twice count 1) (Base row rows) (Addr rows row row twice 3 0)
       (Store rows row 0 used) (Store rows row 8 n)
       (Imm next 1) (Add next count next)
       (Store table slot-at 0 next)
       (Store header hdr 0 next)
       (Add used used n) (Store header hdr 8 used)
       (Return FIRED count))))

; An empty slot: append, if a row is free.
(= (name:append)
   (Block name_append
     (With (As code v4) (As hdr v8) (As count v9) (As cap v10) (As room v11)
       (Base hdr header) (Load header count hdr 0)
       (Len cap rows) (Shr cap cap 4)
       (Cmp Ult room count cap)
       (If room (name:append-room) (Seq (Imm code 1) (Return UNSUPPORTED code))))))

; One probe: the slot at (hash + probe) and (slots - 1).
(= (name:body)
   (Block name_body
     (With (As one v4) (As mask v4) (As pos v5) (As slot-at v6) (As e v7) (As empty v8)
       (Imm one 1) (Sub mask slots one)
       (Add pos hash probe) (And pos pos mask)
       (Base slot-at table) (Addr table slot-at slot-at pos 3 0)
       (Load table e slot-at 0)
       (CmpI Eq empty e 0)
       (If empty (name:append) (name:occupied)))))

(= (name:program)
   (p1:program intern_name
     (Regions (Region input RO 0 1) (Region rows RW 16 8) (Region arena RW 1 1)
              (Region table RW 8 8) (Region header RW 16 8))
     (Registers (As hash v1) (As probe v2) (As slots v3) (As code v4))
     (Init (Entry hash TyU64))
     (Seq (name:prologue)
          (Invariant name_inv "\\N j s. name_inv st N j s"
            (Loop probe slots (name:cap) (name:body)))
          (Imm code 3) (Return UNSUPPORTED code))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write name:program $text $notes))
