; le8_next.metta -- the reader's leaf 29 (tcalc/native/PLANS.txt, sections 2
; and 10): the 8 bytes at the cursor, read little-endian, authored with
; p1.metta as one standalone t-ISA p1 program. Its specification is
; pl_le8_next_spec (tcalc/native/hol/plans_leaves.ml); the proof is
; le8_next.ml.
;
;   cetta --no-results le8_next.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Regions: 0 the input (RO), 1 the reader's state (RW, at least 16 bytes;
; word 0 the cursor, word 1 work), as every reader leaf binds them. No
; arguments. Outcomes:
;   FIRED    ret_val the 8 bytes at the cursor c, little-endian; c + 8
;            written to state word 0; when c + 8 is at most the input's length
;   REFUSED  ret_val 0, the state unchanged, otherwise
; The comparison never wraps: c <= len, then 8 <= len - c.
; No run writes memory outside the state's word 0 and the frame's status and
; return words.

!(import! &self "../../p1/p1.metta")

(= (le8_next:program)
   (p1:program le8_next
     (Regions (Region input RO 0 1) (Region state RW 16 8))
     (Registers (As at v1) (As c v2) (As len v3) (As ok v4) (As d v5) (As e v6)
                (As ip v7) (As p v8) (As v v9))
     (Init)
     (Seq (Base at state) (Load state c at 0) (Len len input)
          (Cmp Ule ok c len)
          (If ok (Seq (Sub d len c) (Imm e 8) (Cmp Ule ok e d)
                      (If ok (Seq (Base ip input) (Addr input p ip c 0 0)
                                  (Load 8 TyU64 input v p 0)
                                  (Add c c e) (Store state at 0 c)
                                  (Return FIRED v)))))
          (Imm ok 0)
          (Return REFUSED ok))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write le8_next:program $text $notes))
