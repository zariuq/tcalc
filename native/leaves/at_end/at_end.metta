; at_end.metta -- the reader's leaf 30 (tcalc/native/PLANS.txt, sections 2
; and 10): the input fully read, authored with p1.metta as one standalone
; t-ISA p1 program. Its specification is pl_at_end_spec
; (tcalc/native/hol/plans_leaves.ml); the proof is at_end.ml.
;
;   cetta --no-results at_end.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Regions: 0 the input (RO), 1 the reader's state (RO, at least 16 bytes;
; word 0 the cursor, word 1 work), as every reader leaf binds them. No
; arguments. Outcomes:
;   FIRED    ret_val 1, when the cursor is the input's length
;   REFUSED  ret_val 0, otherwise
; No run writes memory outside the frame's status and return words.

!(import! &self "../../p1/p1.metta")

(= (at_end:program)
   (p1:program at_end
     (Regions (Region input RO 0 1) (Region state RO 16 8))
     (Registers (As at v1) (As c v2) (As n v3) (As ok v4))
     (Init)
     (Seq (Base at state) (Load state c at 0) (Len n input)
          (Cmp Eq ok c n)
          (If ok (Return FIRED ok))
          (Return REFUSED ok))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write at_end:program $text $notes))
