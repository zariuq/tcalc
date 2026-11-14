; cur.metta -- the reader's leaf 25 (tcalc/native/PLANS.txt, sections 2 and
; 10): the cursor, authored with p1.metta as one standalone t-ISA p1 program.
; Its specification is pl_cur_spec (tcalc/native/hol/plans_leaves.ml); the
; proof is cur.ml.
;
;   cetta --no-results cur.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Regions: 0 the input (RO), 1 the reader's state (RO, at least 16 bytes;
; word 0 the cursor, word 1 work), as every reader leaf binds them. No
; arguments. Outcome:
;   FIRED  ret_val = word 0 of the state
; No run writes memory outside the frame's status and return words.

!(import! &self "../../p1/p1.metta")

(= (cur:program)
   (p1:program cur
     (Regions (Region input RO 0 1) (Region state RO 16 8))
     (Registers (As at v1) (As c v2))
     (Init)
     (Seq (Base at state) (Load state c at 0) (Return FIRED c))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write cur:program $text $notes))
