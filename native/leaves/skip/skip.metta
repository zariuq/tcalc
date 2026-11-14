; skip.metta -- the reader's leaf 28 (tcalc/native/PLANS.txt, sections 2 and
; 10): the cursor advanced past n bytes, authored with p1.metta as one
; standalone t-ISA p1 program. Its specification is pl_skip_spec
; (tcalc/native/hol/plans_leaves.ml); the proof is skip.ml.
;
;   cetta --no-results skip.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Regions: 0 the input (RO), 1 the reader's state (RW, at least 16 bytes;
; word 0 the cursor, word 1 work), as every reader leaf binds them.
; Argument: arg0 n. Outcomes:
;   FIRED    the cursor c + n, written to state word 0 and returned, when
;            c + n is at most the input's length
;   REFUSED  ret_val 0, the state unchanged, otherwise
; The comparison never wraps: c <= len, then n <= len - c.
; No run writes memory outside the state's word 0 and the frame's status and
; return words.

!(import! &self "../../p1/p1.metta")

(= (skip:program)
   (p1:program skip
     (Regions (Region input RO 0 1) (Region state RW 16 8))
     (Registers (As at v1) (As c v2) (As len v3) (As n v4) (As ok v5) (As d v6))
     (Init)
     (Seq (Base at state) (Load state c at 0) (Len len input) (Arg0 n)
          (Cmp Ule ok c len)
          (If ok (Seq (Sub d len c) (Cmp Ule ok n d)
                      (If ok (Seq (Add c c n) (Store state at 0 c) (Return FIRED c)))))
          (Imm ok 0)
          (Return REFUSED ok))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write skip:program $text $notes))
