; inc.metta -- the reader's leaf 32 (tcalc/native/PLANS.txt, sections 2 and
; 10): a count plus one, authored with p1.metta as one standalone t-ISA p1
; program. Its specification is pl_inc_spec (tcalc/native/hol/plans_leaves.ml);
; the proof is inc.ml.
;
;   cetta --no-results inc.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; No regions. Argument: arg0 a. Outcomes:
;   FIRED        ret_val = a + 1, when a + 1 < 2^62
;   UNSUPPORTED  ret_val 0, otherwise
; No run writes memory outside the frame's status and return words.

!(import! &self "../../p1/p1.metta")

(= (inc:program)
   (p1:program inc
     (Regions)
     (Registers (As a v1) (As ok v2) (As r v3))
     (Init)
     (Seq (Arg0 a)
          (CmpI Ult ok a 4611686018427387903)
          (If ok (Seq (Imm r 1) (Add r a r) (Return FIRED r)))
          (Return UNSUPPORTED ok))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write inc:program $text $notes))
