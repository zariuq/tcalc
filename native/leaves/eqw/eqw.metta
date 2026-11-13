; eqw.metta -- the record plans' leaf 3 (tcalc/native/PLANS.txt, sections 2
; and 5): a guard that two control words are equal, authored with p1.metta
; as one standalone t-ISA p1 program. Its specification is pl_eqw_spec
; (tcalc/native/hol/plans_leaves.ml); the proof is eqw.ml.
;
;   cetta --no-results eqw.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; No regions. Arguments: arg0 and arg1. Outcomes:
;   FIRED    ret_val = arg0, when arg0 = arg1
;   REFUSED  ret_val 0, otherwise
; No run writes memory outside the frame's status and return words.

!(import! &self "../../p1/p1.metta")

(= (eqw:program)
   (p1:program eqw
     (Regions)
     (Registers (As a v1) (As b v2) (As same v3))
     (Init)
     (Seq (Arg0 a) (Arg1 b)
          (Cmp Eq same a b)
          (If same (Return FIRED a))
          (Return REFUSED same))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write eqw:program $text $notes))
