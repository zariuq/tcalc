; pack.metta -- the record plans' leaf 1 (tcalc/native/PLANS.txt, sections 2
; and 5): the packed key word tag + 8a of a type or de Bruijn row, authored
; with p1.metta as one standalone t-ISA p1 program. Its specification is
; pl_pack_spec (tcalc/native/hol/plans_leaves.ml); the proof is pack.ml.
;
;   cetta --no-results pack.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; No regions. Arguments: arg0 a, arg1 the tag. Outcomes:
;   FIRED        ret_val = tag + 8a, when a < 2^60 and tag < 8
;   UNSUPPORTED  ret_val 0, otherwise
; No run writes memory outside the frame's status and return words.

!(import! &self "../../p1/p1.metta")

(= (pack:program)
   (p1:program pack
     (Regions)
     (Registers (As a v1) (As tag v2) (As ok v3) (As key v4))
     (Init)
     (Seq (Arg0 a) (Arg1 tag)
          (CmpI Ult ok a 1152921504606846976)
          (If ok
              (Seq (CmpI Ult ok tag 8)
                   (If ok (Seq (Shl key a 3) (Add key key tag) (Return FIRED key)))))
          (Return UNSUPPORTED ok))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write pack:program $text $notes))
