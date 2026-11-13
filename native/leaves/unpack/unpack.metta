; unpack.metta -- the record plans' leaf 2 (tcalc/native/PLANS.txt, sections
; 2 and 5): the field a of a packed key word k0 = tag + 8a whose tag is the
; expected one, authored with p1.metta as one standalone t-ISA p1 program.
; Its specification is pl_unpack_spec (tcalc/native/hol/plans_leaves.ml);
; the proof is unpack.ml.
;
;   cetta --no-results unpack.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; No regions. Arguments: arg0 k0, arg1 the tag. Outcomes:
;   FIRED    ret_val = k0 DIV 8, when k0 MOD 8 is the tag
;   REFUSED  ret_val 0, otherwise
; No run writes memory outside the frame's status and return words.

!(import! &self "../../p1/p1.metta")

(= (unpack:program)
   (p1:program unpack
     (Regions)
     (Registers (As k0 v1) (As tag v2) (As low v3) (As ok v4) (As a v5))
     (Init)
     (Seq (Arg0 k0) (Arg1 tag)
          (Imm low 7) (And low k0 low)
          (Cmp Eq ok low tag)
          (If ok (Seq (Shr a k0 3) (Return FIRED a)))
          (Return REFUSED ok))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write unpack:program $text $notes))
