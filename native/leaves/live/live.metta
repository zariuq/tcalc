; live.metta -- the record plans' leaf 5 (tcalc/native/PLANS.txt, sections
; 2, 4 and 5): an id is live when it is below its space's count and its
; dropped mark is 0, authored with p1.metta as one standalone t-ISA p1
; program. Its specification is pl_live_spec
; (tcalc/native/hol/plans_leaves.ml); the proof is live.ml.
;
;   cetta --no-results live.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Regions: 0 count (RO, word 0 the count c), 1 marks (RO, one word per id).
; Argument: arg0 the id. Outcomes:
;   UNSUPPORTED  the marks shorter than 8 c bytes
;   FIRED        ret_val = the id, when id < c and its mark is 0
;   REFUSED      ret_val 0, otherwise
; No run writes memory outside the frame's status and return words.

!(import! &self "../../p1/p1.metta")

(= (live:program)
   (p1:program live
     (Regions (Region count RO 8 8) (Region marks RO 0 8))
     (Registers (As id v1) (As c v2) (As n v3) (As t v4) (As at v5) (As m v6))
     (Init)
     (Seq (Arg0 id)
          (Base at count) (Load count c at 0)
          (Len n marks) (Shr n n 3)
          (Cmp Ult t n c) (If t (Return UNSUPPORTED t))
          (Cmp Ult t id c)
          (If t (Seq (Base at marks) (Addr marks at at id 3 0) (Load marks m at 0)
                     (CmpI Eq t m 0) (If t (Return FIRED id))))
          (Return REFUSED t))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write live:program $text $notes))
