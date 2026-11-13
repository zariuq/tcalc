; row_word.metta -- the record plans' leaf 4 (tcalc/native/PLANS.txt,
; sections 2, 4 and 5): word w of row i of a table of rows of s words,
; authored with p1.metta as one standalone t-ISA p1 program. Its
; specification is pl_row_word_spec (tcalc/native/hol/plans_leaves.ml); the
; proof is row_word.ml.
;
;   cetta --no-results row_word.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Regions: 0 rows (RO), 1 count (RO, word 0 the row count c). Arguments:
; arg0 the row i, arg1 the word w; the entry register v1 the stride s.
; Outcomes:
;   FIRED        ret_val = word s i + w of the rows, when i < c, w < s and
;                8 s c <= the rows' length
;   UNSUPPORTED  otherwise
; No run writes memory outside the frame's status and return words.

!(import! &self "../../p1/p1.metta")
!(import! &self "../common/leaves.metta")

(= (row_word:program)
   (p1:program row_word
     (Regions (Region rows RO 0 8) (Region count RO 8 8))
     (Registers (As s v1) (As i v2) (As w v3) (As c v4) (As lim v5) (As xh v6) (As yh v7)
                (As xl v8) (As yl v9) (As t v10) (As u v11))
     (Init (Entry s TyU64))
     (Seq (Block row_word_checks
            (Arg0 i) (Arg1 w)
            (Base t count) (Load count c t 0)
            (Cmp Ult t i c) (If t Skip (Return UNSUPPORTED t))
            (Cmp Ult t w s) (If t Skip (Return UNSUPPORTED t))
            (Len lim rows) (Shr lim lim 3)
            (leaves:product-within s c lim xh yh xl yl t u))
          (Block row_word_access
            (Mul t s i) (Add t t w)
            (Base u rows) (Addr rows u u t 3 0) (Load rows t u 0)
            (Return FIRED t)))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write row_word:program $text $notes))
