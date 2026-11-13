; append_row.metta -- the record plans' leaf 6 (tcalc/native/PLANS.txt,
; sections 2, 5 and 6): append a row of w words to a table and count it,
; authored with p1.metta as one standalone t-ISA p1 program. Its
; specification is pl_append_row_spec (tcalc/native/hol/plans_leaves.ml);
; the proof is append_row.ml.
;
;   cetta --no-results append_row.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Regions: 0 rows (RW), 1 count (RW, word 0 the row count c). Entry
; registers: v1 the width w; the row's words are arg0, arg1, v2, v3, v4, its
; first w of them. Outcomes:
;   FIRED        ret_val = c: the row's words at words w c .. w c + w - 1 of
;                the rows, the count c + 1; when 1 <= w <= 5 and
;                8 w (c + 1) <= the rows' length
;   UNSUPPORTED  otherwise, and nothing written
; The checks come first (append_row_checks); the writes follow
; (append_row_access).

!(import! &self "../../p1/p1.metta")

(= (append_row:program)
   (p1:program append_row
     (Regions (Region rows RW 0 8) (Region count RW 8 8))
     (Registers (As w v1) (As x2 v2) (As x3 v3) (As x4 v4) (As c v5) (As lim v6) (As t v7)
                (As at v8) (As a v9) (As o v10))
     (Init (Entry w TyU64) (Entry x2 TyU64) (Entry x3 TyU64) (Entry x4 TyU64))
     (Seq (Block append_row_checks
            (Base at count) (Load count c at 0)
            (CmpI Ult t w 1) (If t (Return UNSUPPORTED t))
            (CmpI Ult t w 6) (If t Skip (Return UNSUPPORTED t))
            (Len lim rows) (Shr lim lim 3)
            (Cmp Ult t c lim) (If t Skip (Return UNSUPPORTED t))
            (Imm t 1) (Add o c t) (Mul o o w)
            (Cmp Ult t lim o) (If t (Return UNSUPPORTED t)))
          (Block append_row_access
            (Mul o w c)
            (Base at rows) (Addr rows at at o 3 0)
            (Arg0 a) (Store rows at 0 a)
            (CmpI Ult t w 2) (If t Skip (Seq (Arg1 a) (Store rows at 8 a)))
            (CmpI Ult t w 3) (If t Skip (Store rows at 16 x2))
            (CmpI Ult t w 4) (If t Skip (Store rows at 24 x3))
            (CmpI Ult t w 5) (If t Skip (Store rows at 32 x4))
            (Imm t 1) (Add t c t) (Base at count) (Store count at 0 t)
            (Return FIRED c)))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write append_row:program $text $notes))
