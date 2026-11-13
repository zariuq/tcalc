; put_word.metta -- the record plans' leaf 9 (tcalc/native/PLANS.txt,
; sections 2, 5 and 6): set word w of row i of a table of rows of s words,
; authored with p1.metta as one standalone t-ISA p1 program. Its
; specification is pl_put_word_spec (tcalc/native/hol/plans_leaves.ml); the
; proof is put_word.ml.
;
;   cetta --no-results put_word.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Regions: 0 the table (RW), 1 its count (RO, word 0 the row count c).
; Entry registers: v1 the stride s, v2 the word w. Arguments: arg0 the row
; i, arg1 the value. Outcomes:
;   FIRED        ret_val = the value, now word s i + w of the table, when
;                i < c, w < s and 8 s c <= the table's length
;   UNSUPPORTED  otherwise, and nothing written
; The checks come first (put_word_checks); the write follows
; (put_word_access).

!(import! &self "../../p1/p1.metta")
!(import! &self "../common/leaves.metta")

(= (put_word:program)
   (p1:program put_word
     (Regions (Region table RW 0 8) (Region count RO 8 8))
     (Registers (As s v1) (As w v2) (As i v3) (As c v4) (As lim v5) (As xh v6) (As yh v7)
                (As xl v8) (As yl v9) (As t v10) (As u v11) (As x v6))
     (Init (Entry s TyU64) (Entry w TyU64))
     (Seq (Block put_word_checks
            (Arg0 i)
            (Base t count) (Load count c t 0)
            (Cmp Ult t i c) (If t Skip (Return UNSUPPORTED t))
            (Cmp Ult t w s) (If t Skip (Return UNSUPPORTED t))
            (Len lim table) (Shr lim lim 3)
            (leaves:product-within s c lim xh yh xl yl t u))
          (Block put_word_access
            (Mul t s i) (Add t t w)
            (Base u table) (Addr table u u t 3 0)
            (Arg1 x) (Store table u 0 x)
            (Return FIRED x)))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write put_word:program $text $notes))
