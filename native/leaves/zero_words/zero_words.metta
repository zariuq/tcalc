; Clear one region of complete eight-byte words before publication.
; The receipt is preserved: source-cost compilation places FUND points.
; FIRED returns the number of words. A partial word or a count beyond the
; loop cap is UNSUPPORTED, with the region unchanged. No host-zero premise.

!(import! &self "../../p1/p1.metta")

(= (zero_words:program)
   (p1:program zero_words
     (Regions (Region rows RW 0 8))
     (Registers (As bytes v1) (As count v2) (As exact v3) (As ok v4)
                (As index v5) (As base v6) (As zero v7) (As at v8))
     (Init)
     (Seq (Block zero_words_checks
            (Len bytes rows)
            (Shr count bytes 3)
            (Shl exact count 3)
            (Cmp Eq ok exact bytes)
            (If ok Skip (Return UNSUPPORTED count))
            (Base base rows)
            (Imm zero 0))
          (Invariant zero_words_inv
            "zero_words_inv entry N index state"
            (Loop index count 4294967295
              (Block zero_words_body
                (Addr rows at base index 3 0)
                (Store rows at 0 zero))))
          (Return FIRED count))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write zero_words:program $text $notes))
