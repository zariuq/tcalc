; Read a count followed by that many minimal unsigned LEB128 integers.
; Region 0 holds input bytes, region 1 holds the cursor and a private count,
; and region 2 holds the destination words. Publish the cursor after the
; last integer. A malformed list refuses, with any written prefix in the
; private stack. A valid list that exceeds the stack returns UNSUPPORTED
; without writing stack words.

!(import! &self "../../p1/p1.metta")

(= (ids_next:chunk-size) 2147483648)
(= (ids_next:reject) (Seq (Imm tmp 0) (Return REFUSED tmp)))

(= (ids_next:final-byte)
   (Seq (CmpI Eq again tmp 0)
        (If again
            (Seq (Mov scale digit) (CmpI Ne again scale 0)
                 (If again (ids_next:reject)))
            (Seq (Mul tmp tmp scale) (Add value value tmp)))
        (Imm tmp 4611686018427387904) (Cmp Ule again tmp value)
        (If again (ids_next:reject))
        (Imm tmp 1) (Add cursor cursor digit) (Add cursor cursor tmp)
        (Imm TyBool again 0)))

(= (ids_next:leb-byte)
   (Block ids_next_leb_byte
        (Len tmp input) (Sub tmp tmp cursor)
        (Cmp Ult again digit tmp)
        (If again Skip (ids_next:reject))
        (Base tmp input) (Addr input tmp tmp cursor 0 0)
        (Addr input tmp tmp digit 0 0) (Load 1 TyU64 input tmp tmp 0)
        (CmpI Ult again tmp 128)
        (If again (ids_next:final-byte)
            (Seq (Extract tmp tmp 0 7) (Mul tmp tmp scale)
                 (Add value value tmp) (Shl scale scale 7)
                 (Imm TyBool again 1)))))

; The cursor is at or below the input length. One scalar read changes only
; registers until a complete integer has been admitted.
(= (ids_next:leb)
   (Block ids_next_leb
        (Imm value 0) (Imm scale 1) (Imm digits 9) (Imm TyBool again 1)
        (EarlyLoop digit digits again 9 (ids_next:leb-byte))
        (If again (ids_next:reject))))

(= (ids_next:store-id)
   (Seq (Base tmp state) (Load state scale tmp 8)
        (Len tmp stack) (Shr tmp tmp 3) (Cmp Ule again scale tmp)
        (If again
            (Seq (Shl scale chunk 31) (Add scale scale item)
                 (Base tmp stack) (Addr stack tmp tmp scale 3 0)
                 (Store stack tmp 0 value)))))

; For n < 2^62, floor(n / 2^31) + 1 and each chunk length are at most 2^31.
; The last chunk is empty when n is a multiple of 2^31.
(= (ids_next:read-chunk)
   (Block ids_next_chunk
     (Shl tmp chunk 31)
     (Base scale state) (Load state items scale 8) (Sub items items tmp)
     (Imm tmp (ids_next:chunk-size)) (Cmp Ult again tmp items)
     (If again (Mov items tmp))
     (Loop item items 2147483648 (Seq (ids_next:leb) (ids_next:store-id)))))

(= (ids_next:program)
   (p1:program ids_next
     (Regions (Region input RO 0 1) (Region state RW 16 8) (Region stack RW 0 8))
     (Registers (As chunk v1) (As chunks v2) (As item v3) (As items v4)
                (As again v5) (As cursor v6) (As value v7) (As scale v8)
                (As digit v9) (As digits v10) (As tmp v11))
     (Init)
     (Seq (Block ids_next_count
            (Base tmp state) (Load state cursor tmp 0)
            (Len tmp input) (Cmp Ult again tmp cursor)
            (If again (ids_next:reject))
            (ids_next:leb)
            (Len tmp input) (Sub tmp tmp cursor) (Cmp Ult again tmp value)
            (If again (ids_next:reject))
            (Base tmp state) (Store state tmp 8 value)
            (Shr chunks value 31) (Imm tmp 1) (Add chunks chunks tmp))
          (Loop chunk chunks 2147483648 (ids_next:read-chunk))
          (Block ids_next_finish
            (Base tmp state) (Load state value tmp 8)
            (Len tmp stack) (Shr tmp tmp 3) (Cmp Ule again value tmp)
            (If again
                (Seq (Base tmp state) (Store state tmp 0 cursor) (Return FIRED value))
                (Seq (Imm tmp 0) (Return UNSUPPORTED tmp)))))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write ids_next:program $text $notes))
