; leaves.metta -- p1 templates the plan leaves share (tcalc/native/leaves).
; A leaf imports p1.metta first, then this file; nothing here imports.

; x * y <= lim, exactly, for 1 <= x, 1 <= y and lim < 2^61 (a region's length
; in words); UNSUPPORTED otherwise, and then nothing has been written. With
; xh, yh the high and xl, yl the low 32 bits of x and y,
;   x * y = xh yh 2^64 + (xh yl + yh xl) 2^32 + xl yl,
; and once x, y <= lim (so xh, yh < 2^29) every product and sum below fits
; 64 bits: xh yh = 0 is tested as xh = 0 or yh = 0, then mid = xh yl + yh xl
; < 2^62, xl yl < 2^64, and the total mid 2^32 + xl yl is formed only when
; mid < 2^29 and xl yl <= lim. Registers xh, yh, xl, yl, t, u are clobbered.
(= (leaves:product-within $x $y $lim $xh $yh $xl $yl $t $u)
   (Seq (Cmp Ult $t $lim $x) (If $t (Return UNSUPPORTED $t))
        (Cmp Ult $t $lim $y) (If $t (Return UNSUPPORTED $t))
        (Shr $xh $x 32) (Shr $yh $y 32)
        (CmpI Ne $t $xh 0) (CmpI Ne $u $yh 0) (Bin BinAnd TyBool $t $t $u)
        (If $t (Return UNSUPPORTED $t))
        (Imm $u 4294967295) (And $xl $x $u) (And $yl $y $u)
        (Mul $t $xh $yl) (Mul $u $yh $xl) (Add $t $t $u)
        (CmpI Ult $u $t 536870912) (If $u Skip (Return UNSUPPORTED $u))
        (Shl $t $t 32) (Mul $u $xl $yl)
        (Cmp Ult $xh $lim $u) (If $xh (Return UNSUPPORTED $xh))
        (Add $t $t $u)
        (Cmp Ult $xh $lim $t) (If $xh (Return UNSUPPORTED $xh))))
