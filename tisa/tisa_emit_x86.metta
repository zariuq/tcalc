; =============================================================================
; tisa_emit_x86.metta — Direct Deterministic t-ISA Specializer & x86-64 Emitter
;
; Implements in pure MeTTa:
;   1. Table-driven rule specialization (`tisa-specialize-lean-flat-rule`):
;      derives structured `t-ISA` programs from `RuleTable` flat rule rows.
;   2. Fixed physical register map (`v0..v11` -> `rdi..r13`, `s0..s1` -> `r14..r15`).
;   3. Structured `t-ISA -> x86-64` compilation (`tisa-compile-x86`):
;      - 9-byte System V AMD64 ABI callee-save prologue
;      - Exact per-instruction fuel accounting (`FUEL_STEP`)
;      - Overflow-safe capability bounds checking (`emit-checked-mem-addr`)
;      - Compositional structured control (`Seq`, `If`, `Return`)
;      - Two-pass symbolic `rel32` displacement patching (`resolve-stream`)
;      - 10-byte System V AMD64 ABI callee-restore epilogue
;   4. Self-contained differential verification against `tisa_emit_x86.c`.
; =============================================================================

; -----------------------------------------------------------------------------
; 1. Algebraic Byte Stream & List Utilities
; -----------------------------------------------------------------------------

(= (bcat Nil $ys) $ys)
(= (bcat (Cons $x $xs) $ys) (Cons $x (bcat $xs $ys)))

(= (bcat3 $a $b $c) (bcat $a (bcat $b $c)))
(= (bcat4 $a $b $c $d) (bcat $a (bcat $b (bcat $c $d))))
(= (bcat5 $a $b $c $d $e) (bcat $a (bcat $b (bcat $c (bcat $d $e)))))
(= (bcat6 $a $b $c $d $e $f) (bcat $a (bcat $b (bcat $c (bcat $d (bcat $e $f))))))

(= (b1 $x0) (Cons (B $x0) Nil))
(= (b2 $x0 $x1) (Cons (B $x0) (Cons (B $x1) Nil)))
(= (b3 $x0 $x1 $x2) (Cons (B $x0) (Cons (B $x1) (Cons (B $x2) Nil))))
(= (b4 $x0 $x1 $x2 $x3) (Cons (B $x0) (Cons (B $x1) (Cons (B $x2) (Cons (B $x3) Nil)))))

; Stream byte length: `(B _)` is 1 byte, `(Rel32 _)` is 4 bytes
(= (item-byte-len (B $_)) 1)
(= (item-byte-len (Rel32 $_)) 4)

(= (stream-byte-len Nil) 0)
(= (stream-byte-len (Cons $item $rest))
   (+ (item-byte-len $item) (stream-byte-len $rest)))

(= (stream-uses-label Nil $_) False)
(= (stream-uses-label (Cons (B $_) $rest) $lbl)
   (stream-uses-label $rest $lbl))
(= (stream-uses-label (Cons (Rel32 $t) $rest) $lbl)
   (if (== $t $lbl) True (stream-uses-label $rest $lbl)))

; -----------------------------------------------------------------------------
; 2. Fixed Physical Register Map & Low-Level x86-64 Encoders
; -----------------------------------------------------------------------------

(= (hw-reg 0)  7)  ; V0  -> rdi
(= (hw-reg 1)  6)  ; V1  -> rsi
(= (hw-reg 2)  2)  ; V2  -> rdx
(= (hw-reg 3)  1)  ; V3  -> rcx
(= (hw-reg 4)  8)  ; V4  -> r8
(= (hw-reg 5)  9)  ; V5  -> r9
(= (hw-reg 6)  10) ; V6  -> r10
(= (hw-reg 7)  11) ; V7  -> r11
(= (hw-reg 8)  0)  ; V8  -> rax
(= (hw-reg 9)  3)  ; V9  -> rbx
(= (hw-reg 10) 12) ; V10 -> r12
(= (hw-reg 11) 13) ; V11 -> r13
(= (hw-reg 12) 14) ; S0  -> r14 (emitter scratch 0)
(= (hw-reg 13) 15) ; S1  -> r15 (emitter scratch 1)

(= (idiv $a $b) (/ (- $a (% $a $b)) $b))

(= (rex-byte $w $r_hw $x_hw $b_hw)
   (+ 64
      (+ (* (% $w 2) 8)
         (+ (* (% (idiv $r_hw 8) 2) 4)
            (+ (* (% (idiv $x_hw 8) 2) 2)
               (% (idiv $b_hw 8) 2))))))

(= (modrm-byte $mod $reg_hw $rm_hw)
   (+ (* (% $mod 4) 64)
      (+ (* (% $reg_hw 8) 8)
         (% $rm_hw 8))))

(= (u32-le $v)
   (b4 (% $v 256)
       (% (idiv $v 256) 256)
       (% (idiv $v 65536) 256)
       (% (idiv $v 16777216) 256)))

(= (i32-le $rel)
   (let $u (if (< $rel 0) (+ 4294967296 $rel) $rel)
     (u32-le $u)))

(= (u64-le $v)
   (bcat (u32-le (% $v 4294967296))
         (u32-le (idiv $v 4294967296))))

(= (emit-opt-rex $rx)
   (if (== $rx 64) Nil (b1 $rx)))

(= (emit-mov-r64-r64 $dst_v $src_v)
   (if (== $dst_v $src_v)
       Nil
       (let* (($d (hw-reg $dst_v))
              ($s (hw-reg $src_v)))
         (b3 (rex-byte 1 $s 0 $d)
             137 ; 0x89
             (modrm-byte 3 $s $d)))))

(= (emit-zext32-reg $dst_v)
   (let* (($d (hw-reg $dst_v))
          ($rx (rex-byte 0 $d 0 $d)))
     (bcat (emit-opt-rex $rx)
           (b2 137 (modrm-byte 3 $d $d)))))

(= (emit-sext32-reg $dst_v)
   (let $d (hw-reg $dst_v)
     (b3 (rex-byte 1 $d 0 $d) 99 (modrm-byte 3 $d $d))))

(= (emit-canon-reg $dst_v TypeU64) Nil)
(= (emit-canon-reg $dst_v TypePtr) Nil)
(= (emit-canon-reg $dst_v TypeU32Z) (emit-zext32-reg $dst_v))
(= (emit-canon-reg $dst_v TypeI32S) (emit-sext32-reg $dst_v))
(= (emit-canon-reg $dst_v TypeBool)
   (let* (($d (hw-reg $dst_v))
          ($rx (rex-byte 0 0 0 $d)))
     (bcat (emit-opt-rex $rx)
           (b3 131 (modrm-byte 3 4 $d) 1))))

(= (emit-mov-imm64 $dst_v $val)
   (let $d (hw-reg $dst_v)
     (if (== $val 0)
         (let $rx (rex-byte 0 $d 0 $d)
           (bcat (emit-opt-rex $rx)
                 (b2 49 (modrm-byte 3 $d $d)))) ; xor r32, r32
         (if (<= $val 4294967295)
             (let $rx (rex-byte 0 0 0 $d)
               (bcat3 (emit-opt-rex $rx)
                      (b1 (+ 184 (% $d 8)))
                      (u32-le $val)))
             (bcat (b2 (rex-byte 1 0 0 $d) (+ 184 (% $d 8)))
                   (u64-le $val))))))

(= (emit-load-frame-u64 $dst_v $disp32)
   (let $d (hw-reg $dst_v)
     (bcat (b3 (rex-byte 1 $d 0 7) 139 (modrm-byte 2 $d 7))
           (u32-le $disp32))))

(= (emit-store-frame-u64 $disp32 $src_v)
   (let $s (hw-reg $src_v)
     (bcat (b3 (rex-byte 1 $s 0 7) 137 (modrm-byte 2 $s 7))
           (u32-le $disp32))))

(= (emit-store-frame-imm32 $disp32 $imm32)
   (bcat3 (b3 72 199 (modrm-byte 2 0 7))
          (u32-le $disp32)
          (u32-le $imm32)))

(= (emit-jcc-sym $cc_op $lbl)
   (Cons (B 15) (Cons (B $cc_op) (Cons (Rel32 $lbl) Nil))))

(= (emit-jcc-disp $cc_op $rel32)
   (bcat (b2 15 $cc_op) (i32-le $rel32)))

(= (emit-jmp-sym $lbl)
   (Cons (B 233) (Cons (Rel32 $lbl) Nil)))

(= (emit-jmp-disp $rel32)
   (bcat (b1 233) (i32-le $rel32)))

; -----------------------------------------------------------------------------
; 3. Fuel Step & Overflow-Safe Capability Bounds Checking
; -----------------------------------------------------------------------------

(= (emit-fuel-step)
   (bcat6
     (emit-load-frame-u64 12 160)        ; mov r14, [rdi + 160] (fuel_budget)
     (b3 77 133 246)                     ; test r14, r14
     (emit-jcc-disp 132 16)              ; jz +16 (.no_cap)
     (emit-load-frame-u64 13 168)        ; mov r15, [rdi + 168] (fuel_used)
     (bcat (b3 77 57 247)                ; cmp r15, r14
           (emit-jcc-sym 131 LblExhausted)) ; jae exhausted_label
     (bcat (b3 72 131 (modrm-byte 2 0 7))
           (bcat (u32-le 168) (b1 1))))) ; add qword ptr [rdi + 168], 1

(= (emit-disp-check $disp32)
   (if (== $disp32 0)
       Nil
       (if (> $disp32 0)
           (bcat3 (emit-mov-imm64 13 $disp32)
                  (b3 77 1 254) ; add r14, r15
                  (emit-jcc-sym 130 LblInvalid)) ; jc invalid
           (let $mag (- 0 $disp32)
             (bcat3 (emit-mov-imm64 13 $mag)
                    (b3 77 41 254) ; sub r14, r15
                    (emit-jcc-sym 130 LblInvalid)))))) ; jb invalid

(= (emit-checked-mem-addr-in-r14 $region_id $base_v $disp32 $width)
   (let* (($ptr_off (* $region_id 16))
          ($len_off (+ (* $region_id 16) 8)))
     (bcat6
       (bcat4 (emit-mov-r64-r64 12 $base_v)
              (emit-load-frame-u64 13 $ptr_off)
              (b3 77 41 254) ; sub r14, r15
              (emit-jcc-sym 130 LblInvalid)) ; jb invalid
       (emit-disp-check $disp32)
       (bcat3 (emit-load-frame-u64 13 $len_off)
              (b4 73 131 255 $width) ; cmp r15, width
              (emit-jcc-sym 130 LblInvalid)) ; jb invalid
       (b4 73 131 239 $width) ; sub r15, width
       (bcat (b3 77 57 254)   ; cmp r14, r15
             (emit-jcc-sym 135 LblInvalid)) ; ja invalid
       (bcat (emit-load-frame-u64 13 $ptr_off)
             (b3 77 1 254))))) ; add r14, r15

; -----------------------------------------------------------------------------
; 4. Instruction & Structured Control Emitters
; -----------------------------------------------------------------------------

(= (cmp-setcc-op CmpEq)  148) ; 0x94 sete
(= (cmp-setcc-op CmpNe)  149) ; 0x95 setne
(= (cmp-setcc-op CmpUlt) 146) ; 0x92 setb
(= (cmp-setcc-op CmpUle) 150) ; 0x96 setbe
(= (cmp-setcc-op CmpSlt) 156) ; 0x9C setl
(= (cmp-setcc-op CmpSle) 158) ; 0x9E setle

(= (binop-opcode BinAdd) 1)  ; 0x01
(= (binop-opcode BinSub) 41) ; 0x29
(= (binop-opcode BinAnd) 33) ; 0x21
(= (binop-opcode BinOr)  9)  ; 0x09
(= (binop-opcode BinXor) 49) ; 0x31

(= (shift-ext ShiftShl)  4)
(= (shift-ext ShiftShru) 5)
(= (shift-ext ShiftShrs) 7)

(= (bitmask-wid 8)  255)
(= (bitmask-wid 16) 65535)
(= (bitmask-wid 32) 4294967295)

(= (emit-cmp-tail $cond $ty $dst)
   (let* (($canon_s0 (emit-canon-reg 12 $ty))
          ($canon_s1 (emit-canon-reg 13 $ty))
          ($d (hw-reg $dst))
          ($setcc (cmp-setcc-op $cond)))
     (bcat5
       (bcat $canon_s0 $canon_s1)
       (b3 77 57 254) ; cmp r14, r15
       (b4 (rex-byte 0 0 0 $d) 15 $setcc (modrm-byte 3 0 $d))
       (b4 (rex-byte 0 $d 0 $d) 15 182 (modrm-byte 3 $d $d))
       Nil)))

(= (emit-instr (InsnImm $ty $dst $imm64))
   (bcat (emit-fuel-step)
         (emit-mov-imm64 $dst $imm64)))

(= (emit-instr (InsnMov $ty $dst $src1))
   (bcat3 (emit-fuel-step)
          (emit-mov-r64-r64 $dst $src1)
          (emit-canon-reg $dst $ty)))

(= (emit-instr (InsnBin $op $ty $dst $src1 $src2))
   (let* (($s2 (hw-reg $src2))
          ($r14 14))
     (bcat5 (emit-fuel-step)
            (emit-mov-r64-r64 12 $src1)
            (b3 (rex-byte 1 $s2 0 $r14) (binop-opcode $op) (modrm-byte 3 $s2 $r14))
            (emit-mov-r64-r64 $dst 12)
            (emit-canon-reg $dst $ty))))

(= (emit-instr (InsnShift $subop $ty $dst $src1 $sh))
   (let* (($d (hw-reg $dst))
          ($ext (shift-ext $subop))
          ($pre_ext
            (if (== $subop ShiftShru)
                (if (== $ty TypeU32Z) (emit-zext32-reg $dst)
                    (if (== $ty TypeI32S) (emit-zext32-reg $dst) Nil))
                (if (== $subop ShiftShrs)
                    (if (== $ty TypeU32Z) (emit-sext32-reg $dst)
                        (if (== $ty TypeI32S) (emit-sext32-reg $dst) Nil))
                    Nil))))
     (bcat5 (emit-fuel-step)
            (emit-mov-r64-r64 $dst $src1)
            $pre_ext
            (b4 (rex-byte 1 0 0 $d) 193 (modrm-byte 3 $ext $d) $sh)
            (emit-canon-reg $dst $ty))))

(= (emit-instr (InsnExtract $ty $dst $src1 $lsb $wid))
   (let* (($d (hw-reg $dst))
          ($shr_bytes
            (if (> $lsb 0)
                (b4 (rex-byte 1 0 0 $d) 193 (modrm-byte 3 5 $d) $lsb)
                Nil))
          ($mask_bytes
            (if (< $wid 64)
                (bcat (emit-mov-imm64 12 (bitmask-wid $wid))
                      (b3 (rex-byte 1 14 0 $d) 33 (modrm-byte 3 14 $d)))
                Nil)))
     (bcat5 (emit-fuel-step)
            (emit-mov-r64-r64 $dst $src1)
            $shr_bytes
            $mask_bytes
            (emit-canon-reg $dst $ty))))

(= (emit-addr-idx $len_off $idx_v $scale_lg2)
   (if (== $idx_v 255)
       Nil
       (let* (($hi_check
                (if (> $scale_lg2 0)
                    (bcat3 (emit-mov-r64-r64 13 $idx_v)
                           (b4 73 193 239 (- 64 $scale_lg2))
                           (emit-jcc-sym 133 LblInvalid))
                    Nil))
              ($shl_idx
                (if (> $scale_lg2 0)
                    (b4 73 193 231 $scale_lg2)
                    Nil)))
         (bcat6 $hi_check
                (emit-mov-r64-r64 13 $idx_v)
                $shl_idx
                (bcat (b3 77 1 254) (emit-jcc-sym 130 LblInvalid))
                (emit-load-frame-u64 13 $len_off)
                (bcat (b3 77 57 254) (emit-jcc-sym 135 LblInvalid))))))

(= (emit-addr-disp $len_off $disp32)
   (if (== $disp32 0)
       Nil
       (if (> $disp32 0)
           (bcat5 (emit-mov-imm64 13 $disp32)
                  (b3 77 1 254)
                  (emit-jcc-sym 130 LblInvalid)
                  (emit-load-frame-u64 13 $len_off)
                  (bcat (b3 77 57 254) (emit-jcc-sym 135 LblInvalid)))
           (let $mag (- 0 $disp32)
             (bcat3 (emit-mov-imm64 13 $mag)
                    (b3 77 41 254)
                    (emit-jcc-sym 130 LblInvalid))))))

(= (emit-instr (InsnAddr $region_id $dst $base_v $idx_v $scale_lg2 $disp32))
   (let* (($ptr_off (* $region_id 16))
          ($len_off (+ (* $region_id 16) 8)))
     (bcat6
       (emit-fuel-step)
       (bcat4 (emit-mov-r64-r64 12 $base_v)
              (emit-load-frame-u64 13 $ptr_off)
              (b3 77 41 254)
              (emit-jcc-sym 130 LblInvalid))
       (bcat3 (emit-load-frame-u64 13 $len_off)
              (b3 77 57 254)
              (emit-jcc-sym 135 LblInvalid))
       (emit-addr-idx $len_off $idx_v $scale_lg2)
       (emit-addr-disp $len_off $disp32)
       (bcat3 (emit-load-frame-u64 13 $ptr_off)
              (b3 77 1 254)
              (emit-mov-r64-r64 $dst 12)))))

(= (emit-instr (InsnLoad $region_id $width $ty $dst $base_v $disp32))
   (if (== $region_id 255)
       (bcat3 (emit-fuel-step)
              (emit-load-frame-u64 $dst $disp32)
              (emit-canon-reg $dst $ty))
       (let* (($d (hw-reg $dst))
              ($r14 14)
              ($ld_bytes
                (if (== $width 1)
                    (b4 (rex-byte 0 $d 0 $r14) 15 182 (modrm-byte 0 $d $r14))
                    (if (== $width 4)
                        (b3 (rex-byte 0 $d 0 $r14) 139 (modrm-byte 0 $d $r14))
                        (b3 (rex-byte 1 $d 0 $r14) 139 (modrm-byte 0 $d $r14))))))
         (bcat4 (emit-fuel-step)
                (emit-checked-mem-addr-in-r14 $region_id $base_v $disp32 $width)
                $ld_bytes
                (emit-canon-reg $dst $ty)))))

(= (emit-instr (InsnStore $region_id $width $base_v $disp32 $val_v))
   (let* (($s (hw-reg $val_v))
          ($r14 14)
          ($st_bytes
            (if (== $width 1)
                (b3 (rex-byte 0 $s 0 $r14) 136 (modrm-byte 0 $s $r14))
                (if (== $width 4)
                    (b3 (rex-byte 0 $s 0 $r14) 137 (modrm-byte 0 $s $r14))
                    (b3 (rex-byte 1 $s 0 $r14) 137 (modrm-byte 0 $s $r14))))))
     (bcat3 (emit-fuel-step)
            (emit-checked-mem-addr-in-r14 $region_id $base_v $disp32 $width)
            $st_bytes)))

(= (emit-instr (InsnCmpImm $cond $ty $dst $src1 $imm64))
   (bcat4 (emit-fuel-step)
          (emit-mov-r64-r64 12 $src1)
          (emit-mov-imm64 13 $imm64)
          (emit-cmp-tail $cond $ty $dst)))

(= (emit-instr (InsnCmpReg $cond $ty $dst $src1 $src2))
   (bcat4 (emit-fuel-step)
          (emit-mov-r64-r64 12 $src1)
          (emit-mov-r64-r64 13 $src2)
          (emit-cmp-tail $cond $ty $dst)))

; Structured Control Statements
(= (emit-stmt (StmtInstr $ins))
   (emit-instr $ins))

(= (emit-stmt (StmtSeq $s1 $s2))
   (bcat (emit-stmt $s1) (emit-stmt $s2)))

(= (emit-stmt (StmtIf $cond_reg $then_stmt $else_stmt))
   (let* (($c (hw-reg $cond_reg))
          ($then_bytes (emit-stmt $then_stmt))
          ($else_bytes (emit-stmt $else_stmt))
          ($then_len (stream-byte-len $then_bytes))
          ($else_len (stream-byte-len $else_bytes))
          ($jz_disp (+ $then_len 5)))
     (bcat5
       (b3 (rex-byte 1 $c 0 $c) 133 (modrm-byte 3 $c $c)) ; test r64(cond), r64(cond)
       (emit-jcc-disp 132 $jz_disp)                        ; jz else_branch
       $then_bytes
       (emit-jmp-disp $else_len)                           ; jmp end_if
       $else_bytes)))

(= (emit-stmt (StmtCountLoop $ir $br $max_iters $body_stmt))
   (let* (($ir_hw (hw-reg $ir))
          ($br_hw (hw-reg $br))
          ($body_bytes (emit-stmt $body_stmt))
          ($body_len (stream-byte-len $body_bytes))
          ($jae_disp (+ $body_len 9))
          ($jmp_back (- 0 (+ $body_len 18))))
     (bcat6
       (emit-mov-imm64 12 $max_iters)
       (bcat (b3 (rex-byte 1 14 0 $br_hw) 57 (modrm-byte 3 14 $br_hw))
             (emit-jcc-sym 135 LblUnsupported))
       (emit-mov-imm64 $ir 0)
       (bcat (b3 (rex-byte 1 $br_hw 0 $ir_hw) 57 (modrm-byte 3 $br_hw $ir_hw))
             (emit-jcc-disp 131 $jae_disp))
       $body_bytes
       (bcat (b4 (rex-byte 1 0 0 $ir_hw) 131 (modrm-byte 3 0 $ir_hw) 1)
             (emit-jmp-disp $jmp_back)))))

(= (emit-stmt (StmtEarlyExitLoop $ir $br $cr $max_iters $body_stmt))
   (let* (($ir_hw (hw-reg $ir))
          ($br_hw (hw-reg $br))
          ($cr_hw (hw-reg $cr))
          ($body_bytes (emit-stmt $body_stmt))
          ($body_len (stream-byte-len $body_bytes))
          ($jae_disp (+ $body_len 27))
          ($jz1_disp (+ $body_len 18))
          ($jmp_back (- 0 (+ $body_len 36))))
     (bcat6
       (emit-mov-imm64 12 $max_iters)
       (bcat (b3 (rex-byte 1 14 0 $br_hw) 57 (modrm-byte 3 14 $br_hw))
             (emit-jcc-sym 135 LblUnsupported))
       (emit-mov-imm64 $ir 0)
       (bcat4 (b3 (rex-byte 1 $br_hw 0 $ir_hw) 57 (modrm-byte 3 $br_hw $ir_hw))
              (emit-jcc-disp 131 $jae_disp)
              (b3 (rex-byte 1 $cr_hw 0 $cr_hw) 133 (modrm-byte 3 $cr_hw $cr_hw))
              (emit-jcc-disp 132 $jz1_disp))
       $body_bytes
       (bcat4 (b3 (rex-byte 1 $cr_hw 0 $cr_hw) 133 (modrm-byte 3 $cr_hw $cr_hw))
              (emit-jcc-disp 132 9)
              (b4 (rex-byte 1 0 0 $ir_hw) 131 (modrm-byte 3 0 $ir_hw) 1)
              (emit-jmp-disp $jmp_back)))))

(= (emit-stmt (StmtReturn $outcome $ret_reg))
   (bcat4
     (emit-mov-r64-r64 8 $ret_reg)
     (emit-store-frame-imm32 144 $outcome)
     (emit-store-frame-u64 152 8)
     (emit-jmp-sym LblEpilogue)))

; -----------------------------------------------------------------------------
; 5. Top-Level Program Wrapper & Two-Pass Symbolic Rel32 Resolver
; -----------------------------------------------------------------------------

(= (emit-prologue)
   (bcat (b4 83 65 84 65)
         (bcat (b4 85 65 86 65) (b1 87))))

(= (emit-init-fuel-used)
   (emit-store-frame-imm32 168 0))

(= (emit-handler-block $outcome)
   (bcat4
     (emit-mov-imm64 8 $outcome)
     (emit-store-frame-imm32 144 $outcome)
     (emit-store-frame-u64 152 8)
     (emit-jmp-sym LblEpilogue)))

(= (emit-epilogue)
   (bcat3 (b4 65 95 65 94)
          (b4 65 93 65 92)
          (b2 91 195)))

(= (lookup-target LblInvalid     $inv_off $exh_off $uns_off $epi_off) $inv_off)
(= (lookup-target LblExhausted   $inv_off $exh_off $uns_off $epi_off) $exh_off)
(= (lookup-target LblUnsupported $inv_off $exh_off $uns_off $epi_off) $uns_off)
(= (lookup-target LblEpilogue    $inv_off $exh_off $uns_off $epi_off) $epi_off)

(= (resolve-stream Nil $_ $_ $_ $_ $_) Nil)
(= (resolve-stream (Cons (B $b) $rest) $cur_off $inv_off $exh_off $uns_off $epi_off)
   (Cons (B $b) (resolve-stream $rest (+ $cur_off 1) $inv_off $exh_off $uns_off $epi_off)))
(= (resolve-stream (Cons (Rel32 $lbl) $rest) $cur_off $inv_off $exh_off $uns_off $epi_off)
   (let* (($target_off (lookup-target $lbl $inv_off $exh_off $uns_off $epi_off))
          ($rel (- $target_off (+ $cur_off 4))))
     (bcat (i32-le $rel)
           (resolve-stream $rest (+ $cur_off 4) $inv_off $exh_off $uns_off $epi_off))))

(= (tisa-compile-x86 $root_stmt)
   (let* (($pre (bcat (emit-prologue) (emit-init-fuel-used))) ; 20 bytes
          ($body (emit-stmt $root_stmt))
          ($has_inv (stream-uses-label $body LblInvalid))
          ($has_exh (stream-uses-label $body LblExhausted))
          ($has_uns (stream-uses-label $body LblUnsupported))
          ($inv_blk (if $has_inv (emit-handler-block 3) Nil))
          ($exh_blk (if $has_exh (emit-handler-block 4) Nil))
          ($uns_blk (if $has_uns (emit-handler-block 2) Nil))
          ($epi (emit-epilogue))
          ($body_len (stream-byte-len $body))
          ($inv_off (+ 20 $body_len))
          ($exh_off (+ $inv_off (stream-byte-len $inv_blk)))
          ($uns_off (+ $exh_off (stream-byte-len $exh_blk)))
          ($epi_off (+ $uns_off (stream-byte-len $uns_blk)))
          ($full_sym (bcat6 $pre $body $inv_blk $exh_blk $uns_blk $epi)))
     (resolve-stream $full_sym 0 $inv_off $exh_off $uns_off $epi_off)))

; -----------------------------------------------------------------------------
; 6. Table-Driven Lean Flat-Rule Specializer (`RuleTable -> t-ISA AST`)
; -----------------------------------------------------------------------------

(= (specialize-out-field $np $out_reg $j (FromField $mi $mj))
   (StmtSeq
     (StmtInstr (InsnLoad $mi 8 TypeU64 6 (+ 1 $mi) (+ 8 (* $mj 8))))
     (StmtInstr (InsnStore $np 8 $out_reg (+ 8 (* $j 8)) 6))))

(= (specialize-out-field $np $out_reg $j (FromConst $cval))
   (StmtSeq
     (StmtInstr (InsnImm TypeU64 6 $cval))
     (StmtInstr (InsnStore $np 8 $out_reg (+ 8 (* $j 8)) 6))))

(= (specialize-concl $np $mtag $f0 $f1 $f2)
   (let $out_reg (+ 1 $np)
     (StmtSeq
       (StmtSeq
         (StmtSeq
           (StmtSeq
             (StmtSeq
               (StmtSeq
                 (StmtInstr (InsnImm TypeU32Z 6 $mtag))
                 (StmtInstr (InsnStore $np 4 $out_reg 0 6)))
               (StmtSeq
                 (StmtInstr (InsnImm TypeU32Z 6 0))
                 (StmtInstr (InsnStore $np 4 $out_reg 4 6))))
             (specialize-out-field $np $out_reg 0 $f0))
           (specialize-out-field $np $out_reg 1 $f1))
         (specialize-out-field $np $out_reg 2 $f2))
       (StmtSeq
         (StmtInstr (InsnImm TypeU64 8 1))
         (StmtReturn 1 8)))))

(= (refuse-stmt)
   (StmtSeq
     (StmtInstr (InsnImm TypeU64 8 0))
     (StmtReturn 0 8)))

(= (wrap-guard (GuardConst $i $j $cval) $curr)
   (let $preg (+ 1 $i)
     (StmtSeq
       (StmtSeq
         (StmtInstr (InsnLoad $i 8 TypeU64 6 $preg (+ 8 (* $j 8))))
         (StmtInstr (InsnCmpImm CmpEq TypeU64 7 6 $cval)))
       (StmtIf 7 $curr (refuse-stmt)))))

(= (wrap-guard (GuardField $i $j $i0 $j0) $curr)
   (let* (($preg1 (+ 1 $i))
          ($preg2 (+ 1 $i0)))
     (StmtSeq
       (StmtSeq
         (StmtSeq
           (StmtInstr (InsnLoad $i 8 TypeU64 6 $preg1 (+ 8 (* $j 8))))
           (StmtInstr (InsnLoad $i0 8 TypeU64 8 $preg2 (+ 8 (* $j0 8)))))
         (StmtInstr (InsnCmpReg CmpEq TypeU64 7 6 8)))
       (StmtIf 7 $curr (refuse-stmt)))))

(= (wrap-guards Nil $curr) $curr)
(= (wrap-guards (Cons $g $rest) $curr)
   (wrap-guard $g (wrap-guards $rest $curr)))

(= (wrap-ktag $i $ktag $curr)
   (let $preg (+ 1 $i)
     (StmtSeq
       (StmtSeq
         (StmtInstr (InsnLoad $i 4 TypeU32Z 6 $preg 0))
         (StmtInstr (InsnCmpImm CmpEq TypeU32Z 7 6 $ktag)))
       (StmtIf 7 $curr (refuse-stmt)))))

(= (wrap-ktags $_ Nil $curr) $curr)
(= (wrap-ktags $i (Cons $kt $rest) $curr)
   (wrap-ktag $i $kt (wrap-ktags (+ $i 1) $rest $curr)))

(= (tisa-specialize-lean-flat-rule (FlatRule $name $np $ktags $guards $mtag $f0 $f1 $f2))
   (let $concl (specialize-concl $np $mtag $f0 $f1 $f2)
     (wrap-ktags 0 $ktags (wrap-guards $guards $concl))))

; Table-driven Micromath 4-premise substitution specializer (`mm_sub1_leaf` / `mm_sub2_leaf`)
(= (mm-load-out $j (FromField $mi $mj))
   (StmtInstr (InsnLoad $mi 8 TypeU64 (+ 6 $j) (+ 1 $mi) (* $mj 8))))

(= (mm-store-out $j)
   (StmtInstr (InsnStore 4 8 5 (* $j 8) (+ 6 $j))))

(= (mm-wrap-guard (GuardField $i $j $i0 $j0) $curr)
   (let* (($p1 (+ 1 $i))
          ($p2 (+ 1 $i0)))
     (StmtSeq
       (StmtSeq
         (StmtSeq
           (StmtInstr (InsnLoad $i 8 TypeU64 6 $p1 (* $j 8)))
           (StmtInstr (InsnLoad $i0 8 TypeU64 8 $p2 (* $j0 8))))
         (StmtInstr (InsnCmpReg CmpEq TypeU64 7 6 8)))
       (StmtIf 7 $curr (refuse-stmt)))))

(= (mm-wrap-guards Nil $curr) $curr)
(= (mm-wrap-guards (Cons $g $rest) $curr)
   (mm-wrap-guard $g (mm-wrap-guards $rest $curr)))

(= (tisa-specialize-mm-sub-rule (MmSubRule $name $guards $m0 $m1 $m2 $m3))
   (let* (($write_out
            (StmtSeq
              (StmtSeq
                (StmtSeq
                  (StmtSeq
                    (StmtSeq
                      (StmtSeq
                        (StmtSeq
                          (StmtSeq
                            (mm-load-out 0 $m0)
                            (mm-load-out 1 $m1))
                          (mm-load-out 2 $m2))
                        (mm-load-out 3 $m3))
                      (mm-store-out 0))
                    (mm-store-out 1))
                  (mm-store-out 2))
                (mm-store-out 3))
              (StmtSeq
                (StmtInstr (InsnImm TypeU64 8 1))
                (StmtReturn 1 8))))
          ($unsup
            (StmtSeq
              (StmtInstr (InsnImm TypeU64 8 2))
              (StmtReturn 2 8)))
          ($dest_check
            (StmtSeq
              (StmtSeq
                (StmtInstr (InsnLoad 255 8 TypeU64 6 0 176)) ; frame->arg0
                (StmtInstr (InsnLoad 255 8 TypeU64 8 0 184))) ; frame->arg1
              (StmtInstr (InsnCmpReg CmpUlt TypeU64 7 6 8))))
          ($core (StmtSeq $dest_check (StmtIf 7 $write_out $unsup))))
     (mm-wrap-guards $guards $core)))

(= (mm-sub-rule-row mm_sub1_leaf)
   (MmSubRule mm_sub1_leaf
              (Cons (GuardField 1 1 0 2)
              (Cons (GuardField 2 1 0 3)
              (Cons (GuardField 2 2 1 2)
              (Cons (GuardField 2 3 1 3)
              (Cons (GuardField 3 1 0 0)
              (Cons (GuardField 3 2 1 2)
              (Cons (GuardField 3 3 1 3) Nil)))))))
              (FromField 3 0) (FromField 0 1) (FromField 1 0) (FromField 2 0)))

(= (mm-sub-rule-row mm_sub2_leaf)
   (MmSubRule mm_sub2_leaf
              (Cons (GuardField 1 1 0 2)
              (Cons (GuardField 2 1 0 3)
              (Cons (GuardField 2 2 1 2)
              (Cons (GuardField 2 3 1 3)
              (Cons (GuardField 3 1 0 1)
              (Cons (GuardField 3 2 1 0)
              (Cons (GuardField 3 3 2 0) Nil)))))))
              (FromField 3 0) (FromField 0 0) (FromField 1 2) (FromField 1 3)))

(= (compile-mm-sub-rule-x86 $rule_name)
   (let* (($ast (tisa-specialize-mm-sub-rule (mm-sub-rule-row $rule_name)))
          ($bytes (tisa-compile-x86 $ast))
          ($len (stream-byte-len $bytes)))
     (EmittedProgram $rule_name $len $bytes)))

; -----------------------------------------------------------------------------
; 6b. Generic Consumer Builders (`ordinary_flat_fire` & `ordinary_flat_adapter`)
; -----------------------------------------------------------------------------

(= (seq-list (Cons $s Nil)) $s)
(= (seq-list (Cons $s (Cons $s2 $rest)))
   (StmtSeq $s (seq-list (Cons $s2 $rest))))

(= (s-imm $ty $dst $imm64)
   (StmtInstr (InsnImm $ty $dst $imm64)))
(= (s-bin $op $ty $dst $src1 $src2)
   (StmtInstr (InsnBin $op $ty $dst $src1 $src2)))
(= (s-shift $subop $ty $dst $src1 $sh)
   (StmtInstr (InsnShift $subop $ty $dst $src1 $sh)))
(= (s-extract $ty $dst $src1 $lsb $wid)
   (StmtInstr (InsnExtract $ty $dst $src1 $lsb $wid)))
(= (s-addr $rid $dst $base $idx $scale $disp)
   (StmtInstr (InsnAddr $rid $dst $base $idx $scale $disp)))
(= (s-load $rid $wid $ty $dst $base $disp)
   (StmtInstr (InsnLoad $rid $wid $ty $dst $base $disp)))
(= (s-load-ptr $dst $rid)
   (StmtInstr (InsnLoad 255 8 TypePtr $dst 0 (* $rid 16))))
(= (s-load-len $dst $rid)
   (StmtInstr (InsnLoad 255 8 TypeU64 $dst 0 (+ (* $rid 16) 8))))
(= (s-store $rid $wid $base $disp $val)
   (StmtInstr (InsnStore $rid $wid $base $disp $val)))
(= (s-cmp-reg $cond $ty $dst $src1 $src2)
   (StmtInstr (InsnCmpReg $cond $ty $dst $src1 $src2)))
(= (s-cmp-imm $cond $ty $dst $src1 $imm64)
   (StmtInstr (InsnCmpImm $cond $ty $dst $src1 $imm64)))

(= (unsup-stmt)
   (StmtSeq (s-imm TypeU64 8 2) (StmtReturn 2 8)))

(= (build-ordinary-flat-fire-ast)
   (let* (($gbody
            (seq-list
              (Cons (s-addr 2 7 3 6 2 0)
              (Cons (s-load 2 4 TypeU32Z 8 7 0)
              (Cons (s-extract TypeU32Z 9 8 0 8)
              (Cons (s-extract TypeU32Z 10 8 8 8)
              (Cons (s-addr 1 7 2 9 2 0)
              (Cons (s-load 1 4 TypeU32Z 9 7 0)
              (Cons (s-bin BinAdd TypeU32Z 9 9 10)
              (Cons (s-addr 0 7 1 9 2 0)
              (Cons (s-load 0 4 TypeU32Z 9 7 0)
              (Cons (s-extract TypeU32Z 10 8 16 8)
              (Cons (s-extract TypeU32Z 11 8 24 8)
              (Cons (s-addr 1 7 2 10 2 0)
              (Cons (s-load 1 4 TypeU32Z 10 7 0)
              (Cons (s-bin BinAdd TypeU32Z 10 10 11)
              (Cons (s-addr 0 7 1 10 2 0)
              (Cons (s-load 0 4 TypeU32Z 10 7 0)
              (Cons (s-cmp-reg CmpEq TypeU32Z 5 9 10) Nil)))))))))))))))))))
          ($mbody
            (seq-list
              (Cons (s-addr 3 7 3 6 2 0)
              (Cons (s-load 3 4 TypeU32Z 8 7 0)
              (Cons (s-extract TypeU32Z 9 8 0 8)
              (Cons (s-extract TypeU32Z 10 8 8 8)
              (Cons (s-addr 1 7 2 9 2 0)
              (Cons (s-load 1 4 TypeU32Z 9 7 0)
              (Cons (s-bin BinAdd TypeU32Z 9 9 10)
              (Cons (s-addr 0 7 1 9 2 0)
              (Cons (s-load 0 4 TypeU32Z 9 7 0)
              (Cons (s-addr 5 7 4 6 2 0)
              (Cons (s-store 5 4 7 0 9) Nil)))))))))))))
          ($cbody
            (seq-list
              (Cons (s-addr 5 7 4 6 2 0)
              (Cons (s-load 5 4 TypeU32Z 9 7 0)
              (Cons (s-addr 4 7 3 6 2 0)
              (Cons (s-store 4 4 7 0 9) Nil))))))
          ($accept
            (seq-list
              (Cons (s-load-ptr 3 3)
              (Cons (s-load-ptr 4 5)
              (Cons (s-load-len 5 3)
              (Cons (s-shift ShiftShru TypeU64 5 5 2)
              (Cons (StmtCountLoop 6 5 32 $mbody)
              (Cons (s-load-ptr 3 4)
              (Cons (StmtCountLoop 6 5 32 $cbody)
              (Cons (s-imm TypeU64 8 1)
              (Cons (StmtReturn 1 8) Nil))))))))))))
     (seq-list
       (Cons (s-load-ptr 1 0)
       (Cons (s-load-ptr 2 1)
       (Cons (s-load-ptr 3 2)
       (Cons (s-load-len 4 2)
       (Cons (s-shift ShiftShru TypeU64 4 4 2)
       (Cons (s-imm TypeBool 5 1)
       (Cons (StmtEarlyExitLoop 6 4 5 32 $gbody)
       (Cons (StmtIf 5 $accept (refuse-stmt)) Nil)))))))))))

(= (build-ordinary-flat-adapter-ast)
   (let* (($gbody
            (seq-list
              (Cons (s-addr 3 7 3 6 2 0)
              (Cons (s-load 3 4 TypeU32Z 8 7 0)
              (Cons (s-extract TypeU32Z 9 8 0 8)
              (Cons (s-extract TypeU32Z 10 8 8 8)
              (Cons (s-addr 6 7 2 9 2 0)
              (Cons (s-load 6 4 TypeU32Z 9 7 0)
              (Cons (s-bin BinAdd TypeU32Z 9 9 10)
              (Cons (s-addr 5 7 1 9 2 0)
              (Cons (s-load 5 4 TypeU32Z 9 7 0)
              (Cons (s-extract TypeU32Z 10 8 16 8)
              (Cons (s-extract TypeU32Z 11 8 24 8)
              (Cons (s-addr 6 7 2 10 2 0)
              (Cons (s-load 6 4 TypeU32Z 10 7 0)
              (Cons (s-bin BinAdd TypeU32Z 10 10 11)
              (Cons (s-addr 5 7 1 10 2 0)
              (Cons (s-load 5 4 TypeU32Z 10 7 0)
              (Cons (s-cmp-reg CmpEq TypeU32Z 5 9 10) Nil)))))))))))))))))))
          ($mbody
            (seq-list
              (Cons (s-addr 4 7 3 6 2 0)
              (Cons (s-load 4 4 TypeU32Z 8 7 0)
              (Cons (s-extract TypeU32Z 9 8 0 8)
              (Cons (s-extract TypeU32Z 10 8 8 8)
              (Cons (s-addr 6 7 2 9 2 0)
              (Cons (s-load 6 4 TypeU32Z 9 7 0)
              (Cons (s-bin BinAdd TypeU32Z 9 9 10)
              (Cons (s-addr 5 7 1 9 2 0)
              (Cons (s-load 5 4 TypeU32Z 9 7 0)
              (Cons (s-addr 8 7 11 6 2 0)
              (Cons (s-store 8 4 7 0 9)
              (Cons (s-addr 7 7 4 6 2 0)
              (Cons (s-store 7 4 7 0 9) Nil)))))))))))))))
          ($p3_make
            (seq-list
              (Cons (s-load-ptr 3 4)
              (Cons (s-load-ptr 4 7)
              (Cons (s-load-ptr 11 8)
              (Cons (s-load-len 5 4)
              (Cons (s-shift ShiftShru TypeU64 5 5 2)
              (Cons (StmtCountLoop 6 5 32 $mbody)
              (Cons (s-imm TypeU64 8 1)
              (Cons (StmtReturn 1 8) Nil))))))))))
          ($p3
            (seq-list
              (Cons (s-load-ptr 1 5)
              (Cons (s-load-ptr 2 6)
              (Cons (s-load-ptr 3 3)
              (Cons (s-load-len 4 3)
              (Cons (s-shift ShiftShru TypeU64 4 4 2)
              (Cons (s-imm TypeBool 5 1)
              (Cons (StmtEarlyExitLoop 6 4 5 32 $gbody)
              (Cons (StmtIf 5 $p3_make (refuse-stmt)) Nil))))))))))
          ($pack_p
            (seq-list
              (Cons (s-shift ShiftShl TypeU32Z 8 6 2)
              (Cons (s-addr 6 7 4 6 2 0)
              (Cons (s-store 6 4 7 0 8)
              (Cons (s-addr 1 7 2 6 2 0)
              (Cons (s-load 1 4 TypeU32Z 9 7 0)
              (Cons (s-addr 0 7 1 9 2 0)
              (Cons (s-addr 5 10 3 8 2 0)
              (Cons (s-load 0 4 TypeU32Z 11 7 0)
              (Cons (s-store 5 4 10 0 11)
              (Cons (s-load 0 4 TypeU32Z 11 7 4)
              (Cons (s-store 5 4 10 4 11)
              (Cons (s-load 0 4 TypeU32Z 11 7 8)
              (Cons (s-store 5 4 10 8 11)
              (Cons (s-load 0 4 TypeU32Z 11 7 12)
              (Cons (s-store 5 4 10 12 11) Nil)))))))))))))))))
          ($pack_c
            (seq-list
              (Cons (s-addr 2 7 1 6 2 0)
              (Cons (s-load 2 4 TypeU32Z 9 7 0)
              (Cons (s-bin BinAdd TypeU64 10 8 6)
              (Cons (s-addr 5 7 3 10 2 0)
              (Cons (s-store 5 4 7 0 9) Nil)))))))
          ($p2
            (seq-list
              (Cons (s-load-ptr 1 0)
              (Cons (s-load-ptr 2 1)
              (Cons (s-load-ptr 3 5)
              (Cons (s-load-ptr 4 6)
              (Cons (s-load-len 5 1)
              (Cons (s-shift ShiftShru TypeU64 5 5 2)
              (Cons (StmtCountLoop 6 5 24 $pack_p)
              (Cons (s-shift ShiftShl TypeU32Z 8 5 2)
              (Cons (s-addr 6 7 4 5 2 0)
              (Cons (s-store 6 4 7 0 8)
              (Cons (s-load-ptr 1 2)
              (Cons (s-load-len 4 2)
              (Cons (s-shift ShiftShru TypeU64 4 4 2)
              (Cons (StmtCountLoop 6 4 32 $pack_c)
              (Cons $p3 Nil)))))))))))))))))
          ($ebody
            (seq-list
              (Cons (s-addr 1 9 7 6 2 0)
              (Cons (s-load 1 4 TypeU32Z 10 9 0)
              (Cons (s-imm TypeU64 11 4)
              (Cons (s-bin BinAdd TypeU64 10 10 11)
              (Cons (s-cmp-reg CmpUle TypeU64 8 10 1) Nil)))))))
          ($after_caps
            (seq-list
              (Cons (s-load-ptr 7 1)
              (Cons (s-imm TypeBool 8 1)
              (Cons (StmtEarlyExitLoop 6 2 8 24 $ebody)
              (Cons (StmtIf 8 $p2 (unsup-stmt)) Nil))))))
          ($cap_checks
            (seq-list
              (Cons (s-shift ShiftShl TypeU64 6 2 2)
              (Cons (s-bin BinAdd TypeU64 6 6 3)
              (Cons (s-load-len 7 5)
              (Cons (s-shift ShiftShru TypeU64 7 7 2)
              (Cons (s-cmp-reg CmpUle TypeU64 8 6 7)
              (Cons (s-imm TypeU64 6 1)
              (Cons (s-bin BinAdd TypeU64 6 2 6)
              (Cons (s-load-len 7 6)
              (Cons (s-shift ShiftShru TypeU64 7 7 2)
              (Cons (s-cmp-reg CmpUle TypeU64 9 6 7)
              (Cons (s-bin BinAnd TypeBool 8 8 9)
              (Cons (s-load-len 7 7)
              (Cons (s-shift ShiftShru TypeU64 7 7 2)
              (Cons (s-cmp-reg CmpUle TypeU64 9 5 7)
              (Cons (s-bin BinAnd TypeBool 8 8 9)
              (Cons (s-load-len 7 8)
              (Cons (s-shift ShiftShru TypeU64 7 7 2)
              (Cons (s-cmp-reg CmpUle TypeU64 9 5 7)
              (Cons (s-bin BinAnd TypeBool 8 8 9)
              (Cons (s-cmp-imm CmpUle TypeU64 9 2 24)
              (Cons (s-bin BinAnd TypeBool 8 8 9)
              (Cons (s-cmp-imm CmpUle TypeU64 9 3 32)
              (Cons (s-bin BinAnd TypeBool 8 8 9)
              (Cons (s-cmp-imm CmpUle TypeU64 9 4 32)
              (Cons (s-bin BinAnd TypeBool 8 8 9)
              (Cons (s-cmp-imm CmpUle TypeU64 9 5 32)
              (Cons (s-bin BinAnd TypeBool 8 8 9) Nil))))))))))))))))))))))))))))))
     (seq-list
       (Cons (s-load-len 1 0)
       (Cons (s-shift ShiftShru TypeU64 1 1 2)
       (Cons (s-load-len 2 1)
       (Cons (s-shift ShiftShru TypeU64 2 2 2)
       (Cons (s-load-len 3 2)
       (Cons (s-shift ShiftShru TypeU64 3 3 2)
       (Cons (s-load-len 4 3)
       (Cons (s-shift ShiftShru TypeU64 4 4 2)
       (Cons (s-load-len 5 4)
       (Cons (s-shift ShiftShru TypeU64 5 5 2)
       (Cons $cap_checks
       (Cons (StmtIf 8 $after_caps (unsup-stmt)) Nil)))))))))))))))

(= (compile-ordinary-flat-fire-x86)
   (let* (($ast (build-ordinary-flat-fire-ast))
          ($bytes (tisa-compile-x86 $ast))
          ($len (stream-byte-len $bytes)))
     (EmittedProgram ordinary_flat_fire $len $bytes)))

(= (compile-ordinary-flat-adapter-x86)
   (let* (($ast (build-ordinary-flat-adapter-ast))
          ($bytes (tisa-compile-x86 $ast))
          ($len (stream-byte-len $bytes)))
     (EmittedProgram ordinary_flat_adapter $len $bytes)))

; -----------------------------------------------------------------------------
; 7. All 11 Premise-Bearing Lean Rule Rows (`R_DERIVE_IS_TYPE .. R_ADMIT_THM`)
; -----------------------------------------------------------------------------

(= (lean-flat-rule-row R_DERIVE_IS_TYPE)
   (FlatRule R_DERIVE_IS_TYPE 2
             (Cons 5637 (Cons 7685 Nil))
             (Cons (GuardField 1 0 0 1) Nil)
             6661 (FromField 0 0) (FromField 1 1) (FromConst 0)))

(= (lean-flat-rule-row R_DERIVE_IS_PROP)
   (FlatRule R_DERIVE_IS_PROP 1
             (Cons 6661 Nil)
             (Cons (GuardConst 0 1 0) Nil)
             7173 (FromField 0 0) (FromConst 0) (FromConst 0)))

(= (lean-flat-rule-row R_CHECK_CONV)
   (FlatRule R_CHECK_CONV 3
             (Cons 5637 (Cons 6149 (Cons 6661 Nil)))
             (Cons (GuardField 1 0 0 1) (Cons (GuardField 2 0 1 1) Nil))
             5637 (FromField 0 0) (FromField 1 1) (FromConst 0)))

(= (lean-flat-rule-row R_ADMIT_AXIOM)
   (FlatRule R_ADMIT_AXIOM 2
             (Cons 8197 (Cons 6661 Nil))
             (Cons (GuardField 1 0 0 1) Nil)
             1539 (FromField 0 0) (FromField 0 1) (FromConst 0)))

(= (lean-flat-rule-row R_ADMIT_QUOT)
   (FlatRule R_ADMIT_QUOT 2
             (Cons 8197 (Cons 6661 Nil))
             (Cons (GuardField 1 0 0 1) Nil)
             3587 (FromField 0 0) (FromField 0 1) (FromConst 0)))

(= (lean-flat-rule-row R_ADMIT_IND)
   (FlatRule R_ADMIT_IND 2
             (Cons 8197 (Cons 6661 Nil))
             (Cons (GuardField 1 0 0 1) Nil)
             4099 (FromField 0 0) (FromField 0 1) (FromConst 0)))

(= (lean-flat-rule-row R_ADMIT_CTOR)
   (FlatRule R_ADMIT_CTOR 3
             (Cons 8709 (Cons 4099 (Cons 6661 Nil)))
             (Cons (GuardField 1 0 0 1) (Cons (GuardField 2 0 0 2) Nil))
             4611 (FromField 0 0) (FromField 0 1) (FromField 0 2)))

(= (lean-flat-rule-row R_ADMIT_REC)
   (FlatRule R_ADMIT_REC 2
             (Cons 8709 (Cons 6661 Nil))
             (Cons (GuardField 1 0 0 2) Nil)
             5123 (FromField 0 0) (FromField 0 1) (FromField 0 2)))

(= (lean-flat-rule-row R_ADMIT_DEFN)
   (FlatRule R_ADMIT_DEFN 3
             (Cons 8709 (Cons 6661 (Cons 5637 Nil)))
             (Cons (GuardField 1 0 0 1) (Cons (GuardField 2 0 0 2) (Cons (GuardField 2 1 0 1) Nil)))
             2051 (FromField 0 0) (FromField 0 1) (FromField 0 2)))

(= (lean-flat-rule-row R_ADMIT_OPAQUE)
   (FlatRule R_ADMIT_OPAQUE 3
             (Cons 8709 (Cons 6661 (Cons 5637 Nil)))
             (Cons (GuardField 1 0 0 1) (Cons (GuardField 2 0 0 2) (Cons (GuardField 2 1 0 1) Nil)))
             3075 (FromField 0 0) (FromField 0 1) (FromField 0 2)))

(= (lean-flat-rule-row R_ADMIT_THM)
   (FlatRule R_ADMIT_THM 3
             (Cons 8709 (Cons 7173 (Cons 5637 Nil)))
             (Cons (GuardField 1 0 0 1) (Cons (GuardField 2 0 0 2) (Cons (GuardField 2 1 0 1) Nil)))
             2563 (FromField 0 0) (FromField 0 1) (FromField 0 2)))

(= (compile-lean-rule-x86 $rule_name)
   (let* (($ast (tisa-specialize-lean-flat-rule (lean-flat-rule-row $rule_name)))
          ($bytes (tisa-compile-x86 $ast))
          ($len (stream-byte-len $bytes)))
     (EmittedProgram $rule_name $len $bytes)))

!(compile-lean-rule-x86 R_DERIVE_IS_TYPE)
!(compile-lean-rule-x86 R_DERIVE_IS_PROP)
!(compile-lean-rule-x86 R_CHECK_CONV)
!(compile-lean-rule-x86 R_ADMIT_AXIOM)
!(compile-lean-rule-x86 R_ADMIT_QUOT)
!(compile-lean-rule-x86 R_ADMIT_IND)
!(compile-lean-rule-x86 R_ADMIT_CTOR)
!(compile-lean-rule-x86 R_ADMIT_REC)
!(compile-lean-rule-x86 R_ADMIT_DEFN)
!(compile-lean-rule-x86 R_ADMIT_OPAQUE)
!(compile-lean-rule-x86 R_ADMIT_THM)
!(compile-mm-sub-rule-x86 mm_sub1_leaf)
!(compile-mm-sub-rule-x86 mm_sub2_leaf)
!(compile-ordinary-flat-fire-x86)
!(compile-ordinary-flat-adapter-x86)
