; =============================================================================
; verify_tisa_emit_x86.metta — Pure CeTTa Differential Gate for `tisa_emit_x86.metta`
;
; Uses CeTTa's native `fs`, `json`, `str`, and `re` libraries (zero Python) to:
;   1. Read `tisa/manifests/tisa_x86_programs_v1.json` (run from the repository root)
;   2. Compile all 15 `t-ISA` programs (`46,769` machine bytes) in pure MeTTa
;   3. Validate the manifest hex format via `lib_re` (`re:is-match`)
;   4. Verify exact byte length and exact lowercase hex byte-for-byte identity
;      for all 15 / 15 programs (`R_DERIVE_IS_TYPE .. R_ADMIT_THM`,
;      `mm_sub1_leaf`, `mm_sub2_leaf`, `ordinary_flat_fire`,
;      `ordinary_flat_adapter`).
; =============================================================================

!(import! &self fs)
!(import! &self json)
!(import! &self str)
!(import! &self re)
!(import! &self system)
!(import! &self "tisa_emit_x86.metta")

(= (hex-digit-cp $n)
   (if (< $n 10) (+ 48 $n) (+ 87 $n)))

(= (byte-to-hex $b)
   (let* (($lo (% $b 16))
          ($hi (idiv $b 16))
          ($c1 (hex-digit-cp $hi))
          ($c2 (hex-digit-cp $lo)))
     (str:from-codepoints ($c1 $c2))))

(= (stream-to-hex Nil) "")
(= (stream-to-hex (Cons (B $b) $rest))
   (str:concat (byte-to-hex $b) (stream-to-hex $rest)))

(= (verify-emitted-prog $manifest_text $hex_re $idx (EmittedProgram $name $len $bytes))
   (let* (($ref_name (json:parse-at $manifest_text ("programs" $idx "program_name")))
          ($ref_len  (json:parse-at $manifest_text ("programs" $idx "x86_64_artifact" "byte_len")))
          ($ref_hex  (json:parse-at $manifest_text ("programs" $idx "x86_64_artifact" "bytes_hex")))
          ($re_ok    (re:is-match $hex_re $ref_hex))
          ($hex      (stream-to-hex $bytes))
          ($len_ok   (== $len $ref_len))
          ($hex_ok   (== $hex $ref_hex)))
     (if (and $re_ok (and $len_ok $hex_ok))
         (VerifiedProg $idx $ref_name $len PASS)
         (VerifiedProg $idx $ref_name $len FAIL))))

(= (all-progs-pass? Nil) True)
(= (all-progs-pass? (Cons (VerifiedProg $idx $name $len PASS) $rest))
   (all-progs-pass? $rest))
(= (all-progs-pass? (Cons (VerifiedProg $idx $name $len FAIL) $rest))
   False)

!(let* (($manifest_text (fs:read-text "tisa/manifests/tisa_x86_programs_v1.json"))
        ($hex_re (re:compile "^[0-9a-f]+$"))
        ($results
          (Cons (verify-emitted-prog $manifest_text $hex_re 0  (compile-lean-rule-x86 R_DERIVE_IS_TYPE))
          (Cons (verify-emitted-prog $manifest_text $hex_re 1  (compile-lean-rule-x86 R_DERIVE_IS_PROP))
          (Cons (verify-emitted-prog $manifest_text $hex_re 2  (compile-lean-rule-x86 R_CHECK_CONV))
          (Cons (verify-emitted-prog $manifest_text $hex_re 3  (compile-lean-rule-x86 R_ADMIT_AXIOM))
          (Cons (verify-emitted-prog $manifest_text $hex_re 4  (compile-lean-rule-x86 R_ADMIT_QUOT))
          (Cons (verify-emitted-prog $manifest_text $hex_re 5  (compile-lean-rule-x86 R_ADMIT_IND))
          (Cons (verify-emitted-prog $manifest_text $hex_re 6  (compile-lean-rule-x86 R_ADMIT_CTOR))
          (Cons (verify-emitted-prog $manifest_text $hex_re 7  (compile-lean-rule-x86 R_ADMIT_REC))
          (Cons (verify-emitted-prog $manifest_text $hex_re 8  (compile-lean-rule-x86 R_ADMIT_DEFN))
          (Cons (verify-emitted-prog $manifest_text $hex_re 9  (compile-lean-rule-x86 R_ADMIT_OPAQUE))
          (Cons (verify-emitted-prog $manifest_text $hex_re 10 (compile-lean-rule-x86 R_ADMIT_THM))
          (Cons (verify-emitted-prog $manifest_text $hex_re 11 (compile-mm-sub-rule-x86 mm_sub1_leaf))
          (Cons (verify-emitted-prog $manifest_text $hex_re 12 (compile-mm-sub-rule-x86 mm_sub2_leaf))
          (Cons (verify-emitted-prog $manifest_text $hex_re 13 (compile-ordinary-flat-fire-x86))
          (Cons (verify-emitted-prog $manifest_text $hex_re 14 (compile-ordinary-flat-adapter-x86))
          Nil)))))))))))))))))
   (if (all-progs-pass? $results)
       $results
       (let $_ (println! $results)
         (system:exit 1))))
