; x86_census.metta -- what machine code actually uses (CeTTa, PeTTa lane).
;
;   (census:report (TARGET ...))      one line per target, then a comparison
;   (census:hot BINARY PERFDATA)      the same classes weighted by sampled cycles
;   (census:xed-report (TARGET ...))  XED's exact classes, the differential
;                                     against the mnemonic classes, s2n coverage
;   (census:xed-hot BINARY PERFDATA)  the same weighted by sampled cycles
;   (census:gate TARGET)              the instructions outside the forms that
;                                     s2n-bignum's x86 decoder decodes
;
; A TARGET is an ELF binary or a t-ISA image record (.hol, whose program
; bytes are the record's longest double-quoted hex run). The classes are
; those that matter for s2n-bignum's x86 model: indirect branches, jump
; tables, push/pop of memory, bit scans, BMI2, ADX, SIMD, string operations,
; endbr64 and privileged instructions; an instruction in none of them is
; base. PERFDATA is a `perf record -e cycles:u` file of BINARY; the weighted
; census reads `perf annotate`, so a sample counts for the instruction perf
; attributes it to (skid included).
;
; Read-only: it runs objdump, xxd, perf and xed, and reads files. An image,
; and the encodings handed to xed, go to a private temporary directory made
; by `mktemp -d` (so under $TMPDIR), removed afterwards.

!(import! &self proc)
!(import! &self str)
!(import! &self fs)
!(import! &self system)
!(import! &self "s2n_allowlist.metta")

; ---- running tools -----------------------------------------------------------

(= (census:stdout $result)
   (let (proc:result $term $cause $out $err $cap) $result
     (if (== $term (proc:exited 0)) $out (Error $result "command failed"))))

(= (census:run $argv $ms) (census:stdout (proc:run $argv ((timeout-ms $ms)))))

(= (census:disasm-elf $path)
   (census:run ("objdump" "-d" "-w" "--no-addresses" "-M" "att" $path) 120000))

(= (census:is-hex $s) (str:is-all-in xdigit $s))

(= (census:longest-hex $parts $best)
   (if (== $parts ())
       $best
       (let ($s $rest) (decons-atom $parts)
         (if (and (> (str:byte-length $s) (str:byte-length $best)) (census:is-hex $s))
             (census:longest-hex $rest $s)
             (census:longest-hex $rest $best)))))

(= (census:disasm-image $path)
   (let* (($hex (census:longest-hex (str:split "\"" (fs:read-text $path)) ""))
          ($dir (str:trim (census:run ("mktemp" "-d") 10000)))
          ($bin (str:concat $dir "/image.bin"))
          ($w (census:stdout (proc:run ("xxd" "-r" "-p" "-" $bin) ((stdin $hex) (timeout-ms 10000)))))
          ($out (census:run ("objdump" "-D" "-w" "--no-addresses" "-b" "binary"
                             "-m" "i386:x86-64" "-M" "att" $bin) 60000))
          ($r1 (proc:run ("rm" "-f" $bin) ((timeout-ms 10000))))
          ($r2 (proc:run ("rmdir" $dir) ((timeout-ms 10000)))))
     $out))

; ---- parsing ---------------------------------------------------------------

(= (census:member $x $ys)
   (if (== $ys ()) False
       (let ($y $rest) (decons-atom $ys) (if (== $x $y) True (census:member $x $rest)))))

(= (census:prefix $m)
   (census:member $m ("rep" "repz" "repe" "repnz" "repne" "lock" "notrack" "bnd" "data16" "cs" "ds")))

; (insn prefixes mnemonic operands) from assembly text, or () when it is not
; an instruction ("(bad)", padding).
(= (census:parse-asm $asm) (census:strip (str:split-whitespace $asm) ()))

(= (census:strip $toks $pfx)
   (if (== $toks ()) ()
       (let ($t $more) (decons-atom $toks)
         (if (str:starts-with $t "(")
             ()
             (if (and (census:prefix $t) (not (== $more ())))
                 (census:strip $more (cons-atom $t $pfx))
                 (insn $pfx $t (str:join " " $more)))))))

; An objdump -w --no-addresses line is "\tHEX BYTES \tASSEMBLY".
(= (census:objdump-line $line)
   (let $fields (str:split "\t" $line)
     (if (== (length $fields) 3)
         (let ($a $r1) (decons-atom $fields)
           (let ($hex $r2) (decons-atom $r1)
             (let ($asm $r3) (decons-atom $r2)
               (if (== $a "") (census:parse-asm $asm) ()))))
         ())))

; ---- classes ---------------------------------------------------------------

(= (census:has $text $needle) (not (== (str:find $text $needle) (TextNotFound $needle))))

(= (census:when $c $tag $acc) (if $c (cons-atom $tag $acc) $acc))

; The mnemonic without an AT&T size suffix, for the class lists.
(= (census:base $m)
   (let $n (str:byte-length $m)
     (if (> $n 1)
         (if (census:member (str:byte-slice $m (- $n 1) $n) ("b" "w" "l" "q"))
             (str:byte-slice $m 0 (- $n 1))
             $m)
         $m)))

(= (census:in $m $names) (or (census:member $m $names) (census:member (census:base $m) $names)))

(= (census:simd $m $ops)
   (or (census:has $ops "%xmm")
       (or (census:has $ops "%ymm")
           (or (census:has $ops "%zmm")
               (or (census:has $ops "%mm")
                   (or (census:has $ops "%k")
                       (and (str:starts-with $m "v") (not (census:member $m ("verr" "verw"))))))))))

(= (census:tags $pfx $m $ops)
   (let* (($ind-call (and (str:starts-with $m "call") (census:has $ops "*")))
          ($ind-jmp (and (str:starts-with $m "jmp") (census:has $ops "*")))
          ($table (and $ind-jmp (and (census:has $ops "(") (census:has $ops ","))))
          ($a1 (census:when $ind-call indirect-branch ()))
          ($a2 (census:when (and $ind-jmp (not $table)) indirect-branch $a1))
          ($a3 (census:when $table jump-table $a2))
          ($a4 (census:when (and (or (str:starts-with $m "push") (str:starts-with $m "pop"))
                                 (census:has $ops "(")) push-pop-rm $a3))
          ($a5 (census:when (or (census:member "rep" $pfx)
                                (or (census:member "repz" $pfx)
                                    (or (census:member "repe" $pfx)
                                        (or (census:member "repnz" $pfx) (census:member "repne" $pfx)))))
                            string $a4))
          ($a6 (census:when (== $m "endbr64") endbr $a5))
          ($a7 (census:when (census:simd $m $ops) simd $a6))
          ($a8 (census:when (census:in $m ("lzcnt" "tzcnt" "popcnt" "bsf" "bsr")) bitscan $a7))
          ($a9 (census:when (census:in $m ("shlx" "shrx" "sarx" "rorx" "pdep" "pext" "mulx" "bzhi")) bmi2 $a8))
          ($a10 (census:when (census:in $m ("adcx" "adox")) adx $a9))
          ($a11 (census:when (census:in $m ("syscall" "int" "int3" "cpuid" "rdtsc" "rdtscp" "hlt" "ud2"))
                             privileged $a10)))
     (if (== $a11 ()) (base) $a11)))

; ---- counting, in spaces ------------------------------------------------------

(= (census:bump $space $key $w)
   (let $old (collapse (match $space (count $key $n) $n))
     (if (== $old ())
         (add-atom $space (count $key $w))
         (let ($n $rest) (decons-atom $old)
           (let* (($r (remove-atom $space (count $key $n)))
                  ($m (+ $n $w)))
             (add-atom $space (count $key $m)))))))

(= (census:bump-all $space $keys $w)
   (if (== $keys ()) ok
       (let ($k $rest) (decons-atom $keys)
         (let $u (census:bump $space $k $w) (census:bump-all $space $rest $w)))))

(= (census:tally $i $w $mn $cl)
   (let (insn $p $m $o) $i
     (let $u (census:bump $mn $m $w) (census:bump-all $cl (census:tags $p $m $o) $w))))

(= (census:count $lines $mn $cl $total)
   (if (== $lines ()) $total
       (let ($line $rest) (decons-atom $lines)
         (let $i (census:objdump-line $line)
           (if (== $i ())
               (census:count $rest $mn $cl $total)
               (let $u (census:tally $i 1 $mn $cl)
                 (census:count $rest $mn $cl (+ $total 1))))))))

(= (census:counts $space) (collapse (match $space (count $k $n) ($k $n))))
(= (census:keys $space) (sort (collapse (match $space (count $k $n) $k))))

; (census PATH (instructions N) (mnemonics (M ...)) (classes ((CLASS N) ...)))
(= (census:target $path)
   (let* (($out (if (str:ends-with $path ".hol") (census:disasm-image $path) (census:disasm-elf $path)))
          ($mn (new-space))
          ($cl (new-space))
          ($total (census:count (str:split "\n" $out) $mn $cl 0)))
     (census $path (instructions $total) (mnemonics (census:keys $mn)) (classes (sort (census:counts $cl))))))

; ---- the report -------------------------------------------------------------

; system:write, not fs:write on /dev/stdout: the latter truncates a stdout
; redirected to a file, losing the lines.
(= (census:say $text) (system:write stdout (str:concat $text "\n")))

(= (census:show-classes $classes)
   (if (== $classes ()) ""
       (let (($c $n) $rest) (decons-atom $classes)
         (str:concat (format-args " {} {}" ($c $n)) (census:show-classes $rest)))))

(= (census:say-target $c)
   (let (census $path (instructions $n) (mnemonics $ms) (classes $cs)) $c
     (census:say (format-args "{}: {} instructions, {} mnemonics;{}"
                              ($path $n (length $ms) (census:show-classes $cs))))))

(= (census:union $lists)
   (if (== $lists ()) ()
       (let ($l $rest) (decons-atom $lists)
         (unique-atom (append $l (census:union $rest))))))

(= (census:minus $xs $ys)
   (if (== $xs ()) ()
       (let ($x $rest) (decons-atom $xs)
         (if (census:member $x $ys) (census:minus $rest $ys) (cons-atom $x (census:minus $rest $ys))))))

(= (census:mnemonics-of $results $images)
   (if (== $results ()) ()
       (let ((census $path $n (mnemonics $ms) $cs) $rest) (decons-atom $results)
         (if (== (str:ends-with $path ".hol") $images)
             (cons-atom $ms (census:mnemonics-of $rest $images))
             (census:mnemonics-of $rest $images)))))

(= (census:say-all $results)
   (if (== $results ()) ok
       (let ($c $rest) (decons-atom $results)
         (let $u (census:say-target $c) (census:say-all $rest)))))

(= (census:report $targets)
   (let* (($results (map-atom $targets $t (census:target $t)))
          ($u (census:say-all $results))
          ($img (sort (census:union (census:mnemonics-of $results True))))
          ($elf (sort (census:union (census:mnemonics-of $results False))))
          ($only (census:minus $elf $img))
          ($v (census:say (format-args "images use {} mnemonics: {}" ((length $img) (str:join " " $img)))))
          ($w (census:say (format-args "binaries use {} mnemonics that no image uses: {}"
                                       ((length $only) (str:join " " $only))))))
     $results))

; ---- weighted by cycles -------------------------------------------------------
; perf annotate --stdio prints, per symbol, a header carrying that symbol's
; sample count, then "  PERCENT :   ADDRESS:   ASSEMBLY" for each instruction,
; with the percentage local to the symbol.

(= (census:header-samples $line)
   (if (census:has $line " samples, percent")
       (let $parts (str:split "(" $line)
         (let $last (index-atom $parts (- (length $parts) 1))
           (str:string->number (index-atom (str:split-whitespace $last) 0))))
       ()))

(= (census:annotated $line)
   (let $parts (str:split ":" $line)
     (if (< (length $parts) 3) ()
         (let ($p $r1) (decons-atom $parts)
           (let ($addr $r2) (decons-atom $r1)
             (let $pt (str:trim $p)
               (if (str:is-initial-in digit $pt)
                   (if (census:is-hex (str:trim $addr))
                       ((str:string->number $pt) (census:parse-asm (str:join ":" $r2)))
                       ())
                   ())))))))

(= (census:hot-lines $lines $weight $mn $cl $total)
   (if (== $lines ()) $total
       (let ($line $rest) (decons-atom $lines)
         (let $h (census:header-samples $line)
           (if (not (== $h ()))
               (census:hot-lines $rest $h $mn $cl (+ $total $h))
               (let $a (census:annotated $line)
                 (if (== $a ())
                     (census:hot-lines $rest $weight $mn $cl $total)
                     (let ($pct $i) $a
                       (if (or (== $i ()) (== $pct 0))
                           (census:hot-lines $rest $weight $mn $cl $total)
                           (let $u (census:tally $i (/ (* $pct $weight) 100.0) $mn $cl)
                             (census:hot-lines $rest $weight $mn $cl $total)))))))))))

(= (census:share $pairs $total)
   (map-atom $pairs $p (let ($k $n) $p ($k (/ (round-math (/ (* 1000.0 $n) $total)) 10.0)))))

; Heaviest first: msort orders (-weight key) pairs by weight and keeps ties.
(= (census:by-weight $pairs)
   (map-atom (msort (map-atom $pairs $p (let ($k $n) $p ((- 0 $n) $k))))
             $q (let ($m $k) $q ($k (- 0 $m)))))

(= (census:top $pairs $k)
   (if (or (== $k 0) (== $pairs ())) ()
       (let ($p $rest) (decons-atom $pairs) (cons-atom $p (census:top $rest (- $k 1))))))

; (census-hot BINARY (samples N) (class-percent ...) (top-mnemonic-percent ...))
(= (census:hot $binary $perfdata)
   (let* (($out (census:run ("perf" "annotate" "-i" $perfdata "--stdio") 600000))
          ($mn (new-space))
          ($cl (new-space))
          ($total (census:hot-lines (str:split "\n" $out) 0 $mn $cl 0))
          ($classes (census:share (census:counts $cl) $total))
          ($mnems (census:share (census:counts $mn) $total))
          ($top (census:top (census:by-weight $mnems) 20)))
     (census-hot $binary (samples $total) (class-percent (sort $classes)) (top-mnemonic-percent $top))))

; ---- XED mode ------------------------------------------------------------------
; Intel XED (github.com/intelxed/xed, its `xed` example tool) names each
; instruction exactly: its iclass, its iform (the iclass with its operand
; forms), its category, ISA extension and ISA set. The XED mode keeps
; objdump's instruction stream and asks xed about each distinct encoding
; once, with `xed -64 -cet -v 4 -isa-set -ih FILE`. For each instruction xed
; prints a header "ICLASS IFORM FIELD, FIELD, ..." (its decoder fields: EOSZ,
; VEXVALID, VL, REXW, MEM0, ...) and later "XDIS ADDRESS: CATEGORY EXTENSION
; ISA_SET HEX DISASSEMBLY". With -cet, F3 0F 1E FA is ENDBR64 (else a NOP).
; Every encoding must come back as exactly one XDIS line with the same bytes;
; the census reports any that do not.

(= (census:xed) (system:getenv-or-default "XED" "xed"))

; Written flat: the same six replacements as a recursion over a list of
; pairs cost sixteen times as much in CeTTa.
(= (census:upper-hex $s)
   (str:join "F" (str:split "f" (str:join "E" (str:split "e" (str:join "D" (str:split "d"
     (str:join "C" (str:split "c" (str:join "B" (str:split "b" (str:join "A" (str:split "a" $s)))))))))))))

; (entry HEX (insn PREFIXES MNEMONIC OPERANDS)) from an objdump line, HEX in
; xed's spelling (upper case, no spaces), or () when it is not an instruction.
(= (census:objdump-entry $line)
   (let $fields (str:split "\t" $line)
     (if (== (length $fields) 3)
         (let ($a $r1) (decons-atom $fields)
           (let ($hex $r2) (decons-atom $r1)
             (let ($asm $r3) (decons-atom $r2)
               (if (== $a "")
                   (let $i (census:parse-asm $asm)
                     (if (== $i ()) () (entry (census:upper-hex (str:join "" (str:split-whitespace $hex))) $i)))
                   ()))))
         ())))

; ---- the key s2n's allowlist is written in -----------------------------------
; IFORM|SHAPE|PREFIXES. SHAPE is oN, xed's effective operand size, for a
; legacy encoding (oNr2 after an APX REX2 prefix, D5), and vVlLwW (VEXVALID,
; VL, REXW) for VEX and EVEX. PREFIXES is the set of legacy prefix bytes
; before REX or VEX, in byte order, with ".dup" when a byte other than 66
; repeats, or "-". s2n's decoder sees prefixes only as that set (66 may
; repeat; any other repeat is rejected), so the key decides its verdict.

(= (census:legacy-prefixes) ("26" "2E" "36" "3E" "64" "65" "66" "67" "F0" "F2" "F3"))

(= (census:leading-prefixes $hex $i $acc)
   (if (> (+ $i 2) (str:byte-length $hex))
       ($acc $i)
       (let $b (str:byte-slice $hex $i (+ $i 2))
         (if (census:member $b (census:legacy-prefixes))
             (census:leading-prefixes $hex (+ $i 2) (cons-atom $b $acc))
             ($acc $i)))))

(= (census:repeats $bs)
   (if (== $bs ()) False
       (let ($b $rest) (decons-atom $bs)
         (if (== $b "66")
             (census:repeats $rest)
             (if (census:member $b $rest) True (census:repeats $rest))))))

(= (census:prefix-set $bs)
   (if (== $bs ()) "-"
       (let $set (str:join "." (sort (unique-atom $bs)))
         (if (census:repeats $bs) (str:concat $set ".dup") $set))))

(= (census:osize $e) (if (== $e "1") "16" (if (== $e "2") "32" (if (== $e "3") "64" "?"))))

(= (census:xed-key $iform $hex $eosz $vv $vl $w)
   (let ($bs $i) (census:leading-prefixes $hex 0 ())
     (let $rex2 (if (> (+ $i 2) (str:byte-length $hex)) False (== (str:byte-slice $hex $i (+ $i 2)) "D5"))
       (let $shape (if (== $vv "0")
                       (str:concat (str:concat "o" (census:osize $eosz)) (if $rex2 "r2" ""))
                       (format-args "v{}l{}w{}" ($vv $vl $w)))
         (str:join "|" ($iform $shape (census:prefix-set $bs)))))))

; ---- classes from xed's fields -------------------------------------------------
; The same classes as the mnemonic census, decided by xed: indirect branches
; are the iforms CALL_NEAR_GPRv/MEMv, JMP_GPRv/MEMv and the far forms, a jump
; table is JMP_MEMv through a scaled index; string operations are the
; REP_/REPE_/REPNE_ iclasses; SIMD is an iform with a vector or mask register
; operand (XMM, YMM, ZMM, MMX, MASK), or VZEROUPPER/VZEROALL; bit scans are
; BSF, BSR, LZCNT, TZCNT and POPCNT; BMI2 and ADX are xed's extensions.

(= (census:field $toks $name $default)
   (if (== $toks ()) $default
       (let ($t $rest) (decons-atom $toks)
         (if (str:starts-with $t $name)
             (census:strip-comma (str:byte-slice $t (str:byte-length $name) (str:byte-length $t)))
             (census:field $rest $name $default)))))

(= (census:strip-comma $s)
   (if (str:ends-with $s ",") (str:byte-slice $s 0 (- (str:byte-length $s) 1)) $s))

(= (census:flag $toks $name)
   (if (== $toks ()) "0"
       (let ($t $rest) (decons-atom $toks)
         (if (== (census:strip-comma $t) $name) "1" (census:flag $rest $name)))))

(= (census:vector-token $t)
   (if (str:starts-with $t "XMM") True
       (if (str:starts-with $t "YMM") True
           (if (str:starts-with $t "ZMM") True
               (if (str:starts-with $t "MMX") True (str:starts-with $t "MASK"))))))

(= (census:any-vector $toks)
   (if (== $toks ()) False
       (let ($t $rest) (decons-atom $toks)
         (if (census:vector-token $t) True (census:any-vector $rest)))))

(= (census:xed-simd $iclass $iform)
   (if (census:member $iclass ("VZEROUPPER" "VZEROALL"))
       True
       (let $n (str:byte-length $iclass)
         (if (> (str:byte-length $iform) (+ $n 1))
             (census:any-vector (str:split "_" (str:byte-slice $iform (+ $n 1) (str:byte-length $iform))))
             False))))

(= (census:rep-iclass $c)
   (if (str:starts-with $c "REP_") True
       (if (str:starts-with $c "REPE_") True (str:starts-with $c "REPNE_"))))

(= (census:xtags $iclass $iform $ext $hdr)
   (let* (($table (if (== $iform "JMP_MEMv") (census:has $hdr "*") False))
          ($ind (census:member $iform ("CALL_NEAR_GPRv" "CALL_NEAR_MEMv" "JMP_GPRv" "JMP_MEMv"
                                       "CALL_FAR_MEMp2" "JMP_FAR_MEMp2")))
          ($a1 (census:when (if $ind (not $table) False) indirect-branch ()))
          ($a2 (census:when $table jump-table $a1))
          ($a3 (census:when (census:member $iform ("PUSH_MEMv" "POP_MEMv")) push-pop-rm $a2))
          ($a4 (census:when (census:rep-iclass $iclass) string $a3))
          ($a5 (census:when (census:member $iclass ("ENDBR64" "ENDBR32")) endbr $a4))
          ($a6 (census:when (census:xed-simd $iclass $iform) simd $a5))
          ($a7 (census:when (census:member $iclass ("BSF" "BSR" "LZCNT" "TZCNT" "POPCNT")) bitscan $a6))
          ($a8 (census:when (== $ext "BMI2") bmi2 $a7))
          ($a9 (census:when (== $ext "ADOX_ADCX") adx $a8))
          ($a10 (census:when (census:member $iclass ("SYSCALL" "INT" "INT3" "CPUID" "RDTSC" "RDTSCP" "HLT" "UD2"))
                             privileged $a9)))
     (if (== $a10 ()) (base) $a10)))

; ---- asking xed ------------------------------------------------------------------
; (xrec HEX ICLASS IFORM CATEGORY EXTENSION ISA_SET KEY CLASSES) in space $xs
; for each encoding; returns (records N errors E).

(= (census:xed-decode $hexes $xs)
   (let* (($dir (str:trim (census:run ("mktemp" "-d") 10000)))
          ($file (str:concat $dir "/encodings.hex"))
          ($w (fs:write $file (str:concat (str:join "\n" $hexes) "\n")))
          ($out (census:run ((census:xed) "-64" "-cet" "-v" "4" "-isa-set" "-ih" $file) 600000))
          ($r1 (proc:run ("rm" "-f" $file) ((timeout-ms 10000))))
          ($r2 (proc:run ("rmdir" $dir) ((timeout-ms 10000)))))
     (census:xed-lines (str:split "\n" $out) $xs () 0 0)))

(= (census:xed-lines $lines $xs $hdr $n $errors)
   (if (== $lines ())
       (records $n errors $errors)
       (let ($line $rest) (decons-atom $lines)
         (if (str:starts-with $line "XDIS ")
             (let $u (census:xed-record $xs $hdr $line)
               (census:xed-lines $rest $xs $hdr (+ $n 1) $errors))
             (if (str:starts-with $line "ERROR")
                 (census:xed-lines $rest $xs $hdr $n (+ $errors 1))
                 (if (str:is-initial-in upper $line)
                     (let $toks (str:split-whitespace $line)
                       (if (census:xed-header $toks)
                           (census:xed-lines $rest $xs $toks $n $errors)
                           (census:xed-lines $rest $xs $hdr $n $errors)))
                     (census:xed-lines $rest $xs $hdr $n $errors)))))))

; A header's second word, the iform, begins with its first, the iclass.
(= (census:xed-header $toks)
   (if (< (length $toks) 2) False
       (let ($a $r) (decons-atom $toks)
         (let ($b $r2) (decons-atom $r) (str:starts-with $b $a)))))

(= (census:xed-record $xs $hdr $line)
   (let $t (str:split-whitespace $line)
     (if (< (length $t) 6) ()
         (if (== $hdr ()) ()
             (let* (($cat (index-atom $t 2)) ($ext (index-atom $t 3)) ($isa (index-atom $t 4))
                    ($hex (index-atom $t 5)) ($iclass (index-atom $hdr 0)) ($iform (index-atom $hdr 1))
                    ($key (census:xed-key $iform $hex (census:field $hdr "EOSZ:" "0")
                                          (census:field $hdr "VEXVALID:" "0") (census:field $hdr "VL:" "0")
                                          (census:flag $hdr "REXW")))
                    ($xt (census:xtags $iclass $iform $ext (str:join " " $hdr))))
               (add-atom $xs (xrec $hex $iclass $iform $cat $ext $isa $key $xt)))))))

(= (census:dedupe-sorted $xs $prev $acc)
   (if (== $xs ()) $acc
       (let ($x $rest) (decons-atom $xs)
         (if (== $x $prev)
             (census:dedupe-sorted $rest $prev $acc)
             (census:dedupe-sorted $rest $x (cons-atom $x $acc))))))

; ---- grouping and tallying ---------------------------------------------------------
; Instructions are grouped as (count (g HEX MNEMONIC MNEMONIC-CLASSES) WEIGHT):
; a static census weighs each instruction 1, the hot census by its cycles.
; The tally looks each group up in xed's records and counts, by weight:
;   (ext E) (isa S) (cat C) (iclass I) (iform F) (xclass K) (s2n allowed|outside)
;   (diff CLASS IN-MNEMONIC IN-XED) for the classes the two modes share
;   (dis CLASS MNEMONIC IFORM mnemonic-only|xed-only) for each disagreement
;   (oform F) for an instruction outside s2n's allowlist
;   (missing) for a group xed gave no record for.

(= (census:shared-classes) (simd bmi2 bitscan string indirect))

(= (census:in-class $c $tags)
   (if (== $c indirect)
       (if (census:member indirect-branch $tags) True (census:member jump-table $tags))
       (census:member $c $tags)))

(= (census:group-lines $lines $gs $n)
   (if (== $lines ()) $n
       (let ($line $rest) (decons-atom $lines)
         (let $e (census:objdump-entry $line)
           (if (== $e ())
               (census:group-lines $rest $gs $n)
               (let (entry $hex (insn $p $m $o)) $e
                 (let $u (census:bump $gs (g $hex $m (census:tags $p $m $o)) 1)
                   (census:group-lines $rest $gs (+ $n 1)))))))))

(= (census:groups $gs) (collapse (match $gs (count (g $h $m $t) $w) (grp $h $m $t $w))))

(= (census:group-hexes $groups)
   (census:dedupe-sorted (sort (map-atom $groups $q (let (grp $h $m $t $w) $q $h))) "" ()))

(= (census:diff-one $cs $mt $xt $m $iform $w $c)
   (if (== $cs ()) ok
       (let ($k $rest) (decons-atom $cs)
         (let* (($a (census:in-class $k $mt))
                ($b (census:in-class $k $xt))
                ($u (census:bump $c (diff $k $a $b) $w))
                ($v (if (== $a $b) ok
                        (census:bump $c (dis $k $m $iform (if $a mnemonic-only xed-only)) $w))))
           (census:diff-one $rest $mt $xt $m $iform $w $c)))))

; Each group adds its weight to one composite key (rec ICLASS IFORM CATEGORY
; EXTENSION ISA_SET IN-ALLOWLIST MNEMONIC-CLASSES XED-CLASSES MNEMONIC); the
; few hundred distinct composites are then spread over the counters above.
(= (census:tally-groups $groups $xs $allow $c)
   (let* (($r (new-space))
          ($u (census:composites $groups $xs $allow $r $c)))
     (census:expand-composites (collapse (match $r (count $k $n) ($k $n))) $c)))

(= (census:composites $groups $xs $allow $r $c)
   (if (== $groups ()) ok
       (let ($q $rest) (decons-atom $groups)
         (let (grp $h $m $mt $w) $q
           (let $x (collapse (match $xs (xrec $h $ic $if $cat $ext $isa $key $xt) ($ic $if $cat $ext $isa $key $xt)))
             (if (== $x ())
                 (let $u (census:bump $c (missing) $w) (census:composites $rest $xs $allow $r $c))
                 (let (($ic $if $cat $ext $isa $key $xt) $more) (decons-atom $x)
                   (let $u (census:bump $r (rec $ic $if $cat $ext $isa (str:is-set-member $allow $key) $mt $xt $m) $w)
                     (census:composites $rest $xs $allow $r $c)))))))))

(= (census:expand-composites $items $c)
   (if (== $items ()) ok
       (let (((rec $ic $if $cat $ext $isa $in $mt $xt $m) $w) $rest) (decons-atom $items)
         (let* (($u1 (census:bump-all $c ((ext $ext) (isa $isa) (cat $cat) (iclass $ic) (iform $if)) $w))
                ($u2 (census:bump-all $c (map-atom $xt $k (xclass $k)) $w))
                ($u3 (census:bump $c (s2n (if $in allowed outside)) $w))
                ($u5 (if $in ok (census:bump $c (oform $if) $w)))
                ($u4 (census:diff-one (census:shared-classes) $mt $xt $m $if $w $c)))
           (census:expand-composites $rest $c)))))

(= (census:pick $c $pattern) (collapse (match $c (count $pattern $n) $n)))

(= (census:sum $xs) (if (== $xs ()) 0 (let ($x $rest) (decons-atom $xs) (+ $x (census:sum $rest)))))

(= (census:tagged $c $tag) (collapse (match $c (count ($tag $k) $n) ($k $n))))

(= (census:differential $c)
   (map-atom (census:shared-classes) $k
     (let* (($tt (census:sum (census:pick $c (diff $k True True))))
            ($tf (census:sum (census:pick $c (diff $k True False))))
            ($ft (census:sum (census:pick $c (diff $k False True)))))
       ($k (mnemonic (+ $tt $tf)) (xed (+ $tt $ft)) (agree $tt)))))

(= (census:disagreements $c)
   (collapse (match $c (count (dis $k $m $if $side) $n) ($k $m $if $side $n))))

; The allowlist's keys as a string set. s2n_allowlist.metta defines
; (census:s2n-allowlist-source); without it (a failed import is silent) the
; set is an error, never an empty allowlist.
(= (census:allowlist-loaded)
   (== (index-atom (census:s2n-allowlist-source) 0) s2n-bignum))

(= (census:allow-set)
   (if (census:allowlist-loaded)
       (str:set (census:s2n-allowed-keys))
       (Error (census:s2n-allowlist-source) "s2n_allowlist.metta is not loaded")))

; XED's view of a group space: decode, tally, and the summary terms.
(= (census:xed-view $gs)
   (let* (($groups (census:groups $gs))
          ($hexes (census:group-hexes $groups))
          ($xs (new-space))
          ((records $nrec errors $nerr) (census:xed-decode $hexes $xs))
          ($c (new-space))
          ($allow (census:allow-set))
          ($u (census:tally-groups $groups $xs $allow $c)))
     (xed-view (encodings (length $hexes)) (xed-records $nrec) (xed-errors $nerr)
               (missing (census:sum (census:pick $c (missing))))
               $c)))

; (census-xed PATH (instructions N) (encodings D) (xed-records R) (xed-errors E)
;   (missing M) (iclasses K) (iforms F) (extensions ...) (isa-sets ...)
;   (categories ...) (classes ...) (s2n ...) (s2n-outside-iforms ...)
;   (differential ...) (disagreements ...))
(= (census:xed-target $path)
   (let* (($out (if (str:ends-with $path ".hol") (census:disasm-image $path) (census:disasm-elf $path)))
          ($gs (new-space))
          ($total (census:group-lines (str:split "\n" $out) $gs 0))
          ((xed-view $e $r $x $m $c) (census:xed-view $gs)))
     (census-xed $path (instructions $total) $e $r $x $m
                 (iclasses (length (census:tagged $c iclass))) (iforms (length (census:tagged $c iform)))
                 (extensions (census:by-weight (census:tagged $c ext)))
                 (isa-sets (census:by-weight (census:tagged $c isa)))
                 (categories (census:by-weight (census:tagged $c cat)))
                 (classes (sort (census:tagged $c xclass)))
                 (s2n (sort (census:tagged $c s2n)))
                 (s2n-outside-iforms (census:top (census:by-weight (census:tagged $c oform)) 15))
                 (differential (census:differential $c))
                 (disagreements (census:disagreements $c)))))

; ---- the XED report ---------------------------------------------------------------

(= (census:pairs-text $pairs)
   (if (== $pairs ()) ""
       (let (($k $n) $rest) (decons-atom $pairs)
         (str:concat (format-args " {} {}" ($k $n)) (census:pairs-text $rest)))))

(= (census:diff-text $rows)
   (if (== $rows ()) ""
       (let (($k (mnemonic $m) (xed $x) (agree $a)) $rest) (decons-atom $rows)
         (str:concat (format-args " {} {}/{}/{}" ($k $m $x $a)) (census:diff-text $rest)))))

(= (census:say-dis $rows)
   (if (== $rows ()) ok
       (let ($r $rest) (decons-atom $rows)
         (let $u (census:say (format-args "    disagreement: {}" ($r))) (census:say-dis $rest)))))

(= (census:say-xed $c)
   (let (census-xed $path (instructions $n) (encodings $d) (xed-records $r) (xed-errors $e) (missing $m)
                    (iclasses $ki) (iforms $kf) (extensions $exts) (isa-sets $isas) (categories $cats)
                    (classes $cls) (s2n $s2n) (s2n-outside-iforms $outs) (differential $diff)
                    (disagreements $dis)) $c
     (let* (($u1 (census:say (format-args "{}: {} instructions, {} encodings (xed: {} records, {} errors, {} missing), {} iclasses, {} iforms"
                                          ($path $n $d $r $e $m $ki $kf))))
            ($u2 (census:say (str:concat "  extensions:" (census:pairs-text $exts))))
            ($u3 (census:say (str:concat "  classes:" (census:pairs-text $cls))))
            ($u4 (census:say (str:concat (str:concat "  s2n forms:" (census:pairs-text $s2n))
                                         (if (== $outs ()) "" (str:concat "; outside by iform:" (census:pairs-text $outs))))))
            ($u5 (census:say (str:concat "  differential (class mnemonic/xed/both):" (census:diff-text $diff)))))
       (census:say-dis $dis))))

(= (census:say-xed-all $results)
   (if (== $results ()) ok
       (let ($c $rest) (decons-atom $results)
         (let $u (census:say-xed $c) (census:say-xed-all $rest)))))

(= (census:xed-report $targets)
   (let* (($results (map-atom $targets $t (census:xed-target $t)))
          ($u (census:say-xed-all $results)))
     $results))

; ---- XED mode weighted by cycles ------------------------------------------------
; `perf annotate --asm-raw` prints an instruction's bytes before its assembly;
; an instruction longer than perf's byte column continues on the next lines,
; which carry bytes only (with their own address and 0.00). Those bytes join
; the pending instruction, so each sample is classified by its full encoding.

(= (census:byte-token $t) (if (== (str:byte-length $t) 2) (census:is-hex $t) False))

(= (census:reverse $xs $acc)
   (if (== $xs ()) $acc (let ($x $rest) (decons-atom $xs) (census:reverse $rest (cons-atom $x $acc)))))

; (BYTES ASSEMBLY-TOKENS) from the tokens after the address.
(= (census:raw-split $toks $bytes)
   (if (== $toks ()) ((census:reverse $bytes ()) ())
       (let ($t $rest) (decons-atom $toks)
         (if (census:byte-token $t)
             (census:raw-split $rest (cons-atom $t $bytes))
             ((census:reverse $bytes ()) $toks)))))

; (PERCENT BYTES ASSEMBLY-TOKENS) from "PERCENT : ADDRESS: BYTES ASSEMBLY", or ().
(= (census:raw-annotated $line)
   (let $parts (str:split ":" $line)
     (if (< (length $parts) 3) ()
         (let ($p $r1) (decons-atom $parts)
           (let ($addr $r2) (decons-atom $r1)
             (let $pt (str:trim $p)
               (if (str:is-initial-in digit $pt)
                   (if (census:is-hex (str:trim $addr))
                       (let ($bs $asm) (census:raw-split (str:split-whitespace (str:join ":" $r2)) ())
                         ((str:string->number $pt) $bs $asm))
                       ())
                   ())))))))

(= (census:xhot-flush $pending $gs)
   (if (== $pending ()) ok
       (let (pend $w $bs $asm) $pending
         (if (== $w 0) ok
             (if (== $bs ()) ok
                 (let $i (census:parse-asm (str:join " " $asm))
                   (if (== $i ()) ok
                       (let (insn $p $m $o) $i
                         (census:bump $gs (g (census:upper-hex (str:join "" $bs)) $m (census:tags $p $m $o)) $w)))))))))

(= (census:extend $pending $bs)
   (if (== $pending ()) ()
       (let (pend $w $old $asm) $pending (pend $w (append $old $bs) $asm))))

(= (census:xhot-lines $lines $weight $pending $gs $total)
   (if (== $lines ())
       (let $u (census:xhot-flush $pending $gs) $total)
       (let ($line $rest) (decons-atom $lines)
         (let $h (census:header-samples $line)
           (if (not (== $h ()))
               (let $u (census:xhot-flush $pending $gs)
                 (census:xhot-lines $rest $h () $gs (+ $total $h)))
               (let $a (census:raw-annotated $line)
                 (if (== $a ())
                     (census:xhot-lines $rest $weight $pending $gs $total)
                     (let ($pct $bs $asm) $a
                       (if (== $asm ())
                           (census:xhot-lines $rest $weight (census:extend $pending $bs) $gs $total)
                           (let $u (census:xhot-flush $pending $gs)
                             (census:xhot-lines $rest $weight (pend (/ (* $pct $weight) 100.0) $bs $asm)
                                                $gs $total)))))))))))

(= (census:diff-share $rows $total)
   (map-atom $rows $r
     (let ($k (mnemonic $m) (xed $x) (agree $a)) $r
       ($k (mnemonic (/ (round-math (/ (* 1000.0 $m) $total)) 10.0))
           (xed (/ (round-math (/ (* 1000.0 $x) $total)) 10.0))
           (agree (/ (round-math (/ (* 1000.0 $a) $total)) 10.0))))))

; (census-xed-hot BINARY (samples N) (encodings D) (xed-records R) (xed-errors E)
;   (missing-percent M) (class-percent ...) (extension-percent ...)
;   (category-percent ...) (top-iclass-percent ...) (s2n-percent ...)
;   (s2n-outside-iform-percent ...) (differential-percent ...) (disagreements ...))
(= (census:xed-hot $binary $perfdata)
   (let* (($out (census:run ("perf" "annotate" "-i" $perfdata "--stdio" "--asm-raw") 600000))
          ($gs (new-space))
          ($total (census:xhot-lines (str:split "\n" $out) 0 () $gs 0))
          ((xed-view $e $r $x (missing $m) $c) (census:xed-view $gs)))
     (census-xed-hot $binary (samples $total) $e $r $x
                     (missing-percent (/ (round-math (/ (* 1000.0 $m) $total)) 10.0))
                     (class-percent (sort (census:share (census:tagged $c xclass) $total)))
                     (extension-percent (census:by-weight (census:share (census:tagged $c ext) $total)))
                     (category-percent (census:top (census:by-weight (census:share (census:tagged $c cat) $total)) 12))
                     (top-iclass-percent (census:top (census:by-weight (census:share (census:tagged $c iclass) $total)) 20))
                     (s2n-percent (sort (census:share (census:tagged $c s2n) $total)))
                     (s2n-outside-iform-percent
                       (census:top (census:by-weight (census:share (census:tagged $c oform) $total)) 15))
                     (differential-percent (census:diff-share (census:differential $c) $total))
                     (disagreements (census:disagreements $c)))))

; ---- the s2n gate ----------------------------------------------------------------
; (census-gate TARGET (instructions N) (encodings D) (xed-records R)
;   (xed-errors E) (outside ((outside ADDRESS HEX KEY STATUS REASON) ...)))
; lists, in address order, every instruction whose form (census:xed-key) is
; not in s2n_allowlist.metta: forms s2n's decoder rejects, decodes only with
; a caveat (LZCNT, TZCNT, F2 A4), or that the coverage table never saw. An
; image's addresses are offsets into its bytes. An empty outside list with
; R = D and E = 0 is a pass; anything else is a failure, and so is an Error.

(= (census:disasm-addressed $path)
   (if (str:ends-with $path ".hol")
       (let* (($hex (census:longest-hex (str:split "\"" (fs:read-text $path)) ""))
              ($dir (str:trim (census:run ("mktemp" "-d") 10000)))
              ($bin (str:concat $dir "/image.bin"))
              ($w (census:stdout (proc:run ("xxd" "-r" "-p" "-" $bin) ((stdin $hex) (timeout-ms 10000)))))
              ($out (census:run ("objdump" "-D" "-w" "-b" "binary" "-m" "i386:x86-64" "-M" "att" $bin) 60000))
              ($r1 (proc:run ("rm" "-f" $bin) ((timeout-ms 10000))))
              ($r2 (proc:run ("rmdir" $dir) ((timeout-ms 10000)))))
         $out)
       (census:run ("objdump" "-d" "-w" "-M" "att" $path) 120000)))

; (at ADDRESS HEX) from "ADDRESS:\tHEX BYTES \tASSEMBLY", or (). Bytes that
; objdump calls "(bad)" are kept: xed then fails on them, and the gate says so.
(= (census:addressed-entry $line)
   (let $fields (str:split "\t" $line)
     (if (== (length $fields) 3)
         (let ($a $r1) (decons-atom $fields)
           (let ($hex $r2) (decons-atom $r1)
             (let $addr (str:trim $a)
               (if (str:ends-with $addr ":")
                   (at (str:byte-slice $addr 0 (- (str:byte-length $addr) 1))
                       (census:upper-hex (str:join "" (str:split-whitespace $hex))))
                   ()))))
         ())))

(= (census:addressed-entries $lines $acc)
   (if (== $lines ()) $acc
       (let ($line $rest) (decons-atom $lines)
         (let $e (census:addressed-entry $line)
           (if (== $e ())
               (census:addressed-entries $rest $acc)
               (census:addressed-entries $rest (cons-atom $e $acc)))))))

; Why a key is outside: its row in s2n_allowlist.metta, else what s2n's
; read_prefixes does with its prefix set before it looks at the opcode.
(= (census:why $key)
   (let $r (collapse (match &self (census:s2n-known $key $st $why) ($st $why)))
     (if (== $r ())
         (let $pfx (index-atom (str:split "|" $key) 2)
           (if (census:member "64" (str:split "." $pfx)) (rejected "FS segment prefix (decode.ml:91)")
               (if (census:member "65" (str:split "." $pfx)) (rejected "GS segment prefix (decode.ml:92)")
                   (if (census:member "F0" (str:split "." $pfx)) (rejected "LOCK prefix (decode.ml:90)")
                       (if (census:member "67" (str:split "." $pfx)) (rejected "address-size prefix (decode.ml:93)")
                           (if (census:has $pfx ".dup") (rejected "repeated prefix (decode.ml:50-74)")
                               (not-in-table "no row for this form in the coverage table")))))))
         (let ($first $more) (decons-atom $r) $first))))

; Entries come reversed; consing while walking restores address order.
(= (census:gate-check $entries $xs $allow $acc)
   (if (== $entries ()) $acc
       (let ($e $rest) (decons-atom $entries)
         (let (at $addr $hex) $e
           (let $r (collapse (match $xs (xrec $hex $ic $if $cat $ext $isa $key $xt) $key))
             (if (== $r ())
                 (census:gate-check $rest $xs $allow
                                    (cons-atom (outside $addr $hex "-" xed-missing "xed gave no record") $acc))
                 (let ($key $more) (decons-atom $r)
                   (if (str:is-set-member $allow $key)
                       (census:gate-check $rest $xs $allow $acc)
                       (let ($st $why) (census:why $key)
                         (census:gate-check $rest $xs $allow
                                            (cons-atom (outside $addr $hex $key $st $why) $acc)))))))))))

(= (census:gate $path)
   (if (not (census:allowlist-loaded))
       (Error (census:gate $path) "s2n_allowlist.metta is not loaded")
       (let* (($entries (census:addressed-entries (str:split "\n" (census:disasm-addressed $path)) ()))
              ($hexes (census:dedupe-sorted (sort (map-atom $entries $e (let (at $a $h) $e $h))) "" ()))
              ($xs (new-space))
              ((records $nrec errors $nerr) (census:xed-decode $hexes $xs))
              ($allow (census:allow-set)))
         (census-gate $path (instructions (length $entries)) (encodings (length $hexes))
                      (xed-records $nrec) (xed-errors $nerr)
                      (outside (census:gate-check $entries $xs $allow ()))))))

; A pass: a census-gate term whose outside list is empty, with one xed record
; per encoding and no xed errors. An Error is not a pass.
(= (census:gate-passed $g)
   (if (== (index-atom $g 0) census-gate)
       (let (census-gate $path (instructions $n) (encodings $d) (xed-records $r) (xed-errors $e) (outside $o)) $g
         (if (== $o ()) (if (== $r $d) (== $e 0) False) False))
       False))

(= (census:say-outside $os)
   (if (== $os ()) ok
       (let ($o $rest) (decons-atom $os)
         (let $u (census:say (format-args "  outside: {}" ($o))) (census:say-outside $rest)))))

; For evidence scripts: one verdict line (and the outside instructions), then
; exit status 0 for a pass and 1 for anything else.
(= (census:gate-exit $path)
   (let $g (census:gate $path)
     (if (census:gate-passed $g)
         (let (census-gate $p (instructions $n) $d $r $e $o) $g
           (let $u (census:say (format-args "gate pass {}: {} instructions, every form in s2n_allowlist.metta" ($path $n)))
             (system:exit 0)))
         (let* (($u (census:say (format-args "gate FAIL {}: {}" ($path (if (== (index-atom $g 0) census-gate) "instructions outside the allowlist, or xed did not decode every encoding" $g)))))
                ($v (if (== (index-atom $g 0) census-gate)
                        (let (census-gate $p $n $d $r $e (outside $os)) $g
                          (let $w (census:say (format-args "  {} {} {}" ($d $r $e))) (census:say-outside $os)))
                        ok)))
           (system:exit 1)))))
