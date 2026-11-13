; test_tisa_metta.metta -- tisa_x86.metta against tisa_x86.c, bytes and spans.
;
;   cetta --no-results test_tisa_metta.metta CORPUS EXPECTED [SHARD COUNT]
;
; CORPUS holds one (tisa-case "ID" (TProg ...)) per line. EXPECTED holds the C
; emitter's image of each program, one line per program in the same order:
;   ID HEX OFFSET:LENGTH:TEMPLATE ...
; The programs whose line index is SHARD modulo COUNT (default: all of them)
; are emitted by tisa_x86.metta and compared with the C image. Each mismatch
; prints a MISMATCH line with the program ID and the first differing byte
; offset and span; the last line is
;   RESULT checked=N identical=M mismatched=K ms=T

!(import! &self str)
!(import! &self fs)
!(import! &self system)
!(import! &self "tisa_x86.metta")

; ---- Image text, as the C test prints it --------------------------------------

(= (hex8 0) "00") (= (hex8 1) "01") (= (hex8 2) "02") (= (hex8 3) "03") (= (hex8 4) "04") (= (hex8 5) "05") (= (hex8 6) "06") (= (hex8 7) "07") (= (hex8 8) "08") (= (hex8 9) "09") (= (hex8 10) "0a") (= (hex8 11) "0b") (= (hex8 12) "0c") (= (hex8 13) "0d") (= (hex8 14) "0e") (= (hex8 15) "0f")
(= (hex8 16) "10") (= (hex8 17) "11") (= (hex8 18) "12") (= (hex8 19) "13") (= (hex8 20) "14") (= (hex8 21) "15") (= (hex8 22) "16") (= (hex8 23) "17") (= (hex8 24) "18") (= (hex8 25) "19") (= (hex8 26) "1a") (= (hex8 27) "1b") (= (hex8 28) "1c") (= (hex8 29) "1d") (= (hex8 30) "1e") (= (hex8 31) "1f")
(= (hex8 32) "20") (= (hex8 33) "21") (= (hex8 34) "22") (= (hex8 35) "23") (= (hex8 36) "24") (= (hex8 37) "25") (= (hex8 38) "26") (= (hex8 39) "27") (= (hex8 40) "28") (= (hex8 41) "29") (= (hex8 42) "2a") (= (hex8 43) "2b") (= (hex8 44) "2c") (= (hex8 45) "2d") (= (hex8 46) "2e") (= (hex8 47) "2f")
(= (hex8 48) "30") (= (hex8 49) "31") (= (hex8 50) "32") (= (hex8 51) "33") (= (hex8 52) "34") (= (hex8 53) "35") (= (hex8 54) "36") (= (hex8 55) "37") (= (hex8 56) "38") (= (hex8 57) "39") (= (hex8 58) "3a") (= (hex8 59) "3b") (= (hex8 60) "3c") (= (hex8 61) "3d") (= (hex8 62) "3e") (= (hex8 63) "3f")
(= (hex8 64) "40") (= (hex8 65) "41") (= (hex8 66) "42") (= (hex8 67) "43") (= (hex8 68) "44") (= (hex8 69) "45") (= (hex8 70) "46") (= (hex8 71) "47") (= (hex8 72) "48") (= (hex8 73) "49") (= (hex8 74) "4a") (= (hex8 75) "4b") (= (hex8 76) "4c") (= (hex8 77) "4d") (= (hex8 78) "4e") (= (hex8 79) "4f")
(= (hex8 80) "50") (= (hex8 81) "51") (= (hex8 82) "52") (= (hex8 83) "53") (= (hex8 84) "54") (= (hex8 85) "55") (= (hex8 86) "56") (= (hex8 87) "57") (= (hex8 88) "58") (= (hex8 89) "59") (= (hex8 90) "5a") (= (hex8 91) "5b") (= (hex8 92) "5c") (= (hex8 93) "5d") (= (hex8 94) "5e") (= (hex8 95) "5f")
(= (hex8 96) "60") (= (hex8 97) "61") (= (hex8 98) "62") (= (hex8 99) "63") (= (hex8 100) "64") (= (hex8 101) "65") (= (hex8 102) "66") (= (hex8 103) "67") (= (hex8 104) "68") (= (hex8 105) "69") (= (hex8 106) "6a") (= (hex8 107) "6b") (= (hex8 108) "6c") (= (hex8 109) "6d") (= (hex8 110) "6e") (= (hex8 111) "6f")
(= (hex8 112) "70") (= (hex8 113) "71") (= (hex8 114) "72") (= (hex8 115) "73") (= (hex8 116) "74") (= (hex8 117) "75") (= (hex8 118) "76") (= (hex8 119) "77") (= (hex8 120) "78") (= (hex8 121) "79") (= (hex8 122) "7a") (= (hex8 123) "7b") (= (hex8 124) "7c") (= (hex8 125) "7d") (= (hex8 126) "7e") (= (hex8 127) "7f")
(= (hex8 128) "80") (= (hex8 129) "81") (= (hex8 130) "82") (= (hex8 131) "83") (= (hex8 132) "84") (= (hex8 133) "85") (= (hex8 134) "86") (= (hex8 135) "87") (= (hex8 136) "88") (= (hex8 137) "89") (= (hex8 138) "8a") (= (hex8 139) "8b") (= (hex8 140) "8c") (= (hex8 141) "8d") (= (hex8 142) "8e") (= (hex8 143) "8f")
(= (hex8 144) "90") (= (hex8 145) "91") (= (hex8 146) "92") (= (hex8 147) "93") (= (hex8 148) "94") (= (hex8 149) "95") (= (hex8 150) "96") (= (hex8 151) "97") (= (hex8 152) "98") (= (hex8 153) "99") (= (hex8 154) "9a") (= (hex8 155) "9b") (= (hex8 156) "9c") (= (hex8 157) "9d") (= (hex8 158) "9e") (= (hex8 159) "9f")
(= (hex8 160) "a0") (= (hex8 161) "a1") (= (hex8 162) "a2") (= (hex8 163) "a3") (= (hex8 164) "a4") (= (hex8 165) "a5") (= (hex8 166) "a6") (= (hex8 167) "a7") (= (hex8 168) "a8") (= (hex8 169) "a9") (= (hex8 170) "aa") (= (hex8 171) "ab") (= (hex8 172) "ac") (= (hex8 173) "ad") (= (hex8 174) "ae") (= (hex8 175) "af")
(= (hex8 176) "b0") (= (hex8 177) "b1") (= (hex8 178) "b2") (= (hex8 179) "b3") (= (hex8 180) "b4") (= (hex8 181) "b5") (= (hex8 182) "b6") (= (hex8 183) "b7") (= (hex8 184) "b8") (= (hex8 185) "b9") (= (hex8 186) "ba") (= (hex8 187) "bb") (= (hex8 188) "bc") (= (hex8 189) "bd") (= (hex8 190) "be") (= (hex8 191) "bf")
(= (hex8 192) "c0") (= (hex8 193) "c1") (= (hex8 194) "c2") (= (hex8 195) "c3") (= (hex8 196) "c4") (= (hex8 197) "c5") (= (hex8 198) "c6") (= (hex8 199) "c7") (= (hex8 200) "c8") (= (hex8 201) "c9") (= (hex8 202) "ca") (= (hex8 203) "cb") (= (hex8 204) "cc") (= (hex8 205) "cd") (= (hex8 206) "ce") (= (hex8 207) "cf")
(= (hex8 208) "d0") (= (hex8 209) "d1") (= (hex8 210) "d2") (= (hex8 211) "d3") (= (hex8 212) "d4") (= (hex8 213) "d5") (= (hex8 214) "d6") (= (hex8 215) "d7") (= (hex8 216) "d8") (= (hex8 217) "d9") (= (hex8 218) "da") (= (hex8 219) "db") (= (hex8 220) "dc") (= (hex8 221) "dd") (= (hex8 222) "de") (= (hex8 223) "df")
(= (hex8 224) "e0") (= (hex8 225) "e1") (= (hex8 226) "e2") (= (hex8 227) "e3") (= (hex8 228) "e4") (= (hex8 229) "e5") (= (hex8 230) "e6") (= (hex8 231) "e7") (= (hex8 232) "e8") (= (hex8 233) "e9") (= (hex8 234) "ea") (= (hex8 235) "eb") (= (hex8 236) "ec") (= (hex8 237) "ed") (= (hex8 238) "ee") (= (hex8 239) "ef")
(= (hex8 240) "f0") (= (hex8 241) "f1") (= (hex8 242) "f2") (= (hex8 243) "f3") (= (hex8 244) "f4") (= (hex8 245) "f5") (= (hex8 246) "f6") (= (hex8 247) "f7") (= (hex8 248) "f8") (= (hex8 249) "f9") (= (hex8 250) "fa") (= (hex8 251) "fb") (= (hex8 252) "fc") (= (hex8 253) "fd") (= (hex8 254) "fe") (= (hex8 255) "ff")

(= (image-hex $bytes) (str:join "" (map-atom $bytes $b (hex8 $b))))

(= (span-text (SpanAt $off $len $name $source $code))
   (str:join ":" ((str:number->string $off) (str:number->string $len) (str:symbol->string $name))))

; ---- Comparing one program --------------------------------------------------

(= (say $text) (system:write stdout (str:concat $text "\n")))

; The index of the first differing element of two lists, or none.
(= (first-difference $xs $ys $i)
   (if (or (== $xs ()) (== $ys ()))
       (if (== $xs $ys) none $i)
       (let* ((($x $xs-rest) (decons-atom $xs))
              (($y $ys-rest) (decons-atom $ys)))
         (if (== $x $y) (first-difference $xs-rest $ys-rest (+ $i 1)) $i))))

; Byte k of a hex image, or "end" past its last byte.
(= (hex-byte-at $hex $k)
   (if (<= (* 2 (+ $k 1)) (str:byte-length $hex))
       (str:byte-slice $hex (* 2 $k) (* 2 (+ $k 1)))
       "end"))
; The first byte offset at which two hex images differ, or none.
(= (first-byte-difference $hex $want-hex $k)
   (let* (($got (hex-byte-at $hex $k))
          ($want (hex-byte-at $want-hex $k)))
     (if (== $got $want)
         (if (== $got "end") none (first-byte-difference $hex $want-hex (+ $k 1)))
         $k)))

(= (half $i) (/ (- $i (% $i 2)) 2))
(= (token-at $tokens $k)
   (if (< $k (length $tokens)) (index-atom $tokens $k) "none"))

(= (bytes-note $hex $want-hex)
   (let $k (first-byte-difference $hex $want-hex 0)
     (if (== $k none)
         "bytes identical;"
         (str:join "" ("bytes differ from offset " (str:number->string $k)
                       " (C " (hex-byte-at $want-hex $k) ", MeTTa " (hex-byte-at $hex $k)
                       "; length C " (str:number->string (half (str:byte-length $want-hex)))
                       ", MeTTa " (str:number->string (half (str:byte-length $hex))) ");")))))

(= (spans-note $tokens $want-tokens)
   (let $k (first-difference $tokens $want-tokens 0)
     (if (== $k none)
         "spans identical"
         (str:join "" ("spans differ from span " (str:number->string $k)
                       " (C " (token-at $want-tokens $k) ", MeTTa " (token-at $tokens $k) ")")))))

(= (check-program $line $want)
   (let* (((tisa-case $id $program) (parse $line))
          ((Image $bytes $spans $labels) (tisa-x86:emit $program))
          ($hex (image-hex $bytes))
          ($tokens (map-atom $spans $s (span-text $s)))
          (($want-id $want-rest) (decons-atom (str:split-whitespace $want)))
          (($want-hex $want-tokens) (decons-atom $want-rest)))
     (if (!= $id $want-id)
         (stop (str:join " " ("program" $id "is paired with the expected line of" $want-id)))
         (if (and (== $hex $want-hex) (== $tokens $want-tokens))
             Identical
             (let $shown (say (str:join " " ("MISMATCH" $id (bytes-note $hex $want-hex)
                                             (spans-note $tokens $want-tokens))))
               Mismatched)))))

; ---- The run ------------------------------------------------------------------

(= (stop $why)
   (let $shown (system:write stderr (str:concat "test_tisa_metta.metta: " (str:concat $why "\n")))
     (system:exit 2)))

(= (tally (Tally $c $i $m) Identical) (Tally (+ $c 1) (+ $i 1) $m))
(= (tally (Tally $c $i $m) Mismatched) (Tally (+ $c 1) $i (+ $m 1)))

; One verdict per program: a check that yields no verdict, or several, is
; reported and counted as a mismatch, never dropped.
(= (verdict $index $case $want)
   (let $verdicts (collapse (check-program $case $want))
     (if (== (length $verdicts) 1)
         (car-atom $verdicts)
         (let $shown (say (str:join " " ("MISMATCH" (str:concat "line " (str:number->string (+ $index 1)))
                                         "the check gave" (str:number->string (length $verdicts))
                                         "verdicts instead of one")))
           Mismatched))))

(= (check-lines $cases $wants $index $shard $count $sum)
   (if (or (== $cases ()) (== $wants ()))
       (if (== $cases $wants) $sum (stop "CORPUS and EXPECTED differ in their number of lines"))
       (let* ((($case $more-cases) (decons-atom $cases))
              (($want $more-wants) (decons-atom $wants)))
         (if (== (% $index $count) $shard)
             (check-lines $more-cases $more-wants (+ $index 1) $shard $count
                          (tally $sum (verdict $index $case $want)))
             (check-lines $more-cases $more-wants (+ $index 1) $shard $count $sum)))))

(= (field $name $value) (str:concat $name (str:concat "=" (str:number->string $value))))

(= (read-lines $path)
   (let $lines (fs:read-lines $path)
     (if (== $lines ())
         $lines
         (if (== (car-atom $lines) Error) (stop (str:concat "cannot read " $path)) $lines))))

(= (run $corpus $expected $shard $count)
   (let* (($cases (read-lines $corpus))
          ($wants (read-lines $expected))
          ($t0 (system:monotonic-ns))
          ((Tally $checked $identical $mismatched)
           (check-lines $cases $wants 0 $shard $count (Tally 0 0 0)))
          ($elapsed (- (system:monotonic-ns) $t0))
          ($shown (say (str:join " " ("RESULT" (field "checked" $checked) (field "identical" $identical)
                                      (field "mismatched" $mismatched)
                                      (field "ms" (/ (- $elapsed (% $elapsed 1000000)) 1000000)))))))
     $mismatched))

; Exit status 0 iff every checked program is identical; a run that ends
; without its RESULT line exits nonzero.
(= (finish $results)
   (if (== (length $results) 1)
       (if (== (car-atom $results) 0) () (system:exit 1))
       (stop "the run ended without a result")))

(= (arg-text $a) (if (== (get-metatype $a) Symbol) (str:symbol->string $a) $a))
(= (arg-number $a) (if (== (get-metatype $a) Symbol) (str:string->number (str:symbol->string $a)) $a))

!(let $argc (system:argc)
   (if (< $argc 2)
       (stop "usage: cetta --no-results test_tisa_metta.metta CORPUS EXPECTED [SHARD COUNT]")
       (let* (($corpus (system:arg 0))
              ($expected (system:arg 1))
              ($shard (if (> $argc 2) (system:arg 2) 0))
              ($count (if (> $argc 3) (system:arg 3) 1)))
         (finish (collapse (run (arg-text $corpus) (arg-text $expected)
                                (arg-number $shard) (arg-number $count)))))))
