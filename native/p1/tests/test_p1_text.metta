; test_p1_text.metta -- p1.metta's printer and resolver against tisa_print.c.
;
;   cetta --no-results test_p1_text.metta SEXPR-LINES HOL-LINES
;
; Line k of SEXPR-LINES is a program as S-expression text, line k of
; HOL-LINES the same program as tisa_print_program writes it in HOL style
; (both written by p1_text). For every program:
;   1. (p1:prog-text PROGRAM) is the HOL line, character for character;
;   2. resolving its root, where every register and region is a number,
;      gives the same root back;
;   3. the atom's own text (repr) is the S-expression line.
; Prints a MISMATCH line per failing program, then
;   RESULT checked=N same=M different=K

!(import! &self str)
!(import! &self fs)
!(import! &self system)
!(import! &self "../p1.metta")

(= (t:say $text) (system:write stdout (str:concat $text "\n")))

(= (t:check $index $sline $hline)
   (let* (($prog (parse $sline))
          ((TProg $decls $inits $root) $prog)
          ($text (p1:prog-text $prog))
          ((R $back $notes) (p1:resolve $root (Env (p1:machine-registers) ()) () ())))
     (if (== $text $hline)
         (if (== $back $root)
             (if (== (repr $prog) $sline)
                 Same
                 (t:mismatch $index "its S-expression text differs"))
             (t:mismatch $index "resolution changed the root"))
         (t:mismatch $index "its HOL text differs"))))

(= (t:mismatch $index $why)
   (let $shown (t:say (str:join " " ("MISMATCH line" (str:number->string (+ $index 1)) $why))) Different))

(= (t:tally (Tally $c $s $d) Same) (Tally (+ $c 1) (+ $s 1) $d))
(= (t:tally (Tally $c $s $d) Different) (Tally (+ $c 1) $s (+ $d 1)))

; One verdict per program; none or several is a mismatch, never a drop.
(= (t:verdict $index $sline $hline)
   (let $all (collapse (t:check $index $sline $hline))
     (if (== (length $all) 1) (car-atom $all) (t:mismatch $index "no single verdict"))))

(= (t:lines $ss $hs $index $sum)
   (if (or (== $ss ()) (== $hs ()))
       (if (== $ss $hs) $sum (let $shown (t:say "MISMATCH the files differ in length") $sum))
       (let* ((($s1 $srest) (decons-atom $ss))
              (($h1 $hrest) (decons-atom $hs)))
         (t:lines $srest $hrest (+ $index 1) (t:tally $sum (t:verdict $index $s1 $h1))))))

(= (t:run $sexpr-path $hol-path)
   (let* (($ss (fs:read-lines $sexpr-path))
          ($hs (fs:read-lines $hol-path))
          ((Tally $checked $same $different) (t:lines $ss $hs 0 (Tally 0 0 0))))
     (t:say (str:join " " ("RESULT" (str:concat "checked=" (str:number->string $checked))
                                    (str:concat "same=" (str:number->string $same))
                                    (str:concat "different=" (str:number->string $different)))))))

!(let* (($s (system:arg 0)) ($h (system:arg 1))) (t:run $s $h))
