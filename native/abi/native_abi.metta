; NativeInterface.module -> checked ABI tables and language bindings.
; cetta --no-results native_abi.metta MODULE BYTE_SCALARS CESTA OUTPUT_PREFIX
; The module and generated declarations are data. Consumer proofs and native
; layout checks establish their agreement with the implemented interfaces.
!(import! &self (library lib_module))
!(import! &self system)
!(import! &self fs)
!(import! &self str)
!(import! &self proc)

(= (abi:cat $parts)
   (if (== $parts ()) ""
     (let ($first $rest) (decons-atom $parts)
       (str:concat $first (abi:cat $rest)))))
(= (abi:identifier? $name)
   (and (> (str:byte-length $name) 0)
        (and (str:is-all-in word $name)
             (or (== (str:byte-slice $name 0 1) "_")
                 (str:is-all-in alpha (str:byte-slice $name 0 1))))))
(= (abi:name (PApp $name LNil) $prefix)
   (if (== (str:byte-slice $name 0 (str:byte-length $prefix)) $prefix)
     (let $tail (str:byte-slice $name (str:byte-length $prefix) (str:byte-length $name))
       (if (abi:identifier? $tail) (ABIName $tail) (ABIRefused InvalidName $name)))
     (ABIRefused InvalidName $name)))

; Layout coordinates and fixed sizes use the unsigned 32-bit profile.
; NatBit comes from the shared byte library, not a second numeral syntax.
(= (abi:nat $number $fuel)
   (case $number
     (((PApp "NatZero" LNil) (ABIValue 0))
      ((PApp "NatBit" (LCons $bit (LCons $rest LNil)))
       (if (== $fuel 0) (ABIRefused LayoutIntegerOverflow)
         (case (abi:nat $rest (- $fuel 1))
           (((ABIValue $n)
             (case $bit
               (((PApp "Bit0" LNil)
                 (if (== $n 0) (ABIRefused NoncanonicalInteger) (ABIValue (* 2 $n))))
                ((PApp "Bit1" LNil) (ABIValue (+ 1 (* 2 $n))))
                ($other (ABIRefused InvalidBit $other)))))
            ($other $other)))))
      ($other (ABIRefused NonliteralInteger $other)))))

(= (abi:entry $entry)
   (case $entry
     (((PApp "ABIConstant" (LCons $name (LCons $number LNil)))
       (case ((abi:name $name "Name_") (abi:nat $number 32))
         ((((ABIName $key) (ABIValue $value)) (ABIRow Constant $key $value))
          ($other (ABIRefused InvalidConstant $other)))))
      ((PApp "ABIField" (LCons $record (LCons $name (LCons $number LNil))))
       (case ((abi:name $record "Record_") (abi:name $name "Name_") (abi:nat $number 32))
         ((((ABIName $kind) (ABIName $key) (ABIValue $value)) (ABIRow Field $kind $key $value))
          ($other (ABIRefused InvalidField $other)))))
      ($other (ABIRefused InvalidEntry $other)))))
(= (abi:entries $entries)
   (case $entries
     (((PApp "ABINil" LNil) (ABIRows ()))
      ((PApp "ABICons" (LCons $entry (LCons $rest LNil)))
       (case ((abi:entry $entry) (abi:entries $rest))
         ((((ABIRow $kind $a $b) (ABIRows $rows)) (ABIRows (cons-atom (ABIRow $kind $a $b) $rows)))
          (((ABIRow $kind $a $b $c) (ABIRows $rows)) (ABIRows (cons-atom (ABIRow $kind $a $b $c) $rows)))
          ($other (ABIRefused InvalidRows $other)))))
      ($other (ABIRefused InvalidEntries $other)))))

(= (abi:decode $export)
   (case $export
     (((ModuleRewriteRulesV1 $core
         (LCons (ModuleRuleOccurrenceV1 $origin
           (RewriteRule "NativeABI" LNil LNil (PApp "NativeInterface" LNil)
             (PApp "ABITable" (LCons $entries LNil)))) LNil))
       (abi:entries $entries))
      ($other (ABIRefused InvalidModule $other)))))

(= (abi:load $module-path $scalar-path)
   (let* (($reader (langdef:load-baked-parser "module-core-reader"))
          ($scalars (module:read-file $reader "native-abi:scalars" $scalar-path))
          ($module (module:read-file $reader "native-abi:source" $module-path))
          ($closed (langdef:close-parser $reader))
          ($values (module:assemble $scalars "Values" LNil LNil OriginViewV1 "native-abi:values"))
          ($catalog (LCons (ModuleCatalogEntryV1 "ByteScalars.module" $scalars) LNil))
          ($presentation (module:assemble $module "Data" (LCons $values LNil) $catalog OriginViewV1 "native:abi")))
     (abi:decode (module:rewrite-rules $presentation "NativeInterface"))))

(= (abi:key (ABIRow Constant $name $value)) $name)
(= (abi:key (ABIRow Field $record $name $value)) (abi:cat ($record "_" $name)))
(= (abi:value (ABIRow Constant $name $value)) $value)
(= (abi:value (ABIRow Field $record $name $value)) $value)
(= (abi:table-row $row $kind)
   (case ($row $kind)
     ((((ABIRow Constant $name $value) Constant)
       (abi:cat (" (Row " $name " " (str:number->string $value) ")")))
      (((ABIRow Field $record $name $value) Field)
       (abi:cat (" (Row " $record " " $name " " (str:number->string $value) ")")))
      ($other ""))))
(= (abi:table-rows $rows $kind)
   (str:join "" (map-atom $rows $row (abi:table-row $row $kind))))
(= (abi:tables $rows)
   (abi:cat ("(cesta-tables/1\n (Table Constants (Columns (Column name Identifier) (Column value Nat)) (Key name) (Rows"
     (abi:table-rows $rows Constant) "))\n (Table Fields (Columns (Column record Identifier) (Column name Identifier) (Column slot Nat)) (Key record name) (Unique record slot) (Rows"
     (abi:table-rows $rows Field) ")))\n")))

(= (abi:c-row $row)
   (abi:cat ("#define TISA_ABI_" (abi:key $row) " UINT64_C(" (str:number->string (abi:value $row)) ")\n")))
(= (abi:c-offset $row)
   (case $row
     (((ABIRow Field $record $name $value)
       (abi:cat ("#define TISA_ABI_" $record "_" $name "_OFFSET (TISA_ABI_WordBytes * TISA_ABI_" $record "_" $name ")\n")))
      ($other ""))))
(= (abi:c-assert $row)
   (case $row
     (((ABIRow Field "RuntimeFrame" $name $value)
       (abi:cat ("_Static_assert(offsetof(TcIsaRuntimeFrame, " $name ") == TISA_ABI_RuntimeFrame_" $name "_OFFSET, \"runtime frame field\");\n")))
      ($other ""))))
(= (abi:runtime-field-count $rows)
   (if (== $rows ()) 0
     (let ($first $rest) (decons-atom $rows)
       (case $first
         (((ABIRow Field "RuntimeFrame" $name $value) (+ 1 (abi:runtime-field-count $rest)))
          ($other (abi:runtime-field-count $rest)))))))
(= (abi:c $rows)
   (abi:cat ("/* Generated from NativeInterface.module. */\n#ifndef TCALC_NATIVE_ABI_H\n#define TCALC_NATIVE_ABI_H\n#include <stddef.h>\n#include <stdint.h>\n#include \"tisa.h\"\n"
     (str:join "" (map-atom $rows $row (abi:c-row $row)))
     (str:join "" (map-atom $rows $row (abi:c-offset $row)))
     "#define TISA_ABI_RuntimeFrame_FieldCount " (str:number->string (abi:runtime-field-count $rows)) "\n"
     "_Static_assert(TISA_ABI_RuntimeFrame_FieldCount == TISA_ABI_FrameWords, \"frame field inventory\");\n_Static_assert(TISA_ABI_FrameWords * TISA_ABI_WordBytes == TISA_ABI_FrameBytes, \"frame word extent\");\n"
     "_Static_assert(sizeof(uint64_t) == TISA_ABI_WordBytes, \"word bytes\");\n_Static_assert(sizeof(TcIsaRuntimeFrame) == TISA_ABI_FrameBytes, \"frame size\");\n_Static_assert(_Alignof(TcIsaRuntimeFrame) == TISA_ABI_CFrameAlignment, \"frame alignment\");\n"
     (str:join "" (map-atom $rows $row (abi:c-assert $row))) "#endif\n")))
(= (abi:asm-row $row)
   (abi:cat (".equ TISA_ABI_" (abi:key $row) ", " (str:number->string (abi:value $row)) "\n")))
(= (abi:asm-offset $row)
   (case $row
     (((ABIRow Field $record $name $value)
       (abi:cat (".equ TISA_ABI_" $record "_" $name "_OFFSET, TISA_ABI_WordBytes * TISA_ABI_" $record "_" $name "\n")))
      ($other ""))))
(= (abi:asm $rows)
   (abi:cat ("/* Generated from NativeInterface.module. */\n"
     (str:join "" (map-atom $rows $row (abi:asm-row $row)))
     (str:join "" (map-atom $rows $row (abi:asm-offset $row))))))
(= (abi:hol-row $row)
   (let $key (abi:key $row)
     (abi:cat ("let NATIVE_ABI_" $key " = new_definition\n `native_abi_" $key " = "
       (str:number->string (abi:value $row)) "`;;\n"))))
(= (abi:hol $rows)
   (abi:cat ("(* Generated from NativeInterface.module. *)\n"
     (str:join "" (map-atom $rows $row (abi:hol-row $row)))
     "let native_abi_definitions = ["
     (str:join ";" (map-atom $rows $row (str:concat "NATIVE_ABI_" (abi:key $row)))) "];;\n")))
(= (abi:lean-row $row)
   (abi:cat ("def " (abi:key $row) " : Nat := " (str:number->string (abi:value $row)) "\n")))
(= (abi:lean-frame-field $row)
   (case $row
     (((ABIRow Field "RuntimeFrame" $name $value)
       (let* (($key (abi:key $row))
              ($pointer (== (str:byte-slice $name (- (str:byte-length $name) 4) (str:byte-length $name)) "_ptr"))
              ($kind (if $pointer (abi:cat (".pointer (" $key " / 2)")) ".u64")))
         (abi:cat ("⟨\"" $name "\", WordBytes * " $key ", WordBytes, " $kind "⟩,\n"))))
      ($other ""))))
(= (abi:lean $rows)
   (abi:cat ("import Mettapedia.Machines.TIsa.Layout\n-- Generated from NativeInterface.module.\nnamespace TIsa.NativeABI\n"
     (str:join "" (map-atom $rows $row (abi:lean-row $row)))
     "def RuntimeFrameLayout : Mettapedia.Machines.TIsa.Layout :=\n  ⟨FrameBytes, CFrameAlignment, [\n"
     (str:join "" (map-atom $rows $row (abi:lean-frame-field $row)))
     "]⟩\nend TIsa.NativeABI\n")))

(= (abi:write $module $scalars $cesta $prefix)
   (case (abi:load $module $scalars)
     (((ABIRows $rows)
       (let* (($data (abi:tables $rows))
              ($pending (str:concat $prefix ".pending.data"))
              ($written (fs:write $pending $data))
              ($check (proc:run ((str:concat "" $cesta) "tables" "check" $pending) ())))
         (case $check
           (((proc:result (proc:exited 0) proc:normal $out $err $capture)
             (let* (($table (fs:rename $pending (str:concat $prefix ".data")))
                    ($c (fs:write (str:concat $prefix ".h") (abi:c $rows)))
                    ($asm (fs:write (str:concat $prefix ".inc") (abi:asm $rows)))
                    ($hol (fs:write (str:concat $prefix ".ml") (abi:hol $rows)))
                    ($lean (fs:write (str:concat $prefix ".lean") (abi:lean $rows))))
               (if (and (== $table ()) (and (== $c ()) (and (== $asm ()) (and (== $hol ()) (== $lean ())))))
                 (ABIGenerated (size-atom $rows))
                 (ABIRefused OutputWrite $table $c $asm $hol $lean))))
            ($other (ABIRefused InvalidTables $other))))))
      ($other $other))))

!(let* (($module (system:arg 0)) ($scalars (system:arg 1))
        ($cesta (system:arg 2)) ($prefix (system:arg 3)))
   (println! (abi:write $module $scalars $cesta $prefix)))
