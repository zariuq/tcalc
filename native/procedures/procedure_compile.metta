; Procedure step compilation for CeTTa's PeTTa lane.
; The emitted data is checked against procedure_step_compile.ml in HOL Light.
; Catalog entries name operations; their positions are source opcodes. A call
; uses the catalog length. Runtime table positions are independent of both.

!(import! &self str)
!(import! &self binary)

(= (pc:nat? $x)
   (if (== (get-metatype $x) Grounded)
       (if (== (get-type $x) Number)
           (if (== (binary:portable-kind $x) Float) false
               (and (> (str:byte-length (repr $x)) 0)
                    (str:is-all-in digit (repr $x))))
           false)
       false))

(= (pc:word? $x)
   (if (pc:nat? $x) (< $x 18446744073709551616) false))

(= (pc:operation? $x)
   (case $x
     (((KernelOperation $k) (pc:nat? $k))
      ((ReaderOperation $r) (pc:nat? $r))
      (ProcedureCallMarker true)
      ($other false))))

(= (pc:member? $x $xs)
   (if (== $xs ()) false
       (let ($head $tail) (decons-atom $xs)
         (if (== $head $x) true (pc:member? $x $tail)))))

(= (pc:operations? $xs)
   (if (== (get-metatype $xs) Expression)
       (if (== $xs ()) true
           (let ($head $tail) (decons-atom $xs)
             (if (pc:operation? $head)
                 (if (pc:member? $head $tail) false (pc:operations? $tail))
                 false)))
       false))

(= (pc:words? $xs)
   (if (== (get-metatype $xs) Expression)
       (if (== $xs ()) true
           (let ($head $tail) (decons-atom $xs)
             (if (pc:word? $head) (pc:words? $tail) false)))
       false))

; These list helpers are called only after list, length and index checks.
(= (pc:nth $xs $i)
   (let ($head $tail) (decons-atom $xs)
     (if (== $i 0) $head (pc:nth $tail (- $i 1)))))

(= (pc:drop $xs $n)
   (if (== $n 0) $xs
       (let ($head $tail) (decons-atom $xs)
         (pc:drop $tail (- $n 1)))))

(= (pc:append $left $right)
   (if (== $left ()) $right
       (let ($head $tail) (decons-atom $left)
         (cons-atom $head (pc:append $tail $right)))))

(= (pc:offset $xs $op)
   (let ($head $tail) (decons-atom $xs)
     (if (== $head $op) 0 (+ 1 (pc:offset $tail $op)))))

(= (pc:primitive-bindings? $st $original $r)
   (if (== $r 9) true
       (if (< (+ 1 (pc:nth $st (+ 1 $r))) $original)
           (pc:primitive-bindings? $st $original (+ $r 1))
           false)))

(= (pc:lower-known $catalog $table $original $procedures $st)
   (let* (($opcode (pc:nth $st 0))
          ($call (size-atom $catalog)))
     (if (< $opcode $call)
         (let $op (pc:nth $catalog $opcode)
           (if (and (pc:member? $op $table)
                    (pc:primitive-bindings? $st $original 0))
               (Some (cons-atom (pc:offset $table $op) (pc:drop $st 1)))
               None))
         (if (and (== $opcode $call)
                  (pc:member? ProcedureCallMarker $table))
             (let $target (pc:nth $st 1)
               (if (and (< $target $procedures)
                        (<= (+ $original (+ 4 (* 2 $procedures))) 18446744073709551616))
                   (let* (($runtime (pc:offset $table ProcedureCallMarker))
                          ($empty (+ $original 2))
                          ($metadata (+ $original (+ 4 (* 2 $target)))))
                     (Some (pc:append ($runtime $original $empty $empty $empty
                                      $empty $empty $empty $empty $metadata)
                                     (pc:drop $st 10))))
                   None))
             None))))

(= (pc:compile-step $catalog $table $original $procedures $st)
   (if (and (pc:operations? $catalog) (pc:operations? $table))
       (if (and (pc:nat? $original) (pc:nat? $procedures))
           (if (pc:words? $st)
               (if (and (== (size-atom $st) 18)
                        (and (< (size-atom $catalog) 18446744073709551616)
                             (and (< (size-atom $table) 18446744073709551616)
                                  (not (pc:member? ProcedureCallMarker $catalog)))))
                   (pc:lower-known $catalog $table $original $procedures $st)
                   None)
               None)
           None)
       None))

(= (pc:hol-word $n) (str:concat "word " (str:number->string $n)))

(= (pc:hol-result $result)
   (case $result
     ((None "(NONE:(int64 list)option)")
      ((Some $words)
       (str:concat "SOME (["
         (str:concat (str:join ";" (map-atom $words $word (pc:hol-word $word)))
                     "]:int64 list)"))))))
