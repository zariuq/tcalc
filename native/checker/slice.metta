; slice.metta -- the first slice of the native HOLR checker (NATIVE-CHECKER.txt,
; section 11), authored with p1.metta: one t-ISA p1 program that checks a
; HOLR v1 stream of the records NAME TYVAR TYAPP VAR CONST COMB REFL TRANS
; EXPECT_ALPHA END over the bootstrap environment (types bool/0 and fun/2,
; the constant "=" : A->A->bool), in strict mode.
;
;   cetta --no-results slice.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Regions and rows are NATIVE-CHECKER.txt's (sections 2 and 3):
;   R0 input     RO  the stream          R5 terms     RW  named term rows, 40 B:
;   R1 control   RW  section 9, below                     tag, a, b, type, image
;   R2 names     RW  (offset, length)    R6 db        RW  de Bruijn rows (k0, k1)
;   R3 bytes     RW  name bytes          R7 theorems  RW  (hyps list, conclusion)
;   R4 types     RW  type rows (k0, k1)  R8 work      RW  tables, maps, buffers
; with k0 = tag | a << 3 and k1 = b for type and de Bruijn rows.
;
; One run checks a whole stream from a fresh state (control words zero): it
; sets up the bootstrap environment, reads the header, then one record per
; iteration of the record loop. The verdict is in control word 0 (2 accepted,
; 3 refused, 4 malformed, 5 resource, 6 unsupported) with a reason in word 34
; (CeTTa's HolReason numbering, hol_kernel.h; 100.. this checker's own), and
; the run returns FIRED (accepted), REFUSED (refused) or UNSUPPORTED (the
; rest), with the number of records committed.
;
; Registers: rec (v1) is the record loop's index, the number of records
; committed; len (v2) the stream's length, the loop's bound; off (v3) the
; offset of the next unread byte while a record is read. Every other value
; lives in control words between uses: a routine's registers hold only what
; it is working on, and each routine names the registers it uses.

!(import! &self "../p1/p1.metta")

; ---- Control words (R1), in words of 8 bytes ---------------------------------
;
; 0..11 and the R8 layout pairs are NATIVE-CHECKER.txt section 9's; from word
; 32 on, this slice's: the N and Y id counts (the maps' lengths), the reason,
; and the routines' working words.

(= (ck:w state) 0) (= (ck:w records) 1) (= (ck:w checksum) 2) (= (ck:w offset) 3)
(= (ck:w names) 4) (= (ck:w bytes-used) 5) (= (ck:w types) 6) (= (ck:w terms) 7)
(= (ck:w dbs) 8) (= (ck:w theorems) 9) (= (ck:w policy) 10) (= (ck:w generation) 11)
; R8 sub-ranges, (offset, length) in bytes
(= (ck:w name-table) 12) (= (ck:w type-table) 14) (= (ck:w db-table) 16) (= (ck:w nmap) 18)
(= (ck:w ymap) 20) (= (ck:w dropped) 22) (= (ck:w stack) 24) (= (ck:w memo) 26)
(= (ck:w sort) 28) (= (ck:w flags) 30)
(= (ck:w nids) 32) (= (ck:w yids) 33) (= (ck:w reason) 34)
; working words
(= (ck:w opcode) 36) (= (ck:w rec-start) 37) (= (ck:w dec-pre) 38) (= (ck:w dec-list) 39)
(= (ck:w dec-post) 40) (= (ck:w dec-total) 41) (= (ck:w known) 42)
(= (ck:w key0) 44) (= (ck:w key1) 45) (= (ck:w result) 46) (= (ck:w hash) 47) (= (ck:w mask) 48)
(= (ck:w slot) 49) (= (ck:w name-len) 50) (= (ck:w name-hash) 51) (= (ck:w cand-o) 52)
(= (ck:w byte1) 53) (= (ck:w rest) 54) (= (ck:w cur) 55)
(= (ck:w ty) 56) (= (ck:w left) 57) (= (ck:w right) 58)
(= (ck:w r0) 59) (= (ck:w r1) 60) (= (ck:w r2) 61) (= (ck:w r3) 62) (= (ck:w r4) 63)
(= (ck:w r5) 64) (= (ck:w r6) 65) (= (ck:w r7) 66)
(= (ck:w end-sum) 67) (= (ck:w hyps) 68) (= (ck:w concl) 69) (= (ck:w sort-n) 70)
; the control region's minimum length: 72 words
(= (ck:control-bytes) 576)

(= (ck:word $w) (if (p1:number? $w) $w (ck:w $w)))
(= (ck:off $w) (* 8 (ck:word $w)))

; R := control word W (R serves as the pointer first). Uses R only.
(= (ck:get $r $w) (Seq (Base $r control) (Load control $r $r (ck:off $w))))
; control word W := V, through the pointer register T (T not V).
(= (ck:put $w $v $t) (Seq (Base $t control) (Store control $t (ck:off $w) $v)))
; control word W := K, through T and U.
(= (ck:set $w $k $t $u) (Seq (Imm $u $k) (ck:put $w $u $t)))

; ---- Constants -------------------------------------------------------------------

(= (ck:magic) 3555957288647544648)                  ; "HOLRPLY1", little-endian
(= (ck:sha 0) 16627743020230071337)                 ; the pinned fusion.ml's SHA-256, 4 words
(= (ck:sha 1) 5431359510077486515)
(= (ck:sha 2) 14788567348201878682)
(= (ck:sha 3) 10005186196861837762)
(= (ck:fnv-offset) 14695981039346656037)
(= (ck:fnv-prime) 1099511628211)
(= (ck:golden) 11400714819323198485)
(= (ck:uv-limit) 4611686018427387904)               ; 2^62
(= (ck:list-limit) 1048576)                         ; 2^20: list operands and name bytes
(= (ck:cap) 4294967295)                             ; the largest loop cap

; Bootstrap rows, made in this order on a fresh state (ck:bootstrap):
; names 0 bool, 1 fun, 2 =, 3 A; types 0 [], 1 bool, 2 A, 3 [bool], 4 [A; bool],
; 5 A->bool, 6 [A->bool], 7 [A; A->bool], 8 A->A->bool; de Bruijn 0 [].
(= (ck:name-fun) 1) (= (ck:name-eq) 2)
(= (ck:ty-nil) 0) (= (ck:ty-bool) 1) (= (ck:ty-bool-nil) 3) (= (ck:db-nil) 0)

; Verdicts and reasons.
(= (ck:state ACCEPTED) 2) (= (ck:state REFUSED) 3) (= (ck:state MALFORMED) 4)
(= (ck:state RESOURCE) 5) (= (ck:state UNSUPPORTED) 6)
(= (ck:outcome ACCEPTED) FIRED) (= (ck:outcome REFUSED) REFUSED) (= (ck:outcome MALFORMED) UNSUPPORTED)
(= (ck:outcome RESOURCE) UNSUPPORTED) (= (ck:outcome UNSUPPORTED) UNSUPPORTED)

(= (ck:reason none) 0) (= (ck:reason mk-type-undeclared) 10) (= (ck:reason mk-type-arity) 11)
(= (ck:reason mk-const-undeclared) 14) (= (ck:reason const-not-instance) 15)
(= (ck:reason mk-comb-types) 17) (= (ck:reason trans) 27) (= (ck:reason nomem) 50)
(= (ck:reason magic) 54) (= (ck:reason version) 55) (= (ck:reason header) 56)
(= (ck:reason truncated) 57) (= (ck:reason integer) 58) (= (ck:reason opcode) 59)
(= (ck:reason future-ref) 60) (= (ck:reason trailing) 63) (= (ck:reason checksum) 64)
(= (ck:reason count) 65) (= (ck:reason limit) 66) (= (ck:reason expect) 67)
(= (ck:reason missing-end) 70)
; this checker's own: a layout outside R8, a state that is not fresh, a probe
; stream, a record outside the slice
(= (ck:reason layout) 100) (= (ck:reason not-fresh) 101) (= (ck:reason probe) 102)
(= (ck:reason not-in-slice) 103)

; The verdict STATE with REASON, then RETURN with rec. T and U are clobbered.
(= (ck:exit $state $reason $t $u)
   (Seq (ck:set state (ck:state $state) $t $u)
        (ck:set reason (ck:reason $reason) $t $u)
        (Return (ck:outcome $state) rec)))

; Go on when the BOOL C holds, else exit.
(= (ck:require $c $state $reason $t $u) (If $c Skip (ck:exit $state $reason $t $u)))

; ---- Rows and R8 sub-ranges --------------------------------------------------------------
;
; (ck:sub-addr P S J T): P := the address of word J (a register) of the R8
; sub-range whose (offset, length) pair is at control word S; RESOURCE when J
; lies outside it. P, J, T distinct; J kept.
(= (ck:sub-addr $p $s $j $t)
   (Seq (ck:get $p (+ (ck:word $s) 1)) (Shr $p $p 3) (Cmp Ult $t $j $p)
        (ck:require $t RESOURCE nomem $p $t)
        (Shl $t $j 3) (ck:get $p $s) (Add $t $t $p) (Base $p work) (Addr work $p $p $t 0 0)))

; R := word J (a register) of sub-range S. R, J, T distinct.
(= (ck:sub-get $r $s $j $t) (Seq (ck:sub-addr $r $s $j $t) (Load work $r $r 0)))

; R := operand K (an immediate) of the record. R, T, U distinct.
(= (ck:arg $r $k $t $u) (Seq (Imm $t $k) (ck:sub-get $r stack $t $u)))

; P := the address of the 16-byte row I of region ROWS. P may be I; T distinct.
(= (ck:row16 $p $rows $i $t) (Seq (Shl $t $i 4) (Base $p $rows) (Addr $rows $p $p $t 0 0)))
; R := word W of the 16-byte row I. R may be I; T distinct.
(= (ck:row-word $r $rows $i $w $t) (Seq (ck:row16 $r $rows $i $t) (Load $rows $r $r (* 8 $w))))
; R := word W of the 40-byte named term row I (0 tag, 1 a, 2 b, 3 type, 4 image).
(= (ck:term-word $r $i $w $t)
   (Seq (Imm $t 40) (Mul $t $i $t) (Base $r terms) (Addr terms $r $r $t 0 0) (Load terms $r $r (* 8 $w))))

; key0 := TAG | A << 3 and key1 := B, from registers A and B. T, U distinct from A, B.
(= (ck:key $tag $a $b $t $u)
   (Seq (Shl $t $a 3) (Imm $u $tag) (Or $t $t $u) (ck:put key0 $t $u) (ck:put key1 $b $u)))

; ---- 1. Entry -----------------------------------------------------------------------------
;
; The layout: each R8 sub-range is word-aligned and lies inside R8. The state:
; fresh (state and every count zero); this slice does not resume a stream.

(= (ck:check-layout)
   (Block ck_check_layout (With (As i v4) (As n v5) (As a v6) (As b v7) (As c v8) (As d v9)
     (Imm n 10)
     (Loop i n 10
       (Shl a i 1) (Base b control) (Addr control b b a 3 96)        ; pair i: words 12 + 2i
       (Load control c b 0) (Load control d b 8)                     ; c offset, d length
       (Or a c d) (Extract a a 0 3) (CmpI Eq a a 0)                  ; both multiples of 8
       (ck:require a UNSUPPORTED layout a b)
       (Len b work) (Cmp Ule a c b) (ck:require a UNSUPPORTED layout a b)   ; offset <= |R8|
       (Sub b b c) (Cmp Ule a d b) (ck:require a UNSUPPORTED layout a b)))))  ; length <= |R8| - offset

(= (ck:check-fresh)
   (Block ck_check_fresh (With (As a v4) (As b v5) (As c v6)
     (Imm c 0)
     (ck:get a state) (Or c c a) (ck:get a records) (Or c c a) (ck:get a offset) (Or c c a)
     (ck:get a checksum) (Or c c a)
     (ck:get a names) (Or c c a) (ck:get a bytes-used) (Or c c a) (ck:get a types) (Or c c a)
     (ck:get a terms) (Or c c a) (ck:get a dbs) (Or c c a) (ck:get a theorems) (Or c c a)
     (ck:get a nids) (Or c c a) (ck:get a yids) (Or c c a)
     (CmpI Eq a c 0) (ck:require a UNSUPPORTED not-fresh a b))))

; ---- 2. Interning --------------------------------------------------------------------------
;
; (ck:intern ROWS TABLE COUNT): find-or-make of the key in control words key0,
; key1 among the 16-byte rows of region ROWS, through the table sub-range at
; control word TABLE (8-byte slots: 0 empty, id + 1 used), with the row count
; in control word COUNT. The id ends in control word result. A slot is
; evidence only: its id is used after a check against the count, and a row is
; the key's only when both words are equal. RESOURCE when the rows or the
; table are full. Uses v5..v11.

(= (ck:intern $name $rows $table $count)
   (Block $name (With (As probe v5) (As slots v6) (As searching v7) (As a v8) (As b v9) (As c v10) (As d v11)
     (ck:get a (+ (ck:word $table) 1)) (Shr slots a 3)
     (Imm b 1) (Sub a slots b) (ck:put mask a b)
     (ck:get a key0) (ck:get b key1) (Xor a a b) (Imm b (ck:golden)) (Mul a a b)
     (Shr b a 29) (Xor a a b) (ck:put hash a b)
     (Imm TyBool searching 1)
     (EarlyLoop probe slots searching (ck:cap)
       (ck:get a hash) (Add a a probe) (ck:get b mask) (And a a b)
       (Shl a a 3) (ck:get b $table) (Add a a b) (ck:put slot a b)
       (Base b work) (Addr work b b a 0 0) (Load work a b 0)
       (CmpI Eq c a 0)
       (If c
           (Seq (ck:get a $count) (Len c $rows) (Shr c c 4) (Cmp Ult c a c)
                (ck:require c RESOURCE nomem c d)
                (ck:row16 b $rows a c)
                (ck:get c key0) (Store $rows b 0 c) (ck:get c key1) (Store $rows b 8 c)
                (Imm c 1) (Add c a c) (ck:put $count c b) (ck:put result a b)
                (ck:get d slot) (Base b work) (Addr work b b d 0 0) (Store work b 0 c)
                (Imm TyBool searching 0))
           (Seq (Imm c 1) (Sub a a c) (ck:get c $count) (Cmp Ult c a c)
                (If c
                    (Seq (ck:row16 b $rows a c)
                         (Load $rows c b 0) (ck:get d key0) (Cmp Eq c c d)
                         (If c
                             (Seq (Load $rows c b 8) (ck:get d key1) (Cmp Eq c c d)
                                  (If c (Seq (ck:put result a d) (Imm TyBool searching 0))))))))))
     (If searching (ck:exit RESOURCE nomem a b)))))

(= (ck:intern-type) (ck:intern ck_intern_type types type-table types))
(= (ck:intern-db) (ck:intern ck_intern_db db db-table dbs))

; (ck:intern-name): find-or-make of the name whose name-len bytes were placed
; at the end of the used arena (R3 from bytes-used). A new name keeps them,
; gets the row (offset, length) and zero theory flags; a known name leaves
; them unused. The id ends in control word result. Uses v3..v11.
(= (ck:intern-name)
   (Block ck_intern_name (With (As cx v3) (As cn v4) (As probe v5) (As slots v6) (As searching v7) (As a v8) (As b v9) (As c v10) (As d v11)
     ; FNV-1a of the candidate bytes, as the table's hash
     (ck:get c bytes-used) (Imm a (ck:fnv-offset)) (ck:get slots name-len)
     (Loop probe slots (ck:list-limit)
       (Add b c probe) (Base d bytes) (Addr bytes d d b 0 0) (Load 1 TyU64 bytes b d 0)
       (Xor a a b) (Imm b (ck:fnv-prime)) (Mul a a b))
     (ck:put name-hash a b)
     (ck:get a (+ (ck:w name-table) 1)) (Shr slots a 3) (Imm b 1) (Sub a slots b) (ck:put mask a b)
     (Imm TyBool searching 1)
     (EarlyLoop probe slots searching (ck:cap)
       (ck:get a name-hash) (Add a a probe) (ck:get b mask) (And a a b)
       (Shl a a 3) (ck:get b name-table) (Add a a b) (ck:put slot a b)
       (Base b work) (Addr work b b a 0 0) (Load work a b 0)
       (CmpI Eq c a 0)
       (If c
           ; a new name: flags (0, 0), row (bytes-used, name-len) at the count
           (Seq (ck:get a names) (Len c names) (Shr c c 4) (Cmp Ult c a c)
                (ck:require c RESOURCE nomem c d)
                (Shl c a 1) (Imm d 1) (Add c c d) (ck:sub-addr b flags c d)      ; word 2a + 1, so 2a too
                (Imm d 0) (Store work b 0 d) (Store work b -8 d)
                (ck:row16 b names a c)
                (ck:get c bytes-used) (Store names b 0 c)
                (ck:get d name-len) (Store names b 8 d)
                (Add c c d) (ck:put bytes-used c d)
                (Imm c 1) (Add c a c) (ck:put names c d)
                (ck:get d slot) (Base b work) (Addr work b b d 0 0) (Store work b 0 c)
                (ck:put result a d) (Imm TyBool searching 0))
           ; a used slot: its id, if a row, is the name when length and bytes agree
           (Seq (Imm c 1) (Sub a a c) (ck:get c names) (Cmp Ult c a c)
                (If c
                    (Seq (ck:row16 b names a c)
                         (Load names c b 8) (ck:get d name-len) (Cmp Eq c c d)
                         (If c
                             (Seq (Load names c b 0) (ck:put cand-o c d)
                                  (Imm c 0) (ck:get cn name-len)
                                  (Loop cx cn (ck:list-limit)
                                    (ck:get b cand-o) (Add b b cx) (Base d bytes) (Addr bytes d d b 0 0)
                                    (Load 1 TyU64 bytes b d 0) (ck:put byte1 b d)
                                    (ck:get b bytes-used) (Add b b cx) (Base d bytes) (Addr bytes d d b 0 0)
                                    (Load 1 TyU64 bytes b d 0) (ck:get d byte1) (Xor b b d) (Or c c b))
                                  (CmpI Eq c c 0)
                                  (If c (Seq (ck:put result a d) (Imm TyBool searching 0))))))))))
     (If searching (ck:exit RESOURCE nomem a b)))))

; ---- 3. The bootstrap environment ------------------------------------------------------
;
; Names bool fun = A, then the types of the bootstrap and the empty hypothesis
; list. Theory flags, two words per name row: word 0 is a type's arity + 1,
; word 1 a constant's generic type + 1, 0 for none: bool a type of arity 0,
; fun of arity 2, = a constant of generic type A->A->bool. Runs before the
; record loop, so v1 and v2 serve as its loop registers.

(= (ck:boot-bytes 0) (98 111 111 108))   ; bool
(= (ck:boot-bytes 1) (102 117 110))      ; fun
(= (ck:boot-bytes 2) (61))               ; =
(= (ck:boot-bytes 3) (65))               ; A

(= (ck:boot-store $bytes $i $p $t)
   (if (== $bytes ())
       Skip
       (let ($b $more) (decons-atom $bytes)
         (Seq (Imm $t $b) (Store 1 bytes $p $i $t) (ck:boot-store $more (+ $i 1) $p $t)))))

; In step S, bootstrap name S's bytes at the arena's end, and name-len.
(= (ck:boot-name $s $k $p $t $u)
   (Seq (CmpI Eq $t $k $s)
        (If $t (Seq (ck:get $u bytes-used) (Base $p bytes) (Addr bytes $p $p $u 0 0)
                    (ck:boot-store (ck:boot-bytes $s) 0 $p $t)
                    (ck:set name-len (length (ck:boot-bytes $s)) $p $t)))))

; types: 0 [] (2,0,0); 1 bool (1,bool,0); 2 A (0,A,0); 3 [bool] (3,1,0); 4 [A; bool] (3,2,3);
; 5 A->bool (1,fun,4); 6 [A->bool] (3,5,0); 7 [A; A->bool] (3,2,6); 8 A->A->bool (1,fun,7)
(= (ck:boot-key 0) (2 0)) (= (ck:boot-key 1) (1 0)) (= (ck:boot-key 2) (24 0))
(= (ck:boot-key 3) (11 0)) (= (ck:boot-key 4) (19 3)) (= (ck:boot-key 5) (9 4))
(= (ck:boot-key 6) (43 0)) (= (ck:boot-key 7) (19 6)) (= (ck:boot-key 8) (9 7))

(= (ck:boot-type $s $k $t $u)
   (let ($k0 $k1) (ck:boot-key $s)
     (Seq (CmpI Eq $t $k $s)
          (If $t (Seq (ck:set key0 $k0 $u $t) (ck:set key1 $k1 $u $t))))))

; flags word W of name row R := V
(= (ck:set-flag $r $w $v $p $j $t)
   (Seq (Imm $j (+ (* 2 $r) $w)) (ck:sub-addr $p flags $j $t) (Imm $t $v) (Store work $p 0 $t)))

(= (ck:bootstrap)
   (Block ck_bootstrap
     (With (As s v1) (As n v2) (As p v4) (As t v5) (As u v6)
       (Imm n 4)
       (Loop s n 4
         (Len t bytes) (ck:get u bytes-used) (Sub t t u) (CmpI Ult t t 4)    ; room for 4 bytes
         (If t (ck:exit RESOURCE nomem t u))
         (ck:boot-name 0 s p t u) (ck:boot-name 1 s p t u)
         (ck:boot-name 2 s p t u) (ck:boot-name 3 s p t u)
         (ck:intern-name)))
     (With (As s v1) (As n v2) (As t v3) (As u v4)
       (Imm n 9)
       (Loop s n 9
         (ck:boot-type 0 s t u) (ck:boot-type 1 s t u) (ck:boot-type 2 s t u)
         (ck:boot-type 3 s t u) (ck:boot-type 4 s t u) (ck:boot-type 5 s t u)
         (ck:boot-type 6 s t u) (ck:boot-type 7 s t u) (ck:boot-type 8 s t u)
         (ck:intern-type)))
     (With (As t v3) (As u v4)
       (ck:set key0 5 t u) (ck:set key1 0 t u))
     (ck:intern-db)
     (With (As p v3) (As j v4) (As t v5)
       (ck:set-flag 0 0 1 p j t)         ; bool: a type, arity 0
       (ck:set-flag 1 0 3 p j t)         ; fun: a type, arity 2
       (ck:set-flag 2 1 9 p j t))))      ; =: a constant, generic type row 8

; ---- 4. Reading ---------------------------------------------------------------------------
;
; (ck:read-uv VAL P B T U): an unsigned LEB128 value at off into VAL, in its
; minimal form, at most 9 bytes, below 2^62; off moves past it. MALFORMED
; truncated before a missing byte, integer otherwise. Unrolled: t-ISA shifts
; by immediates only, so byte i's seven bits are shifted by 7i in its own copy.

(= (ck:read-uv $val $p $b $t $u) (Block ck_read_uv (Imm $val 0) (ck:uv-byte 0 $val $p $b $t $u)))

(= (ck:uv-byte $i $val $p $b $t $u)
   (Seq (Cmp Ule $t len off) (If $t (ck:exit MALFORMED truncated $t $u))
        (Base $p input) (Addr input $p $p off 0 0) (Load 1 TyU64 input $b $p 0)
        (Imm $t 1) (Add off off $t)
        (Imm $t 127) (And $t $b $t)
        (if (== $i 0) Skip (Shl $t $t (* 7 $i)))
        (Or $val $val $t)
        (CmpI Ule $t $b 127)
        (If $t
            (Seq (if (== $i 0) Skip (Seq (CmpI Eq $t $b 0) (If $t (ck:exit MALFORMED integer $t $u))))
                 (Imm $u (ck:uv-limit)) (Cmp Ule $t $u $val) (If $t (ck:exit MALFORMED integer $t $u)))
            (if (== $i 8)
                (ck:exit MALFORMED integer $t $u)
                (ck:uv-byte (+ $i 1) $val $p $b $t $u)))))

; (ck:decode): the record's LEB128 operands into the stack sub-range of R8,
; value j at word j: dec-pre values, then, if dec-list, a count (at most 2^20,
; else MALFORMED limit) and that many values, then dec-post values.
(= (ck:decode)
   (Block ck_decode (With (As j v4) (As most v5) (As more v6) (As val v7) (As p v8) (As b v9) (As t v10) (As u v11)
     (ck:get t dec-pre) (ck:get u dec-list) (Add t t u) (ck:get u dec-post) (Add t t u)
     (ck:put dec-total t u)
     (Imm most (+ (ck:list-limit) 4))
     (CmpI Ne more t 0)
     (EarlyLoop j most more (+ (ck:list-limit) 4)
       (ck:read-uv val p b t u)
       (ck:get t dec-list) (CmpI Ne t t 0)
       (If t (Seq (ck:get t dec-pre) (Cmp Eq t t j)
                  (If t (Seq (Imm u (ck:list-limit)) (Cmp Ult t u val)
                             (If t (ck:exit MALFORMED limit t u))
                             (ck:get t dec-total) (Add t t val) (ck:put dec-total t u)))))
       (ck:sub-addr p stack j t) (Store work p 0 val)
       (Imm t 1) (Add t j t) (ck:get u dec-total) (Cmp Ult more t u)))))

; ---- 5. The header ------------------------------------------------------------------------
;
; Magic, the kernel's SHA-256, then version 1, profile 0, policy <= 2, flags
; (bit 0, probe, is not this slice's: UNSUPPORTED), each checked as soon as it
; is read, as CeTTa does; the checksum starts with the header's bytes.

(= (ck:header-field $f $k $a $t $u)
   (Seq (CmpI Eq $t $k $f)
        (If $t (ck:check-field $f $a $t $u))))
(= (ck:check-field 0 $a $t $u) (Seq (CmpI Eq $t $a 1) (ck:require $t MALFORMED version $t $u)))
(= (ck:check-field 1 $a $t $u) (Seq (CmpI Eq $t $a 0) (ck:require $t MALFORMED header $t $u)))
(= (ck:check-field 2 $a $t $u) (Seq (CmpI Ule $t $a 2) (ck:require $t MALFORMED header $t $u)
                                    (ck:put policy $a $t)))
(= (ck:check-field 3 $a $t $u) (Seq (CmpI Ule $t $a 1) (ck:require $t MALFORMED header $t $u)
                                    (CmpI Eq $t $a 0) (ck:require $t UNSUPPORTED probe $t $u)))

(= (ck:header)
   (Block ck_header
     (With (As a v4) (As b v5) (As p v6) (As t v7) (As u v8)
       (CmpI Ult t len 8) (If t (ck:exit MALFORMED truncated t u))
       (Base p input) (Load input a p 0) (Imm b (ck:magic)) (Cmp Eq t a b) (ck:require t MALFORMED magic t u)
       (CmpI Ult t len 40) (If t (ck:exit MALFORMED truncated t u))
       (Load input a p 8) (Imm b (ck:sha 0)) (Cmp Eq t a b) (ck:require t MALFORMED header t u)
       (Load input a p 16) (Imm b (ck:sha 1)) (Cmp Eq t a b) (ck:require t MALFORMED header t u)
       (Load input a p 24) (Imm b (ck:sha 2)) (Cmp Eq t a b) (ck:require t MALFORMED header t u)
       (Load input a p 32) (Imm b (ck:sha 3)) (Cmp Eq t a b) (ck:require t MALFORMED header t u)
       (Imm off 40))
     (With (As f v4) (As n v5) (As a v7) (As p v8) (As b v9) (As t v10) (As u v11)
       (Imm n 4)
       (Loop f n 4
         (ck:read-uv a p b t u)
         (ck:header-field 0 f a t u) (ck:header-field 1 f a t u)
         (ck:header-field 2 f a t u) (ck:header-field 3 f a t u)))
     (With (As t v4) (As u v5)
       (ck:put offset off t) (ck:set rec-start 0 t u) (ck:set checksum (ck:fnv-offset) t u))
     (ck:checksum-span)))

; checksum := FNV-1a, continued from checksum, of input bytes [rec-start, offset).
(= (ck:checksum-span)
   (Block ck_checksum_span (With (As i v4) (As n v5) (As h v6) (As s v7) (As p v8) (As b v9) (As t v10)
     (ck:get s rec-start) (ck:get n offset) (Sub n n s)
     (ck:get h checksum)
     (Loop i n (ck:cap)
       (Add t s i) (Base p input) (Addr input p p t 0 0) (Load 1 TyU64 input b p 0)
       (Xor h h b) (Imm t (ck:fnv-prime)) (Mul h h t))
     (ck:put checksum h t))))

; ---- 6. Records: layout ------------------------------------------------------------------

(= (ck:layout-of $op $pre $list $post $opc $t $u)
   (Seq (CmpI Eq $t $opc $op)
        (If $t (Seq (ck:set dec-pre $pre $u $t) (ck:set dec-list $list $u $t)
                    (ck:set dec-post $post $u $t) (ck:set known 1 $u $t)))))

; ACC := ACC or LO <= OPC <= HI
(= (ck:in-range $lo $hi $opc $t $u $acc)
   (Seq (CmpI Ult $t $opc $lo) (CmpI Ule $u $opc $hi) (Bin BinXor TyBool $t $t $u)
        (Bin BinOr TyBool $acc $acc $t)))

; A known HOLR opcode outside this slice: UNSUPPORTED; any other: MALFORMED.
(= (ck:layout)
   (Block ck_layout (With (As opc v4) (As t v5) (As u v6) (As acc v7)
     (ck:get opc opcode)
     (ck:set known 0 t u)
     (ck:layout-of 1 1 0 0 opc t u)        ; NAME     b      (the count; the bytes follow)
     (ck:layout-of 2 1 0 0 opc t u)        ; TYVAR    N
     (ck:layout-of 3 1 1 0 opc t u)        ; TYAPP    N*Y
     (ck:layout-of 4 2 0 0 opc t u)        ; VAR      NY
     (ck:layout-of 5 2 0 0 opc t u)        ; CONST    NY
     (ck:layout-of 6 2 0 0 opc t u)        ; COMB     TT
     (ck:layout-of 16 1 0 0 opc t u)       ; REFL     T
     (ck:layout-of 17 2 0 0 opc t u)       ; TRANS    HH
     (ck:layout-of 53 1 1 1 opc t u)       ; EXPECT_ALPHA H*TT
     (ck:layout-of 127 1 0 0 opc t u)      ; END      uc     (the count; the checksum follows)
     (ck:get t known) (CmpI Eq t t 0)
     (If t
         (Seq (Imm TyBool acc 0)
              (ck:in-range 1 7 opc t u acc) (ck:in-range 16 25 opc t u acc)
              (ck:in-range 32 37 opc t u acc) (ck:in-range 48 53 opc t u acc)
              (ck:in-range 64 66 opc t u acc)
              (If acc (ck:exit UNSUPPORTED not-in-slice t u) (ck:exit MALFORMED opcode t u)))))))

; The raw bytes after the counts: NAME's bytes (at most 2^20: MALFORMED limit;
; past the end: truncated) are copied to the end of the used arena; END's
; 8-byte checksum is read into end-sum.
(= (ck:raw-operands)
   (Block ck_raw_operands (With (As op v4) (As n v5) (As t v6) (As u v7) (As p v8) (As i v9) (As q v10) (As b v11)
     (ck:get op opcode)
     (CmpI Eq t op 1)
     (If t
         (Seq (ck:arg n 0 t u)
              (Imm u (ck:list-limit)) (Cmp Ult t u n) (If t (ck:exit MALFORMED limit t u))
              (Sub t len off) (Cmp Ult t t n) (If t (ck:exit MALFORMED truncated t u))
              (ck:put name-len n t)
              (Len t bytes) (ck:get u bytes-used) (Sub t t u) (Cmp Ult t t n)   ; room in the arena
              (If t (ck:exit RESOURCE nomem t u))
              (Loop i n (ck:list-limit)
                (Add t off i) (Base p input) (Addr input p p t 0 0) (Load 1 TyU64 input b p 0)
                (ck:get t bytes-used) (Add t t i) (Base q bytes) (Addr bytes q q t 0 0) (Store 1 bytes q 0 b))
              (Add off off n)))
     (CmpI Eq t op 127)
     (If t
         (Seq (Sub t len off) (CmpI Ult t t 8) (If t (ck:exit MALFORMED truncated t u))
              (Base p input) (Addr input p p off 0 0) (Load input b p 0) (ck:put end-sum b t)
              (Imm t 8) (Add off off t))))))

; ---- 7. Records: validation ----------------------------------------------------------------
;
; Every id operand names a defined id of its space, else MALFORMED
; future-ref. (No id is dropped: this slice has no DROP records.)

; operand K (immediate) is below control word COUNT
(= (ck:valid $k $count $a $b $t $u)
   (Seq (ck:arg $a $k $t $u) (ck:get $b $count) (Cmp Ult $t $a $b)
        (ck:require $t MALFORMED future-ref $a $b)))

; operands FIRST .. FIRST + (operand CNT) - 1 are below control word COUNT
(= (ck:valid-list $cnt $first $count $i $n $a $b $t $u)
   (Seq (ck:arg $n $cnt $t $u)
        (Loop $i $n (ck:list-limit)
          (Imm $t $first) (Add $t $i $t) (ck:sub-get $a stack $t $u)
          (ck:get $b $count) (Cmp Ult $t $a $b) (ck:require $t MALFORMED future-ref $a $b))))

(= (ck:validate)
   (Block ck_validate (With (As op v4) (As c v5) (As i v6) (As n v7) (As a v8) (As b v9) (As t v10) (As u v11)
     (ck:get op opcode)
     (CmpI Eq c op 2) (If c (ck:valid 0 nids a b t u))
     (CmpI Eq c op 3) (If c (Seq (ck:valid 0 nids a b t u) (ck:valid-list 1 2 yids i n a b t u)))
     (CmpI Eq c op 4) (If c (Seq (ck:valid 0 nids a b t u) (ck:valid 1 yids a b t u)))
     (CmpI Eq c op 5) (If c (Seq (ck:valid 0 nids a b t u) (ck:valid 1 yids a b t u)))
     (CmpI Eq c op 6) (If c (Seq (ck:valid 0 terms a b t u) (ck:valid 1 terms a b t u)))
     (CmpI Eq c op 16) (If c (ck:valid 0 terms a b t u))
     (CmpI Eq c op 17) (If c (Seq (ck:valid 0 theorems a b t u) (ck:valid 1 theorems a b t u)))
     (CmpI Eq c op 53)
     (If c (Seq (ck:valid 0 theorems a b t u) (ck:valid-list 1 2 terms i n a b t u)
                ; the conclusion: operand 2 + count
                (ck:arg n 1 t u) (Imm t 2) (Add t n t) (ck:sub-get a stack t u)
                (ck:get b terms) (Cmp Ult t a b) (ck:require t MALFORMED future-ref a b))))))

; ---- 8. Records: execution ------------------------------------------------------------------

; Append V to the map at control word MAP whose length is control word COUNT.
(= (ck:map-append $map $count $v $p $j $t)
   (Seq (ck:get $j $count) (ck:sub-addr $p $map $j $t) (Store work $p 0 $v)
        (Imm $t 1) (Add $j $j $t) (ck:put $count $j $p)))

; Append the named term row (TAG, A, B, TY, IMG) (registers) at the terms count.
(= (ck:term-append $tag $a $b $ty $img $p $j $t)
   (Seq (ck:get $j terms) (Len $p terms) (Imm $t 40) (Mul $t $j $t) (Sub $p $p $t)
        (CmpI Ult $p $p 40) (If $p (ck:exit RESOURCE nomem $p $t))
        (Base $p terms) (Addr terms $p $p $t 0 0)
        (Imm $t $tag) (Store terms $p 0 $t) (Store terms $p 8 $a) (Store terms $p 16 $b)
        (Store terms $p 24 $ty) (Store terms $p 32 $img)
        (Imm $t 1) (Add $j $j $t) (ck:put terms $j $p)))

; Append the theorem row (HYPS, CONCL) (registers) at the theorems count.
(= (ck:thm-append $hyps $concl $p $j $t)
   (Seq (ck:get $j theorems) (Len $p theorems) (Shr $p $p 4) (Cmp Ult $t $j $p)
        (ck:require $t RESOURCE nomem $p $t)
        (ck:row16 $p theorems $j $t) (Store theorems $p 0 $hyps) (Store theorems $p 8 $concl)
        (Imm $t 1) (Add $j $j $t) (ck:put theorems $j $p)))

; R := flags word W of name row N (every row has flags: they are made with it).
(= (ck:flag $r $n $w $t $u)
   (Seq (Shl $t $n 1) (Imm $u $w) (Add $t $t $u) (ck:sub-get $r flags $t $u)))

; FIRST, SECOND := the arguments of the type row Y when it is TyApp(fun, [_; _]);
; else REFUSED FAIL. Y kept; T, U clobbered; all five distinct.
(= (ck:fun-args $first $second $y $t $u $fail)
   (Seq (ck:row-word $t types $y 0 $u) (Imm $u (+ 1 (* 8 (ck:name-fun)))) (Cmp Eq $u $t $u)
        (ck:require $u REFUSED $fail $t $u)
        (ck:row-word $t types $y 1 $u)                                     ; t: the list
        (ck:row-word $u types $t 0 $first) (Extract $first $u 0 3) (CmpI Eq $first $first 3)
        (ck:require $first REFUSED $fail $first $second)
        (Shr $first $u 3)                                                  ; the first argument
        (ck:row-word $t types $t 1 $u)                                     ; t: the rest
        (ck:row-word $u types $t 0 $second) (Extract $second $u 0 3) (CmpI Eq $second $second 3)
        (ck:require $second REFUSED $fail $second $t)
        (Shr $second $u 3)                                                 ; the second argument
        (ck:row-word $t types $t 1 $u)                                     ; t: the rest of the rest
        (ck:row-word $t types $t 0 $u) (CmpI Eq $u $t 2) (ck:require $u REFUSED $fail $t $u)))

; NAME: intern the bytes; the N map gets the name's row.
(= (ck:exec-name)
   (Block ck_exec_name (ck:intern-name)
        (With (As v v4) (As p v5) (As j v6) (As t v7)
          (ck:get v result) (ck:map-append nmap nids v p j t))))

; TYVAR N: the type row TyVar(name).
(= (ck:exec-tyvar)
   (Block ck_exec_tyvar (With (As a v4) (As n v5) (As z v6) (As t v7) (As u v8)
          (ck:arg a 0 t u) (ck:sub-get n nmap a t) (Imm z 0) (ck:key 0 n z t u))
        (ck:intern-type)
        (With (As v v4) (As p v5) (As j v6) (As t v7)
          (ck:get v result) (ck:map-append ymap yids v p j t))))

; TYAPP N [Y...]: N a declared type whose arity is the list's length; the
; argument list's cells from the last, then TyApp(name, list).
(= (ck:exec-tyapp)
   (Block ck_exec_tyapp (With (As a v4) (As n v5) (As k v6) (As t v7) (As u v8)
          (ck:arg a 0 t u) (ck:sub-get n nmap a t) (ck:put cur n t)
          (ck:flag k n 0 t u)
          (CmpI Eq t k 0) (If t (ck:exit REFUSED mk-type-undeclared t u))
          (Imm t 1) (Sub k k t) (ck:arg a 1 t u) (Cmp Eq t k a) (ck:require t REFUSED mk-type-arity t u)
          (ck:set rest (ck:ty-nil) t u))
        (With (As i v3) (As n v4) (As a v5) (As b v6) (As t v7) (As u v8)
          (ck:arg n 1 t u)
          (Loop i n (ck:list-limit)
            ; argument n - i, operand 1 + n - i, from the last
            (Sub t n i) (Imm a 1) (Add t t a) (ck:sub-get a stack t u) (ck:sub-get b ymap a u)
            (ck:get a rest) (ck:key 3 b a t u)
            (ck:intern-type)
            (ck:get a result) (ck:put rest a t)))
        (With (As n v4) (As b v5) (As t v6) (As u v7)
          (ck:get n cur) (ck:get b rest) (ck:key 1 n b t u))
        (ck:intern-type)
        (With (As v v4) (As p v5) (As j v6) (As t v7)
          (ck:get v result) (ck:map-append ymap yids v p j t))))

; VAR N Y: the named row (0, name, type, type, image), image dbVar(name, type).
(= (ck:exec-var)
   (Block ck_exec_var (With (As a v4) (As n v5) (As y v6) (As t v7) (As u v8)
          (ck:arg a 0 t u) (ck:sub-get n nmap a t) (ck:arg a 1 t u) (ck:sub-get y ymap a t)
          (ck:put left n t) (ck:put ty y t) (ck:key 0 n y t u))
        (ck:intern-db)
        (With (As n v4) (As y v5) (As img v6) (As p v7) (As j v8) (As t v9)
          (ck:get n left) (ck:get y ty) (ck:get img result) (ck:term-append 0 n y y img p j t))))

; CONST N Y: N the constant = (the bootstrap's only constant), Y an instance
; of its generic type A->A->bool, that is fun [a; fun [a; bool]]. The named
; row (1, name, type, type, image), image dbConst(name, type).
(= (ck:exec-const)
   (Block ck_exec_const (With (As n v3) (As y v4) (As a v5) (As f v6) (As a2 v7) (As b v8) (As t v9) (As u v10)
          (ck:arg t 0 a u) (ck:sub-get n nmap t a) (ck:arg t 1 a u) (ck:sub-get y ymap t a)
          (ck:put left n t) (ck:put ty y t)
          (ck:flag t n 1 a u) (CmpI Eq t t 0) (If t (ck:exit REFUSED mk-const-undeclared t u))
          (ck:fun-args a f y t u const-not-instance)
          (ck:fun-args a2 b f t u const-not-instance)
          (Cmp Eq t a a2) (ck:require t REFUSED const-not-instance t u)
          (CmpI Eq t b (ck:ty-bool)) (ck:require t REFUSED const-not-instance t u)
          (ck:key 2 n y t u))
        (ck:intern-db)
        (With (As n v4) (As y v5) (As img v6) (As p v7) (As j v8) (As t v9)
          (ck:get n left) (ck:get y ty) (ck:get img result) (ck:term-append 1 n y y img p j t))))

; COMB T1 T2: T1's type fun [a; b] with a the type of T2. The named row
; (2, T1, T2, b, image), image dbComb(image1, image2).
(= (ck:exec-comb)
   (Block ck_exec_comb (With (As f v3) (As x v4) (As a v5) (As b v6) (As fy v7) (As t v8) (As u v9)
          (ck:arg f 0 t u) (ck:arg x 1 t u) (ck:put left f t) (ck:put right x t)
          (ck:term-word fy f 3 t)
          (ck:fun-args a b fy t u mk-comb-types)
          (ck:term-word t x 3 u) (Cmp Eq t a t) (ck:require t REFUSED mk-comb-types t u)
          (ck:put ty b t)
          (ck:term-word a f 4 t) (ck:term-word b x 4 t) (ck:key 3 a b t u))
        (ck:intern-db)
        (With (As f v4) (As x v5) (As y v6) (As img v7) (As p v8) (As j v9) (As t v10)
          (ck:get f left) (ck:get x right) (ck:get y ty) (ck:get img result)
          (ck:term-append 2 f x y img p j t))))

; eq_build: the conclusion left = right at type ty (control words) into
; result: the types ty->bool and ty->ty->bool, the constant = at the latter,
; then two combinations. Eight internings, step s's result in word r0 + s.
(= (ck:eq-key 0 $t $u $a $b) (Seq (ck:get $a ty) (Imm $b (ck:ty-bool-nil)) (ck:key 3 $a $b $t $u)))   ; [ty; bool]
(= (ck:eq-key 1 $t $u $a $b) (Seq (Imm $a (ck:name-fun)) (ck:get $b r0) (ck:key 1 $a $b $t $u)))      ; ty -> bool
(= (ck:eq-key 2 $t $u $a $b) (Seq (ck:get $a r1) (Imm $b (ck:ty-nil)) (ck:key 3 $a $b $t $u)))        ; [ty -> bool]
(= (ck:eq-key 3 $t $u $a $b) (Seq (ck:get $a ty) (ck:get $b r2) (ck:key 3 $a $b $t $u)))             ; [ty; ty -> bool]
(= (ck:eq-key 4 $t $u $a $b) (Seq (Imm $a (ck:name-fun)) (ck:get $b r3) (ck:key 1 $a $b $t $u)))      ; ty -> ty -> bool
(= (ck:eq-key 5 $t $u $a $b) (Seq (Imm $a (ck:name-eq)) (ck:get $b r4) (ck:key 2 $a $b $t $u)))       ; the constant =
(= (ck:eq-key 6 $t $u $a $b) (Seq (ck:get $a r5) (ck:get $b left) (ck:key 3 $a $b $t $u)))            ; (=) left
(= (ck:eq-key 7 $t $u $a $b) (Seq (ck:get $a r6) (ck:get $b right) (ck:key 3 $a $b $t $u)))           ; (=) left right

(= (ck:eq-step $s $k $c $t $u $a $b) (Seq (CmpI Eq $c $k $s) (If $c (ck:eq-key $s $t $u $a $b))))

(= (ck:eq-build)
   (Block ck_eq_build (With (As s v3) (As n v4) (As c v5) (As t v6) (As u v7) (As a v8) (As b v9)
     (Imm n 8)
     (Loop s n 8
       (ck:eq-step 0 s c t u a b) (ck:eq-step 1 s c t u a b) (ck:eq-step 2 s c t u a b)
       (ck:eq-step 3 s c t u a b) (ck:eq-step 4 s c t u a b) (ck:eq-step 5 s c t u a b)
       (ck:eq-step 6 s c t u a b) (ck:eq-step 7 s c t u a b)
       (CmpI Ult c s 5)
       (If c (ck:intern-type) (ck:intern-db))
       (ck:get a result) (Base b control) (Addr control b b s 3 (ck:off r0)) (Store control b 0 a)))))

; REFL T: |- t = t: hypotheses [], conclusion eq_build(image, image, type).
(= (ck:exec-refl)
   (Block ck_exec_refl (With (As a v4) (As b v5) (As t v6) (As u v7)
          (ck:arg a 0 t u) (ck:term-word b a 4 t) (ck:put left b t) (ck:put right b t)
          (ck:term-word b a 3 t) (ck:put ty b t))
        (ck:eq-build)
        (With (As h v4) (As c v5) (As p v6) (As j v7) (As t v8)
          (Imm h (ck:db-nil)) (ck:get c r7) (ck:thm-append h c p j t))))

; ---- Hypothesis lists ---------------------------------------------------------------
;
; A hypothesis list is an interned list of de Bruijn ids in increasing order
; without repetition (cells 6 cons(a, b), 5 nil), so equal sets have one id.
; The ids go to the sort sub-range of R8 (control word sort-n of them); sorting
; them, dropping repeats and interning the cells from the last gives the list
; (control word result).

; Append the id V to the sort buffer.
(= (ck:sort-push $v $p $j $t)
   (Seq (ck:get $j sort-n) (ck:sub-addr $p sort $j $t) (Store work $p 0 $v)
        (Imm $t 1) (Add $j $j $t) (ck:put sort-n $j $p)))

; Push every element of the hypothesis list L (a register; consumed).
(= (ck:sort-push-list $l $more $k $n $e $p $j $t)
   (Seq (ck:get $n dbs) (Imm TyBool $more 1)
        (EarlyLoop $k $n $more (ck:cap)
          (ck:row-word $e db $l 0 $t) (Extract $t $e 0 3) (CmpI Eq $t $t 6)       ; a cell?
          (If $t
              (Seq (Shr $e $e 3) (ck:sort-push $e $p $j $t) (ck:row-word $l db $l 1 $t))
              (Imm TyBool $more 0)))))

(= (ck:sort-to-list)
   (Block ck_sort_to_list
     ; exchange sort: m passes of neighbour exchanges
     (With (As pass v3) (As m v4) (As i v5) (As n v6) (As a v7) (As b v8) (As p v9) (As q v10) (As t v11)
       (ck:get m sort-n) (Imm t 1) (Sub n m t) (CmpI Eq t m 0) (If t (Imm n 0))
       (Loop pass m (ck:cap)
         (Loop i n (ck:cap)
           (ck:sub-addr p sort i t) (Load work a p 0)
           (Imm t 1) (Add t i t) (ck:sub-addr q sort t b) (Load work b q 0)
           (Cmp Ult t b a) (If t (Seq (Store work p 0 b) (Store work q 0 a))))))
     ; the cells from the last, a repeat skipped
     (With (As i v3) (As m v4) (As a v5) (As b v6) (As t v7) (As u v8)
       (ck:set result (ck:db-nil) t u) (ck:set rest (ck:db-nil) t u)
       (ck:get m sort-n)
       (Loop i m (ck:cap)
         (Sub t m i) (Imm u 1) (Sub t t u) (ck:sub-get a sort t u)           ; element m - 1 - i
         (Imm TyBool b 1)
         (CmpI Ne u i 0)
         (If u (Seq (Sub t m i) (ck:sub-get u sort t b) (Cmp Ne b a u)))      ; differs from the next
         (If b (Seq (ck:get u rest) (ck:key 6 a u t b)
                    (ck:intern-db)
                    (ck:get a result) (ck:put rest a t)))))
     (With (As a v3) (As t v4) (ck:get a rest) (ck:put result a t))))

; TRANS H1 H2: |- l = m1 and |- m2 = r with m1 = m2 (one id: alpha-equal):
; |- l = r, the conclusion dbComb(th1's (=) l, r), hypotheses the union.
; dbComb rows are (3, a, b), dbConst (2, name, type).

; C an equation dbComb(E, R) with E = dbComb(dbConst(=, _), L): E, L, R its
; parts; else REFUSED trans. C kept; all six distinct.
(= (ck:eq-parts $c $e $l $r $t $u)
   (Seq (ck:row-word $t db $c 0 $u) (Extract $u $t 0 3) (CmpI Eq $u $u 3) (ck:require $u REFUSED trans $t $u)
        (Shr $e $t 3) (ck:row-word $r db $c 1 $u)
        (ck:row-word $t db $e 0 $u) (Extract $u $t 0 3) (CmpI Eq $u $u 3) (ck:require $u REFUSED trans $t $u)
        (ck:row-word $l db $e 1 $u)
        (Shr $t $t 3) (ck:row-word $t db $t 0 $u) (Imm $u (+ 2 (* 8 (ck:name-eq)))) (Cmp Eq $u $t $u)
        (ck:require $u REFUSED trans $t $u)))

(= (ck:exec-trans)
   (Block ck_exec_trans (With (As h1 v3) (As h2 v4) (As c v5) (As e v6) (As l v7) (As r v8) (As t v9) (As u v10) (As mid v11)
          (ck:arg h1 0 t u) (ck:arg h2 1 t u)
          (ck:row-word c theorems h1 1 t) (ck:eq-parts c e l r t u)
          (ck:put left e t) (Mov mid r)                          ; th1's (=) l, and its right side
          (ck:row-word c theorems h2 1 t) (ck:eq-parts c e l r t u)
          (Cmp Eq t mid l) (ck:require t REFUSED trans t u)      ; th2's left side is th1's right
          (ck:put right r t))
        (With (As a v4) (As b v5) (As t v6) (As u v7)
          (ck:get a left) (ck:get b right) (ck:key 3 a b t u))
        (ck:intern-db)
        (With (As a v3) (As t v4) (ck:get a result) (ck:put concl a t))
        ; the hypotheses: both lists' elements, sorted
        (With (As l v3) (As more v4) (As k v5) (As n v6) (As e v7) (As p v8) (As j v9) (As t v10) (As u v11)
          (ck:set sort-n 0 t u)
          (ck:arg u 0 t j) (ck:row-word l theorems u 0 t) (ck:sort-push-list l more k n e p j t)
          (ck:arg u 1 t j) (ck:row-word l theorems u 0 t) (ck:sort-push-list l more k n e p j t))
        (ck:sort-to-list)
        (With (As h v4) (As c v5) (As p v6) (As j v7) (As t v8)
          (ck:get h result) (ck:get c concl) (ck:thm-append h c p j t))))

; EXPECT_ALPHA H [T...] T: theorem H's conclusion is the image of the last
; term, and its hypotheses are the images of the listed terms, as a set: one
; list id each. REFUSED expect otherwise.
(= (ck:exec-expect-alpha)
   (Block ck_exec_expect_alpha (With (As i v3) (As n v4) (As a v5) (As b v6) (As p v7) (As j v8) (As t v9) (As u v10)
          (ck:set sort-n 0 t u)
          (ck:arg n 1 t u)
          (Loop i n (ck:list-limit)
            (Imm t 2) (Add t i t) (ck:sub-get a stack t u) (ck:term-word b a 4 t)
            (ck:sort-push b p j t)))
        (ck:sort-to-list)
        (With (As h v3) (As n v4) (As a v5) (As b v6) (As t v7) (As u v8)
          (ck:arg h 0 t u)
          (ck:arg n 1 t u) (Imm t 2) (Add t n t) (ck:sub-get a stack t u) (ck:term-word a a 4 t)  ; the image
          (ck:row-word b theorems h 1 t) (Cmp Eq t a b) (ck:require t REFUSED expect t u)
          (ck:get a result) (ck:row-word b theorems h 0 t) (Cmp Eq t a b) (ck:require t REFUSED expect t u))))

; END n sum: n is the number of records, sum the checksum before END, and
; nothing follows: ACCEPTED.
(= (ck:exec-end)
   (Block ck_exec_end (With (As a v4) (As b v5) (As t v6) (As u v7)
     (ck:arg a 0 t u) (Cmp Eq t a rec) (ck:require t MALFORMED count t u)
     (ck:get a end-sum) (ck:get b checksum) (Cmp Eq t a b) (ck:require t MALFORMED checksum t u)
     (ck:get a offset) (Cmp Eq t a len) (ck:require t MALFORMED trailing t u)
     (ck:exit ACCEPTED none t u))))

; ---- 9. The record loop ----------------------------------------------------------------------

(= (ck:on $op $body)
   (With (As c v4) (Seq (ck:get c opcode) (CmpI Eq c c $op) (If c $body))))

(= (ck:execute)
   (Seq (ck:on 1 (ck:exec-name)) (ck:on 2 (ck:exec-tyvar)) (ck:on 3 (ck:exec-tyapp))
        (ck:on 4 (ck:exec-var)) (ck:on 5 (ck:exec-const)) (ck:on 6 (ck:exec-comb))
        (ck:on 16 (ck:exec-refl)) (ck:on 17 (ck:exec-trans)) (ck:on 53 (ck:exec-expect-alpha))
        (ck:on 127 (ck:exec-end))))

; After a record: the checksum takes its bytes; it is counted; off resumes.
(= (ck:commit)
   (Block ck_commit (ck:checksum-span)
        (With (As t v4) (As p v5) (Imm t 1) (Add t rec t) (ck:put records t p))
        (ck:get off offset)))

(= (ck:record)
   (Block ck_record
     (With (As t v4) (As u v5) (As p v6) (As b v7)
       (Cmp Ule t len off) (If t (ck:exit MALFORMED missing-end t u))      ; no record, no END
       (ck:put rec-start off t)
       (Base p input) (Addr input p p off 0 0) (Load 1 TyU64 input b p 0)
       (Imm t 1) (Add off off t) (ck:put opcode b t))
     (ck:layout)
     (ck:decode)
     (ck:raw-operands)
     (With (As t v4) (ck:put offset off t))
     (ck:validate)
     (ck:execute)
     (ck:commit)))

(= (ck:main)
   (Seq (Imm rec 0)
        (ck:check-layout)
        (ck:check-fresh)
        (ck:bootstrap)
        (Imm rec 0) (Len len input)
        (ck:header)
        (Loop rec len (ck:cap) (ck:record))
        (With (As t v4) (As u v5) (ck:exit MALFORMED missing-end t u))))

(= (ck:program)
   (p1:program holr_slice
     (Regions (Region input RO 0 1) (Region control RW (ck:control-bytes) 8) (Region names RW 0 8)
              (Region bytes RW 0 1) (Region types RW 0 8) (Region terms RW 0 8)
              (Region db RW 0 8) (Region theorems RW 0 8) (Region work RW 0 8))
     (Registers (As rec v1) (As len v2) (As off v3))
     (Init)
     (ck:main)))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write ck:program $text $notes))
