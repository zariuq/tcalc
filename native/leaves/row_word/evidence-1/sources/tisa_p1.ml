(* ========================================================================= *)
(* t-ISA profile p1: the machine semantics of tcalc/tisa/SEMANTICS.txt.      *)
(*                                                                           *)
(* Each definition implements the section it names; the C reference          *)
(* (tcalc/tisa/tisa_ref.c) implements the same sections. Memory is the x86   *)
(* model's memory: a function from 64-bit addresses to bytes, read and       *)
(* written little-endian through the bytes(a,k) component, so a native       *)
(* realization and this semantics speak about the same object.               *)
(*                                                                           *)
(* The run is defined for every program; the theorems about native code are  *)
(* stated for admitted programs and entry states that satisfy section 6.     *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(* ------------------------------------------------------------------------- *)
(* 1. Values and types.                                                      *)
(* ------------------------------------------------------------------------- *)

let tisa_ty_INDUCT,tisa_ty_RECURSION = define_type
 "tisa_ty = TyU64 | TyU32Z | TyI32S | TyBool | TyPtr";;

let tisa_norm = define
 `(tisa_norm TyU32Z (w:int64) = word_zx(word_zx w:int32):int64) /\
  (tisa_norm TyI32S w = word_sx(word_zx w:int32):int64) /\
  (tisa_norm TyU64 w = w) /\
  (tisa_norm TyBool w = w) /\
  (tisa_norm TyPtr w = w)`;;

let tisa_bool = new_definition
 `tisa_bool (w:int64) <=> val w <= 1`;;

let tisa_canonical = new_definition
 `tisa_canonical t (w:int64) <=> tisa_norm t w = w /\ (t = TyBool ==> tisa_bool w)`;;

let tisa_narrow = new_definition
 `tisa_narrow t <=> t = TyU32Z \/ t = TyI32S`;;

(* ------------------------------------------------------------------------- *)
(* 3. Programs. Only the fields an instruction uses are part of it.          *)
(* ------------------------------------------------------------------------- *)

let tisa_binop_INDUCT,tisa_binop_RECURSION = define_type
 "tisa_binop = BinAdd | BinSub | BinAnd | BinOr | BinXor | BinMulLo";;

let tisa_shiftop_INDUCT,tisa_shiftop_RECURSION = define_type
 "tisa_shiftop = ShiftLeft | ShiftRightU | ShiftRightS";;

let tisa_cond_INDUCT,tisa_cond_RECURSION = define_type
 "tisa_cond = CondEq | CondNe | CondUlt | CondUle | CondSlt | CondSle";;

let tisa_operand_INDUCT,tisa_operand_RECURSION = define_type
 "tisa_operand = OpReg num | OpImm (64)word";;

(* IMM t d k; MOV t d a; BIN op t d a b; SHIFT op t d a s; EXTRACT t d a l w;
   CMP c t d a rhs; SELECT t d k a b; ADDR r d p index s o;
   LOAD t w r d p o; LOAD frame t d i (frame word i); STORE w r p o v. *)
let tisa_instr_INDUCT,tisa_instr_RECURSION = define_type
 "tisa_instr = TImm tisa_ty num (64)word
             | TMov tisa_ty num num
             | TBin tisa_binop tisa_ty num num num
             | TShift tisa_shiftop tisa_ty num num num
             | TExtract tisa_ty num num num num
             | TCmp tisa_cond tisa_ty num num tisa_operand
             | TSelect tisa_ty num num num num
             | TAddr num num num (num option) num int
             | TLoad tisa_ty num num num num int
             | TLoadFrame tisa_ty num num
             | TStore num num num int num";;

(* COUNT_LOOP x n cap body; EARLY_EXIT_LOOP x n k cap body; RETURN o r. *)
let tisa_stmt_INDUCT,tisa_stmt_RECURSION = define_type
 "tisa_stmt = TSkip
            | TInstr tisa_instr
            | TSeq tisa_stmt tisa_stmt
            | TIf num tisa_stmt tisa_stmt
            | TCountLoop num num num tisa_stmt
            | TEarlyLoop num num num num tisa_stmt
            | TReturn num num
            | TFund num";;

(* Region declarations (mode, minimum length, alignment), mode 0 none,
   1 read-only, 2 read-write; initialized registers (v, type, region). *)
let tisa_prog_INDUCT,tisa_prog_RECURSION = define_type
 "tisa_prog = TProg ((num#num#num)list) ((num#tisa_ty#num)list) tisa_stmt";;

let tisa_root = define
 `tisa_root (TProg decls init root) = root`;;

(* ------------------------------------------------------------------------- *)
(* 2. State: registers v0..v11 (v0 the frame address) and memory.            *)
(* ------------------------------------------------------------------------- *)

let tisa_state_INDUCT,tisa_state_RECURSION = define_type
 "tisa_state = TState (num->(64)word) ((64)word->byte)";;

let tregs = define
 `tregs (TState r m) = r`;;

let tmem = define
 `tmem (TState r m) = m`;;

let tisa_result_INDUCT,tisa_result_RECURSION = define_type
 "tisa_result = TCont tisa_state | TStop num tisa_state";;

let tisa_frame = new_definition
 `tisa_frame st = tregs st 0`;;

let tisa_read = new_definition
 `tisa_read st (a:int64) w = word(read (bytes(a,w)) (tmem st)):int64`;;

(* Frame word i: region r's base is word 2r and its length word 2r + 1;
   status 18, ret_val 19, fuel_budget 20, fuel_used 21, arg0 22, arg1 23. *)
let tisa_fword = new_definition
 `tisa_fword st i = tisa_read st (word_add (tisa_frame st) (word(8 * i))) 8`;;

let tisa_base = new_definition
 `tisa_base st r = tisa_fword st (2 * r)`;;

let tisa_len = new_definition
 `tisa_len st r = tisa_fword st (2 * r + 1)`;;

let tisa_setreg = new_definition
 `tisa_setreg d (v:int64) st = TState (\i. if i = d then v else tregs st i) (tmem st)`;;

let tisa_store = new_definition
 `tisa_store (a:int64) w (v:int64) st =
    TState (tregs st) (write (bytes(a,w)) (val v) (tmem st))`;;

let tisa_setfword = new_definition
 `tisa_setfword i v st = tisa_store (word_add (tisa_frame st) (word(8 * i))) 8 v st`;;

(* ------------------------------------------------------------------------- *)
(* 7. Outcomes: FIRED 1, REFUSED 0, UNSUPPORTED 2, INVALID_INPUT 3,          *)
(* EXHAUSTED 4. A failure leaves its code in status and ret_val.             *)
(* ------------------------------------------------------------------------- *)

let tisa_fail = new_definition
 `tisa_fail k st = TStop k (tisa_setfword 19 (word k) (tisa_setfword 18 (word k) st))`;;

let tisa_finish = new_definition
 `tisa_finish out v st = TStop out (tisa_setfword 19 v (tisa_setfword 18 (word out) st))`;;

(* ------------------------------------------------------------------------- *)
(* 5. Instructions.                                                          *)
(* ------------------------------------------------------------------------- *)

let tisa_binop = define
 `(tisa_binop BinAdd (x:int64) y = word_add x y) /\
  (tisa_binop BinSub x y = word_sub x y) /\
  (tisa_binop BinAnd x y = word_and x y) /\
  (tisa_binop BinOr x y = word_or x y) /\
  (tisa_binop BinXor x y = word_xor x y) /\
  (tisa_binop BinMulLo x y = word_mul x y)`;;

let tisa_shift32 = define
 `(tisa_shift32 ShiftLeft (u:int32) s = word_shl u s) /\
  (tisa_shift32 ShiftRightU u s = word_ushr u s) /\
  (tisa_shift32 ShiftRightS u s = word_ishr u s)`;;

let tisa_shift64 = define
 `(tisa_shift64 ShiftLeft (w:int64) s = word_shl w s) /\
  (tisa_shift64 ShiftRightU w s = word_ushr w s) /\
  (tisa_shift64 ShiftRightS w s = word_ishr w s)`;;

(* 32-bit types shift the low 32 bits, then normalize. *)
let tisa_shift = new_definition
 `tisa_shift op t (w:int64) s =
    if tisa_narrow t then tisa_norm t (word_zx(tisa_shift32 op (word_zx w:int32) s))
    else tisa_shift64 op w s`;;

let tisa_extract = new_definition
 `tisa_extract (w:int64) l n =
    if n < 64 then word_and (word_ushr w l) (word(2 EXP n - 1)) else word_ushr w l`;;

let tisa_compare_at = define
 `(tisa_compare_at CondEq (x:N word) y <=> x = y) /\
  (tisa_compare_at CondNe x y <=> ~(x = y)) /\
  (tisa_compare_at CondUlt x y <=> val x < val y) /\
  (tisa_compare_at CondUle x y <=> val x <= val y) /\
  (tisa_compare_at CondSlt x y <=> ival x < ival y) /\
  (tisa_compare_at CondSle x y <=> ival x <= ival y)`;;

(* 32-bit types compare the low 32 bits. *)
let tisa_compare = new_definition
 `tisa_compare c t (x:int64) y <=>
    if tisa_narrow t then tisa_compare_at c (word_zx x:int32) (word_zx y:int32)
    else tisa_compare_at c x y`;;

let tisa_rhs = define
 `(tisa_rhs st (OpReg b) = tregs st b) /\
  (tisa_rhs st (OpImm k) = k)`;;

let tisa_index = define
 `(tisa_index st NONE = &0:int) /\
  (tisa_index st (SOME q) = &(val(tregs st q)))`;;

(* [e, e + w) inside region r, computed without wraparound. *)
let tisa_inside = new_definition
 `tisa_inside st r (e:int) w <=>
    &(val(tisa_base st r)) <= e /\
    e + &w <= &(val(tisa_base st r)) + &(val(tisa_len st r))`;;

let tisa_ea = new_definition
 `tisa_ea st p (off:int) = &(val(tregs st p)) + off`;;

let tisa_addr_mid = new_definition
 `tisa_addr_mid st p i s = &(val(tregs st p)) + tisa_index st i * &2 pow s`;;

let tisa_instr = define
 `(tisa_instr (TImm t d imm) st = TCont (tisa_setreg d (tisa_norm t imm) st)) /\
  (tisa_instr (TMov t d a) st =
     if t = TyBool /\ ~tisa_bool (tregs st a) then tisa_fail 3 st
     else TCont (tisa_setreg d (tisa_norm t (tregs st a)) st)) /\
  (tisa_instr (TBin bop t d a b) st =
     if t = TyBool /\ ~(tisa_bool (tregs st a) /\ tisa_bool (tregs st b)) then tisa_fail 3 st
     else TCont (tisa_setreg d (tisa_norm t (tisa_binop bop (tregs st a) (tregs st b))) st)) /\
  (tisa_instr (TShift sop t d a s) st =
     TCont (tisa_setreg d (tisa_shift sop t (tregs st a) s) st)) /\
  (tisa_instr (TExtract t d a l n) st =
     TCont (tisa_setreg d (tisa_norm t (tisa_extract (tregs st a) l n)) st)) /\
  (tisa_instr (TCmp c t d a rhs) st =
     TCont (tisa_setreg d (if tisa_compare c t (tregs st a) (tisa_rhs st rhs)
                           then word 1 else word 0) st)) /\
  (tisa_instr (TSelect t d k a b) st =
     if ~tisa_bool (tregs st k) \/
        (t = TyBool /\ ~(tisa_bool (tregs st a) /\ tisa_bool (tregs st b)))
     then tisa_fail 3 st
     else TCont (tisa_setreg d (tisa_norm t (if tregs st k = word 0 then tregs st b
                                             else tregs st a)) st)) /\
  (tisa_instr (TAddr r d p i s off) st =
     if tisa_inside st r (tisa_addr_mid st p i s) 0 /\
        tisa_inside st r (tisa_addr_mid st p i s + off) 0
     then TCont (tisa_setreg d (iword(tisa_addr_mid st p i s + off)) st)
     else tisa_fail 3 st) /\
  (tisa_instr (TLoad t w r d p off) st =
     if ~tisa_inside st r (tisa_ea st p off) w then tisa_fail 3 st
     else if t = TyBool /\ ~tisa_bool (tisa_read st (iword(tisa_ea st p off)) w)
     then tisa_fail 3 st
     else TCont (tisa_setreg d (tisa_norm t (tisa_read st (iword(tisa_ea st p off)) w)) st)) /\
  (tisa_instr (TLoadFrame t d fi) st =
     if t = TyBool /\ ~tisa_bool (tisa_fword st fi) then tisa_fail 3 st
     else TCont (tisa_setreg d (tisa_norm t (tisa_fword st fi)) st)) /\
  (tisa_instr (TStore w r p off v) st =
     if ~tisa_inside st r (tisa_ea st p off) w then tisa_fail 3 st
     else TCont (tisa_store (iword(tisa_ea st p off)) w (tregs st v) st))`;;

(* ------------------------------------------------------------------------- *)
(* 3, 7 and 8. Statements.                                                   *)
(* ------------------------------------------------------------------------- *)

let tisa_then = define
 `(tisa_then (TCont st) f = f st) /\
  (tisa_then (TStop k st) f = TStop k st)`;;

(* 8. FUND u: if A - R < u then EXHAUSTED (R unchanged) else R := R + u. *)
let tisa_fund = new_definition
 `tisa_fund u st =
    if val(word_sub (tisa_fword st 20) (tisa_fword st 21)) < u then tisa_fail 4 st
    else TCont (tisa_setfword 21 (word_add (tisa_fword st 21) (word u)) st)`;;

(* COUNT_LOOP after its entry check: m iterations remain and the next has
   index j; the body f runs with x = j. A complete loop leaves x = n. *)
let tisa_count_iter = new_recursive_definition num_RECURSION
 `(tisa_count_iter 0 f x j st = TCont (tisa_setreg x (word j) st)) /\
  (tisa_count_iter (SUC m) f x j st =
     tisa_then (f (tisa_setreg x (word j) st))
               (\st'. tisa_count_iter m f x (j + 1) st'))`;;

(* EARLY_EXIT_LOOP tests its BOOL k before and after each body. *)
let tisa_early_check = new_definition
 `tisa_early_check k st (g:tisa_state->tisa_result) =
    if ~tisa_bool (tregs st k) then tisa_fail 3 st
    else if tregs st k = word 0 then TCont st else g st`;;

let tisa_early_iter = new_recursive_definition num_RECURSION
 `(tisa_early_iter 0 f x k j st = TCont (tisa_setreg x (word j) st)) /\
  (tisa_early_iter (SUC m) f x k j st =
     tisa_early_check k (tisa_setreg x (word j) st)
       (\st1. tisa_then (f st1)
                (\st2. tisa_early_check k st2
                         (\st3. tisa_early_iter m f x k (j + 1) st3))))`;;

let tisa_exec = new_recursive_definition tisa_stmt_RECURSION
 `(tisa_exec TSkip st = TCont st) /\
  (tisa_exec (TInstr i) st = tisa_instr i st) /\
  (tisa_exec (TSeq a b) st = tisa_then (tisa_exec a st) (\st'. tisa_exec b st')) /\
  (tisa_exec (TIf c a b) st =
     if ~tisa_bool (tregs st c) then tisa_fail 3 st
     else if tregs st c = word 0 then tisa_exec b st else tisa_exec a st) /\
  (tisa_exec (TCountLoop x n cap body) st =
     if cap < val(tregs st n) then tisa_fail 2 st
     else tisa_count_iter (val(tregs st n)) (\st'. tisa_exec body st') x 0 st) /\
  (tisa_exec (TEarlyLoop x n k cap body) st =
     if cap < val(tregs st n) then tisa_fail 2 st
     else tisa_early_iter (val(tregs st n)) (\st'. tisa_exec body st') x k 0 st) /\
  (tisa_exec (TReturn out r) st = tisa_finish out (tregs st r) st) /\
  (tisa_exec (TFund u) st = tisa_fund u st)`;;

(* ------------------------------------------------------------------------- *)
(* 6. Entry.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* One declared region with base b and length l, the frame at f. A writable
   region is disjoint from the frame; a read-only one from the frame words a
   run writes (status onward). *)
let tisa_region_ok = new_definition
 `tisa_region_ok mode minlen align b l f <=>
    minlen <= l /\ (l = 0 \/ ~(b = 0)) /\ b + l < 2 EXP 64 /\
    (align <= 1 \/ b MOD align = 0) /\
    (l = 0 \/ (if mode = 2 then b + l <= f \/ f + 192 <= b
               else b + l <= f + 144 \/ f + 192 <= b))`;;

(* Region (mode, b, l) against a later declared region (mode', b', l'). *)
let tisa_pair_ok = new_definition
 `tisa_pair_ok mode b l mode' b' l' <=>
    mode' = 0 \/ l' = 0 \/ ~(mode = 2 \/ mode' = 2) \/
    (b' + l' < 2 EXP 64 /\ (b + l <= b' \/ b' + l' <= b))`;;

let tisa_pairs_ok = define
 `(tisa_pairs_ok st mode b l q [] <=> T) /\
  (tisa_pairs_ok st mode b l q (CONS (d:num#num#num) ds) <=>
     tisa_pair_ok mode b l (FST d) (val(tisa_base st q)) (val(tisa_len st q)) /\
     tisa_pairs_ok st mode b l (q + 1) ds)`;;

let tisa_decls_ok = define
 `(tisa_decls_ok st r [] <=> T) /\
  (tisa_decls_ok st r (CONS (d:num#num#num) ds) <=>
     (FST d = 0 \/
      (tisa_region_ok (FST d) (FST(SND d)) (SND(SND d))
                      (val(tisa_base st r)) (val(tisa_len st r)) (val(tisa_frame st)) /\
       (val(tisa_len st r) = 0 \/
        tisa_pairs_ok st (FST d) (val(tisa_base st r)) (val(tisa_len st r)) (r + 1) ds))) /\
     tisa_decls_ok st (r + 1) ds)`;;

let tisa_init_ok = define
 `(tisa_init_ok st [] <=> T) /\
  (tisa_init_ok st (CONS (v:num#tisa_ty#num) vs) <=>
     (if FST(SND v) = TyPtr
      then val(tisa_base st (SND(SND v))) <= val(tregs st (FST v)) /\
           val(tregs st (FST v)) - val(tisa_base st (SND(SND v))) <=
           val(tisa_len st (SND(SND v)))
      else tisa_canonical (FST(SND v)) (tregs st (FST v))) /\
     tisa_init_ok st vs)`;;

let tisa_entry_ok = define
 `tisa_entry_ok (TProg decls init root) st <=>
    val(tisa_frame st) + 192 <= 2 EXP 64 /\
    val(tisa_fword st 21) <= val(tisa_fword st 20) /\
    tisa_decls_ok st 0 decls /\
    tisa_init_ok st init`;;

(* ------------------------------------------------------------------------- *)
(* A run (sections 6 to 8): admitted programs always reach RETURN; one that  *)
(* fell through would be UNSUPPORTED.                                        *)
(* ------------------------------------------------------------------------- *)

let tisa_run = new_definition
 `tisa_run prog st =
    if tisa_entry_ok prog st
    then tisa_then (tisa_exec (tisa_root prog) st) (\st'. tisa_fail 2 st')
    else tisa_fail 3 st`;;
