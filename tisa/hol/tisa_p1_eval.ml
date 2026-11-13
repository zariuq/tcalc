(* ========================================================================= *)
(* Evaluating the p1 semantics on concrete programs and entry states, by     *)
(* call-by-value reduction inside the logic: each result is a theorem        *)
(* |- tisa_observe bufs (tisa_run prog st) = (outcome, ...). The fidelity    *)
(* check compares these theorems with the C reference evaluator's results.  *)
(* ========================================================================= *)

needs "tisa/hol/tisa_p1_memory.ml";;

(* What the C reference's tests observe after a run: the outcome, status,
   ret_val, receipt, and the 128-byte buffer behind each declared region. *)
let tisa_observe = define
 `(tisa_observe bufs (TStop k st) =
     (k, val(tisa_fword st 18), val(tisa_fword st 19), val(tisa_fword st 21),
      MAP (\b. read (bytes(word b:int64,128)) (tmem st)) bufs)) /\
  (tisa_observe bufs (TCont st) = (99, 0, 0, 0, []:num list))`;;

(* Memory reads in a form call-by-value reduction can use. Test memories are
   chains of byte-range writes over the zero memory. A read inside or
   outside one write is settled in one step; a read straddling a write's
   edge is split in half. *)
let tisa_zero_mem = new_definition
 `tisa_zero_mem (a:int64) = word 0:byte`;;

let TISA_READ_ZERO = prove
 (`!(a:int64) k. read (bytes(a,k)) tisa_zero_mem = 0`,
  REWRITE_TAC[READ_BYTES; tisa_zero_mem; VAL_WORD_0; MULT_CLAUSES; NSUM_0]);;

let TISA_READ_WRITE = prove
 (`!(a:int64) k c j n (m:int64->byte).
     read (bytes(a,k)) (write (bytes(c,j)) n m) =
     if val(word_sub a c) + k <= j /\ j <= 2 EXP 64
     then ((n MOD 2 EXP (8 * j)) DIV 2 EXP (8 * val(word_sub a c))) MOD
          2 EXP (8 * k)
     else if j <= val(word_sub a c) /\ val(word_sub a c) + k <= 2 EXP 64
     then read (bytes(a,k)) m
     else if k <= 1 then (if k = 0 then 0 else val(write (bytes(c,j)) n m a))
     else read (bytes(a,k DIV 2)) (write (bytes(c,j)) n m) +
          2 EXP (8 * (k DIV 2)) *
          read (bytes(word_add a (word(k DIV 2)),k - k DIV 2))
               (write (bytes(c,j)) n m)`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL [ASM_SIMP_TAC[TISA_READ_INSIDE_WRITE]; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_SIMP_TAC[TISA_READ_OUTSIDE_WRITE]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[READ_BYTES_TRIVIAL] THEN
    SUBGOAL_THEN `k = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[READ_BYTES_1];
    REWRITE_TAC[GSYM READ_BYTES_COMBINE] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC]);;

let TISA_WRITE_BYTES_APPLY = prove
 (`!(a:int64) k n (m:int64->byte) b.
        write (bytes(a,k)) n m b =
        if val(word_sub b a) < k then word(limb 8 n (val(word_sub b a))) else m b`,
  REWRITE_TAC[WRITE_BYTES]);;

(* The loop iterators recurse on 0 and SUC m; call-by-value reduction meets
   numerals, so it uses these forms. *)
let TISA_COUNT_ITER_EVAL = prove
 (`!n f x j st.
        tisa_count_iter n f x j st =
        if n = 0 then TCont (tisa_setreg x (word j) st)
        else tisa_then (f (tisa_setreg x (word j) st))
                       (\st'. tisa_count_iter (n - 1) f x (j + 1) st')`,
  INDUCT_TAC THEN REWRITE_TAC[tisa_count_iter; NOT_SUC; SUC_SUB1]);;

let TISA_EARLY_ITER_EVAL = prove
 (`!n f x k j st.
        tisa_early_iter n f x k j st =
        if n = 0 then TCont (tisa_setreg x (word j) st)
        else tisa_early_check k (tisa_setreg x (word j) st)
               (\st1. tisa_then (f st1)
                        (\st2. tisa_early_check k st2
                                 (\st3. tisa_early_iter (n - 1) f x k (j + 1) st3)))`,
  INDUCT_TAC THEN REWRITE_TAC[tisa_early_iter; NOT_SUC; SUC_SUB1]);;

(* Equality of the values that occur: numerals, integers, words, and the
   constructors of the enumerated syntax types. *)
let TISA_EQ_CONV =
  let distinct = CONJUNCTS(prove_constructors_distinct tisa_ty_RECURSION) @
                 CONJUNCTS(prove_constructors_distinct tisa_shiftop_RECURSION) in
  let distinct = distinct @ map GSYM distinct in
  let neq = map EQF_INTRO distinct in
  fun tm ->
    let l,r = dest_eq tm in
    if l = r then EQT_INTRO(REFL l)
    else (NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
          GEN_REWRITE_CONV I neq) tm;;

let tisa_compset =
  let cs = Compute.bool_compset() in
  Compute.set_skip cs `COND:bool->A->A->A` (Some 1);
  Compute.add_thms
   [tisa_norm; tisa_bool; tisa_canonical; tisa_narrow; tisa_root; tregs; tmem;
    tisa_frame; tisa_read; tisa_fword; tisa_base; tisa_len; tisa_setreg;
    tisa_store; tisa_setfword; tisa_fail; tisa_finish; tisa_binop;
    tisa_shift32; tisa_shift64; tisa_shift; tisa_extract; tisa_compare_at;
    tisa_compare; tisa_rhs; tisa_index; tisa_inside; tisa_ea; tisa_addr_mid;
    tisa_instr; tisa_then; tisa_fund; TISA_COUNT_ITER_EVAL; tisa_early_check;
    TISA_EARLY_ITER_EVAL; tisa_exec; tisa_region_ok; tisa_pair_ok; tisa_pairs_ok;
    tisa_decls_ok; tisa_init_ok; tisa_entry_ok; tisa_run; tisa_observe;
    tisa_zero_mem; TISA_READ_ZERO; TISA_READ_WRITE; TISA_WRITE_BYTES_APPLY;
    limb; MAP; FST; SND] cs;
  let word_ops =
   [`word:num->N word`,1; `val:N word->num`,1; `ival:N word->int`,1;
    `word_add:N word->N word->N word`,2; `word_sub:N word->N word->N word`,2;
    `word_mul:N word->N word->N word`,2; `word_and:N word->N word->N word`,2;
    `word_or:N word->N word->N word`,2; `word_xor:N word->N word->N word`,2;
    `word_shl:N word->num->N word`,2; `word_ushr:N word->num->N word`,2;
    `word_ishr:N word->num->N word`,2; `word_zx:N word->M word`,1;
    `word_sx:N word->M word`,1; `iword:int->N word`,1] in
  List.iter (fun (c,n) -> Compute.add_conv (c,n,WORD_RED_CONV) cs) word_ops;
  let num_ops =
   [`(+):num->num->num`,2; `(-):num->num->num`,2; `( * ):num->num->num`,2;
    `(DIV):num->num->num`,2; `(MOD):num->num->num`,2; `(EXP):num->num->num`,2;
    `(<):num->num->bool`,2; `(<=):num->num->bool`,2; `SUC`,1] in
  List.iter (fun (c,n) -> Compute.add_conv (c,n,NUM_RED_CONV) cs) num_ops;
  let int_ops =
   [`(+):int->int->int`,2; `( * ):int->int->int`,2; `(<=):int->int->bool`,2;
    `(<):int->int->bool`,2; `(pow):int->num->int`,2; `(--):int->int`,1] in
  List.iter (fun (c,n) -> Compute.add_conv (c,n,INT_RED_CONV) cs) int_ops;
  Compute.add_conv (`(=):A->A->bool`,2,TISA_EQ_CONV) cs;
  cs;;

let TISA_EVAL_CONV = Compute.CBV_CONV tisa_compset;;
