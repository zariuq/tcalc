(* An exact unsigned comparison guard for procedure clauses. *)
needs "native/leaves/common/leaf_lib.ml";;
needs "native/leaves/relw/relw_program.ml";;

let RELW_DECLS = prove
 (`tisa_decls relw = []`,REWRITE_TAC[RELW_TERM;tisa_decls]);;
let RELW_LEAF_WF = prove
 (`tisa_leaf_wf relw`,LEAF_WF_TAC RELW_DECLS RELW_TERM);;

let relw_mask = new_definition
 `relw_mask (a:int64) (b:int64) (mask:int64) <=>
    if val a < val b then ~(word_and mask (word 1) = word 0)
    else if a = b then ~(word_and mask (word 2) = word 0)
    else ~(word_and mask (word 4) = word 0)`;;

let relw_post = new_definition
 `relw_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 20 = tisa_fword t 20 /\
    tisa_fword u 21 = tisa_fword t 21 /\
    (if relw_mask (tisa_fword t 22) (tisa_fword t 23) (tregs t 1)
     then k = 1 /\ tisa_fword u 19 = tisa_fword t 22
     else k = 0 /\ tisa_fword u 19 = word 0)`;;

let RELW_WP = prove
 (`!t. tisa_entry_ok relw t ==> tisa_wp (tisa_root relw) (\s. F) (relw_post t) t`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP LEAF_ENTRY_FRAME) THEN
  REWRITE_TAC[RELW_TERM;tisa_root] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[relw_post;relw_mask] THEN TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[LT_REFL]);;

let RELW_RUN = prove
 (`!t k u. tisa_entry_ok relw t /\ tisa_run relw t = TStop k u ==> relw_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP;RELW_WP]);;

let RELW_OUTCOMES = prove
 (`!t k u. tisa_entry_ok relw t /\ tisa_run relw t = TStop k u
     ==> (k = 1 <=> relw_mask (tisa_fword t 22) (tisa_fword t 23) (tregs t 1)) /\
         (k = 0 <=> ~relw_mask (tisa_fword t 22) (tisa_fword t 23) (tregs t 1)) /\
         tisa_fword u 20 = tisa_fword t 20 /\ tisa_fword u 21 = tisa_fword t 21`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] RELW_RUN) THEN
  ASM_REWRITE_TAC[relw_post] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ]);;

let RELW_MASK_BITS = prove
 (`!mask:int64.
    (~(word_and mask (word 1) = word 0) <=> ODD(val mask)) /\
    (~(word_and mask (word 2) = word 0) <=> ODD(val mask DIV 2)) /\
    (~(word_and mask (word 4) = word 0) <=> ODD(val mask DIV 4))`,
  GEN_TAC THEN
  MAP_EVERY (fun n ->
    MP_TAC(CONV_RULE NUM_REDUCE_CONV
      (ISPECL [`mask:int64`;mk_small_numeral n] (CONJUNCT1 WORD_AND_POW2))) THEN
    REWRITE_TAC[BIT_VAL] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN DISCH_THEN SUBST1_TAC) [0;1;2] THEN
  REWRITE_TAC[bitval] THEN REPEAT COND_CASES_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  ASM_REWRITE_TAC[]);;

let RELW_MASK_NUMERIC = prove
 (`!a b mask:int64. relw_mask a b mask <=>
    val a < val b /\ ODD(val mask) \/
    val a = val b /\ ODD(val mask DIV 2) \/
    val b < val a /\ ODD(val mask DIV 4)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[relw_mask;RELW_MASK_BITS;GSYM VAL_EQ] THEN
  ASM_CASES_TAC `val(a:int64) < val(b:int64)` THENL
   [ASM_SIMP_TAC[ARITH_RULE `x < y ==> ~(x = y) /\ ~(y < x)`];ALL_TAC] THEN
  ASM_CASES_TAC `val(a:int64) = val(b:int64)` THENL
   [ASM_REWRITE_TAC[LT_REFL];ALL_TAC] THEN
  SUBGOAL_THEN `val(b:int64) < val(a:int64)` ASSUME_TAC THENL
   [ASM_ARITH_TAC;ASM_REWRITE_TAC[]]);;

let relw_theorems =
 ["RELW_DECLS",RELW_DECLS;"RELW_LEAF_WF",RELW_LEAF_WF;
  "RELW_WP",RELW_WP;"RELW_RUN",RELW_RUN;"RELW_OUTCOMES",RELW_OUTCOMES;
  "RELW_MASK_BITS",RELW_MASK_BITS;"RELW_MASK_NUMERIC",RELW_MASK_NUMERIC];;
