(* Every other complete table word is preserved by put_word, including the *)
(* unpublished tail. The program and entry/geometry facts are the existing *)
(* leaf's; this strengthens its postcondition without replacing its model. *)

needs "native/leaves/put_word/put_word.ml";;

let put_word_frame_post = new_definition
 `put_word_frame_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    (if val(tisa_fword t 22) < val(tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8) /\
        val(tregs t 2) < val(tregs t 1) /\
        8 * val(tregs t 1) * val(tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8) <=
        val(tisa_len t 0)
     then k = 1 /\ tisa_fword u 19 = tisa_fword t 23 /\
          tisa_read u (word_add (tisa_base u 0)
                        (word(8 * (val(tregs t 1) * val(tisa_fword t 22) + val(tregs t 2))))) 8 =
          tisa_fword t 23 /\
          (!j. 8 * j + 8 <= val(tisa_len t 0) /\
               ~(j = val(tregs t 1) * val(tisa_fword t 22) + val(tregs t 2))
               ==> tisa_read u (word_add (tisa_base u 0) (word(8 * j))) 8 =
                   tisa_read t (word_add (tisa_base t 0) (word(8 * j))) 8)
     else k = 2 /\
          (!j. 8 * j + 8 <= val(tisa_len t 0)
               ==> tisa_read u (word_add (tisa_base u 0) (word(8 * j))) 8 =
                   tisa_read t (word_add (tisa_base t 0) (word(8 * j))) 8))`;;

let PUT_WORD_FRAME_STOP_TAC =
  REWRITE_TAC[put_word_frame_post] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  LEAF_VAL_NUMERALS_TAC THEN TISA_STATE_NORM_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  W(fun (asl,w) ->
    if is_forall w then PUT_WORD_KEPT_TAC
    else FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
         FIRST [ASM_ARITH_TAC; PUT_WORD_GUARD_TAC]);;

let PUT_WORD_FRAME_CHECKS_WP = prove
 (`!t. tisa_entry_ok put_word t
       ==> tisa_wp put_word_checks (put_word_mid t) (put_word_frame_post t) t`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PUT_WORD_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[put_word_checks] THEN TISA_VCG_TAC THEN
  FIRST [PUT_WORD_FRAME_STOP_TAC THEN NO_TAC; PUT_WORD_CONT_TAC THEN NO_TAC]);;

(* The access: the value stored at word s i + w, inside the table. *)
let PUT_WORD_FRAME_ACCESS_WP = prove
 (`!t s. val(tregs t 0) + 192 <= 2 EXP 64 /\
         val(tisa_base t 0) + val(tisa_len t 0) < 2 EXP 64 /\
         (val(tisa_len t 0) = 0 \/
          val(tisa_base t 0) + val(tisa_len t 0) <= val(tregs t 0) \/
          val(tregs t 0) + 192 <= val(tisa_base t 0)) /\
         put_word_mid t s
         ==> tisa_wp put_word_access (\s. F) (put_word_frame_post t) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[put_word_mid] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:tisa_state`; `t:tisa_state`] TISA_SAME_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`val(tregs t 1)`; `val(tisa_fword t 22)`; `val(tregs t 2)`;
                `val(tisa_read t (tisa_base t 1) 8)`; `val(tisa_len t 0)`] LEAF_ROW_INDEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_mul (tregs t 1) (tisa_fword t 22)) = val(tregs t 1) * val(tisa_fword t 22)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LEAF_VAL_MUL_EXACT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add (word_mul (tregs t 1) (tisa_fword t 22)) (tregs t 2)) =
                val(tregs t 1) * val(tisa_fword t 22) + val(tregs t 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD_ADD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[put_word_access] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[put_word_frame_post] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * j + 8 <= val(tisa_len t 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 * j + 8 <= 8 * (val(tregs t 1) * val(tisa_fword t 22) + val(tregs t 2)) \/
                8 * (val(tregs t 1) * val(tisa_fword t 22) + val(tregs t 2)) + 8 <= 8 * j`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  TISA_STATE_NORM_TAC);;

let PUT_WORD_FRAME_WP = prove
 (`!t. tisa_entry_ok put_word t ==> tisa_wp (tisa_root put_word) (\s. F) (put_word_frame_post t) t`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[put_word; tisa_root; TISA_WP_SEQ] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  MAP_EVERY EXISTS_TAC [`put_word_mid t`; `put_word_frame_post t`] THEN
  ASM_SIMP_TAC[PUT_WORD_FRAME_CHECKS_WP] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PUT_WORD_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PUT_WORD_FRAME_ACCESS_WP THEN ASM_REWRITE_TAC[]);;

let PUT_WORD_FRAME_RUN = prove
 (`!t k u. tisa_entry_ok put_word t /\ tisa_run put_word t = TStop k u ==> put_word_frame_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; PUT_WORD_FRAME_WP]);;

let put_word_frame_theorems =
 ["put_word_frame_post",put_word_frame_post;
  "PUT_WORD_FRAME_CHECKS_WP",PUT_WORD_FRAME_CHECKS_WP;
  "PUT_WORD_FRAME_ACCESS_WP",PUT_WORD_FRAME_ACCESS_WP;
  "PUT_WORD_FRAME_WP",PUT_WORD_FRAME_WP;
  "PUT_WORD_FRAME_RUN",PUT_WORD_FRAME_RUN];;
