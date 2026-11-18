(* The emitted publisher loads the reservation count, installs its entries,
   advances the type count, and returns the prepared tail. *)

needs "native/leaves/ty_list/ty_list_commit_loop.ml";;

let ty_list_load_reservations = new_definition
 `ty_list_load_reservations =
    TSeq (TInstr (TLoadFrame TyPtr 6 14))
         (TInstr (TLoad TyU64 8 7 6 6 (&48:int)))`;;

let ty_list_publish_finish = new_definition
 `ty_list_publish_finish =
    TSeq (TInstr (TCmp CondNe TyU64 10 6 (OpImm (word 0))))
      (TSeq
        (TIf 10
          (TSeq (TSeq (TInstr (TLoadFrame TyPtr 9 14))
                       (TInstr (TLoad TyU64 8 7 9 9 (&24:int))))
            (TSeq (TInstr (TBin BinAdd TyU64 9 9 6))
              (TSeq (TInstr (TLoadFrame TyPtr 8 4))
                    (TInstr (TStore 8 2 8 (&0:int) 9)))))
          TSkip)
        (TSeq (TSeq (TInstr (TLoadFrame TyPtr 8 14))
                     (TInstr (TLoad TyU64 8 7 8 8 (&64:int))))
              (TReturn 1 8)))`;;

let TY_LIST_PUBLISH_BLOCKS = prove
 (`ty_list_publish =
    TSeq ty_list_load_reservations
      (TSeq (TCountLoop 5 6 16777216 ty_list_commit_row) ty_list_publish_finish)`,
  REWRITE_TAC[ty_list_publish; ty_list_load_reservations; ty_list_publish_finish]);;

let TY_LIST_LOAD_RESERVATIONS_WP = prove
 (`!st old n. ty_list_commit_ready st old n
      ==> tisa_wp ty_list_load_reservations (ty_list_commit_at st old n 0) (\k u. F) st`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ty_list_commit_ready; ty_list_commit_geometry; ty_list_word] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `val(tisa_base st 7) + val(tisa_len st 7) < 2 EXP 64` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ty_list_load_reservations] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[ty_list_commit_at; ty_list_commit_view; ty_list_commit_prefix] THEN
  TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[]);;

let ty_list_finish_state = new_definition
 `ty_list_finish_state st old n =
    tisa_finst 1 (ty_list_word st 7 64)
       (if n = 0 then st else tisa_store (tisa_base st 2) 8 (word(old + n)) st)`;;

let TY_LIST_FINISH_STATE_VIEW = prove
 (`!st u old n. tregs u 0 = tregs st 0 /\ tmem u = tmem st
       ==> tmem(ty_list_finish_state u old n) = tmem(ty_list_finish_state st old n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TISA_SAME_VIEW) THEN
  REWRITE_TAC[ty_list_finish_state; ty_list_word] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[tisa_finst; tisa_setfword; tisa_frame; TISA_TMEM_STORE; TISA_TREGS_STORE]);;

let TY_LIST_PUBLISH_FINISH_WP = prove
 (`!st old n. ty_list_commit_ready st old n /\ tregs st 6 = word n
      ==> tisa_wp ty_list_publish_finish (\u. F)
           (\k u. k = 1 /\ tregs u 0 = tregs st 0 /\
                  tmem u = tmem(ty_list_finish_state st old n)) st`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ty_list_commit_ready; ty_list_commit_geometry; ty_list_word] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(val(tisa_base st 2) + val(tisa_len st 2) < 2 EXP 64 /\ ty_list_frame_apart st 2) /\
    val(tisa_base st 7) + val(tisa_len st 7) < 2 EXP 64 /\ ty_list_regions_apart st 2 7`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `2 < 3`]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word n:int64) = n /\ ((word n:int64) = word 0 <=> n = 0)`
   STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word n:int64) = n` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0]];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ty_list_frame_apart; ty_list_regions_apart]) THEN
  ASM_CASES_TAC `n = 0` THEN REWRITE_TAC[ty_list_publish_finish] THEN TISA_VCG_TAC THEN
  ASM_REWRITE_TAC[ty_list_finish_state; ty_list_word; GSYM WORD_ADD; TISA_TREGS_FINST] THEN
  TISA_STATE_NORM_TAC THEN
  ASM_REWRITE_TAC[tisa_finst; tisa_setfword; tisa_frame; TISA_TMEM_STORE; TISA_TREGS_STORE;
                  TISA_TMEM_SETREG; TISA_TREGS_SETREG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let ty_list_publish_post = new_definition
 `ty_list_publish_post st old n k u <=>
    k = 1 /\ tregs u 0 = tregs st 0 /\
    tmem u =
      tmem(ty_list_finish_state (TState (tregs st) (ty_list_commit_prefix st old n)) old n)`;;

let TY_LIST_PUBLISH_WP = prove
 (`!st old n. ty_list_commit_ready st old n
      ==> tisa_wp ty_list_publish (\u. F) (ty_list_publish_post st old n) st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[TY_LIST_PUBLISH_BLOCKS; TISA_WP_SEQ] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN EXISTS_TAC `ty_list_commit_at st old n 0` THEN
  EXISTS_TAC `\k:num u:tisa_state. F` THEN BETA_TAC THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC TY_LIST_LOAD_RESERVATIONS_WP THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `v:tisa_state` THEN STRIP_TAC THEN MATCH_MP_TAC TISA_WP_MONO THEN
  EXISTS_TAC `ty_list_commit_at st old n n` THEN EXISTS_TAC `\k:num u:tisa_state. F` THEN
  BETA_TAC THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC TY_LIST_COMMIT_LOOP_WP THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `s:tisa_state` THEN REWRITE_TAC[ty_list_commit_at] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ty_list_commit_ready s old n /\ tregs s 0 = tregs st 0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC (SPECL [`st:tisa_state`; `s:tisa_state`; `old:num`; `n:num`]
                     TY_LIST_READY_AFTER_VIEW) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[ty_list_commit_view] o
        check (fun th -> concl th = `ty_list_commit_view st s`))];
    ALL_TAC] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN EXISTS_TAC `\u:tisa_state. F` THEN
  EXISTS_TAC `\k u. k = 1 /\ tregs u 0 = tregs s 0 /\ tmem u = tmem(ty_list_finish_state s old n)` THEN
  BETA_TAC THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[ty_list_publish_post] THEN
    MATCH_MP_TAC TY_LIST_FINISH_STATE_VIEW THEN ASM_REWRITE_TAC[tregs; tmem];
    MATCH_MP_TAC TY_LIST_PUBLISH_FINISH_WP THEN ASM_REWRITE_TAC[]]);;
