(* Preparation preserves the layout and the old count. Publication installs
   the prepared entries and returns the tail's row ID. *)

needs "native/leaves/ty_list/ty_list_prepare.ml";;
needs "native/leaves/ty_list/ty_list_publish.ml";;

let TY_LIST_PREPARED_LAYOUT = prove
 (`!st. tisa_entry_ok ty_list st
      ==> let u = tisa_state_of(tisa_exec ty_list_prepare st) in
          ty_list_commit_geometry u /\ ty_list_word u 2 0 = ty_list_word st 2 0`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `u = tisa_state_of(tisa_exec ty_list_prepare st)` THEN
  SUBGOAL_THEN `ty_list_commit_geometry st /\ tisa_frame_sep ty_list_scratch_decls st /\
                tisa_keeps ty_list_scratch_decls st u` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_SIMP_TAC[TY_LIST_COMMIT_GEOMETRY_ENTRY;
     TY_LIST_PREPARE_ENTRY; TY_LIST_PREPARE_FRAME]; ALL_TAC] THEN
  SUBGOAL_THEN `tregs u 0 = tregs st 0` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[tisa_keeps] o
      check (fun th -> concl th = `tisa_keeps ty_list_scratch_decls st u`));
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r < 8 ==> tisa_base u r = tisa_base st r /\ tisa_len u r = tisa_len st r`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_base; tisa_len] THEN
    MATCH_MP_TAC (SPECL [`ty_list_scratch_decls`; `st:tisa_state`; `u:tisa_state`]
                   TISA_FWORD_KEEP) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `ty_list_commit_geometry st`)) THEN
    REWRITE_TAC[ty_list_commit_geometry; ty_list_frame_apart; ty_list_regions_apart] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < 8 /\ 1 < 8 /\ 2 < 8 /\ 7 < 8`;
      ARITH_RULE `r < 3 \/ r = 7 ==> r < 8`; ARITH_RULE `r < 3 ==> r < 8`];
    REWRITE_TAC[ty_list_word; tisa_read] THEN ASM_SIMP_TAC[ARITH_RULE `2 < 8`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[READ_BYTES_EQ; TISA_WORD_ADD_OFFSETS; ADD_CLAUSES] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(tisa_base st 2) + val(tisa_len st 2) < 2 EXP 64 /\
                  8 <= val(tisa_len st 2)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ty_list_commit_geometry; ARITH_RULE `2 < 3`]; ALL_TAC] THEN
    EXPAND_TAC "u" THEN
    MATCH_MP_TAC (SPECL [`st:tisa_state`; `2`; `word_add (tisa_base st 2) (word j):int64`]
                   TY_LIST_PREPARE_TABLE_FRAME) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 < 3`] THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 2) (word j):int64) = val(tisa_base st 2) + j`
     SUBST1_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let TY_LIST_PUBLISH_RUN = prove
 (`!st u old n.
      tisa_entry_ok ty_list st /\ tisa_exec ty_list_prepare st = TCont u /\
      ty_list_commit_ready u old n
      ==> ?v. tisa_run ty_list st = TStop 1 v /\ ty_list_publish_post u old n 1 v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:tisa_state`; `old:num`; `n:num`] TY_LIST_PUBLISH_WP) THEN
  ASM_REWRITE_TAC[tisa_run; TY_LIST_SPLIT_EXEC; tisa_then; tisa_wp] THEN
  MP_TAC(ISPEC `tisa_exec ty_list_publish u` TISA_RESULT_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `u':tisa_state` SUBST1_TAC)
     (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u':tisa_state` SUBST1_TAC))) THEN
  REWRITE_TAC[tisa_then; TISA_RWP_CONT; TISA_RWP_STOP; ty_list_publish_post] THEN
  MESON_TAC[]);;
