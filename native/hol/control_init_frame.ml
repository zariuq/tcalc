(* Control initialization preserves its caller's frame and fuel receipt. *)
needs "native/hol/control_init_words.ml";;

let CONTROL_PATCH_KEEPS_WORD = prove
 (`!indices base (values:num->int64) m length a.
     val(base:int64) + length < 2 EXP 64 /\ val(a:int64) + 8 <= 2 EXP 64 /\
     (val base + length <= val a \/ val a + 8 <= val base) /\
     ALL (\i. 8 * i + 8 <= length) indices
     ==> drv_word
          (ITLIST (\i mem. write (bytes(word_add base (word(8 * i)),8))
                                (val(values i)) mem) indices m) a = drv_word m a`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[ITLIST];ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ITLIST;ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `val(word_add base (word(8 * h)):int64) = val base + 8 * h`
    ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN
   `drv_word (write (bytes(word_add base (word(8 * h)),8))
                    (val((values:num->int64) h))
                    (ITLIST (\i mem. write (bytes(word_add base (word(8 * i)),8))
                                          (val(values i)) mem) t m)) a =
    drv_word (ITLIST (\i mem. write (bytes(word_add base (word(8 * i)),8))
                                  (val(values i)) mem) t m) a`
    SUBST1_TAC THENL
   [REWRITE_TAC[drv_word] THEN AP_TERM_TAC THEN MATCH_MP_TAC TISA_READ_WRITE_APART THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `length:num` THEN ASM_REWRITE_TAC[]]);;

let CONTROL_INIT_PATCH_FRAME = prove
 (`!t i.
     tisa_entry_ok control_init t /\ i < 24
     ==> tisa_fword
          (TState (tregs t) (control_init_patch (tisa_base t 0) (tisa_fword t 22) (tmem t))) i =
         tisa_fword t i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o MATCH_MP CONTROL_INIT_ENTRY) THEN
  SUBGOAL_THEN `val(word_add (tregs t 0) (word(8 * i)):int64) = val(tregs t 0) + 8 * i`
    ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[tisa_fword;tisa_read;tisa_frame;tregs;tmem;GSYM drv_word;control_init_patch] THEN
  MATCH_MP_TAC CONTROL_PATCH_KEEPS_WORD THEN EXISTS_TAC `val(tisa_len t 0)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC[GSYM ALL_MEM;CONTROL_INDEX_MEMBER] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC]);;

let CONTROL_FRAME_OBSERVE = prove
 (`!s t i. tregs s 0 = tregs t 0 /\ tmem s = tmem t ==> tisa_fword s i = tisa_fword t i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_fword;tisa_read;tisa_frame] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let CONTROL_FRAME_CLOSE_TAC : tactic = fun (asl,w) ->
  let eq = find (fun th -> let c = concl th in is_eq c &&
    lhs c = `tmem (u:tisa_state)` && fst(strip_comb(rhs c)) = `tmem`) (map snd asl) in
  let expected = rand(rhs(concl eq)) and i = rand(lhs w) in
  (TRANS_TAC EQ_TRANS (mk_comb(mk_comb(`tisa_fword`,expected),i)) THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC CONTROL_FRAME_OBSERVE THEN
     ASM_REWRITE_TAC[tisa_finst;tisa_setfword;TISA_TREGS_STORE;tregs];
     ASM_SIMP_TAC[TISA_FWORD_FINST;tregs;CONTROL_INIT_PATCH_FRAME;
                  ARITH_RULE `18 < 24 /\ 19 < 24 /\ 20 < 24 /\ 21 < 24`] THEN
     CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]]) (asl,w);;

let CONTROL_INIT_FRAME_RESULT = prove
 (`!t k u.
     tisa_entry_ok control_init t /\ tisa_run control_init t = TStop k u
     ==> tregs u 0 = tregs t 0 /\
         tisa_fword u 18 = word k /\
         tisa_fword u 19 = (if val(tisa_fword t 22) <= 2 then tisa_fword t 22 else word 0) /\
         tisa_fword u 20 = tisa_fword t 20 /\ tisa_fword u 21 = tisa_fword t 21 /\
         k = (if val(tisa_fword t 22) <= 2 then 1 else 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `tregs u 0 = tregs t 0` ASSUME_TAC THENL
   [MP_TAC(SPECL [`control_init`;`t:tisa_state`;`k:num`;`u:tisa_state`] TISA_RUN_KEEPS) THEN
    ASM_REWRITE_TAC[CONTROL_INIT_LEAF_WF;tisa_keeps] THEN SIMP_TAC[];ALL_TAC] THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o MATCH_MP CONTROL_INIT_ENTRY) THEN
  ASM_CASES_TAC `val(tisa_fword t 22) <= 2` THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] CONTROL_INIT_RUN) THEN
  ASM_REWRITE_TAC[control_init_post] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (REPEAT CONJ_TAC THEN CONTROL_FRAME_CLOSE_TAC));;

let control_init_frame_theorems =
 ["CONTROL_PATCH_KEEPS_WORD",CONTROL_PATCH_KEEPS_WORD;
  "CONTROL_INIT_PATCH_FRAME",CONTROL_INIT_PATCH_FRAME;"CONTROL_FRAME_OBSERVE",CONTROL_FRAME_OBSERVE;
  "CONTROL_INIT_FRAME_RESULT",CONTROL_INIT_FRAME_RESULT];;
