(* Semantic row validity and source-index bounds during the binding walk. *)
needs "native/hol/bind_walk_intern_rows.ml";;

let bwt_input = new_definition
 `bwt_input nms tys st <=>
    bw_rows_valid nms tys (bw_rows st (val(intern_count st))) /\
    ?TY X. bw_ctx nms tys (val(tisa_fword st 22)) (val(tisa_fword st 23)) TY /\
           fddb nms tys (bw_rows st (val(intern_count st))) (val(tregs st 1)) X`;;

let bw_task_bounds = new_definition
 `bw_task_bounds st s <=>
    !e. e < val(bw_w s 1) ==> val(bw_ent s 0 e 1) < val(intern_count st)`;;

let bwt_mid = new_definition
 `bwt_mid nms tys st s <=>
    bw_mid st s /\ bw_rows_valid nms tys (bw_rows s (val(bw_w s 0))) /\ bw_task_bounds st s`;;

let bwt_tail = new_definition
 `bwt_tail nms tys st s <=>
    bw_tail_pre st s /\ bwt_mid nms tys st s /\
    (~(tregs s 9 = word 0)
     ==> (val(bw_w s 8) = 2 \/ val(bw_w s 8) < 2 /\
          ?X. fddb nms tys (bw_rows st (val(intern_count st))) (val(bw_w s 6)) X) /\
         (val(tregs s 1) MOD 8 = 1 ==> val(tregs s 2) = 0))`;;

let bwt_result = new_definition
 `bwt_result nms tys st k s <=>
    bw_result st k s /\ (k = 1 ==> bw_rows_valid nms tys (bw_rows s (val(intern_count s))))`;;

let BW_TASK_WORD_BOUND = prove
 (`!L e. 256 <= L /\ e < L DIV 128 - 1
         ==> 8 * (16 + 4 * e + 1) + 8 <= L`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:num`;`128`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN ASM_ARITH_TAC);;

let BWT_MID_SAME = prove
 (`!nms tys st s u.
     tregs u 0 = tregs s 0 /\ tmem u = tmem s
     ==> (bwt_mid nms tys st u <=> bwt_mid nms tys st s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BW_SAME_VIEWS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(SPECL [`st:tisa_state`;`s:tisa_state`;`u:tisa_state`] BW_MID_SAME)) THEN
  ASM_REWRITE_TAC[bwt_mid;bw_task_bounds;bw_ent]);;

let BWT_MID_TRANSFER = prove
 (`!nms tys st s u.
     bwt_mid nms tys st s /\ bw_mid st u /\ bw_w u 0 = bw_w s 0 /\
     (!i. i < 2 * val(bw_w s 0) ==> intern_word u i = intern_word s i) /\
     val(bw_w u 1) <= val(bw_w s 1) /\
     (!e. e < val(bw_w u 1) ==> bw_ent u 0 e 1 = bw_ent s 0 e 1)
     ==> bwt_mid nms tys st u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bwt_mid;bw_task_bounds] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `bw_rows u (val(bw_w s 0)) = bw_rows s (val(bw_w s 0))` SUBST1_TAC THENL
     [MATCH_MP_TAC BW_ROWS_EQ THEN ASM_REWRITE_TAC[];ASM_REWRITE_TAC[]];
    X_GEN_TAC `e:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let BWT_MID_INIT = prove
 (`!nms tys st s.
     bwt_input nms tys st /\ bw_mid st s /\ bw_w s 0 = intern_count st /\
     (!i. i < 2 * val(intern_count st) ==> intern_word s i = intern_word st i) /\
     bw_w s 1 = word 1 /\ bw_ent s 0 0 1 = tregs st 1
     ==> bwt_mid nms tys st s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bwt_input;bwt_mid;bw_task_bounds] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VAL_WORD_1] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `bw_rows s (val(intern_count st)) = bw_rows st (val(intern_count st))`
      SUBST1_TAC THENL
     [MATCH_MP_TAC BW_ROWS_EQ THEN ASM_REWRITE_TAC[];ASM_REWRITE_TAC[]];
    X_GEN_TAC `e:num` THEN REWRITE_TAC[ARITH_RULE `e < 1 <=> e = 0`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`nms:string list`;`tys:(num#num#num)list`;
                  `bw_rows st (val(intern_count st))`;`val(tregs st 1)`;`X:hdbterm`] FDDB_LT) THEN
    ASM_REWRITE_TAC[LENGTH_BW_ROWS]]);;

let BW_AFTER_INTERN_WORK_WORD = prove
 (`!st s u k.
     bw_mid st s /\ bw_after_intern s u /\
     0 < k /\ 8 * k + 8 <= val(tisa_len st 3) ==> bw_w u k = bw_w s k`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_mid] o
    check (fun th -> concl th = `bw_mid st s`)) THEN
  FIRST_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o REWRITE_RULE[bw_after_intern] o
    check (fun th -> concl th = `bw_after_intern s u`)) THEN
  SUBGOAL_THEN `tisa_len s 3 = tisa_len st 3` ASSUME_TAC THENL
   [REWRITE_TAC[tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[ARITH_RULE `7 < 24`];ALL_TAC] THEN
  FIND_ASSUM (MATCH_MP_TAC o REWRITE_RULE[ASSUME `tisa_len s 3 = tisa_len st 3`])
     `!k. 0 < k /\ 8 * k + 8 <= val(tisa_len s 3)
          ==> bw_w u k = bw_w s k` THEN ASM_REWRITE_TAC[]);;

let BW_AFTER_INTERN_TASK_WORDS = prove
 (`!st s u.
     bw_regions st /\ bw_mid st s /\ bw_after_intern s u
     ==> bw_w u 1 = bw_w s 1 /\
         (!e. e < val(bw_w s 1) ==> bw_ent u 0 e 1 = bw_ent s 0 e 1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_mid] o
    check (fun th -> concl th = `bw_mid st s`)) THEN
  BW_REGIONS_TAC THEN
  SUBGOAL_THEN `!k. 0 < k /\ 8 * k + 8 <= val(tisa_len st 3)
                    ==> bw_w u k = bw_w s k` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN MATCH_MP_TAC BW_AFTER_INTERN_WORK_WORD THEN
    EXISTS_TAC `st:tisa_state` THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `bw_w u 1 = bw_w s 1 /\ bw_w u 4 = bw_w s 4`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(ASSUME `!k. 0 < k /\ 8 * k + 8 <= val(tisa_len st 3)
                             ==> bw_w u k = bw_w s k`) THEN
    MP_TAC(ASSUME `256 <= val(tisa_len st 3)`) THEN ARITH_TAC;ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[bw_ent;MULT_CLAUSES;ADD_CLAUSES] THEN
  MATCH_MP_TAC(ASSUME `!k. 0 < k /\ 8 * k + 8 <= val(tisa_len st 3)
                           ==> bw_w u k = bw_w s k`) THEN
  CONJ_TAC THENL [ARITH_TAC;ALL_TAC] THEN
  MATCH_MP_TAC BW_TASK_WORD_BOUND THEN
  SUBGOAL_THEN `e < val(bw_w s 4)` ASSUME_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME)
     [`e < val(bw_w s 1)`;`val(bw_w s 1) <= val(bw_w s 4)`] THEN ARITH_TAC;
    REWRITE_TAC[GSYM(ASSUME
      `val(bw_w s 4) = val(tisa_len st 3) DIV 128 - 1`)] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let BWT_MID_INTERNED = prove
 (`!nms tys st s u.
     bw_regions st /\ bwt_mid nms tys st s /\ bw_after_intern s u /\
     bw_row_admissible nms tys (bw_rows s (val(bw_w s 0)))
       (val(tregs s 1) MOD 8,val(tregs s 1) DIV 8,val(tregs s 2))
     ==> bwt_mid nms tys st u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bwt_mid] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BW_MID_INTERNED THEN EXISTS_TAC `s:tisa_state` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC BW_AFTER_INTERN_ROWS_VALID THEN EXISTS_TAC `s:tisa_state` THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`st:tisa_state`;`s:tisa_state`;`u:tisa_state`] BW_AFTER_INTERN_TASK_WORDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[bw_task_bounds] THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[bw_task_bounds]]);;

let BWT_RESOK_DECODES = prove
 (`!nms tys st m i n D r.
     bwt_input nms tys st /\ bw_resok st m i n D r /\
     (m = 2 \/
      m < 2 /\ ?X. fddb nms tys (bw_rows st (val(intern_count st))) i X)
     ==> ?U. fddb nms tys D r U`,
  REWRITE_TAC[bwt_input;bw_resok;bw_claim;bw_final] THEN MESON_TAC[]);;

let BWT_INTERN_POST_DECODES = prove
 (`!nms tys st s u.
     bw_regions st /\ bwt_input nms tys st /\ bwt_tail nms tys st s /\
     ~(tregs s 9 = word 0) /\ bw_after_intern s u
     ==> ?X. fddb nms tys (bw_rows u (val(bw_w u 0))) (val(tregs u 5)) X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o REWRITE_RULE[bwt_tail] o
    check (fun th -> concl th = `bwt_tail nms tys st s`)) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[bwt_mid] o
    check (fun th -> concl th = `bwt_mid nms tys st s`)) THEN
  MP_TAC(SPECL [`st:tisa_state`;`s:tisa_state`;`u:tisa_state`] BW_POST_PRE_INTERNED) THEN
  ASM_REWRITE_TAC[bw_post_pre] THEN STRIP_TAC THEN
  SUBGOAL_THEN `bw_w u 6 = bw_w s 6 /\ bw_w u 8 = bw_w s 8` STRIP_ASSUME_TAC THENL
   [BW_REGIONS_TAC THEN CONJ_TAC THEN MATCH_MP_TAC BW_AFTER_INTERN_WORK_WORD THEN
    EXISTS_TAC `st:tisa_state` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `256 <= val(tisa_len st 3)`) THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[ASSUME `bw_w u 6 = bw_w s 6`;
        ASSUME `bw_w u 8 = bw_w s 8`] o
    check (fun th -> fst(strip_comb(concl th)) = `bw_resok`)) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
     (fun th -> MP th (ASSUME `~(tregs s 9 = word 0)`)) o
     check (fun th -> is_imp(concl th) && lhand(concl th) = `~(tregs s 9 = word 0)`)) THEN
  MATCH_MP_TAC(SPECL [`nms:string list`;`tys:(num#num#num)list`;`st:tisa_state`;
                      `val(bw_w s 8)`;`val(bw_w s 6)`;`val(bw_w u 7)`;
                      `bw_rows u (val(bw_w u 0))`;`val(tregs u 5)`] BWT_RESOK_DECODES) THEN
  ASM_REWRITE_TAC[]);;

(* The old table suffices on a hit. An append must be a decodable key at the
   returned row. This covers the actual row that the inline interner wrote. *)
let BWT_INTERN_FRAME = prove
 (`!nms tys st s u.
     bw_regions st /\ bwt_mid nms tys st s /\ bw_after_intern s u /\
     bw_rows_valid nms tys (bw_rows u (val(bw_w u 0)))
     ==> bwt_mid nms tys st u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bwt_mid] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BW_MID_INTERNED THEN EXISTS_TAC `s:tisa_state` THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`st:tisa_state`;`s:tisa_state`;`u:tisa_state`] BW_AFTER_INTERN_TASK_WORDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[bw_task_bounds] THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[bw_task_bounds]]);;

let BWT_INTERNED_FROM_RESULT = prove
 (`!nms tys st s u.
     bw_regions st /\ bwt_input nms tys st /\ bwt_tail nms tys st s /\
     ~(tregs s 9 = word 0) /\ bw_after_intern s u
     ==> bwt_mid nms tys st u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o REWRITE_RULE[bwt_tail] o
     check (fun th -> concl th = `bwt_tail nms tys st s`)) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[bwt_mid] o
     check (fun th -> concl th = `bwt_mid nms tys st s`)) THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o REWRITE_RULE[bw_after_intern] o
     check (fun th -> concl th = `bw_after_intern s u`)) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[bwt_mid] o
     check (fun th -> concl th = `bwt_mid nms tys st s`)) THEN
  MATCH_MP_TAC BWT_INTERN_FRAME THEN EXISTS_TAC `s:tisa_state` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`s:tisa_state`;`u:tisa_state`] BW_AFTER_INTERN_ROWS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> ASM_REWRITE_TAC[th]) (LABEL_TAC "append")) THEN
  MP_TAC(SPECL [`nms:string list`;`tys:(num#num#num)list`;`st:tisa_state`;
                  `s:tisa_state`;`u:tisa_state`] BWT_INTERN_POST_DECODES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `X:hdbterm`) THEN
  USE_THEN "append" (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC BW_ROWS_VALID_APPEND THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC BW_LAST_TERM_ADMISSIBLE THEN EXISTS_TAC `X:hdbterm` THEN
  SUBGOAL_THEN `~(val(bw_w u 0) = val(bw_w s 0))` ASSUME_TAC THENL
   [USE_THEN "append" (MP_TAC o AP_TERM `LENGTH:(num#num#num)list->num`) THEN
    REWRITE_TAC[LENGTH_BW_ROWS;LENGTH_APPEND;LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(tregs u 5) = val(bw_w s 0)` ASSUME_TAC THENL
   [FIND_ASSUM (MP_TAC o REWRITE_RULE[ASSUME `~(val(bw_w u 0) = val(bw_w s 0))`])
     `val(bw_w u 0) = val(bw_w s 0) \/ val(tregs u 5) = val(bw_w s 0)` THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT2 o
     (fun th -> MP th (ASSUME `~(tregs s 9 = word 0)`)) o
     check (fun th -> is_imp(concl th) && lhand(concl th) = `~(tregs s 9 = word 0)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[ASSUME `val(tregs u 5) = val(bw_w s 0)`] o
     check (fun th -> fst(strip_comb(concl th)) = `fddb`)) THEN
  ASM_REWRITE_TAC[LENGTH_BW_ROWS;FST;SND]);;

let BWT_INTERN_WP = prove
 (`!nms tys st s.
     bw_regions st /\ bwt_input nms tys st /\ bwt_tail nms tys st s /\
     ~(tregs s 9 = word 0)
     ==> tisa_wp bw_intern (bwt_mid nms tys st) (bw_result st) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC BW_INTERN_WP THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC;ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[bwt_tail;bwt_mid];ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BWT_INTERNED_FROM_RESULT THEN
  EXISTS_TAC `s:tisa_state` THEN ASM_REWRITE_TAC[]);;

(* Publication changes the count and frame receipt, exposing exactly the
   private table already checked by the invariant. *)
let BW_PUBLISHED_ROWS = prove
 (`!st s X r.
     bw_regions st /\ bw_mid st s /\ tregs X 0 = tregs st 0 /\ tmem X = tmem s
     ==> let u = tisa_finst 1 r
                   (tisa_store (tisa_base st 2) 8 (bw_w s 0) X) in
         bw_rows u (val(intern_count u)) = bw_rows s (val(bw_w s 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF;LET_END_DEF] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BW_MID_FACTS_TAC `s:tisa_state` THEN BW_REGIONS_TAC THEN
  MP_TAC(ISPECL [`X:tisa_state`;`s:tisa_state`] BW_SAME_VIEWS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[];STRIP_TAC] THEN
  MP_TAC(SPECL [`st:tisa_state`;`X:tisa_state`;`bw_w s 0`] BW_HDR_STORE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN
  ABBREV_TAC `Y = tisa_store (tisa_base st 2) 8 (bw_w s 0) X` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`st:tisa_state`;`Y:tisa_state`;`1`;`r:int64`] BW_FINST_KEEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[];ALL_TAC] THEN
  ABBREV_TAC `Z = tisa_finst 1 r Y` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BW_ROWS_EQ THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `i < 2 * (val(tisa_len st 0) DIV 16) /\ 8 * i + 8 <= val(tisa_len st 0)`
    STRIP_ASSUME_TAC THENL [BW_ARITH_TAC;ASM_SIMP_TAC[]]);;

let BWT_PUBLISH_RESULT = prove
 (`!nms tys st s X (c:int64) (r:int64).
     bw_regions st /\ bwt_mid nms tys st s /\
     tregs X 0 = tregs st 0 /\ tmem X = tmem s /\
     c = bw_w s 0 /\ val r < val(bw_w s 0) /\
     bw_final (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
         (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val(tregs st 1)) (val r)
     ==> bwt_result nms tys st 1 (tisa_finst 1 r (tisa_store (tisa_base st 2) 8 c X))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bwt_mid] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `c:int64 = bw_w s 0`)) THEN
  REWRITE_TAC[bwt_result] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BW_PUBLISH_RESULT THEN EXISTS_TAC `s:tisa_state` THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`st:tisa_state`;`s:tisa_state`;`X:tisa_state`;`r:int64`]
          BW_PUBLISHED_ROWS) THEN ASM_REWRITE_TAC[LET_DEF;LET_END_DEF] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let BWT_PUBLISH_WP = prove
 (`!nms tys st s.
     bw_regions st /\ bw_entered st /\ bwt_mid nms tys st s /\
     bw_post_pre st s /\ val(bw_w s 8) = 2 /\ tregs s 2 = tisa_base st 3
     ==> tisa_wp bw_publish (\u. F) (bwt_result nms tys st) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o REWRITE_RULE[bw_post_pre] o
    check (fun th -> concl th = `bw_post_pre st s`)) THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
    REWRITE_RULE[bw_resok;ASSUME `val(bw_w s 8) = 2`;ARITH_EQ;LENGTH_BW_ROWS] o
    check (fun th -> fst(strip_comb(concl th)) = `bw_resok`)) THEN
  BW_BLOCK_SETUP_TAC `s:tisa_state` THEN
  REWRITE_TAC[bw_publish] THEN TISA_VCG_TAC THEN
  W(fun (_,w) ->
    if can (find_term ((=) `tisa_store (tisa_base st 2)`)) w then
      MATCH_MP_TAC BWT_PUBLISH_RESULT THEN EXISTS_TAC `s:tisa_state` THEN
      REPEAT CONJ_TAC THEN TISA_STATE_NORM_TAC THEN
      REWRITE_TAC[TISA_TMEM_SETREG] THEN ASM_REWRITE_TAC[]
    else REWRITE_TAC[bwt_result;ARITH_EQ] THEN BW_STOP_LEAF_TAC));;

let bind_walk_table_invariant_theorems =
 ["BW_TASK_WORD_BOUND",BW_TASK_WORD_BOUND;"BWT_MID_SAME",BWT_MID_SAME;
  "BWT_MID_TRANSFER",BWT_MID_TRANSFER;"BWT_MID_INIT",BWT_MID_INIT;
  "BW_AFTER_INTERN_WORK_WORD",BW_AFTER_INTERN_WORK_WORD;
  "BW_AFTER_INTERN_TASK_WORDS",BW_AFTER_INTERN_TASK_WORDS;"BWT_MID_INTERNED",BWT_MID_INTERNED;
  "BWT_RESOK_DECODES",BWT_RESOK_DECODES;"BWT_INTERN_POST_DECODES",BWT_INTERN_POST_DECODES;
  "BWT_INTERN_FRAME",BWT_INTERN_FRAME;
  "BWT_INTERNED_FROM_RESULT",BWT_INTERNED_FROM_RESULT;"BWT_INTERN_WP",BWT_INTERN_WP;
  "BW_PUBLISHED_ROWS",BW_PUBLISHED_ROWS;"BWT_PUBLISH_RESULT",BWT_PUBLISH_RESULT;
  "BWT_PUBLISH_WP",BWT_PUBLISH_WP];;
