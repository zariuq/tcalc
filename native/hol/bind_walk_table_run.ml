(* Carry the semantic row and task invariants through the walk's blocks. *)
needs "native/hol/bind_walk_table_invariant.ml";;
needs "native/driver/driver_leaf.ml";;

let BWT_MID_SETREG = prove
 (`!nms tys st (s:tisa_state) d (v:int64).
     ~(d = 0) /\ bwt_mid nms tys st s
     ==> bwt_mid nms tys st (tisa_setreg d v s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`nms:string list`;`tys:(num#num#num)list`;`st:tisa_state`;
    `s:tisa_state`;`tisa_setreg d v s`] BWT_MID_SAME) THEN
  ASM_REWRITE_TAC[TISA_TREGS_SETREG;TISA_TMEM_SETREG;ARITH_RULE `0 = d <=> d = 0`]);;

let BW_TASKS_FROM_PREFIX = prove
 (`!st s u.
     bw_task_bounds st s /\ val(bw_w u 1) <= val(bw_w s 1) /\
     (!e. e < val(bw_w u 1) ==> bw_ent u 0 e 1 = bw_ent s 0 e 1)
     ==> bw_task_bounds st u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_task_bounds] THEN STRIP_TAC THEN
  X_GEN_TAC `e:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* A block which only changes registers and work words leaves the table
   encoding alone. Prove the task bound separately, by reading just the
   active task fields through those stores. *)
let BWT_TASK_PREFIX_TAC u =
  let count = mk_eq(list_mk_comb(`bw_w`,[u;`1`]), `bw_w s 1`) in
  SUBGOAL_THEN count ASSUME_TAC THENL
   [BW_EVAL_TAC THEN REFL_TAC;ALL_TAC] THEN
  MATCH_MP_TAC BW_TASKS_FROM_PREFIX THEN EXISTS_TAC `s:tisa_state` THEN
  ASM_REWRITE_TAC[LE_REFL] THEN X_GEN_TAC `e:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `8 * (16 + 4 * e + 1) + 8 <= val(tisa_len st 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC BW_TASK_WORD_BOUND THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY (MP_TAC o ASSUME)
       [`e < val(bw_w s 1)`;`val(bw_w s 1) <= val(bw_w s 4)`;
        `val(bw_w s 4) = val(tisa_len st 3) DIV 128 - 1`] THEN ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[bw_ent;MULT_CLAUSES;ADD_CLAUSES] THEN BW_EVAL_TAC THEN REFL_TAC;;

let BWT_POST_SPLIT_TAC claim_tac = W(fun (_,w) ->
  let u = rand w in
  REWRITE_TAC[bwt_mid] THEN CONJ_TAC THENL
   [BW_PEEL_MID_GEN_TAC claim_tac;
    CONJ_TAC THENL
     [BW_EVAL_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      BWT_TASK_PREFIX_TAC u]]);;

let BWT_POST_SETUP_TAC =
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o REWRITE_RULE[bwt_mid] o
    check (fun th -> concl th = `bwt_mid nms tys st s`)) THEN
  BW_BLOCK_SETUP_TAC `s:tisa_state`;;

(* Use the same focused arithmetic as the base walk proof. *)
let BWT_FOCUS_TAC tac : tactic = fun g ->
  let old = !tisa_arith_focus in
  tisa_arith_focus := true;
  Fun.protect ~finally:(fun () -> tisa_arith_focus := old)
    (fun () -> tac g);;

let BWT_VCG_TAC = BWT_FOCUS_TAC TISA_VCG_TAC;;

let BW_NCLAIM_MEMO_TAC =
  REWRITE_TAC[bw_nclaim] THEN BW_EVAL_TAC THEN
  CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN FIRST_ASSUM ACCEPT_TAC;;

let BWT_MEMO_WP = prove
 (`!nms tys st s.
     bw_regions st /\ bw_entered st /\ bwt_mid nms tys st s /\
     tregs s 2 = tisa_base st 3 /\
     bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
       (val(tisa_fword st 22)) (val(tisa_fword st 23))
       (val(tregs s 7)) (val(tregs s 8)) (val(tregs s 5))
     ==> tisa_wp bw_memo (bwt_mid nms tys st) (bwt_result nms tys st) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BWT_POST_SETUP_TAC THEN
  REWRITE_TAC[bw_memo] THEN BWT_VCG_TAC THEN
  W(fun (_,w) ->
    if fst(strip_comb w) = `bwt_result` then
      REWRITE_TAC[bwt_result;ARITH_EQ] THEN BW_STOP_LEAF_TAC
    else BWT_POST_SPLIT_TAC BW_NCLAIM_MEMO_TAC));;

(* Publish or record the processed result. *)

let BW_POST_PRE_SAME = prove
 (`!st s u. tregs u 0 = tregs s 0 /\ tmem u = tmem s /\ tregs u 5 = tregs s 5
             ==> (bw_post_pre st u <=> bw_post_pre st s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:tisa_state`; `s:tisa_state`] BW_SAME_VIEWS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[];STRIP_TAC] THEN
  MP_TAC(ISPECL [`st:tisa_state`; `s:tisa_state`; `u:tisa_state`] BW_MID_SAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[bw_post_pre]);;

let BWT_PUBLISH_CONT_WP = prove
 (`!nms tys st s Q.
     bw_regions st /\ bw_entered st /\ bwt_mid nms tys st s /\
     bw_post_pre st s /\ val(bw_w s 8) = 2 /\ tregs s 2 = tisa_base st 3
     ==> tisa_wp bw_publish Q (bwt_result nms tys st) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC TISA_WP_MONO THEN
  EXISTS_TAC `\u:tisa_state. F` THEN EXISTS_TAC `bwt_result nms tys st` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC BWT_PUBLISH_WP THEN ASM_REWRITE_TAC[]);;

let BWT_PUSH_WP = prove
 (`!nms tys st s.
     bw_regions st /\ bw_entered st /\ bwt_mid nms tys st s /\
     bw_post_pre st s /\ tregs s 2 = tisa_base st 3 /\
     tregs s 3 = bw_w s 8 /\ val(bw_w s 8) < 2
     ==> tisa_wp bw_push (bwt_mid nms tys st) (bwt_result nms tys st) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BWT_POST_SETUP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_post_pre;bw_resok] o
    check (fun th -> concl th = `bw_post_pre st s`)) THEN
  FIRST_ASSUM(ASSUME_TAC o (fun th -> MP th (ASSUME `val(bw_w s 8) < 2`)) o
    check (fun th -> is_imp(concl th) && fst(strip_comb(rand(concl th))) = `bw_claim`)) THEN
  REWRITE_TAC[bw_push] THEN BWT_VCG_TAC THEN
  W(fun (_,w) ->
    if fst(strip_comb w) = `tisa_wp` then
      MATCH_MP_TAC BWT_MEMO_WP THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [BWT_POST_SPLIT_TAC BW_PUSH_CLAIM_TAC;
        TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[];
        BW_EVAL_TAC THEN TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[]]
    else if fst(strip_comb w) = `bwt_result` then
      REWRITE_TAC[bwt_result;ARITH_EQ] THEN BW_STOP_LEAF_TAC
    else BWT_POST_SPLIT_TAC BW_PUSH_CLAIM_TAC));;

let BWT_POST_CALL_TAC = W(fun (asl,w) ->
  let head,args = strip_comb w in
  if head = `tisa_wp` then
    let u = last args in
    let pre = subst [u,`u:tisa_state`] `bw_post_pre st u` in
    let rule = if hd args = `bw_publish` then BWT_PUBLISH_CONT_WP else BWT_PUSH_WP in
    SUBGOAL_THEN pre ASSUME_TAC THENL
     [MP_TAC(ISPECL [`st:tisa_state`;`s:tisa_state`;u] BW_POST_PRE_SAME) THEN
      TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[TISA_TMEM_SETREG];
      MATCH_MP_TAC rule THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST [REPEAT(MATCH_MP_TAC BWT_MID_SETREG THEN CONJ_TAC THENL
           [CONV_TAC NUM_REDUCE_CONV;ALL_TAC]) THEN FIRST_ASSUM ACCEPT_TAC;
        BW_EVAL_TAC THEN TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[] THEN
        TRY BW_SIDE_ARITH_TAC]]
  else if head = `bwt_result` then
    REWRITE_TAC[bwt_result;ARITH_EQ] THEN BW_STOP_LEAF_TAC
  else (REPEAT(MATCH_MP_TAC BWT_MID_SETREG THEN CONJ_TAC THENL
          [CONV_TAC NUM_REDUCE_CONV;ALL_TAC]) THEN FIRST_ASSUM ACCEPT_TAC));;

let BWT_POST_WP = prove
 (`!nms tys st s.
     bw_regions st /\ bw_entered st /\ bw_post_pre st s /\ bwt_mid nms tys st s
     ==> tisa_wp bw_post (bwt_mid nms tys st) (bwt_result nms tys st) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BWT_POST_SETUP_TAC THEN REWRITE_TAC[bw_post] THEN BWT_VCG_TAC THEN BWT_POST_CALL_TAC);;

let BW_INTERN_NO_SUCCESS = prove
 (`!s u. ~(tisa_exec bw_intern s = TStop 1 u)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP TISA_EXEC_STOP) THEN
  REWRITE_TAC[tisa_stop_ok;bw_intern;bw_probe;bw_append;bw_occupied;tisa_returns] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let BWT_INTERN_WP_WITH_CODES = prove
 (`!st s Q.
     tisa_wp bw_intern Q (bw_result st) s
     ==> tisa_wp bw_intern Q (\k u. bw_result st k u /\ ~(k = 1)) s`,
  REWRITE_TAC[tisa_wp;tisa_rwp] THEN MESON_TAC[BW_INTERN_NO_SUCCESS]);;

let BWT_TAIL_WP = prove
 (`!nms tys st s.
     bw_regions st /\ bw_entered st /\ bwt_input nms tys st /\ bwt_tail nms tys st s
     ==> tisa_wp bw_tail (bwt_mid nms tys st) (bwt_result nms tys st) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o REWRITE_RULE[bwt_tail] o
    check (fun th -> concl th = `bwt_tail nms tys st s`)) THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o REWRITE_RULE[bw_tail_pre] o
    check (fun th -> concl th = `bw_tail_pre st s`)) THEN
  REWRITE_TAC[bw_tail;TISA_WP_SEQ;TISA_WP_IF] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[TISA_WP_SKIP] THEN MATCH_MP_TAC BWT_POST_WP THEN
    ASM_REWRITE_TAC[bw_post_pre] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC TISA_WP_MONO THEN
    EXISTS_TAC `bw_after_intern s` THEN
    EXISTS_TAC `\k u. bw_result st k u /\ ~(k = 1)` THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `u:tisa_state` THEN STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC BWT_POST_WP THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BW_POST_PRE_INTERNED THEN EXISTS_TAC `s:tisa_state` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC BWT_INTERNED_FROM_RESULT THEN EXISTS_TAC `s:tisa_state` THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[bwt_result] THEN MESON_TAC[];
      MATCH_MP_TAC BWT_INTERN_WP_WITH_CODES THEN
      MATCH_MP_TAC BW_INTERN_WP THEN ASM_REWRITE_TAC[]]]);;

let BWT_PROLOGUE_CONT_TAC = W(fun (_,w) ->
  let u = rand(find_term (fun t ->
    let h,args = strip_comb t in h = `bwt_mid` && length args = 4) w) in
  let facts = subst [u,`u:tisa_state`]
    `bw_entered st /\ bw_mid st u /\ tregs u 11 = word 4294967295` in
  SUBGOAL_THEN facts STRIP_ASSUME_TAC THENL
   [TISA_STATE_NORM_TAC THEN BW_PROLOGUE_CONT_TAC;ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BWT_MID_INIT THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (subst [u,`u:tisa_state`] `bw_keep st st u`) MP_TAC THENL
   [BW_KEEP_TAC `st:tisa_state`;ALL_TAC] THEN
  REWRITE_TAC[bw_keep] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BW_EVAL_TAC THEN ASM_REWRITE_TAC[intern_count] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN BW_SIDE_ARITH_TAC);;

let BWT_PROLOGUE_WP = prove
 (`!nms tys st.
     tisa_entry_ok bind_walk st /\ bwt_input nms tys st
     ==> tisa_wp bw_prologue
           (\s. bw_entered st /\ bwt_mid nms tys st s /\ tregs s 11 = word 4294967295)
           (bwt_result nms tys st) st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BW_ENTRY) THEN BW_REGIONS_TAC THEN
  REWRITE_TAC[bw_prologue] THEN
  BWT_VCG_TAC THEN
  W(fun (_,w) ->
    if fst(strip_comb w) = `bwt_result` then
      REWRITE_TAC[bwt_result;ARITH_EQ] THEN BW_PROLOGUE_STOP_TAC
    else BWT_PROLOGUE_CONT_TAC));;

(* Operation of the pending stack. *)

let BWT_TAIL_LEAF_TAC claim_tac task_tac key_tac : tactic = fun (asl,w) ->
  let h,_ = strip_comb w in
  if h = `bwt_result` then
    (REWRITE_TAC[bwt_result;ARITH_EQ] THEN (BW_CONTRA_TAC ORELSE BW_STOP_LEAF_TAC)) (asl,w)
  else
    (let u = rand w in
     SUBGOAL_THEN (mk_comb(`bw_mid st`,u)) ASSUME_TAC THENL
      [BW_PEEL_MID_TAC;ALL_TAC] THEN
     REWRITE_TAC[bwt_tail] THEN CONJ_TAC THENL
      [REWRITE_TAC[bw_tail_pre] THEN ASM_REWRITE_TAC[] THEN
       TISA_STATE_NORM_TAC THEN REWRITE_TAC[TISA_BOOL_01;WORD_1_NE_0] THEN claim_tac;
       REWRITE_TAC[bwt_mid] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
        [BW_EVAL_TAC THEN FIRST_ASSUM ACCEPT_TAC;
         W(fun (_,w) -> task_tac (rand w));
         TISA_STATE_NORM_TAC THEN REWRITE_TAC[WORD_1_NE_0] THEN key_tac]]) (asl,w);;

let BW_PACKED_TAG = prove
 (`!(x:int64) tag. val(word_add (word_shl x 3) (word tag)) MOD 8 = tag MOD 8`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_ADD;VAL_WORD_SHL;VAL_WORD;DIMINDEX_64] THEN
  REWRITE_TAC[MOD_ADD_MOD;ARITH_RULE `2 EXP 64 = 8 * 2 EXP 61`;MOD_MOD;
              ARITH_RULE `2 EXP 3 = 8`;MOD_MULT_ADD]);;

let BWT_EMPTY_TASKS_TAC u =
  SUBGOAL_THEN (subst [u,`u:tisa_state`] `val(bw_w u 1) = 0`) ASSUME_TAC THENL
   [BW_EVAL_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[bw_task_bounds;LT]];;

let BWT_LAST_WP = prove
 (`!nms tys st s.
     bw_regions st /\ bw_entered st /\ bwt_mid nms tys st s /\
     tregs s 2 = tisa_base st 3 /\ val(bw_w s 1) = 0
     ==> tisa_wp bw_last (bwt_tail nms tys st) (bwt_result nms tys st) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BWT_POST_SETUP_TAC THEN REWRITE_TAC[bw_last] THEN BWT_VCG_TAC THEN
  BWT_TAIL_LEAF_TAC BW_LAST_CLAIM_TAC BWT_EMPTY_TASKS_TAC
    (BW_EVAL_TAC THEN REWRITE_TAC[VAL_WORD_1;BW_PACKED_TAG] THEN
     CONV_TAC(DEPTH_CONV BW_VAL_NUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV));;

let bwt_step_frame = new_definition
 `bwt_step_frame nms tys st u <=>
    bw_rows_valid nms tys (bw_rows u (val(bw_w u 0))) /\ bw_task_bounds st u /\
    (~(tregs u 9 = word 0)
     ==> (val(bw_w u 8) = 2 \/ val(bw_w u 8) < 2 /\
          ?X. fddb nms tys (bw_rows st (val(intern_count st))) (val(bw_w u 6)) X) /\
         (val(tregs u 1) MOD 8 = 1 ==> val(tregs u 2) = 0))`;;

let BWT_STEP_FRAME_INTRO = prove
 (`!nms tys st u. bw_tail_pre st u /\ bwt_step_frame nms tys st u
                  ==> bwt_tail nms tys st u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[bw_tail_pre] o
    check (fun th -> fst(strip_comb(concl th)) = `bw_tail_pre`)) THEN
  REWRITE_TAC[bwt_tail;bwt_mid] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[bwt_step_frame] o
    check (fun th -> fst(strip_comb(concl th)) = `bwt_step_frame`)) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC]);;

let BWT_STEP_COMPOSE = prove
 (`!S nms tys st s.
     tisa_wp S (bw_tail_pre st) (bw_result st) s /\
     tisa_wp S (\u. bw_tail_pre st u ==> bwt_step_frame nms tys st u) (\k u. ~(k = 1)) s
     ==> tisa_wp S (bwt_tail nms tys st) (bwt_result nms tys st) s`,
  REWRITE_TAC[tisa_wp;tisa_rwp;bwt_result] THEN MESON_TAC[BWT_STEP_FRAME_INTRO]);;

let BWT_STEP_FRAME_TAC task_tac key_tac =
  DISCH_TAC THEN REWRITE_TAC[bwt_step_frame] THEN REPEAT CONJ_TAC THENL
   [BW_EVAL_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    W(fun (_,w) -> task_tac (rand w));
    TISA_STATE_NORM_TAC THEN REWRITE_TAC[WORD_1_NE_0] THEN key_tac];;

let BWT_COMPOSE_STEP_TAC base source task_tac key_tac =
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BWT_POST_SETUP_TAC THEN MATCH_MP_TAC BWT_STEP_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC base THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[source] THEN BWT_VCG_TAC THEN BWT_STEP_FRAME_TAC task_tac key_tac];;

let BWT_TASK_GROW_TAC width u =
  let newcount = subst [u,`u:tisa_state`;mk_small_numeral width,`width:num`]
    `val(bw_w u 1) = val(bw_w s 1) + width` in
  let limit = subst [mk_small_numeral width,`width:num`]
    `val(bw_w s 1) + width <= val(bw_w s 4)` in
  let active = subst [mk_small_numeral width,`width:num`]
    `e < val(bw_w s 1) + width` in
  (* The parent task reuses the popped entry's index word. *)
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[bw_ent;MULT_CLAUSES;ADD_CLAUSES] o
    check (fun th -> can (find_term ((=) `bw_ent s 0 (val(bw_w s 1)) 1`)) (concl th))) THEN
  SUBGOAL_THEN newcount ASSUME_TAC THENL
   [BW_EVAL_TAC THEN BW_SIDE_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN limit ASSUME_TAC THENL [BW_SIDE_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[bw_task_bounds;ASSUME newcount] THEN X_GEN_TAC `e:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `8 * (16 + 4 * e + 1) + 8 <= val(tisa_len st 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC BW_TASK_WORD_BOUND THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[GSYM(ASSUME `val(bw_w s 4) = val(tisa_len st 3) DIV 128 - 1`)] THEN
      MAP_EVERY (MP_TAC o ASSUME) [active;limit] THEN ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[bw_ent;MULT_CLAUSES;ADD_CLAUSES] THEN
  ASM_CASES_TAC `e < val(bw_w s 1)` THENL
   [BW_EVAL_TAC THEN
    MP_TAC(SPEC `e:num` (REWRITE_RULE[bw_task_bounds] (ASSUME `bw_task_bounds st s`))) THEN
    ASM_REWRITE_TAC[bw_ent;MULT_CLAUSES;ADD_CLAUSES];
    let positions = List.init width (fun j -> subst [mk_small_numeral j,`j:num`]
        `e = val(bw_w s 1) + j`) in
    SUBGOAL_THEN (list_mk_disj positions) MP_TAC THENL
     [MAP_EVERY (MP_TAC o ASSUME) [active;`~(e < val(bw_w s 1))`] THEN ARITH_TAC;
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
      BW_EVAL_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES;VAL_WORD_USHR] THEN
      TRY(CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]) THEN TRY BW_SIDE_ARITH_TAC]];;

let BWT_COMB_EXPAND_WP = prove
 (`!nms tys st s.
     bw_regions st /\ bw_entered st /\ bwt_mid nms tys st s /\
     tregs s 2 = tisa_base st 3 /\ tregs s 3 = bw_w s 1 /\
     bw_ent s 0 (val(bw_w s 1)) 1 = tregs s 8 /\
     val(tregs s 8) < val(intern_count st) /\
     val(tregs s 6) DIV 8 < val(intern_count st) /\
     val(tregs s 5) < val(intern_count st)
     ==> tisa_wp bw_comb_expand (bwt_tail nms tys st) (bwt_result nms tys st) s`,
  BWT_COMPOSE_STEP_TAC BW_COMB_EXPAND_WP bw_comb_expand (BWT_TASK_GROW_TAC 3) ALL_TAC);;
let BWT_ABS_EXPAND_WP = prove
 (`!nms tys st s.
     bw_regions st /\ bw_entered st /\ bwt_mid nms tys st s /\
     tregs s 2 = tisa_base st 3 /\ tregs s 3 = bw_w s 1 /\
     bw_ent s 0 (val(bw_w s 1)) 1 = tregs s 8 /\
     val(tregs s 8) < val(intern_count st) /\
     val(tregs s 5) < val(intern_count st)
     ==> tisa_wp bw_abs_expand (bwt_tail nms tys st) (bwt_result nms tys st) s`,
  BWT_COMPOSE_STEP_TAC BW_ABS_EXPAND_WP bw_abs_expand (BWT_TASK_GROW_TAC 2) ALL_TAC);;

let BW_FDDBS_TAG = prove
 (`!nms tys D i l. fddbs nms tys D i l
                   ==> FST(EL i D) = 5 \/ FST(EL i D) = 6`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[fddb_CASES] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST]);;

let BW_ROWS_SOURCE_TERM = prove
 (`!nms tys D i. bw_rows_valid nms tys D /\ i < LENGTH D /\ FST(EL i D) < 5
                ==> ?X. fddb nms tys D i X`,
  REWRITE_TAC[bw_rows_valid] THEN
  MESON_TAC[BW_FDDBS_TAG;ARITH_RULE `!n. n < 5 ==> ~(n = 5 \/ n = 6)`]);;

let BW_KEY_CHILD_BOUNDS = prove
 (`!i tag a b C. i < C /\ bw_key_ok i (tag,a,b)
     ==> (tag = 3 ==> a < C /\ b < C) /\ (tag = 4 ==> b < C)`,
  REWRITE_TAC[bw_key_ok] THEN ARITH_TAC);;

let BW_SOURCE_ROW = prove
 (`!nms tys st s (i:int64) k0 k1.
     bwt_input nms tys st /\ bw_mid st s /\ tisa_base s 0 = tisa_base st 0 /\
     val i < val(intern_count st) /\
     k0 = tisa_read s (word_add (tisa_base st 0) (word(8 * val(word_shl i 1)))) 8 /\
     k1 = tisa_read s (word_add (tisa_base st 0) (word(8 * val(word_shl i 1) + 8))) 8
     ==> (val k0 MOD 8 < 5 ==> ?X. fddb nms tys (bw_rows st (val(intern_count st))) (val i) X) /\
         (val k0 MOD 8 = 3 ==> val k0 DIV 8 < val(intern_count st) /\ val k1 < val(intern_count st)) /\
         (val k0 MOD 8 = 4 ==> val k1 < val(intern_count st))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`st:tisa_state`;`s:tisa_state`;`i:int64`] BW_ROW_READ) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_mid] o
     check (fun th -> concl th = `bw_mid st s`)) THEN
    MP_TAC(SPEC `tisa_len st 0` VAL_BOUND_64) THEN BW_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`st:tisa_state`;`s:tisa_state`;`i:int64`;`k0:int64`;`k1:int64`] BW_ROW_TRIPLE) THEN
  ASM_REWRITE_TAC[LENGTH_BW_ROWS] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[bwt_input] o
    check (fun th -> concl th = `bwt_input nms tys st`)) THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC BW_ROWS_SOURCE_TERM THEN ASM_REWRITE_TAC[LENGTH_BW_ROWS;FST];
    MATCH_MP_TAC BW_KEY_CHILD_BOUNDS THEN EXISTS_TAC `val(i:int64)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `val(i:int64)` o CONJUNCT1 o REWRITE_RULE[bw_rows_valid] o
      check (fun th -> fst(strip_comb(concl th)) = `bw_rows_valid`)) THEN
    ASM_REWRITE_TAC[LENGTH_BW_ROWS]]);;

let BWT_SOURCE_TAG_TAC tag =
  let i = `bw_w s 6` in
  let k0,k1 = bw_rowrd i false,bw_rowrd i true in
  let tag_eq = mk_eq(mk_binop `(MOD):num->num->num` (mk_comb(tisa_val64,k0)) `8`,
                     mk_small_numeral tag) in
  let check_tag = if tag = 0 then
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_entered] o
      check (fun th -> concl th = `bw_entered st`)) THEN
    MP_TAC(ISPECL [k0;`tisa_fword st 22`] BW_SHL3_EQ) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]
    else BW_TAG_TAC in
  SUBGOAL_THEN tag_eq ASSUME_TAC THENL [check_tag;ALL_TAC] THEN
  MP_TAC(ISPECL [`nms:string list`;`tys:(num#num#num)list`;`st:tisa_state`;`s:tisa_state`;i;k0;k1]
    BW_SOURCE_ROW) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

let BWT_CONSTRUCTOR_GOAL blk =
  subst [blk,`bw_comb:tisa_stmt`]
    `!nms tys st s.
       bw_regions st /\ bw_entered st /\ bwt_input nms tys st /\ bwt_mid nms tys st s /\
       tregs s 2 = tisa_base st 3 /\ tregs s 8 = bw_w s 6 /\ tregs s 7 = bw_w s 7 /\
       val(bw_w s 6) < val(intern_count st)
       ==> tisa_wp bw_comb (bwt_tail nms tys st) (bwt_result nms tys st) s`;;

let BWT_COMB_WP = prove
 (BWT_CONSTRUCTOR_GOAL `bw_comb`,
  BWT_COMPOSE_STEP_TAC BW_COMB_WP bw_comb BWT_TASK_PREFIX_TAC
    (BW_EVAL_TAC THEN BWT_SOURCE_TAG_TAC 3 THEN
     REWRITE_TAC[VAL_WORD_1;BW_PACKED_TAG] THEN CONV_TAC NUM_REDUCE_CONV THEN
     ASM_REWRITE_TAC[]));;

let BWT_ABS_WP = prove
 (BWT_CONSTRUCTOR_GOAL `bw_abs`,
  BWT_COMPOSE_STEP_TAC BW_ABS_WP bw_abs BWT_TASK_PREFIX_TAC
    (BW_EVAL_TAC THEN BWT_SOURCE_TAG_TAC 4 THEN
     REWRITE_TAC[VAL_WORD_1] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV));;

let BWT_VISIT_GOAL blk =
  subst [blk,`bw_visit:tisa_stmt`]
   `!nms tys st s.
      bw_regions st /\ bw_entered st /\ bwt_input nms tys st /\ bwt_mid nms tys st s /\
      tregs s 2 = tisa_base st 3 /\ tregs s 8 = bw_w s 6 /\ tregs s 7 = bw_w s 7 /\
      tregs s 3 = bw_w s 1 /\ val(bw_w s 6) < val(intern_count st) /\
      bw_ent s 0 (val(bw_w s 1)) 1 = tregs s 8
      ==> tisa_wp bw_visit (bwt_tail nms tys st) (bwt_result nms tys st) s`;;

let BW_ENT_SETREG = prove
 (`!s d (v:int64) a e f. ~(d = 0)
     ==> bw_ent (tisa_setreg d v s) a e f = bw_ent s a e f`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[bw_ent;BW_W_SETREG]);;

let BWT_SUBBLOCK_TAC task_tac =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_SIMP_TAC[BW_ENT_SETREG;BW_W_SETREG;TISA_TREGS_SETREG;ARITH_EQ] THEN NO_TAC;
         W (fun (_,w) -> if fst(strip_comb w) = `bwt_mid`
                         then BWT_POST_SPLIT_TAC NO_TAC else NO_TAC) THEN NO_TAC;
         TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         TISA_STATE_NORM_TAC THEN BW_EVAL_ALL_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         task_tac];;

let BWT_BOUND_KEY_TAC =
  BW_EVAL_TAC THEN BWT_SOURCE_TAG_TAC 0 THEN
  REWRITE_TAC[VAL_WORD_0;VAL_WORD_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[];;

let BWT_TAIL_HAS_FRAME = prove
 (`!nms tys st u. bwt_tail nms tys st u ==> bwt_step_frame nms tys st u`,
  REWRITE_TAC[bwt_tail;bwt_mid;bwt_step_frame] THEN MESON_TAC[]);;

let BWT_WP_STEP_FRAME = prove
 (`!S nms tys st s.
     tisa_wp S (bwt_tail nms tys st) (bwt_result nms tys st) s
     ==> tisa_wp S (\u. bw_tail_pre st u ==> bwt_step_frame nms tys st u)
           (\k u. k = 1 ==> bw_rows_valid nms tys (bw_rows u (val(intern_count u)))) s`,
  REWRITE_TAC[tisa_wp;tisa_rwp;bwt_result] THEN MESON_TAC[BWT_TAIL_HAS_FRAME]);;

let BWT_COMPOSE_DISPATCH = prove
 (`!S nms tys st s.
     tisa_wp S (bw_tail_pre st) (bw_result st) s /\
     tisa_wp S (\u. bw_tail_pre st u ==> bwt_step_frame nms tys st u)
           (\k u. k = 1 ==> bw_rows_valid nms tys (bw_rows u (val(intern_count u)))) s
     ==> tisa_wp S (bwt_tail nms tys st) (bwt_result nms tys st) s`,
  REWRITE_TAC[tisa_wp;tisa_rwp;bwt_result] THEN MESON_TAC[BWT_STEP_FRAME_INTRO]);;

let BWT_DISPATCH_SETUP_TAC base defs =
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BWT_POST_SETUP_TAC THEN MATCH_MP_TAC BWT_COMPOSE_DISPATCH THEN CONJ_TAC THENL
   [MATCH_MP_TAC base THEN ASM_REWRITE_TAC[];
    REWRITE_TAC defs THEN BWT_VCG_TAC];;

let BWT_MISS_WP = prove
 (BWT_VISIT_GOAL `bw_miss`,
  BWT_DISPATCH_SETUP_TAC BW_MISS_WP [bw_miss;bw_bound;bw_tags;bw_leaf] THEN
  W(fun (_,w) ->
    let h,args = strip_comb w in
    if h = `tisa_wp` && hd args = `bw_comb_expand` then
      BWT_SOURCE_TAG_TAC 3 THEN MATCH_MP_TAC BWT_WP_STEP_FRAME THEN MATCH_MP_TAC BWT_COMB_EXPAND_WP THEN
      BWT_SUBBLOCK_TAC (REWRITE_TAC[VAL_WORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[])
    else if h = `tisa_wp` && hd args = `bw_abs_expand` then
      BWT_SOURCE_TAG_TAC 4 THEN MATCH_MP_TAC BWT_WP_STEP_FRAME THEN MATCH_MP_TAC BWT_ABS_EXPAND_WP THEN BWT_SUBBLOCK_TAC NO_TAC
    else BWT_STEP_FRAME_TAC BWT_TASK_PREFIX_TAC BWT_BOUND_KEY_TAC));;

let BWT_VISIT_WP = prove
 (BWT_VISIT_GOAL `bw_visit`,
  BWT_DISPATCH_SETUP_TAC BW_VISIT_WP [bw_visit] THEN
  W(fun (_,w) ->
    let h,args = strip_comb w in
    if h = `tisa_wp` && hd args = `bw_miss` then
      MATCH_MP_TAC BWT_WP_STEP_FRAME THEN MATCH_MP_TAC BWT_MISS_WP THEN BWT_SUBBLOCK_TAC NO_TAC
    else BWT_STEP_FRAME_TAC BWT_TASK_PREFIX_TAC NO_TAC));;

let BWT_TASK_POP_TAC u =
  let popped = subst [u,`u:tisa_state`] `val(bw_w u 1) = val(bw_w s 1) - 1` in
  SUBGOAL_THEN popped ASSUME_TAC THENL [BW_EVAL_TAC THEN BW_SIDE_ARITH_TAC;ALL_TAC] THEN
  MATCH_MP_TAC BW_TASKS_FROM_PREFIX THEN EXISTS_TAC `s:tisa_state` THEN
  ASM_REWRITE_TAC[ARITH_RULE `n - 1 <= n`] THEN X_GEN_TAC `e:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `8 * (16 + 4 * e + 1) + 8 <= val(tisa_len st 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC BW_TASK_WORD_BOUND THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[GSYM(ASSUME `val(bw_w s 4) = val(tisa_len st 3) DIV 128 - 1`)] THEN
      MAP_EVERY (MP_TAC o ASSUME)
        [`e < val(bw_w s 1) - 1`;`val(bw_w s 1) <= val(bw_w s 4)`] THEN ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[bw_ent;MULT_CLAUSES;ADD_CLAUSES] THEN BW_EVAL_TAC THEN REFL_TAC;;

let BWT_POP_BOUND_TAC =
  TISA_STATE_NORM_TAC THEN TRY BW_EVAL_TAC THEN BW_EVAL_ALL_TAC THEN
  BW_FOLD_ALL_TAC [`0`,`val(bw_w s 1) - 1`] THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
         MP_TAC(SPEC `val(bw_w s 1) - 1` (REWRITE_RULE[bw_task_bounds]
           (ASSUME `bw_task_bounds st s`))) THEN
         ANTS_TAC THENL [BW_ARITH_TAC;ASM_REWRITE_TAC[]]];;

let BWT_POP_WP = prove
 (`!nms tys st s.
      bw_regions st /\ bw_entered st /\ bwt_input nms tys st /\ bwt_mid nms tys st s /\
      tregs s 2 = tisa_base st 3 /\ tregs s 3 = bw_w s 1 /\ ~(val(bw_w s 1) = 0)
      ==> tisa_wp bw_pop (bwt_tail nms tys st) (bwt_result nms tys st) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BWT_POST_SETUP_TAC THEN REWRITE_TAC[bw_pop] THEN BWT_VCG_TAC THEN
  BWT_FOCUS_TAC (W(fun (_,w) ->
    let h,args = strip_comb w in
    if h = `tisa_wp` then
      let rule = assoc (hd args) [`bw_visit`,BWT_VISIT_WP;`bw_comb`,BWT_COMB_WP;`bw_abs`,BWT_ABS_WP] in
      MATCH_MP_TAC rule THEN REPEAT CONJ_TAC THEN
      W(fun (_,w) ->
        if fst(strip_comb w) = `bwt_mid` then
          REWRITE_TAC[bwt_mid] THEN CONJ_TAC THENL
           [BW_PEEL_MID_TAC;
            CONJ_TAC THENL
             [BW_EVAL_TAC THEN FIRST_ASSUM ACCEPT_TAC;
              W(fun (_,w) -> BWT_TASK_POP_TAC (rand w))]]
        else BWT_SUBBLOCK_TAC BWT_POP_BOUND_TAC)
    else REWRITE_TAC[bwt_result;ARITH_EQ] THEN (BW_CONTRA_TAC ORELSE BW_STOP_LEAF_TAC))));;

let BWT_STEP_WP = prove
 (`!nms tys st s.
      bw_regions st /\ bw_entered st /\ bwt_input nms tys st /\ bwt_mid nms tys st s
      ==> tisa_wp bw_step (bwt_tail nms tys st) (bwt_result nms tys st) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BWT_POST_SETUP_TAC THEN REWRITE_TAC[bw_step] THEN BWT_VCG_TAC THEN
  W(fun (_,w) ->
    let h,args = strip_comb w in
    if h = `tisa_wp` then
      let rule = assoc (hd args) [`bw_last`,BWT_LAST_WP;`bw_pop`,BWT_POP_WP] in
      MATCH_MP_TAC rule THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM VAL_EQ_0]) THEN
      BWT_SUBBLOCK_TAC NO_TAC
    else REWRITE_TAC[bwt_result;ARITH_EQ] THEN (BW_CONTRA_TAC ORELSE BW_STOP_LEAF_TAC)));;

let BWT_BODY_WP = prove
 (`!nms tys st j s.
     bw_regions st /\ bw_entered st /\ bwt_input nms tys st /\ bwt_mid nms tys st s
     ==> tisa_wp bw_body (bwt_mid nms tys st) (bwt_result nms tys st)
           (tisa_setreg 10 (word j) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bw_body;TISA_WP_SEQ] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN EXISTS_TAC `bwt_tail nms tys st` THEN
  EXISTS_TAC `bwt_result nms tys st` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [BETA_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC BWT_TAIL_WP THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC BWT_STEP_WP THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BWT_MID_SETREG THEN ASM_REWRITE_TAC[ARITH_EQ]]);;

let BWT_ROOT_WP = prove
 (`!nms tys st. tisa_entry_ok bind_walk st /\ bwt_input nms tys st
    ==> tisa_wp (tisa_root bind_walk) (\s. F) (bwt_result nms tys st) st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP BW_ENTRY) THEN
  REWRITE_TAC[bind_walk;tisa_root;TISA_WP_SEQ] THEN MATCH_MP_TAC TISA_WP_MONO THEN
  EXISTS_TAC `\s. bw_entered st /\ bwt_mid nms tys st s /\ tregs s 11 = word 4294967295` THEN
  EXISTS_TAC `bwt_result nms tys st` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;MATCH_MP_TAC BWT_PROLOGUE_WP THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `s:tisa_state` THEN BETA_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC TISA_WP_COUNT_LOOP THEN EXISTS_TAC `\(N:num) (j:num). bwt_mid nms tys st` THEN
  ASM_REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC BWT_BODY_WP THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`N:num`;`s1:tisa_state`] THEN DISCH_TAC THEN
    BWT_VCG_TAC THEN REWRITE_TAC[bwt_result;ARITH_EQ] THEN
    MATCH_MP_TAC BW_RESULT_STOP_MID THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    REPEAT(MATCH_MP_TAC BW_MID_SETREG THEN CONV_TAC NUM_REDUCE_CONV) THEN
    ASM_MESON_TAC[bwt_mid]]);;

let BWT_RUN = prove
 (`!nms tys st k st'.
     tisa_entry_ok bind_walk st /\ bwt_input nms tys st /\
     tisa_run bind_walk st = TStop k st'
     ==> bwt_result nms tys st k st'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`nms:string list`;`tys:(num#num#num)list`;`st:tisa_state`] BWT_ROOT_WP) THEN
  ASM_REWRITE_TAC[tisa_wp] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> tisa_has_tm `tisa_run` th)) THEN
  ASM_REWRITE_TAC[tisa_run] THEN
  MP_TAC(ISPEC `tisa_exec (tisa_root bind_walk) st` TISA_RESULT_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC)
     (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC))) THEN
  REWRITE_TAC[tisa_then;TISA_RWP_CONT;TISA_RWP_STOP;TISA_RESULT_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN REWRITE_TAC[]);;

let BWT_RUN_VALID_ROWS = prove
 (`!nms tys st k u.
     intern_ok st /\ tisa_entry_ok bind_walk st /\ bwt_input nms tys st /\
     tisa_run bind_walk st = TStop k u
     ==> bw_rows_valid nms tys (bw_rows u (val(intern_count u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`nms:string list`;`tys:(num#num#num)list`;`st:tisa_state`;`k:num`;`u:tisa_state`]
    BWT_RUN) THEN ASM_REWRITE_TAC[bwt_result] THEN STRIP_TAC THEN
  ASM_CASES_TAC `k = 1` THEN ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[bwt_input] o
    check (fun th -> concl th = `bwt_input nms tys st`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_result] o
    check (fun th -> concl th = `bw_result st k u`)) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[intern_ok] o
    check (fun th -> concl th = `intern_ok st`)) THEN
  SUBGOAL_THEN `intern_count u = intern_count st` SUBST1_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `bw_rows u (val(intern_count st)) = bw_rows st (val(intern_count st))` SUBST1_TAC THENL
   [MATCH_MP_TAC BW_ROWS_EQ THEN ASM_MESON_TAC[];FIRST_ASSUM ACCEPT_TAC]);;

let bind_walk_table_run_theorems =
 ["BWT_MEMO_WP",BWT_MEMO_WP;"BWT_PUSH_WP",BWT_PUSH_WP;"BWT_TAIL_WP",BWT_TAIL_WP;
  "BWT_PROLOGUE_WP",BWT_PROLOGUE_WP;"BWT_LAST_WP",BWT_LAST_WP;
  "BWT_COMB_EXPAND_WP",BWT_COMB_EXPAND_WP;"BWT_ABS_EXPAND_WP",BWT_ABS_EXPAND_WP;
  "BWT_COMB_WP",BWT_COMB_WP;"BWT_ABS_WP",BWT_ABS_WP;
  "BWT_MISS_WP",BWT_MISS_WP;"BWT_VISIT_WP",BWT_VISIT_WP;"BWT_POP_WP",BWT_POP_WP;
  "BWT_STEP_WP",BWT_STEP_WP;"BWT_BODY_WP",BWT_BODY_WP;"BWT_ROOT_WP",BWT_ROOT_WP;
  "BWT_RUN",BWT_RUN;"BWT_RUN_VALID_ROWS",BWT_RUN_VALID_ROWS];;
