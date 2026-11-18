(* The binding walk's p1 contract for the driver, including its fuel receipt. *)
needs "native/hol/bind_walk_table_run.ml";;
needs "native/driver/driver_fuel.ml";;
needs "native/leaves/common/leaf_lib.ml";;

let BIND_WALK_DECLS = prove
 (`tisa_decls bind_walk = [(2,16,8);(2,8,8);(2,8,8);(2,256,8)]`,
  REWRITE_TAC[bind_walk;tisa_decls]);;

let BIND_WALK_LEAF_WF = prove
 (`tisa_leaf_wf bind_walk`,LEAF_WF_TAC BIND_WALK_DECLS BIND_WALK_TERM);;

let BIND_WALK_RW = prove
 (`!r. tisa_rw (tisa_decls bind_walk) r <=> r < 4`,
  GEN_TAC THEN REWRITE_TAC[BIND_WALK_DECLS;tisa_rw;LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN EQ_TAC THENL
   [SIMP_TAC[];
    REWRITE_TAC[ARITH_RULE `r < 4 <=> r = 0 \/ r = 1 \/ r = 2 \/ r = 3`] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[FST] THEN CONV_TAC NUM_REDUCE_CONV]);;

let BIND_WALK_STATUS = prove
 (`!t k u. tisa_run bind_walk t = TStop k u
           ==> tisa_fword u 18 = word k /\ (k = 1 \/ k = 2 \/ k = 3 \/ k = 4)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP TISA_RUN_STATUS) THEN
  REWRITE_TAC[BIND_WALK_TERM;tisa_root;tisa_returns] THEN MESON_TAC[]);;

let BIND_WALK_TABLE_RUN = prove
 (`!t k u. tisa_entry_ok bind_walk t /\ tisa_run bind_walk t = TStop k u
     ==> bw_result t k u /\ tisa_fword u 18 = word k /\
         (k = 1 \/ k = 2 \/ k = 3 \/ k = 4) /\
         val(tisa_fword t 21) <= val(tisa_fword u 21) /\
         val(tisa_fword u 21) <= val(tisa_fword t 20) /\
         (!nms tys. bwt_input nms tys t ==> bwt_result nms tys t k u) /\
         (!nms tys. intern_ok t /\ bwt_input nms tys t
                    ==> bw_rows_valid nms tys (bw_rows u (val(intern_count u))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] BW_RUN) THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] BIND_WALK_STATUS) THEN
  MP_TAC(SPECL [`bind_walk:tisa_prog`;`t:tisa_state`;`k:num`;`u:tisa_state`] TISA_RUN_FUEL) THEN
  ASM_REWRITE_TAC[BIND_WALK_LEAF_WF] THEN
  REPLICATE_TAC 3 (DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`nms:string list`;`tys:(num#num#num)list`] THEN DISCH_TAC THEN
    MATCH_MP_TAC(SPECL [`nms:string list`;`tys:(num#num#num)list`;`t:tisa_state`;`k:num`;`u:tisa_state`] BWT_RUN) THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`nms:string list`;`tys:(num#num#num)list`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(SPECL [`nms:string list`;`tys:(num#num#num)list`;`t:tisa_state`;`k:num`;`u:tisa_state`]
      BWT_RUN_VALID_ROWS) THEN ASM_REWRITE_TAC[]]);;

let bind_walk_table_contract_theorems =
 ["BIND_WALK_DECLS",BIND_WALK_DECLS;"BIND_WALK_LEAF_WF",BIND_WALK_LEAF_WF;
  "BIND_WALK_RW",BIND_WALK_RW;"BIND_WALK_STATUS",BIND_WALK_STATUS;
  "BIND_WALK_TABLE_RUN",BIND_WALK_TABLE_RUN];;
