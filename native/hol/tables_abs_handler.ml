needs "native/hol/tables_abs_driver.ml";;
(* The ABS plan can use the ordinary record framing and operand decoding. *)
needs "native/hol/handlers_tab.ml";;
needs "native/hol/handlers_hol.ml";;
needs "native/hol/reader_plans_tab.ml";;
needs "native/hol/contract_tab.ml";;
needs "native/hol/rec_induction_tab.ml";;
needs "native/hol/every_tab.ml";;

let abs_hol_progs = new_definition
 `abs_hol_progs p <=> pl_progs_ok p /\ p 10 = bind_walk`;;

let ABS_INV_FROM_GROWTH = prove
 (`!cw cw' (s:nstate) s' stk.
      hol_inv (cw,s,stk) /\ pl_grows s s' /\ pl_inv (cw',s',stk) /\
      (!j. j < 24 ==> cw' j = cw j)
      ==> hol_inv (cw',s',stk)`,
  REWRITE_TAC[FORALL_PAIR_THM;HOL_INV;pl_grows] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE `7 < 24 /\ 22 < 24`]);;

let abs_step_q =
 `\(inp:num list) ((cw,s,stk):pstate) (s':nstate). nat_step s (RAbs (cw 8) (cw 9)) s'`;;
let abs_step_g =
 `\(inp:num list) ((cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate).
     ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAbs (cw 8) (cw 9)) /\
       ?x ty body. fdtm nms tys ntms (cw 8) (TmVar x ty) /\ fdtm nms tys ntms (cw 9) body)`;;

let TAB_LIFTS_ABS = prove
 (list_mk_icomb "tab_lifts" [`hol_tables`;`hol_layout`;`abs_hol_progs`;`pl_plan_abs`;
                            abs_step_q;abs_step_g;`hol_inv`],
  REWRITE_TAC[tab_lifts] THEN
  MAP_EVERY X_GEN_TAC [`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
    `budget:int64`;`cfr:int64`;`m:int64->byte`;`used:int64`;`res:int64#num#(int64->byte)#int64`] THEN
  REWRITE_TAC[FORALL_PAIR_THM;abs_hol_progs] THEN
  MAP_EVERY X_GEN_TAC ([`cw:num->num`] @ pl_ns_vars @ [`stk:num list`]) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[HOL_INV] o check (is_const_app "hol_inv" o concl)) THEN
  MP_TAC(SPECL ([`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
    `budget:int64`;`cfr:int64`;`m:int64->byte`;`used:int64`;`res:int64#num#(int64->byte)#int64`;
    `cw:num->num`] @ pl_ns_vars @ [`stk:num list`]) TAB_ABS_DRIVER_RUN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cw':num->num` (X_CHOOSE_THEN `ns':nstate`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `(cw',ns',stk):pstate` THEN ASM_REWRITE_TAC[FST;SND] THEN
  SUBGOAL_THEN `nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAbs (cw 8) (cw 9)) ns' /\
                pl_inv (cw',ns',stk)` STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ABS_INV_FROM_GROWTH THEN
  MAP_EVERY EXISTS_TAC [`cw:num->num`;`(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`] THEN
  ASM_REWRITE_TAC[]);;

let TAB_RD_PLAN_OK_ABS = prove
 (`!progs nctl. abs_hol_progs progs /\ pl_cw_range nctl pl_plan_abs
     ==> tab_rd_plan_ok hol_layout progs nctl pl_plan_abs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_hol_progs;pl_progs_ok;pl_cw_range;tab_rd_plan_ok] THEN STRIP_TAC THEN
  X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(EL 17 (st:int64 list)) < nctl` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o check (is_const_app "MEM" o concl)) THEN
  REWRITE_TAC[pl_plan_abs;MEM] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC)) THEN TRY(DISCH_THEN SUBST1_TAC) THEN
  CONV_TAC STEP_EL_CONV2 THEN
  ASM_REWRITE_TAC(PL_LEAVES_WF @ PL_LEAVES_RW @ [BIND_WALK_LEAF_WF;BIND_WALK_RW;
    ARITH_RULE `r < 4 <=> r = 0 \/ r = 1 \/ r = 2 \/ r = 3`]) THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;FORALL_AND_THM;FORALL_UNWIND_THM2] THEN
  CONV_TAC STEP_EL_CONV2 THEN REWRITE_TAC[TAB_SLOTS_HOL;MEM] THEN CONV_TAC NUM_REDUCE_CONV);;

let ABS_PAYLOADS = prove
 (`!st. MEM st pl_plan_abs ==> 24 <= val(EL 17 st)`,
  MESON_TAC[ABS_PLAN_PRESERVES_CONTROL]);;

let ABS_NCTL = prove
 (`!nctl. pl_cw_range nctl pl_plan_abs ==> 24 < nctl`,
  MESON_TAC[ABS_PLAN_CONTROL_SIZE;ARITH_RULE `39 < n ==> 24 < n`]);;

let pl_handler_abs = tab_handler_def "abs" `APPEND pl_prefix_op01 (APPEND pl_plan_abs pl_inc_cnt)`;;

let ABS_READER_PROGS = `\p:num->tisa_prog. p 3 = eqw`;;

let abs_op01_shape =
  let prefix = REWRITE_RULE[tab_enc_reads]
    (ISPECL [`hol_tables`;`hol_layout`;ABS_READER_PROGS] TAB_ENC_READS_OP01) in
  {tab_op01_shape with ts_rd = prefix};;

let HANDLER_ABS_TAB =
  let sh = abs_op01_shape and plan = `pl_plan_abs` in
  let gen = SPEC_ALL(ISPECL [`hol_tables`;`hol_layout`;ABS_READER_PROGS;sh.ts_pfx;sh.ts_d;sh.ts_w;sh.ts_l;
         `abs_hol_progs`;plan;abs_step_q;abs_step_g;`hol_inv`] TAB_HANDLER_GEN) in
  let premise,result = dest_imp(concl gen) in
  let statics, dynamics = List.partition (fun term -> frees term = []) (conjuncts premise) in
  let static_ths = map (fun term -> prove(term,TAB_STATIC_TAC sh TAB_LIFTS_ABS ABS_PAYLOADS)) statics in
  let derived t = is_const_app "tab_rd_plan_ok" t || t = `(progs:num->tisa_prog) 3 = eqw` || t = `24 < nctl` in
  let retained = filter (fun t -> not(derived t)) dynamics in
  let driver = find (is_const_app "drv_sem") retained in
  let retained = map (fun t -> if t = driver then
     subst [`pl_handler_abs`,rhs(concl pl_handler_abs)] t else rhs(concl(TOP_DEPTH_CONV BETA_CONV t))) retained in
  let goal = mk_imp(list_mk_conj retained,rhs(concl(TAB_HANDLER_NORM_CONV result))) in
  let checked = prove(goal,
    STRIP_TAC THEN MP_TAC gen THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pl_handler_abs]) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP ABS_NCTL o check (is_const_app "pl_cw_range" o concl)) THEN
    SUBGOAL_THEN `tab_rd_plan_ok hol_layout progs nctl pl_plan_abs` ASSUME_TAC THENL
     [MATCH_MP_TAC TAB_RD_PLAN_OK_ABS THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[abs_hol_progs;pl_progs_ok] o
      check (is_const_app "abs_hol_progs" o concl)) THEN
    ASM_REWRITE_TAC static_ths THEN CONV_TAC TAB_HANDLER_NORM_CONV THEN ASM_REWRITE_TAC[]) in
  GEN_ALL checked;;

let KC_ABS_TAB = tab_kind_contract_of HANDLER_ABS_TAB `7`;;
