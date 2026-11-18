(* Constructors whose plans only grow tables need no theorem-row change on any exit. *)
needs "native/hol/tables_abs_handler.ml";;

let TAB_HANDLER_GROWTH = prove
 (`!R pfx (D:num list->A->bool) W Ln P progs bw ctl nctl budget cfr m used res cw ns stk inp c.
    tab_prefix_rd hol_tables hol_layout R pfx D W Ln /\
    (!cw c ns stk v. hol_inv(cw,ns,stk) ==> hol_inv(W cw c v,ns,stk)) /\
    rd_only58_ok progs nctl pfx /\ rd_only58_ok progs nctl pl_inc_cnt /\
    progs 3 = eqw /\ rd_progs_ok progs /\ R progs /\ 24 < nctl /\ rd_tab_apart hol_layout bw /\
    (!j mi used ri cwi.
       drv_sem progs bw ctl budget cfr P j mi used ri /\
       tab_rel hol_tables hol_layout inp bw ctl nctl cfr mi (cwi,ns,stk) /\
       hol_inv(cwi,ns,stk) /\ ~(val budget < val used)
       ==> ?post. tab_rel hol_tables hol_layout inp bw ctl nctl cfr (FST(SND(SND ri))) post /\
                  pl_grows ns (FST(SND post)) /\ ~(val budget < val(SND(SND(SND ri))))) /\
    drv_sem progs bw ctl budget cfr (APPEND pfx (APPEND P pl_inc_cnt)) 0 m used res /\
    tab_rel hol_tables hol_layout inp bw ctl nctl cfr m (cw,ns,stk) /\ hol_inv(cw,ns,stk) /\
    rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
    ==> ?post. tab_rel hol_tables hol_layout inp bw ctl nctl cfr (FST(SND(SND res))) post /\
               pl_grows ns (FST(SND post))`,
  let r1 = `r1:int64#num#(int64->byte)#int64` and r2 = `r2:int64#num#(int64->byte)#int64` in
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[rd_rel] o check (is_const_app "rd_rel" o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_const_app "drv_sem" o concl)) THEN
  REWRITE_TAC[DRV_SEM_APPEND] THEN DISCH_THEN(X_CHOOSE_THEN r1 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_CASES_TAC `FST(r1:int64#num#(int64->byte)#int64) = word 1` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`hol_tables`;`hol_layout`;`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;
      `ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;`pfx:(int64 list)list`;`0`;`m:int64->byte`;
      `used:int64`;r1;`cw:num->num`;`ns:nstate`;`stk:num list`] TAB_RD_ONLY_KEEPS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `cw1:num->num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(cw1,ns,stk):pstate` THEN ASM_REWRITE_TAC[FST;SND;PL_GROWS_REFL]] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
    `budget:int64`;`cfr:int64`;`0`;`m:int64->byte`;`used:int64`;r1;`cw:num->num`;`ns:nstate`;
    `stk:num list`;`c:num`] o REWRITE_RULE[tab_prefix_rd] o check (is_const_app "tab_prefix_rd" o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[DRV_SEM_APPEND] THEN DISCH_THEN(X_CHOOSE_THEN r2 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `hol_inv((W:(num->num)->num->A->num->num) cw c v,ns,stk)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[];ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && tab_has_const "drv_sem" (concl th) && tab_has_const "pl_grows" (concl th) then
      let call = SPECL [`0 + LENGTH(pfx:(int64 list)list)`;
        `FST(SND(SND(r1:int64#num#(int64->byte)#int64)))`;`used:int64`;r2;
        `(W:(num->num)->num->A->num->num) cw c v`] th in
      SUBGOAL_THEN (lhand(concl call)) (X_CHOOSE_THEN `p2:pstate` STRIP_ASSUME_TAC o MP call)
    else failwith "plan growth") THENL [ASM_REWRITE_TAC[];ALL_TAC] THEN
  ASM_CASES_TAC `FST(r2:int64#num#(int64->byte)#int64) = word 1` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `p2:pstate` THEN ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`hol_tables`;`hol_layout`;`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;
    `ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;`pl_inc_cnt`;
    `(0 + LENGTH(pfx:(int64 list)list)) + LENGTH(P:(int64 list)list)`;
    `FST(SND(SND(r2:int64#num#(int64->byte)#int64)))`;`SND(SND(SND(r2:int64#num#(int64->byte)#int64)))`;
    `res:int64#num#(int64->byte)#int64`;`FST(p2:pstate)`;`FST(SND(p2:pstate))`;
    `SND(SND(p2:pstate))`] TAB_RD_ONLY_KEEPS) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN(X_CHOOSE_THEN `cw3:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(cw3,FST(SND(p2:pstate)),SND(SND(p2:pstate))):pstate` THEN ASM_REWRITE_TAC[FST;SND]);;

let ABS_DRIVER_GROWTH = prove
 (`!inp progs bw ctl nctl budget cfr i m used res cw ns stk.
     abs_hol_progs progs /\ pl_cw_range nctl pl_plan_abs /\
     drv_sem progs bw ctl budget cfr pl_plan_abs i m used res /\
     tab_rel hol_tables hol_layout inp bw ctl nctl cfr m (cw,ns,stk) /\
     hol_inv(cw,ns,stk) /\ ~(val budget < val used)
     ==> ?p. tab_rel hol_tables hol_layout inp bw ctl nctl cfr (FST(SND(SND res))) p /\
             pl_grows ns (FST(SND p)) /\ ~(val budget < val(SND(SND(SND res))))`,
  MAP_EVERY X_GEN_TAC [`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
    `budget:int64`;`cfr:int64`;`i:num`;`m:int64->byte`;`used:int64`;
    `res:int64#num#(int64->byte)#int64`;`cw:num->num`] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC (pl_ns_vars @ [`stk:num list`]) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[HOL_INV] o check (is_const_app "hol_inv" o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[abs_hol_progs] o check (is_const_app "abs_hol_progs" o concl)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `r0:int64#num#(int64->byte)#int64` STRIP_ASSUME_TAC o
    MATCH_MP DRV_SEM_AT0 o check (is_const_app "drv_sem" o concl)) THEN
  MP_TAC(SPECL ([`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
    `budget:int64`;`cfr:int64`;`m:int64->byte`;`used:int64`;`r0:int64#num#(int64->byte)#int64`;
    `cw:num->num`] @ pl_ns_vars @ [`stk:num list`]) TAB_ABS_DRIVER_RUN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `cw':num->num` (X_CHOOSE_THEN `ns':nstate`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  EXISTS_TAC `(cw',ns',stk):pstate` THEN ASM_REWRITE_TAC[FST;SND;NOT_LT]);;

let ABS_HANDLER_GROWS = prove
 (`!progs bw ctl nctl budget cfr m used res cw ns stk inp c.
     abs_hol_progs progs /\ rd_progs_ok progs /\ pl_cw_range nctl pl_plan_abs /\ rd_tab_apart hol_layout bw /\
     drv_sem progs bw ctl budget cfr pl_handler_abs 0 m used res /\
     tab_rel hol_tables hol_layout inp bw ctl nctl cfr m (cw,ns,stk) /\ hol_inv(cw,ns,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> ?post. tab_rel hol_tables hol_layout inp bw ctl nctl cfr (FST(SND(SND res))) post /\
                pl_grows ns (FST(SND post))`,
  let sh = abs_op01_shape in
  let gen = SPEC_ALL(ISPECL [ABS_READER_PROGS;sh.ts_pfx;sh.ts_d;sh.ts_w;sh.ts_l;`pl_plan_abs`] TAB_HANDLER_GROWTH) in
  let statics = filter (fun term -> frees term = []) (conjuncts(lhand(concl gen))) in
  let static_ths = map (fun term -> prove(term,TAB_STATIC_TAC sh TAB_LIFTS_ABS ABS_PAYLOADS)) statics in
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ABS_NCTL o check (is_const_app "pl_cw_range" o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[abs_hol_progs;pl_progs_ok] o check (is_const_app "abs_hol_progs" o concl)) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[pl_handler_abs] o check (is_const_app "drv_sem" o concl)) THEN
  MP_TAC gen THEN ASM_REWRITE_TAC static_ths THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RD_ONLY58_PREFIX_OP01 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RD_ONLY58_INC_CNT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`j:num`;`mi:int64->byte`;`ui:int64`;`ri:int64#num#(int64->byte)#int64`;`cwi:num->num`] THEN
      STRIP_TAC THEN
      MP_TAC(SPECL [`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
        `budget:int64`;`cfr:int64`;`j:num`;`mi:int64->byte`;`ui:int64`;`ri:int64#num#(int64->byte)#int64`;
        `cwi:num->num`;`ns:nstate`;`stk:num list`] ABS_DRIVER_GROWTH) THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `post:pstate` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `post:pstate` THEN ASM_REWRITE_TAC[]]);;

let KE_ABS_TAB = prove
 (`!progs bw ctl nctl budget cfr.
     abs_hol_progs progs /\ rd_progs_ok progs /\ pl_cw_range nctl pl_plan_abs /\ rd_tab_apart hol_layout bw
     ==> tab_kind_every hol_layout progs bw ctl nctl budget cfr pl_handler_abs 7`,
  REWRITE_TAC[tab_kind_every] THEN MESON_TAC[ABS_HANDLER_GROWS]);;
