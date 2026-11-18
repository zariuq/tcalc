(* Validate into a temporary, then publish the policy with a total copy. *)
needs "native/hol/kernel_table_writes_load.ml";;

let pl_plan_policy = new_definition(mk_eq(`pl_plan_policy:(int64 list)list`,
  mk_list([pl_step_tm 20 [] 7 8 [] 24;pl_step_tm 3 [] 24 24 [] 7],`:int64 list`)));;

let POLICY_PLAN_FIELDS = prove
 (`MAP (MAP val) pl_plan_policy =
    [[20;56;56;56;56;56;56;56;56;56;7;8;0;0;0;0;0;24];
     [3;56;56;56;56;56;56;56;56;56;24;24;0;0;0;0;0;7]]`,
  REWRITE_TAC[pl_plan_policy;MAP] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV));;

let TAB_POLICY_RUN = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput inp cw ns stk k i cw' ns' stk'.
     tab_run (trow,tn,twd,tdrop,tapp,tput) inp pl_plan_policy 0 (cw,ns,stk) (k,i,(cw',ns',stk'))
     ==> ns' = ns /\ stk' = stk /\ (k = 0 \/ k = 1) /\
         (k = 0 <=> ~(cw 8 <= 2)) /\
         (k = 1 ==> cw' 7 = MAX (cw 7) (cw 8)) /\
         (~(k = 1) ==> cw' 7 = cw 7) /\
         (!j. ~(j = 7) /\ ~(j = 24) ==> cw' j = cw j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pl_plan_policy;tab_run;tab_leaf;LET_DEF;LET_END_DEF;FST;SND] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `(cw:num->num) 8 <= 2` THEN
  ASM_SIMP_TAC[tab_polmax;pl_eqw;pl_set;UNWIND_THM1;UNWIND_THM2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
    ASM_REWRITE_TAC[ARITH_EQ;LEFT_IMP_EXISTS_THM] THEN REPEAT STRIP_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let TAB_POLICY_SAFE = prove
 (`!(tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
        (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) inp s.
     tab_safe tb inp pl_plan_policy s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC TAB_SAFE_TOTAL THEN
  REWRITE_TAC[pl_plan_policy;ALL] THEN CONJ_TAC THEN MATCH_MP_TAC TAB_TOTAL_LEAF THEN
  CONV_TAC STEP_EL_CONV2);;

let POLICY_CW_RANGE = prove
 (`!nctl. 24 < nctl ==> pl_cw_range nctl pl_plan_policy`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_cw_range;pl_plan_policy;MEM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN
  (SUBGOAL_THEN `f = 10 \/ f = 11 \/ f = 12 \/ f = 13 \/ f = 14 \/ f = 15 \/ f = 16 \/ f = 17`
    ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC]) THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
  CONV_TAC STEP_EL_CONV2 THEN ASM_ARITH_TAC);;

let TAB_POLICY_IMPL = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput L inp progs bw ctl nctl budget cfr.
     progs 3 = eqw /\ progs 20 = pol_max /\ pl_cw_range nctl pl_plan_policy
     ==> !st. MEM st pl_plan_policy
              ==> tab_impl (tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr)
                           (trow,tn,twd,tdrop,tapp,tput) inp progs bw ctl budget cfr st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!f. 10 <= f /\ f < 18 ==> val(EL f (st:int64 list)) < nctl` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_cw_range];ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_const_app "MEM" o concl)) THEN
  REWRITE_TAC[pl_plan_policy;MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN
  FIRST(map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN
                      CONV_TAC STEP_EL_CONV2 THEN NO_TAC) [TAB_IMPL_POLMAX;TAB_IMPL_EQW]));;

let TAB_POLICY_DRIVER = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput L inp progs bw ctl nctl budget cfr
    m used res cw ns stk.
     progs 3 = eqw /\ progs 20 = pol_max /\ pl_cw_range nctl pl_plan_policy /\
     drv_sem progs bw ctl budget cfr pl_plan_policy 0 m used res /\
     tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr m (cw,ns,stk) /\
     ~(val budget < val used)
     ==> ?k j cw'. k < 8 /\ FST res = word k /\ FST(SND res) = j /\
          tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr
                  (FST(SND(SND res))) (cw',ns,stk) /\
          ~(val budget < val(SND(SND(SND res)))) /\ (k = 0 \/ k = 1) /\
          (k = 0 <=> ~(cw 8 <= 2)) /\
          (k = 1 ==> cw' 7 = MAX (cw 7) (cw 8)) /\
          (~(k = 1) ==> cw' 7 = cw 7) /\
          (!j. ~(j = 7) /\ ~(j = 24) ==> cw' j = cw j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr:(int64->byte)->(num->num)#S#num list->bool`;
    `(trow,tn,twd,tdrop,tapp,tput):(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
                                  (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
    `inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;
    `pl_plan_policy`;`0`;`m:int64->byte`;`used:int64`;`res:int64#num#(int64->byte)#int64`;
    `(cw,ns,stk):(num->num)#S#num list`] TAB_DRV_BRIDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[TAB_POLICY_SAFE] THEN MATCH_MP_TAC TAB_POLICY_IMPL THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num`
    (X_CHOOSE_THEN `ps:(num->num)#S#num list` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`trow:num->S->num->num list`;`tn:num->S->num`;`twd:num->num`;
                 `tdrop:num->S->num->bool`;`tapp:num->num->S->num list->S->bool`;
                 `tput:num->num->S->num->num->num->S->bool`;`inp:num list`;`cw:num->num`;`ns:S`;
                 `stk:num list`;`k:num`;`j:num`;`FST(ps:(num->num)#S#num list)`;
                 `FST(SND(ps:(num->num)#S#num list))`;`SND(SND(ps:(num->num)#S#num list))`]
                TAB_POLICY_RUN) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `(FST(ps:(num->num)#S#num list),ns,stk) = ps` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM (ASSUME `FST(SND(ps:(num->num)#S#num list)) = ns`);
                GSYM (ASSUME `SND(SND(ps:(num->num)#S#num list)) = stk`);PAIR];ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:num`;`j:num`;`FST(ps:(num->num)#S#num list)`] THEN ASM_REWRITE_TAC[]);;

let policy_plan_theorems =
 ["POLICY_PLAN_FIELDS",POLICY_PLAN_FIELDS;"TAB_POLICY_RUN",TAB_POLICY_RUN;"TAB_POLICY_SAFE",TAB_POLICY_SAFE;
  "POLICY_CW_RANGE",POLICY_CW_RANGE;"TAB_POLICY_IMPL",TAB_POLICY_IMPL;
  "TAB_POLICY_DRIVER",TAB_POLICY_DRIVER];;
leaf_audit policy_plan_theorems policy_plan_theorems;;
