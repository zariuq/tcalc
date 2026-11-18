(* The machine policy word and the logical axiom policy agree at boundaries. *)
needs "native/hol/kernel_boot_load.ml";;
needs "native/hol/policy_plan.ml";;

let HOL_POLICY_DRIVER = prove
 (`!inp progs bw ctl nctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk p.
     progs 3 = eqw /\ progs 20 = pol_max /\ pl_cw_range nctl pl_plan_policy /\
     drv_sem progs bw ctl budget cfr pl_plan_policy 0 m used res /\
     tab_rel hol_tables hol_layout inp bw ctl nctl cfr m
             (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     hol_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     cw 8 = p /\ ~(val budget < val used)
     ==> ?k cw' pol'. FST res = word k /\ (k = 0 \/ k = 1) /\
          tab_rel hol_tables hol_layout inp bw ctl nctl cfr (FST(SND(SND res)))
                  (cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol'),stk) /\
          hol_inv (cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol'),stk) /\
          (k = 0 <=> ~(p <= 2)) /\
          pol' = (if k = 1 then MAX pol p else pol) /\ pol <= pol' /\
          (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RPolicy p)
                              (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hol_trow`;`hol_tn`;`hol_twd`;`hol_tdrop`;`hol_tapp`;`hol_tput`;
                 `hol_layout`;`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;
                 `ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;`m:int64->byte`;`used:int64`;
                 `res:int64#num#(int64->byte)#int64`;`cw:num->num`;
                 `(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`;`stk:num list`]
                TAB_POLICY_DRIVER) THEN
  ASM_REWRITE_TAC[GSYM hol_tables] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num`
    (X_CHOOSE_THEN `cw':num->num` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(cw:num->num) 7 = pol` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOL_INV];ALL_TAC] THEN
  SUBGOAL_THEN `!j. j <= 6 ==> (cw':num->num) j = cw j` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `(cw':num->num) 22 = cw 22` ASSUME_TAC THENL
   [MATCH_MP_TAC(SPEC `22` (ASSUME `!j. ~(j = 7) /\ ~(j = 24) ==> (cw':num->num) j = cw j`)) THEN
    CONV_TAC NUM_REDUCE_CONV;ALL_TAC] THEN
  ASM_CASES_TAC `k = 1` THENL
   [MAP_EVERY EXISTS_TAC [`k:num`;`cw':num->num`;`MAX pol p`];
    MAP_EVERY EXISTS_TAC [`k:num`;`cw':num->num`;`pol:num`]] THEN
  ASM_REWRITE_TAC[LE_REFL;ARITH_RULE `a <= MAX a b`] THEN
  REPEAT CONJ_TAC THEN FIRST
   [ASM_REWRITE_TAC[] THEN NO_TAC;
    MATCH_MP_TAC(GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL TAB_REL_POL_HOL)))) THEN
      EXISTS_TAC `pol:num` THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    MATCH_MP_TAC HOL_INV_POL_CW THEN MAP_EVERY EXISTS_TAC [`cw:num->num`;`pol:num`] THEN
      ASM_SIMP_TAC[] THEN NO_TAC;
    TRY DISCH_TAC THEN MATCH_MP_TAC(NAT_STEP_OF `RPolicy`) THEN ASM_MESON_TAC[ARITH_EQ]]);;

let policy_q =
 `\(inp:num list) (before:pstate) (following:nstate).
    nat_step (FST(SND before)) (RPolicy(FST before 8)) following`;;
let policy_g = `\(inp:num list) (before:pstate). ~(FST before 8 <= 2)`;;

let TAB_LIFTS_POLICY = prove
 (list_mk_icomb "tab_lifts"
   [`hol_tables`;`hol_layout`;`hol_progs`;`pl_plan_policy`;policy_q;policy_g;`hol_inv`],
  REWRITE_TAC[tab_lifts] THEN
  MAP_EVERY X_GEN_TAC
   [`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
    `budget:int64`;`cfr:int64`;`m:int64->byte`;`used:int64`;`res:int64#num#(int64->byte)#int64`] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC (pl_cw_var :: pl_ns_vars @ [pl_stk_var]) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST;SND;hol_progs;pl_progs_ok] THEN STRIP_TAC THEN
  MP_TAC(SPECL ([`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
                `budget:int64`;`cfr:int64`;`m:int64->byte`;`used:int64`;
                `res:int64#num#(int64->byte)#int64`;`cw:num->num`] @
               pl_ns_vars @ [`stk:num list`;`(cw:num->num) 8`]) HOL_POLICY_DRIVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `cw':num->num`
    (X_CHOOSE_THEN `pol':num` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(FST(res:int64#num#(int64->byte)#int64) = word 1 <=> k = 1) /\
                (FST res = word 0 <=> k = 0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[WORD_SMALL_NE];ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `(cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol'),stk):pstate` THEN
  ASM_SIMP_TAC[FST;SND] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    is_const_app "nat_step" (rand(concl th)))) THEN ASM_REWRITE_TAC[]);;

let TAB_RD_PLAN_OK_POLICY = tab_rd_plan_ok_hol pl_plan_policy;;
let POLICY_NCTL = plan_nctl pl_plan_policy;;
let POLICY_PAYLOADS = prove
 (`!st. MEM st pl_plan_policy ==> ~(17 <= val(EL 17 st) /\ val(EL 17 st) < 24)`,
  GEN_TAC THEN REWRITE_TAC[pl_plan_policy;MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN CONV_TAC STEP_EL_CONV2);;
let LF_POLICY = TAB_LIFTS_POLICY,TAB_RD_PLAN_OK_POLICY,POLICY_PAYLOADS,POLICY_NCTL;;
let pl_handler_policy,HANDLER_POLICY_TAB = tab_kind_handler "policy" tab_op0_shape pl_plan_policy LF_POLICY;;
let KC_POLICY_TAB = tab_kind_contract_of HANDLER_POLICY_TAB `37`;;

let TAB_IMPL_POLICY = REWRITE_RULE[GSYM hol_tables] (ISPECL
 [`hol_trow`;`hol_tn`;`hol_twd`;`hol_tdrop`;`hol_tapp`;`hol_tput`;`hol_layout`] TAB_POLICY_IMPL);;
let TAB_SAFE_POLICY = ISPEC `hol_tables` TAB_POLICY_SAFE;;
let KE_POLICY_TAB = tab_kind_every_of "policy" tab_op0_shape RD_ONLY58_PREFIX_OP0
  pl_plan_policy LF_POLICY TAB_IMPL_POLICY TAB_SAFE_POLICY `37`;;

let tables_policy_theorems =
 ["HOL_POLICY_DRIVER",HOL_POLICY_DRIVER;"TAB_LIFTS_POLICY",TAB_LIFTS_POLICY;
  "TAB_RD_PLAN_OK_POLICY",TAB_RD_PLAN_OK_POLICY;"POLICY_NCTL",POLICY_NCTL;"POLICY_PAYLOADS",POLICY_PAYLOADS;
  "HANDLER_POLICY_TAB",HANDLER_POLICY_TAB;"KC_POLICY_TAB",KC_POLICY_TAB;
  "TAB_IMPL_POLICY",TAB_IMPL_POLICY;"TAB_SAFE_POLICY",TAB_SAFE_POLICY;"KE_POLICY_TAB",KE_POLICY_TAB];;
leaf_audit tables_policy_theorems tables_policy_theorems;;
