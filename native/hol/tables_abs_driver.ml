(* ABS through the driver, with exact refusal and an all-outcome table frame. *)
needs "native/hol/tables_abs_walk.ml";;

let TAB_ABS_PREPARE_DRIVER = prove
 (`!inp progs bw ctl nctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
    pl_progs_ok progs /\ pl_cw_range nctl pl_abs_prepare /\ ~(val budget < val used) /\
    pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
    tab_rel hol_tables hol_layout inp bw ctl nctl cfr m
            (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
    drv_sem progs bw ctl budget cfr pl_abs_prepare 0 m used res
    ==> ?k cw'.
       (k = 0 \/ k = 1) /\ FST res = word k /\
       val(SND(SND(SND res))) <= val budget /\
       tab_rel hol_tables hol_layout inp bw ctl nctl cfr (FST(SND(SND res)))
          (cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
       pl_inv (cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
       (!j. j < 24 ==> cw' j = cw j) /\
       (k = 1 <=> holr_live 2 (cw 8) (LENGTH ntms) drops /\
                  holr_live 2 (cw 9) (LENGTH ntms) drops /\ FST(EL (cw 8) ntms) = 0) /\
       (k = 1 ==> cw' 28 = FST(SND(EL (cw 8) ntms)) /\ cw' 29 = ntm_ty(EL (cw 8) ntms) /\
                  cw' 30 = ntm_ty(EL (cw 9) ntms) /\ cw' 31 = ntm_db(EL (cw 9) ntms))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASSUME_TAC(MATCH_MP
    (SPECL [`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;
            `nctl:num`;`budget:int64`;`cfr:int64`] TAB_IMPL_ABS_PREPARE)
    (CONJ (ASSUME `pl_progs_ok progs`) (ASSUME `pl_cw_range nctl pl_abs_prepare`))) THEN
  MP_TAC(ISPECL [`tab_rel hol_tables hol_layout inp bw ctl nctl cfr`;
    `hol_tables`;`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;
    `ctl:int64`;`budget:int64`;`cfr:int64`;`pl_abs_prepare`;`0`;
    `m:int64->byte`;`used:int64`;`res:int64#num#(int64->byte)#int64`;
    `(cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate`] TAB_DRV_BRIDGE) THEN
  ASM_SIMP_TAC[TAB_SAFE_ABS_PREPARE] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `i:num`
    (X_CHOOSE_THEN `post:pstate` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPEC `post:pstate`
    (prove(`!p:pstate. ?c ns st. p = (c,ns,st)`,
      REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cw':num->num` (X_CHOOSE_THEN `ns':nstate`
    (X_CHOOSE_THEN `stk':num list` SUBST_ALL_TAC))) THEN
  MP_TAC(SPECL ([`cw:num->num`] @ pl_ns_vars @
    [`stk:num list`;`inp:num list`;`(cw:num->num) 8`;`(cw:num->num) 9`;
     `k:num`;`i:num`;`cw':num->num`;`ns':nstate`;`stk':num list`])
    PL_ABS_PREPARE_RUN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `ns':nstate`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `stk':num list`)) THEN
  MAP_EVERY EXISTS_TAC [`k:num`;`cw':num->num`] THEN
  ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  MATCH_MP_TAC PL_INV_CW THEN EXISTS_TAC `cw:num->num` THEN
  ASM_SIMP_TAC[ARITH_RULE `j <= 6 ==> j < 24`]);;

(* The walk and publication suffix from operands checked by the admission prefix. *)
let TAB_ABS_TAIL_DRIVER = prove
 (`!inp progs bw ctl nctl budget cfr j0 m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk x ty body.
    pl_progs_ok progs /\ progs 10 = bind_walk /\ pl_cw_range nctl pl_abs_suffix /\
    32 < nctl /\ ~(val budget < val used) /\
    pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
    tab_rel hol_tables hol_layout inp bw ctl nctl cfr m
         (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
    holr_live 2 (cw 8) (LENGTH ntms) drops /\ holr_live 2 (cw 9) (LENGTH ntms) drops /\
    fdtm nms tys ntms (cw 8) (TmVar x ty) /\ fdtm nms tys ntms (cw 9) body /\
    cw 28 = FST(SND(EL (cw 8) ntms)) /\ cw 29 = ntm_ty(EL (cw 8) ntms) /\
    cw 30 = ntm_ty(EL (cw 9) ntms) /\ cw 31 = ntm_db(EL (cw 9) ntms) /\
    drv_sem progs bw ctl budget cfr (CONS (EL 8 pl_plan_abs) pl_abs_suffix) j0 m used res
    ==> ?cw' ns'.
        tab_rel hol_tables hol_layout inp bw ctl nctl cfr (FST(SND(SND res))) (cw',ns',stk) /\
        pl_grows (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) ns' /\
        (!(j:num). j < 24 ==> cw' j = cw j) /\
        ~(FST res = word 0) /\ val(SND(SND(SND res))) <= val budget /\
        (FST res = word 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
           (RAbs (cw 8) (cw 9)) ns' /\ pl_inv (cw',ns',stk))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_const_app "drv_sem" o concl)) THEN
  GEN_REWRITE_TAC LAND_CONV [CONJUNCT2 drv_sem] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ABS_WALK_OPCODE] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `st:tisa_state` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u:tisa_state`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))) THEN
  MP_TAC(SPECL ([`inp:num list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;
                `m:int64->byte`;`used:int64`;`cw:num->num`] @ pl_ns_vars @
               [`stk:num list`;`(cw:num->num) 8`;`(cw:num->num) 9`;`x:string`;`ty:holtype`;`body:holterm`;
                `st:tisa_state`;`k:num`;`u:tisa_state`]) TAB_ABS_WALK_RUN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `md:(num#num#num)list`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ABBREV_TAC `cww = pl_set cw 32 (val(tisa_fword u 19))` THEN
  SUBGOAL_THEN `!j. j < 24 ==> cww j = (cw:num->num) j` ASSUME_TAC THENL
   [EXPAND_TAC "cww" THEN REWRITE_TAC[pl_set] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `k < 8` ASSUME_TAC THENL
   [MP_TAC(ASSUME `k = 1 \/ k = 2 \/ k = 3 \/ k = 4`) THEN ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `k = 1 \/ k = 2 \/ k = 3 \/ k = 4`) THEN ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `(word k:int64) = word 1 <=> k = 1` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_WORD_SMALL_EQ THEN ASM_REWRITE_TAC[ARITH_RULE `1 < 8`];ALL_TAC] THEN
  SUBGOAL_THEN `~((word k:int64) = word 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PL_WORD_SMALL_EQ;ARITH_RULE `0 < 8`];ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k = 1` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `md:(num#num#num)list = []` SUBST_ALL_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC ORELSE
      (FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
        rand(concl th) = `md:(num#num#num)list = []`)) THEN ASM_REWRITE_TAC[]);
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`cww:num->num`;`(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN
    ASM_REWRITE_TAC[FST;SND;APPEND_NIL;PL_GROWS_REFL]] THEN
  SUBGOAL_THEN `pl_inv(cww,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)` ASSUME_TAC THENL
   [EXPAND_TAC "cww" THEN ASM_SIMP_TAC[PL_INV_SET;ARITH_RULE `6 < 32`];ALL_TAC] THEN
  SUBGOAL_THEN `!j. j <= 6 ==> cww j = j` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_const_app "pl_inv" (concl th) &&
         fst(dest_pair(rand(concl th))) = `cww:num->num` then
        ACCEPT_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(REWRITE_RULE[pl_inv] th))))
      else failwith "walk control invariant");
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(val(budget:int64) < val(tisa_fword u 21))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NOT_LT];ALL_TAC] THEN
  ASSUME_TAC(MATCH_MP
    (SPECL [`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;
            `nctl:num`;`budget:int64`;`cfr:int64`] TAB_IMPL_ABS_SUFFIX)
    (CONJ (ASSUME `pl_progs_ok progs`) (ASSUME `pl_cw_range nctl pl_abs_suffix`))) THEN
  MP_TAC(ISPECL [`tab_rel hol_tables hol_layout inp bw ctl nctl cfr`;
    `hol_tables`;`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;
    `ctl:int64`;`budget:int64`;`cfr:int64`;`pl_abs_suffix`;`j0 + 1`;
    `drv_after ctl (EL 8 pl_plan_abs) u`;`tisa_fword u 21`;`res:int64#num#(int64->byte)#int64`;
    `(cww,(ctx,nms,tys,ntms,APPEND dbs md,ths,nmap,ymap,drops,pol),stk):pstate`] TAB_DRV_BRIDGE) THEN
  ASM_SIMP_TAC[TAB_SAFE_ABS_SUFFIX] THEN
  DISCH_THEN(X_CHOOSE_THEN `outcome:num` (X_CHOOSE_THEN `i:num`
    (X_CHOOSE_THEN `post:pstate` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPEC `post:pstate`
    (prove(`!p:pstate. ?c ns st. p = (c,ns,st)`,
      REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cw':num->num` (X_CHOOSE_THEN `ns':nstate`
    (X_CHOOSE_THEN `stk':num list` SUBST_ALL_TAC))) THEN
  PL_ROWS_TAC THEN
  MP_TAC(SPECL ([`inp:num list`;`cww:num->num`] @
    (map (fun v -> if v = `dbs:(num#num#num)list` then `APPEND dbs md:(num#num#num)list` else v) pl_ns_vars) @ [`stk:num list`;
    `j0 + 1`;`outcome:num`;`i:num`;`cw':num->num`;`ns':nstate`;`stk':num list`]) PL_ABS_SUFFIX_GROWS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `stk':num list`)) THEN
  MAP_EVERY EXISTS_TAC [`cw':num->num`;`ns':nstate`] THEN
  ASM_SIMP_TAC[PL_WORD_SMALL_EQ;ARITH_RULE `0 < 8 /\ 1 < 8`;GSYM NOT_LT] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_GROWS_TRANS THEN
    EXISTS_TAC `(ctx,nms,tys,ntms,APPEND dbs md,ths,nmap,ymap,drops,pol):nstate` THEN
    ASM_REWRITE_TAC[pl_grows;PL_APPEND_SELF] THEN EXISTS_TAC `md:(num#num#num)list` THEN REFL_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPECL ([`inp:num list`;`cww:num->num`] @ pl_ns_vars @
      [`stk:num list`;`(cw:num->num) 8`;`(cw:num->num) 9`;`x:string`;`ty:holtype`;`body:holterm`;
       `md:(num#num#num)list`;`val(tisa_fword u 19)`;`j0 + 1`;`i:num`;`cw':num->num`;`ns':nstate`;
       `stk:num list`]) PL_ABS_SUFFIX_FIRED) THEN
    SUBGOAL_THEN `cww 29 = (cw:num->num) 29 /\ cww 30 = cw 30 /\ cww 32 = val(tisa_fword u 19)`
     STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "cww" THEN REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `8 < 24 /\ 9 < 24`]]);;

let TAB_ABS_DRIVER_RUN = prove
 (`!inp progs bw ctl nctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
    pl_progs_ok progs /\ progs 10 = bind_walk /\ pl_cw_range nctl pl_plan_abs /\ ~(val budget < val used) /\
    pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
    tab_rel hol_tables hol_layout inp bw ctl nctl cfr m
         (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
    drv_sem progs bw ctl budget cfr pl_plan_abs 0 m used res
    ==> ?cw' ns'.
        tab_rel hol_tables hol_layout inp bw ctl nctl cfr (FST(SND(SND res))) (cw',ns',stk) /\
        pl_grows (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) ns' /\
        (!j. j < 24 ==> cw' j = cw j) /\ val(SND(SND(SND res))) <= val budget /\
        (FST res = word 0 <=> ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
                                           (RAbs (cw 8) (cw 9)) /\
                ?x ty p. fdtm nms tys ntms (cw 8) (TmVar x ty) /\ fdtm nms tys ntms (cw 9) p)) /\
        (FST res = word 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
                    (RAbs (cw 8) (cw 9)) ns' /\ pl_inv (cw',ns',stk))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ABS_PARTS_CONTROL_RANGE o
    check (fun th -> concl th = `pl_cw_range nctl pl_plan_abs`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ABS_PLAN_CONTROL_SIZE o
    check (fun th -> concl th = `pl_cw_range nctl pl_plan_abs`)) THEN
  PL_INV_ASM(fun th -> ASSUME_TAC(MATCH_MP PL_ABS_GUARDS th)) THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[ABS_PLAN_PARTS] o check (is_const_app "drv_sem" o concl)) THEN
  REWRITE_TAC[DRV_SEM_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `prep:int64#num#(int64->byte)#int64` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(SPECL ([`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
    `budget:int64`;`cfr:int64`;`m:int64->byte`;`used:int64`;`prep:int64#num#(int64->byte)#int64`;
    `cw:num->num`] @ pl_ns_vars @ [`stk:num list`]) TAB_ABS_PREPARE_DRIVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (X_CHOOSE_THEN `cw0:num->num` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  ASM_CASES_TAC `k0 = 1` THENL
   [ALL_TAC;
    SUBGOAL_THEN `k0 = 0` SUBST_ALL_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ]) THEN
    ASM_REWRITE_TAC[WORD_SMALL_NE] THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`cw0:num->num`;`(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`] THEN
    ASM_REWRITE_TAC[ARITH_EQ;WORD_SMALL_NE;PL_GROWS_REFL]] THEN
  ASM_REWRITE_TAC[ABS_PREPARE_LENGTH;ADD_CLAUSES] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C EQ_MP (ASSUME `k0 = 1`) o
    check (fun th -> is_iff(concl th) && lhand(concl th) = `k0 = 1`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `k0 = 1`) o
    check (fun th -> is_imp(concl th) && lhand(concl th) = `k0 = 1`)) THEN
  SUBGOAL_THEN `nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAbs (cw 8) (cw 9)) /\
      ?x ty b. fdtm nms tys ntms (cw 8) (TmVar x ty) /\ fdtm nms tys ntms (cw 9) b`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `(cw0:num->num) 8 = (cw:num->num) 8 /\ cw0 9 = cw 9`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[ARITH_RULE `8 < 24 /\ 9 < 24`];ALL_TAC] THEN
  MP_TAC(SPECL ([`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
    `budget:int64`;`cfr:int64`;`8`;`FST(SND(SND(prep:int64#num#(int64->byte)#int64)))`;
    `SND(SND(SND(prep:int64#num#(int64->byte)#int64)))`;`res:int64#num#(int64->byte)#int64`;`cw0:num->num`]
       @ pl_ns_vars @ [`stk:num list`;`x:string`;`ty:holtype`;`b:holterm`]) TAB_ABS_TAIL_DRIVER) THEN
  ASM_SIMP_TAC[NOT_LT;ARITH_RULE `39 < n ==> 32 < n`] THEN
  DISCH_THEN(X_CHOOSE_THEN `cw':num->num` (X_CHOOSE_THEN `ns':nstate` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`cw':num->num`;`ns':nstate`] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
