(* The abstraction constructor's read-only guard prefix. *)
needs "native/hol/kernel_table_frames_load.ml";;

let FDTM_VAR_TAG = prove
 (`!nms tys ntms i p.
     fdtm nms tys ntms i p
     ==> (FST(EL i ntms) = 0 <=> ?x ty. p = TmVar x ty)`,
  REPLICATE_TAC 3 GEN_TAC THEN MATCH_MP_TAC fdtm_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FST;holterm_DISTINCT;ARITH_EQ] THEN MESON_TAC[]);;

let PL_ABS_GUARDS = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk v t.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> ((nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAbs v t) /\
           ?x ty tb. fdtm nms tys ntms v (TmVar x ty) /\ fdtm nms tys ntms t tb) <=>
          holr_live 2 v (LENGTH ntms) drops /\
          holr_live 2 t (LENGTH ntms) drops /\ FST(EL v ntms) = 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[nat_ops_live;holr_operands;ALL;FST;SND] THEN
  ASM_CASES_TAC `holr_live 2 v (LENGTH(ntms:(num#num#num#num#num)list)) drops` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `holr_live 2 t (LENGTH(ntms:(num#num#num#num#num)list)) drops` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `v < LENGTH(ntms:(num#num#num#num#num)list) /\ t < LENGTH ntms`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[holr_live];ALL_TAC] THEN
  MP_TAC(SPECL ([`cw:num->num`] @ pl_ns_vars @ [`stk:num list`;`v:num`]) PL_TM_ROW) THEN
  MP_TAC(SPECL ([`cw:num->num`] @ pl_ns_vars @ [`stk:num list`;`t:num`]) PL_TM_ROW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `pt:holterm` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `pv:holterm` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`nms:string list`;`tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`;`v:num`;`pv:holterm`] FDTM_VAR_TAG) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[FDTM_FUN]);;

pl_begin();;
let _ = let _ = pl_live_tm pl_OP0 in
        let _ = pl_live_tm pl_OP1 in
        let tag = pl_f_tm pl_OP0 0 in
        pl_eqw_c tag 0;;
let pl_abs_guard_plan = new_definition
  (mk_eq(`pl_abs_guard_plan:(int64 list)list`,pl_plan()));;

let PL_ABS_GUARD_RUN = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp v t k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     cw 8 = v /\ cw 9 = t /\
     tab_run hol_tables inp pl_abs_guard_plan 0
       (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) (k,i,(cw',ns',stk'))
     ==> (k = 0 \/ k = 1) /\
         ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\ stk' = stk /\
         (k = 1 <=> holr_live 2 v (LENGTH ntms) drops /\
                    holr_live 2 t (LENGTH ntms) drops /\ FST(EL v ntms) = 0) /\
         (!j. j < 24 ==> cw' j = cw j)`,
  TAB_START_TAC pl_abs_guard_plan THEN
  REWRITE_TAC[holr_live;pl_f5] THEN ASM_REWRITE_TAC[] THEN
  TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_set] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let TAB_IMPL_ABS_GUARDS = prove
 (tab_plan_impl_goal `pl_abs_guard_plan`,TAB_PLAN_IMPL_TAC2 pl_abs_guard_plan);;

let TAB_SAFE_ABS_GUARDS = prove
 (tab_safe_goal `pl_abs_guard_plan`,TAB_SAFE_PLAN_TAC pl_abs_guard_plan);;

let ABS_GUARD_POSITIVE = prove
 (`?x ty tb.
      fdtm ["x"] [(0,0,0)] [(0,0,0,0,0)] 0 (TmVar x ty) /\
      fdtm ["x"] [(0,0,0)] [(0,0,0,0,0)] 0 tb`,
  MAP_EVERY EXISTS_TAC [`"x":string`;`TyVar "x"`;`TmVar "x" (TyVar "x")`] THEN
  REWRITE_TAC[] THEN
  MP_TAC(SPECL [`["x"]:string list`;`[(0,0,0)]:(num#num#num)list`;
                `[(0,0,0,0,0)]:(num#num#num#num#num)list`;
                `0`;`0`;`0`;`0`;`0`;`TyVar "x"`] FDTM_VAR) THEN
  REWRITE_TAC[LENGTH;EL;HD;ARITH] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(SPECL [`0`;`0`;`0`] (CONJUNCT1(ISPECL
    [`["x"]:string list`;`[(0,0,0)]:(num#num#num)list`] fdty_RULES))) THEN
  REWRITE_TAC[LENGTH;EL;HD;ARITH]);;

let ABS_GUARD_NEGATIVE = prove
 (`(!n drops. ~holr_live 2 n n drops) /\
   (!n v drops. MEM (2,v) drops ==> ~holr_live 2 v n drops) /\
   ~(FST(1,0,0,0,0) = 0)`,
  REWRITE_TAC[holr_live;LT_REFL;FST;ARITH_EQ] THEN MESON_TAC[]);;

let tables_abs_guard_theorems =
 ["FDTM_VAR_TAG",FDTM_VAR_TAG;"PL_ABS_GUARDS",PL_ABS_GUARDS;
  "PL_ABS_GUARD_RUN",PL_ABS_GUARD_RUN;
  "TAB_IMPL_ABS_GUARDS",TAB_IMPL_ABS_GUARDS;"TAB_SAFE_ABS_GUARDS",TAB_SAFE_ABS_GUARDS;
  "ABS_GUARD_POSITIVE",ABS_GUARD_POSITIVE;"ABS_GUARD_NEGATIVE",ABS_GUARD_NEGATIVE];;
