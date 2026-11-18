(* ========================================================================= *)
(* COMB s t over the general layer: its plan (PLANS.txt, section 6: live s,  *)
(* live t; s's type row y; FUNARGS(y) -> (A,B) [REFUSED: not a function];   *)
(* eqw A, t's type row [REFUSED: argument type]; IDB(3, s's image, t's      *)
(* image) -> d; append the term row (K2,s,t,B,d)), its analysis over HOL's  *)
(* tables (PL_COMB: FIRED = COMB's nat_step + pl_inv; REFUSED exactly when  *)
(* an operand is not live or s is not a function of t's type), and through  *)
(* the driver over HOL's full layout (PL_COMB_TAB). The bridge dispatch now *)
(* also reads keyed tables (TAB_HOL_BRIDGE2, TAB_IMPL_ROWW_KEY).            *)
(*                                                                           *)
(* Loaded after tables_old.ml and tables_keyrow.ml.                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The plan.                                                                 *)
(* ------------------------------------------------------------------------- *)

pl_begin();;
let _ = let _ = pl_live_tm pl_OP0 in let _ = pl_live_tm pl_OP1 in
        let fs = pl_f_tm pl_OP0 3 in let tt = pl_f_tm pl_OP1 3 in
        let (a,b) = pl_funargs fs in let _ = pl_eqw_c a tt in
        let is = pl_f_tm pl_OP0 4 in let it = pl_f_tm pl_OP1 4 in
        let d = pl_idb 3 is it in
        pl_emit pl_APPEND pl_TM 2 pl_OP0 [5; pl_OP1; b; d];;
let pl_plan_comb = new_definition(mk_eq(`pl_plan_comb:(int64 list)list`, pl_plan()));;

(* ------------------------------------------------------------------------- *)
(* FIRED: the operands' terms decode, s's type is a function from t's type, *)
(* the combination's image interned, its row appended.                       *)
(* ------------------------------------------------------------------------- *)

let NAT_STEP_COMB = el 5 (CONJUNCTS nat_step_RULES);;
let PL_COMB_FIRED = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk s t d md cw'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     holr_live 2 s (LENGTH ntms) drops /\ holr_live 2 t (LENGTH ntms) drops /\
     pl_fun_ok tys (ntm_ty (EL s ntms)) /\ pl_fun_dom tys (ntm_ty (EL s ntms)) = ntm_ty (EL t ntms) /\
     pl_interned dbs (3,ntm_db (EL s ntms),ntm_db (EL t ntms)) d md /\ LENGTH ntms + 1 < 2 EXP 60 /\
     (!m. m <= 6 ==> cw' m = cw m)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RComb s t)
                  (ctx,nms,tys,APPEND ntms [(2,s,t,pl_fun_cod tys (ntm_ty (EL s ntms)),d)],APPEND dbs md,ths,
                   nmap,ymap,drops,pol) /\
         pl_inv (cw',(ctx,nms,tys,APPEND ntms [(2,s,t,pl_fun_cod tys (ntm_ty (EL s ntms)),d)],APPEND dbs md,ths,
                      nmap,ymap,drops,pol),stk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_TABS_OK) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_NAMES_INJ) THEN
  PL_ROWS_TAC THEN
  SUBGOAL_THEN `s < LENGTH (ntms:(num#num#num#num#num)list) /\ t < LENGTH ntms` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[holr_live]; ALL_TAC] THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `s:num`] PL_TM_ROW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ts:holterm` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `t:num`] PL_TM_ROW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `tt:holterm` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
                `ntm_ty (EL s (ntms:(num#num#num#num#num)list))`; `htypeof ts`] PL_FUN_DEC3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `A:holtype` (X_CHOOSE_THEN `B:holtype` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `ntm_db (EL s (ntms:(num#num#num#num#num)list)) < LENGTH (dbs:(num#num#num)list) /\
                ntm_db (EL t ntms) < LENGTH dbs` STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `A:holtype = htypeof tt` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FDTY_FUN THEN
    MAP_EVERY EXISTS_TAC [`nms:string list`; `tys:(num#num#num)list`; `ntm_ty (EL t (ntms:(num#num#num#num#num)list))`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  PL_DB_STEP_TAC `tys:(num#num#num)list` `dbs:(num#num#num)list`
    `(3,ntm_db (EL s (ntms:(num#num#num#num#num)list)),ntm_db (EL t (ntms:(num#num#num#num#num)list)))`
    `d:num` `md:(num#num#num)list`
    (PL_DBOK_TAC `hdbComb (hdb ts) (hdb tt)` FDDB_COMB
       [`ntm_db (EL s (ntms:(num#num#num#num#num)list))`; `ntm_db (EL t (ntms:(num#num#num#num#num)list))`]) THEN
  SUBGOAL_THEN `fddb nms tys (APPEND dbs md) d (hdbComb (hdb ts) (hdb tt))` ASSUME_TAC THENL
   [PL_DBDEC_TAC FDDB_COMB [`ntm_db (EL s (ntms:(num#num#num#num#num)list))`;
                            `ntm_db (EL t (ntms:(num#num#num#num#num)list))`]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_const_app "pl_tabs_ok" (concl th) &&
                           can (find_term ((=) `md:(num#num#num)list`)) (concl th)
                        then STRIP_ASSUME_TAC(REWRITE_RULE[pl_tabs_ok] th) else failwith "") THEN
  SUBGOAL_THEN `nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RComb s t)
                  (ctx,nms,tys,APPEND ntms [(2,s,t,pl_fun_cod tys (ntm_ty (EL s ntms)),d)],APPEND dbs md,ths,
                   nmap,ymap,drops,pol)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                  `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                  `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `s:num`; `t:num`;
                  `ts:holterm`; `tt:holterm`; `B:holtype`; `[]:(num#num#num)list`; `md:(num#num#num)list`;
                  `pl_fun_cod tys (ntm_ty (EL s (ntms:(num#num#num#num#num)list)))`; `d:num`] NAT_STEP_COMB) THEN
    REWRITE_TAC[APPEND_NIL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND; NAT_TYS_OK_NIL] THEN
    MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                  `[]:(num#num#num)list`; `md:(num#num#num)list`] NAT_KEYS_NEW_ROWS) THEN
    ASM_REWRITE_TAC[APPEND_NIL] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `kk:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
                `cw':num->num`; `RComb s t`; `ctx:hupdate list`; `[]:string list`; `[]:(num#num#num)list`;
                `[(2,s:num,t:num,pl_fun_cod tys (ntm_ty (EL s (ntms:(num#num#num#num#num)list))),d:num)]`;
                `md:(num#num#num)list`; `[]:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`] PL_INV_GROW) THEN
  REWRITE_TAC[APPEND_NIL; LENGTH; ADD_CLAUSES; CONJUNCT1 LT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN PL_INV_FACTS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
  ASM_REWRITE_TAC[ONE] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The guards, and the plan's theorem.                                       *)
(* ------------------------------------------------------------------------- *)

let PL_COMB_GUARDS = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk s t.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> ((nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RComb s t) /\
           ?ts tt B. fdtm nms tys ntms s ts /\ fdtm nms tys ntms t tt /\ htypeof ts = HFun (htypeof tt) B) <=>
          holr_live 2 s (LENGTH ntms) drops /\ holr_live 2 t (LENGTH ntms) drops /\
          pl_fun_ok tys (ntm_ty (EL s ntms)) /\ pl_fun_dom tys (ntm_ty (EL s ntms)) = ntm_ty (EL t ntms))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND] THEN
  ASM_CASES_TAC `holr_live 2 s (LENGTH (ntms:(num#num#num#num#num)list)) drops` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `holr_live 2 t (LENGTH (ntms:(num#num#num#num#num)list)) drops` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s < LENGTH (ntms:(num#num#num#num#num)list) /\ t < LENGTH ntms` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[holr_live]; ALL_TAC] THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `s:num`] PL_TM_ROW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ps:holterm` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `t:num`] PL_TM_ROW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `pt:holterm` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_CANON) THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `ts:holterm` (X_CHOOSE_THEN `tt:holterm` (X_CHOOSE_THEN `B:holtype` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `ts:holterm = ps /\ tt:holterm = pt` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[FDTM_FUN]; ALL_TAC] THEN
    MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                  `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                  `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
                  `ntm_ty (EL s (ntms:(num#num#num#num#num)list))`; `htypeof pt`; `B:holtype`] PL_FUN_DEC2) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    STRIP_TAC THEN
    MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                  `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                  `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
                  `ntm_ty (EL s (ntms:(num#num#num#num#num)list))`; `htypeof ps`] PL_FUN_DEC3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `A:holtype` (X_CHOOSE_THEN `B:holtype` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ps:holterm`; `pt:holterm`; `B:holtype`] THEN ASM_REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC FDTY_FUN THEN
    MAP_EVERY EXISTS_TAC [`nms:string list`; `tys:(num#num#num)list`; `ntm_ty (EL t (ntms:(num#num#num#num#num)list))`] THEN
    ASM_MESON_TAC[]]);;

let pl_comb_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp s t k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = s /\ cw 9 = t /\
     tab_run hol_tables inp pl_plan_comb 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
             (k,i,(cw',ns',stk'))
     ==> (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RComb s t) ns' /\
                    pl_inv (cw',ns',stk')) /\
         (k = 0 <=> ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RComb s t) /\
                      ?ts tt B. fdtm nms tys ntms s ts /\ fdtm nms tys ntms t tt /\
                                htypeof ts = HFun (htypeof tt) B))`;;

(* PL_COMB: the plan's FIRED run is COMB's nat_step and keeps pl_inv; it is *)
(* REFUSED exactly when an operand is not live or the types do not fit.     *)
let PL_COMB = prove(pl_comb_goal,
  TAB_START_TAC pl_plan_comb THEN
  PL_INV_ASM(fun th -> REWRITE_TAC[MATCH_MP PL_COMB_GUARDS th]) THEN
  REWRITE_TAC[holr_live; pl_fun_ok; pl_fun_dom; ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
  TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[pl_fun_ok; pl_fun_dom; pl_fun_cod; holr_live] PL_COMB_FIRED) THEN
  PL_WITNESS_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN PL_SET_LOW_TAC);;

(* ------------------------------------------------------------------------- *)
(* Through the driver: the bridge of a step, row_word on a keyed table too. *)
(* ------------------------------------------------------------------------- *)

let TAB_HOL_BRIDGE2 st =
  let ws = map (fun t -> dest_small_numeral(rand t)) (dest_list st) in
  if el 0 ws = 4 && (el 1 ws = 0 || el 1 ws = 6) then
    INST [mk_small_numeral (el 1 ws), `j:num`]
      (SPEC_ALL (ISPECL [`hol_trow`; `hol_tn`; `hol_twd`; `hol_tdrop`; `hol_tapp`; `hol_tput`; `hol_layout`] TAB_IMPL_ROWW_KEY))
  else TAB_HOL_BRIDGE st;;

let TAB_HOL_IMPL_TAC2 : tactic = fun (asl,w) ->
  (REWRITE_TAC[hol_tables] THEN MATCH_MP_TAC (TAB_HOL_BRIDGE2 (rand w)) THEN
   ASM_REWRITE_TAC[HOL_LAYOUT_MEMS; HOL_LAYOUT_WF; HOL_TB_OK] THEN
   CONV_TAC TAB_REDUCE_CONV THEN REWRITE_TAC[HOL_TAPP_EXISTS]) (asl,w);;

let TAB_PLAN_IMPL_TAC2 plan_def =
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_progs_ok] THEN STRIP_TAC THEN
  X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!f. 10 <= f /\ f < 18 ==> val(EL f (st:int64 list)) < nctl` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_cw_range]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "MEM" (concl th))) THEN
  REWRITE_TAC[plan_def; MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `st:int64 list`
                          then SUBST_ALL_TAC th else failwith "") THEN
  TAB_HOL_IMPL_TAC2;;

let TAB_IMPL_COMB = prove(tab_plan_impl_goal `pl_plan_comb`, TAB_PLAN_IMPL_TAC2 pl_plan_comb);;
let TAB_SAFE_COMB = prove(tab_safe_goal `pl_plan_comb`, TAB_SAFE_PLAN_TAC pl_plan_comb);;
let PL_COMB_TAB = tab_drv_lift PL_COMB `pl_plan_comb` TAB_IMPL_COMB TAB_SAFE_COMB;;

(* Every theorem this file states, for the audits. *)
let tables_comb_theorems =
 ["PL_COMB_FIRED", PL_COMB_FIRED; "PL_COMB_GUARDS", PL_COMB_GUARDS; "PL_COMB", PL_COMB;
  "TAB_IMPL_COMB", TAB_IMPL_COMB; "TAB_SAFE_COMB", TAB_SAFE_COMB; "PL_COMB_TAB", PL_COMB_TAB];;
