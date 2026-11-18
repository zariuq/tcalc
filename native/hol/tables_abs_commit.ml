(* The abstraction constructor's final publication. *)
needs "native/hol/tables_abs_guards.ml";;

let NAT_STEP_ABS = el 6 (CONJUNCTS nat_step_RULES);;

let PL_ABS_COMMIT = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk v t x ty tb mt md yf d cw'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     holr_live 2 v (LENGTH ntms) drops /\ holr_live 2 t (LENGTH ntms) drops /\
     fdtm nms tys ntms v (TmVar x ty) /\ fdtm nms tys ntms t tb /\
     nat_tys_ok ctx nms tys mt /\
     pl_tabs_ok ctx nms (APPEND tys mt) (APPEND dbs md) /\
     fdty nms (APPEND tys mt) yf (HFun ty (htypeof tb)) /\
     fddb nms (APPEND tys mt) (APPEND dbs md) d (hdbAbs ty (hbind (x,ty) 0 (hdb tb))) /\
     LENGTH ntms + 1 < 2 EXP 60 /\ (!j. j <= 6 ==> cw' j = cw j)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAbs v t)
           (ctx,nms,APPEND tys mt,APPEND ntms [(3,v,t,yf,d)],APPEND dbs md,ths,nmap,ymap,drops,pol) /\
         pl_inv (cw',(ctx,nms,APPEND tys mt,APPEND ntms [(3,v,t,yf,d)],APPEND dbs md,ths,
                      nmap,ymap,drops,pol),stk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_NAMES_INJ) THEN
  SUBGOAL_THEN `nat_new_rows nms tys dbs mt md` ASSUME_TAC THENL
   [MATCH_MP_TAC NAT_KEYS_NEW_ROWS THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_tabs_ok] o
      check (fun th -> is_const_app "pl_tabs_ok" (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAbs v t)
      (ctx,nms,APPEND tys mt,APPEND ntms [(3,v,t,yf,d)],APPEND dbs md,ths,nmap,ymap,drops,pol)`
    ASSUME_TAC THENL
   [MP_TAC(SPECL (pl_ns_vars @ [`v:num`;`t:num`;`x:string`;`ty:holtype`;`tb:holterm`;
                  `mt:(num#num#num)list`;`md:(num#num#num)list`;`yf:num`;`d:num`]) NAT_STEP_ABS) THEN
    ASM_REWRITE_TAC[nat_ops_live;holr_operands;ALL;FST;SND];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL ([`cw:num->num`] @ pl_ns_vars @ [`stk:num list`;`cw':num->num`;`RAbs v t`;
                `ctx:hupdate list`;`[]:string list`;`mt:(num#num#num)list`;
                `[(3,v:num,t:num,yf:num,d:num)]`;`md:(num#num#num)list`;`[]:(num#num)list`;
                `nmap:num list`;`ymap:num list`;`drops:(num#num)list`;`pol:num`]) PL_INV_GROW) THEN
  REWRITE_TAC[APPEND_NIL;LENGTH;ADD_CLAUSES;CONJUNCT1 LT] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_tabs_ok] o
    check (fun th -> is_const_app "pl_tabs_ok" (concl th))) THEN
  PL_INV_FACTS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
  ASM_REWRITE_TAC[ONE] THEN ASM_ARITH_TAC);;

let tables_abs_commit_theorems = ["PL_ABS_COMMIT",PL_ABS_COMMIT];;
