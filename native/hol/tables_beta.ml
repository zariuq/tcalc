(* ========================================================================= *)
(* BETA t: the plan (PLANS.txt, section 6: live t; t a combination [R]; its *)
(* operator s an abstraction [R]; the argument's image the bound variable's *)
(* [R]; EQBUILD(t's type row, t's image, the body's image) -> k; append the *)
(* theorem row (K0,k)), its analysis on the record plans' machine          *)
(* (PL_BETA: FIRED = BETA's nat_step + pl_inv; REFUSED exactly when t is not *)
(* live or not a redex (\x. tb) x), and over the general layer and through *)
(* the driver over HOL's full layout (PL_BETA_TABRUN, PL_BETA_TAB).         *)
(* A term row's decoding is read through the row's tag: a combination row   *)
(* decodes to a combination of its fields' terms (FDTM_COMB_ROW), and only  *)
(* a combination row decodes to a combination (FDTM_COMB_TAG); the same for *)
(* abstractions. The redex's argument is the bound variable exactly when    *)
(* their images agree (canonical images; HDB_VAR_INV).                      *)
(*                                                                           *)
(* Loaded after tables_comb.ml.                                              *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Term rows: fields, decodings through the tag.                             *)
(* ------------------------------------------------------------------------- *)

let PL_TM_FIELDS = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> !t. t < LENGTH ntms /\ (FST(EL t ntms) = 2 \/ FST(EL t ntms) = 3)
             ==> FST(SND(EL t ntms)) < LENGTH ntms /\ FST(SND(SND(EL t ntms))) < LENGTH ntms`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `i:num`] PL_TM_ROW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `p:holterm` (MP_TAC o CONJUNCT1)) THEN
  ONCE_REWRITE_TAC[fdtm_CASES] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `EL i (ntms:(num#num#num#num#num)list)`
                          then SUBST_ALL_TAC th else failwith "") THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND; ARITH_EQ]) THEN REWRITE_TAC[FST; SND] THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  ASM_MESON_TAC[FDTM_BOUND]);;

let HDB_VAR_INV = prove
 (`!t x ty. hdb t = hdbVar x ty <=> t = TmVar x ty`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `t:holterm` (cases "holterm")) THEN
  REWRITE_TAC[hdb; hdbterm_DISTINCT; hdbterm_INJ; holterm_DISTINCT; holterm_INJ]);;

(* A combination row decodes to a combination of its fields' terms; an      *)
(* abstraction row to an abstraction.                                        *)
let FDTM_ROW_INV_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o ONCE_REWRITE_RULE[fdtm_CASES]) ASSUME_TAC) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_const_app "EL" (lhs(concl th))
                          then SUBST_ALL_TAC th else failwith "") THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND; ARITH_EQ]) THEN ASM_REWRITE_TAC[FST; SND] THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_MESON_TAC[];;
let FDTM_COMB_ROW = prove
 (`!nms tys ntms i p. fdtm nms tys ntms i p /\ FST(EL i ntms) = 2
     ==> ?s u. p = TmComb s u /\ fdtm nms tys ntms (FST(SND(EL i ntms))) s /\
               fdtm nms tys ntms (FST(SND(SND(EL i ntms)))) u`,
  FDTM_ROW_INV_TAC);;
let FDTM_ABS_ROW = prove
 (`!nms tys ntms i p. fdtm nms tys ntms i p /\ FST(EL i ntms) = 3
     ==> ?v b. p = TmAbs v b /\ fdtm nms tys ntms (FST(SND(EL i ntms))) v /\
               fdtm nms tys ntms (FST(SND(SND(EL i ntms)))) b`,
  FDTM_ROW_INV_TAC);;

let PL_BETA_DEC = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ t < LENGTH ntms /\
     FST(EL t ntms) = 2 /\ FST(EL (FST(SND(EL t ntms))) ntms) = 3 /\
     ntm_db (EL (FST(SND(EL (FST(SND(EL t ntms))) ntms))) ntms) = ntm_db (EL (FST(SND(SND(EL t ntms)))) ntms)
     ==> ?x ty tb. fdtm nms tys ntms t (TmComb (TmAbs (TmVar x ty) tb) (TmVar x ty)) /\
                   fdtm nms tys ntms (FST(SND(SND(EL (FST(SND(EL t ntms))) ntms)))) tb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_INV_NAT) THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `t:num`] PL_TM_ROW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `p:holterm` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `t:num`; `p:holterm`]
               FDTM_COMB_ROW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:holterm` (X_CHOOSE_THEN `U:holterm` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`;
                `FST(SND(EL t (ntms:(num#num#num#num#num)list)))`; `S:holterm`] FDTM_ABS_ROW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `V:holterm` (X_CHOOSE_THEN `B:holterm` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `hterm_ok (hsigof ctx) S` MP_TAC THENL
   [ASM_MESON_TAC[NAT_OK_TM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[hterm_ok] THEN DISCH_THEN(X_CHOOSE_THEN `x:string` (X_CHOOSE_THEN `ty:holtype` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `U = TmVar x ty` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM HDB_VAR_INV] THEN
    SUBGOAL_THEN `fddb nms tys dbs (ntm_db (EL (FST(SND(SND(EL t ntms)))) (ntms:(num#num#num#num#num)list))) (hdb U) /\
                  fddb nms tys dbs (ntm_db (EL (FST(SND(EL (FST(SND(EL t ntms))) ntms))) ntms)) (hdb V)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[NAT_OK_TM]; ALL_TAC] THEN
    SUBGOAL_THEN `hdb U = hdb V` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[FDDB_FUNCTIONAL]; ASM_REWRITE_TAC[hdb]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`x:string`; `ty:holtype`; `B:holterm`] THEN
  ASM_MESON_TAC[]);;

let FDTM_TAG_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[fdtm_CASES]) THEN
  REWRITE_TAC[holterm_DISTINCT; holterm_INJ] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FST; SND] THEN ASM_MESON_TAC[];;
let FDTM_COMB_TAG = prove
 (`!nms tys ntms i s u. fdtm nms tys ntms i (TmComb s u)
     ==> FST(EL i ntms) = 2 /\ fdtm nms tys ntms (FST(SND(EL i ntms))) s /\
         fdtm nms tys ntms (FST(SND(SND(EL i ntms)))) u`,
  FDTM_TAG_TAC);;
let FDTM_ABS_TAG = prove
 (`!nms tys ntms i v b. fdtm nms tys ntms i (TmAbs v b)
     ==> FST(EL i ntms) = 3 /\ fdtm nms tys ntms (FST(SND(EL i ntms))) v /\
         fdtm nms tys ntms (FST(SND(SND(EL i ntms)))) b`,
  FDTM_TAG_TAC);;

let PL_BETA_GUARDS = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> ((nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RBeta t) /\
           ?x ty tb. fdtm nms tys ntms t (TmComb (TmAbs (TmVar x ty) tb) (TmVar x ty))) <=>
          holr_live 2 t (LENGTH ntms) drops /\ FST(EL t ntms) = 2 /\ FST(EL (FST(SND(EL t ntms))) ntms) = 3 /\
          ntm_db (EL (FST(SND(EL (FST(SND(EL t ntms))) ntms))) ntms) = ntm_db (EL (FST(SND(SND(EL t ntms)))) ntms))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND] THEN
  ASM_CASES_TAC `holr_live 2 t (LENGTH (ntms:(num#num#num#num#num)list)) drops` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `t < LENGTH (ntms:(num#num#num#num#num)list)` ASSUME_TAC THENL [ASM_MESON_TAC[holr_live]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_INV_NAT) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_CANON) THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:string` (X_CHOOSE_THEN `ty:holtype` (X_CHOOSE_THEN `tb:holterm` ASSUME_TAC))) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FDTM_COMB_TAG) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FDTM_ABS_TAG o
                check (fun th -> can (find_term ((=) `TmAbs (TmVar x ty) tb`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      (let _,b = strip_forall(concl th) in is_imp b && is_const_app "fddb" (lhand(lhand b))))) THEN
    EXISTS_TAC `hdb (TmVar x ty)` THEN ASM_MESON_TAC[NAT_OK_TM];
    STRIP_TAC THEN
    MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                  `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                  `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `t:num`]
                 PL_BETA_DEC) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The plan; the run starts with the term rows' field bounds.                *)
(* ------------------------------------------------------------------------- *)

pl_begin();;
let _ = let _ = pl_live_tm pl_OP0 in
        let tg = pl_f_tm pl_OP0 0 in let _ = pl_eqw_c tg 2 in
        let s = pl_f_tm pl_OP0 1 in let u = pl_f_tm pl_OP0 2 in
        let tg2 = pl_f_tm s 0 in let _ = pl_eqw_c tg2 3 in
        let v = pl_f_tm s 1 in let b = pl_f_tm s 2 in
        let iv = pl_f_tm v 4 in let iu = pl_f_tm u 4 in let _ = pl_eqw_c iv iu in
        let y = pl_f_tm pl_OP0 3 in let it = pl_f_tm pl_OP0 4 in let ib = pl_f_tm b 4 in
        let k = pl_eqbuild y it ib in pl_append_c 0 k;;
let pl_plan_beta = new_definition(mk_eq(`pl_plan_beta:(int64 list)list`, pl_plan()));;

let PL_START_FIELDS_TAC plan =
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(W(fun (_,w) -> if is_imp w && not(is_const_app "pl_run" (lhand w)) then DISCH_TAC else NO_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_K) THEN PL_ROWS_TAC THEN
  PL_INV_ASM(fun inv -> ASSUME_TAC(MATCH_MP PL_TM_FIELDS inv)) THEN
  REWRITE_TAC[plan] THEN PL_RUN_TAC;;

(* ------------------------------------------------------------------------- *)
(* FIRED: the redex decoded, EQBUILD of t = tb, the theorem row.             *)
(* ------------------------------------------------------------------------- *)

let pl_beta_fired_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t l1 f1 l2 l3 e q x k
   mt1 mt2 mt3 mt4 mt5 md1 md2 md3 cw'.
   pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
   holr_live 2 t (LENGTH ntms) drops /\ FST(EL t ntms) = 2 /\ FST(EL (FST(SND(EL t ntms))) ntms) = 3 /\
   ntm_db (EL (FST(SND(EL (FST(SND(EL t ntms))) ntms))) ntms) = ntm_db (EL (FST(SND(SND(EL t ntms)))) ntms) /\
   pl_interned tys (3,ntm_ty (EL t ntms),3) l1 mt1 /\
   pl_interned (APPEND tys mt1) (1,1,l1) f1 mt2 /\
   pl_interned (APPEND (APPEND tys mt1) mt2) (3,f1,0) l2 mt3 /\
   pl_interned (APPEND (APPEND (APPEND tys mt1) mt2) mt3) (3,ntm_ty (EL t ntms),l2) l3 mt4 /\
   pl_interned (APPEND (APPEND (APPEND (APPEND tys mt1) mt2) mt3) mt4) (1,1,l3) e mt5 /\
   pl_interned dbs (2,2,e) q md1 /\
   pl_interned (APPEND dbs md1) (3,q,ntm_db (EL t ntms)) x md2 /\
   pl_interned (APPEND (APPEND dbs md1) md2)
               (3,x,ntm_db (EL (FST(SND(SND(EL (FST(SND(EL t ntms))) ntms)))) ntms)) k md3 /\
   LENGTH ths + 1 < 2 EXP 60 /\ (!n. n <= 6 ==> cw' n = cw n)
   ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RBeta t)
         (ctx,nms,APPEND (APPEND (APPEND (APPEND (APPEND tys mt1) mt2) mt3) mt4) mt5,ntms,
          APPEND (APPEND (APPEND dbs md1) md2) md3,APPEND ths [(0,k)],nmap,ymap,drops,pol) /\
       pl_inv (cw',(ctx,nms,APPEND (APPEND (APPEND (APPEND (APPEND tys mt1) mt2) mt3) mt4) mt5,ntms,
                    APPEND (APPEND (APPEND dbs md1) md2) md3,APPEND ths [(0,k)],nmap,ymap,drops,pol),stk)`;;

let NAT_STEP_BETA =
  find (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "RBeta")) (concl th))
       (CONJUNCTS nat_step_RULES);;

let PL_BETA_FIRED = prove(pl_beta_fired_goal,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t < LENGTH (ntms:(num#num#num#num#num)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[holr_live]; ALL_TAC] THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `t:num`]
               PL_BETA_DEC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xv:string` (X_CHOOSE_THEN `tyv:holtype` (X_CHOOSE_THEN `tb:holterm` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_INV_NAT) THEN
  SUBGOAL_THEN `fdty nms tys (ntm_ty (EL t (ntms:(num#num#num#num#num)list)))
                     (htypeof (TmComb (TmAbs (TmVar xv tyv) tb) (TmVar xv tyv))) /\
                fddb nms tys dbs (ntm_db (EL t ntms)) (hdb (TmComb (TmAbs (TmVar xv tyv) tb) (TmVar xv tyv))) /\
                fddb nms tys dbs (ntm_db (EL (FST(SND(SND(EL (FST(SND(EL t ntms))) ntms)))) ntms)) (hdb tb)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[NAT_OK_TM]; ALL_TAC] THEN
  ABBREV_TAC `tm = TmComb (TmAbs (TmVar xv tyv) tb) (TmVar xv tyv)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_STD_SIG) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_TABS_OK) THEN
  FIRST_ASSUM(fun th -> if is_const_app "pl_tabs_ok" (concl th)
                        then STRIP_ASSUME_TAC(REWRITE_RULE[pl_tabs_ok] th) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_BOOT_LISTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_BOOL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_NAMES_INJ) THEN
  PL_INV_FACTS_TAC THEN
  SUBGOAL_THEN `ntm_ty (EL t (ntms:(num#num#num#num#num)list)) < LENGTH (tys:(num#num#num)list) /\
                ntm_db (EL t ntms) < LENGTH (dbs:(num#num#num)list) /\
                ntm_db (EL (FST(SND(SND(EL (FST(SND(EL t ntms))) ntms)))) ntms) < LENGTH dbs`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1(SPEC_ALL FDTY_BOUND)) THEN EXISTS_TAC `htypeof tm` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(CONJUNCT1(SPEC_ALL FDDB_BOUND)) THEN EXISTS_TAC `hdb tm` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(CONJUNCT1(SPEC_ALL FDDB_BOUND)) THEN EXISTS_TAC `hdb tb` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `htype_ok (FST(hsigof ctx)) (htypeof tm)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[fibre_ty_ok] o
                C MP (ASSUME `ntm_ty (EL t (ntms:(num#num#num#num#num)list)) < LENGTH (tys:(num#num#num)list)`) o
                SPEC `ntm_ty (EL t (ntms:(num#num#num#num#num)list))` o
                check (fun th -> is_forall(concl th) && can (find_term ((=) `fibre_ty_ok`)) (concl th))) THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `ty:holtype = htypeof tm` (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC FDTY_FUN THEN MAP_EVERY EXISTS_TAC
       [`nms:string list`; `tys:(num#num#num)list`; `ntm_ty (EL t (ntms:(num#num#num#num#num)list))`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `ntm_ty (EL t (ntms:(num#num#num#num#num)list))`;
                    `htypeof tm`; `l:holtype list`] FDTY_NOT_BOTH) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `hsigof ctx` HTYPE_OK_STD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (PL_TY_STEP_TAC PL_TAB0 `(3,ntm_ty (EL t (ntms:(num#num#num#num#num)list)),3)` `l1:num` `mt1:(num#num#num)list`
    (PL_CONS_OK_TAC pl_y_t `3` `[htypeof tm; HBool]`)) THEN
  (SUBGOAL_THEN `fdtys nms (APPEND (tys:(num#num#num)list) mt1) l1 [htypeof tm; HBool]` ASSUME_TAC THENL
   [PL_DEC_CONS_TAC pl_y_t `3`; ALL_TAC]) THEN
  (PL_TY_STEP_TAC PL_TAB1 `(1,1,l1:num)` `f1:num` `mt2:(num#num#num)list` (PL_FUN_OK_TAC `l1:num` `[htypeof tm; HBool]`)) THEN
  (SUBGOAL_THEN `fdty nms (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) f1 (TyApp (EL 1 nms) [htypeof tm; HBool])`
    ASSUME_TAC THENL [PL_DEC_FUN_TAC `l1:num`; ALL_TAC]) THEN
  (PL_TY_STEP_TAC PL_TAB2 `(3,f1:num,0)` `l2:num` `mt3:(num#num#num)list`
    (PL_CONS_OK_TAC `f1:num` `0` `[TyApp (EL 1 nms) [htypeof tm; HBool]]`)) THEN
  (SUBGOAL_THEN `fdtys nms (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) l2
                      [TyApp (EL 1 nms) [htypeof tm; HBool]]` ASSUME_TAC THENL
   [PL_DEC_CONS_TAC `f1:num` `0`; ALL_TAC]) THEN
  (PL_TY_STEP_TAC PL_TAB3 `(3,ntm_ty (EL t (ntms:(num#num#num#num#num)list)),l2:num)` `l3:num` `mt4:(num#num#num)list`
    (PL_CONS_OK_TAC pl_y_t `l2:num` `[htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]]`)) THEN
  (SUBGOAL_THEN `fdtys nms (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) l3
                      [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]]` ASSUME_TAC THENL
   [PL_DEC_CONS_TAC pl_y_t `l2:num`; ALL_TAC]) THEN
  (PL_TY_STEP_TAC PL_TAB4 `(1,1,l3:num)` `e:num` `mt5:(num#num#num)list`
    (PL_FUN_OK_TAC `l3:num` `[htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]]`)) THEN
  (SUBGOAL_THEN `fdty nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5) e
                     (TyApp (EL 1 nms) [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]])` ASSUME_TAC THENL
   [PL_DEC_FUN_TAC `l3:num`; ALL_TAC]) THEN
  (PL_DB_STEP_TAC PL_TAB5 PL_DBT0 `(2,2,e:num)` `q:num` `md1:(num#num#num)list`
    (PL_DBOK_TAC `hdbConst (EL 2 nms) (TyApp (EL 1 nms) [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]])`
                 FDDB_CONST [`e:num`])) THEN
  (SUBGOAL_THEN `fddb nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5)
                     (APPEND (dbs:(num#num#num)list) md1) q
                     (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]]))`
    ASSUME_TAC THENL [PL_DBDEC_TAC FDDB_CONST [`e:num`]; ALL_TAC]) THEN
  (PL_DB_STEP_TAC PL_TAB5 PL_DBT1 `(3,q:num,ntm_db (EL t (ntms:(num#num#num#num#num)list)))` `x:num` `md2:(num#num#num)list`
    (PL_DBOK_TAC `hdbComb (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]])) (hdb tm)`
                 FDDB_COMB [`q:num`; pl_d_t])) THEN
  (SUBGOAL_THEN `fddb nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5)
                     (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) x
                     (hdbComb (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]])) (hdb tm))`
    ASSUME_TAC THENL [PL_DBDEC_TAC FDDB_COMB [`q:num`; pl_d_t]; ALL_TAC]) THEN
  (PL_DB_STEP_TAC PL_TAB5 PL_DBT2 `(3,x:num,ntm_db (EL (FST(SND(SND(EL (FST(SND(EL t ntms))) ntms)))) (ntms:(num#num#num#num#num)list)))` `k:num` `md3:(num#num#num)list`
    (PL_DBOK_TAC `hdbComb (hdbComb (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]])) (hdb tm)) (hdb tb)`
                 FDDB_COMB [`x:num`; `ntm_db (EL (FST(SND(SND(EL (FST(SND(EL t ntms))) ntms)))) (ntms:(num#num#num#num#num)list))`])) THEN
  (SUBGOAL_THEN `fddb nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5)
                     (APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3) k
                     (hdbComb (hdbComb (hdbConst (EL 2 nms) (TyApp (EL 1 nms) [htypeof tm; TyApp (EL 1 nms) [htypeof tm; HBool]])) (hdb tm)) (hdb tb))`
    ASSUME_TAC THENL [PL_DBDEC_TAC FDDB_COMB [`x:num`; `ntm_db (EL (FST(SND(SND(EL (FST(SND(EL t ntms))) ntms)))) (ntms:(num#num#num#num#num)list))`]; ALL_TAC]) THEN
  (SUBGOAL_THEN `fddb nms (APPEND (APPEND (APPEND (APPEND (APPEND (tys:(num#num#num)list) mt1) mt2) mt3) mt4) mt5)
                     (APPEND (APPEND (APPEND (dbs:(num#num#num)list) md1) md2) md3) k (hdb (tm =:= tb))`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "fddb" (concl th) &&
                    can (find_term ((=) `k:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[HDB_EQUATION; HFun];
    ALL_TAC]) THEN
  (FIRST_ASSUM(fun th -> if is_const_app "pl_tabs_ok" (concl th) &&
                           can (find_term ((=) `md3:(num#num#num)list`)) (concl th)
                        then STRIP_ASSUME_TAC(REWRITE_RULE[pl_tabs_ok] th) else failwith "")) THEN
  (SUBGOAL_THEN `nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RBeta t)
         (ctx,nms,APPEND (APPEND (APPEND (APPEND (APPEND tys mt1) mt2) mt3) mt4) mt5,ntms,
          APPEND (APPEND (APPEND dbs md1) md2) md3,APPEND ths [(0,k)],nmap,ymap,drops,pol)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                  `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                  `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `t:num`;
                  `xv:string`; `tyv:holtype`; `tb:holterm`;
                  `APPEND mt1 (APPEND mt2 (APPEND mt3 (APPEND mt4 mt5))):(num#num#num)list`;
                  `APPEND md1 (APPEND md2 md3):(num#num#num)list`; `0`; `k:num`] NAT_STEP_BETA) THEN
    REWRITE_TAC[APPEND_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND] THEN REPEAT CONJ_TAC THENL
     [PL_TYS_OK_TAC;
      MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                    `APPEND mt1 (APPEND mt2 (APPEND mt3 (APPEND mt4 mt5))):(num#num#num)list`;
                    `APPEND md1 (APPEND md2 md3):(num#num#num)list`] NAT_KEYS_NEW_ROWS) THEN
      REWRITE_TAC[APPEND_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM LENGTH_APPEND; GSYM APPEND_ASSOC] THEN REWRITE_TAC[APPEND_ASSOC] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      PL_EXT_TAC];
    ALL_TAC]) THEN
  (ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
                `cw':num->num`; `RBeta t`;
                `APPEND mt1 (APPEND mt2 (APPEND mt3 (APPEND mt4 mt5))):(num#num#num)list`;
                `APPEND md1 (APPEND md2 md3):(num#num#num)list`; `0`; `k:num`] PL_INV_THM_STEP) THEN
  REWRITE_TAC[APPEND_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM LENGTH_APPEND; GSYM APPEND_ASSOC] THEN REWRITE_TAC[APPEND_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `[]:num list` THEN REWRITE_TAC[pl_ids; PAIRWISE] THEN
  ASM_SIMP_TAC[EL_APPEND; LENGTH_APPEND; ARITH_RULE `1 <= l ==> 0 < l /\ 0 < l + m`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN ASM_ARITH_TAC));;

(* ------------------------------------------------------------------------- *)
(* The plan's theorem; over the general layer; through the driver.           *)
(* ------------------------------------------------------------------------- *)

let pl_beta_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = t /\
     pl_run pl_plan_beta 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) (k,i,(cw',ns',stk'))
     ==> (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RBeta t) ns' /\
                    pl_inv (cw',ns',stk')) /\
         (k = 0 <=> ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RBeta t) /\
                      ?x ty tb. fdtm nms tys ntms t (TmComb (TmAbs (TmVar x ty) tb) (TmVar x ty))))`;;
(* PL_BETA: the plan's FIRED run is BETA's nat_step and keeps pl_inv; it is *)
(* REFUSED exactly when t is not live or not a redex (\x. tb) x.           *)
let PL_BETA = prove(pl_beta_goal,
  PL_START_FIELDS_TAC pl_plan_beta THEN
  PL_INV_ASM(fun th -> REWRITE_TAC[MATCH_MP PL_BETA_GUARDS th]) THEN REWRITE_TAC[ARITH_EQ] THEN
  ASM_REWRITE_TAC[] THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN PL_FIRED_TAC PL_BETA_FIRED);;

let PL_BETA_TABRUN = tab_run_lift PL_BETA pl_plan_beta;;
let TAB_IMPL_BETA = prove(tab_plan_impl_goal `pl_plan_beta`, TAB_PLAN_IMPL_TAC2 pl_plan_beta);;
let TAB_SAFE_BETA = prove(tab_safe_goal `pl_plan_beta`, TAB_SAFE_PLAN_TAC pl_plan_beta);;
let PL_BETA_TAB = tab_drv_lift PL_BETA_TABRUN `pl_plan_beta` TAB_IMPL_BETA TAB_SAFE_BETA;;

(* Every theorem this file states, for the audits. *)
let tables_beta_theorems =
 ["PL_TM_FIELDS", PL_TM_FIELDS; "HDB_VAR_INV", HDB_VAR_INV; "FDTM_COMB_ROW", FDTM_COMB_ROW;
  "FDTM_ABS_ROW", FDTM_ABS_ROW; "PL_BETA_DEC", PL_BETA_DEC; "FDTM_COMB_TAG", FDTM_COMB_TAG;
  "FDTM_ABS_TAG", FDTM_ABS_TAG; "PL_BETA_GUARDS", PL_BETA_GUARDS; "PL_BETA_FIRED", PL_BETA_FIRED;
  "PL_BETA", PL_BETA; "PL_BETA_TABRUN", PL_BETA_TABRUN; "TAB_IMPL_BETA", TAB_IMPL_BETA;
  "TAB_SAFE_BETA", TAB_SAFE_BETA; "PL_BETA_TAB", PL_BETA_TAB];;
