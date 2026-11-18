(* ABS admission, input formation, and the semantics of final publication. *)
needs "native/hol/tables_abs_program.ml";;
needs "native/hol/tables_abs_commit.ml";;
needs "native/hol/bind_walk_table_invariant.ml";;
needs "native/hol/plans_every.ml";;

let pl_abs_prepare,pl_abs_suffix =
  let steps = dest_list(rhs(concl pl_plan_abs)) in
  let define_part name part = new_definition
    (mk_eq(mk_var(name,`:(int64 list)list`),mk_list(part,`:int64 list`))) in
  define_part "pl_abs_prepare" (List.filteri (fun i _ -> i < 8) steps),
  define_part "pl_abs_suffix" (List.filteri (fun i _ -> 9 <= i) steps);;

let ABS_PLAN_PARTS = prove
 (`pl_plan_abs = APPEND pl_abs_prepare (CONS (EL 8 pl_plan_abs) pl_abs_suffix)`,
  REWRITE_TAC[pl_plan_abs;pl_abs_prepare;pl_abs_suffix;APPEND] THEN CONV_TAC STEP_EL_CONV2);;

let ABS_WALK_OPCODE = prove
 (`val(EL 0 (EL 8 pl_plan_abs)) = 10`,
  REWRITE_TAC[ABS_PLAN_BINDING;MAP] THEN CONV_TAC STEP_EL_CONV2);;

let PL_ABS_PREPARE_RUN = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp v t k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     cw 8 = v /\ cw 9 = t /\
     tab_run hol_tables inp pl_abs_prepare 0
       (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) (k,i,(cw',ns',stk'))
     ==> (k = 0 \/ k = 1) /\ ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\ stk' = stk /\
         (k = 1 <=> holr_live 2 v (LENGTH ntms) drops /\
                    holr_live 2 t (LENGTH ntms) drops /\ FST(EL v ntms) = 0) /\
         (k = 1 ==> cw' 28 = FST(SND(EL v ntms)) /\ cw' 29 = ntm_ty(EL v ntms) /\
                    cw' 30 = ntm_ty(EL t ntms) /\ cw' 31 = ntm_db(EL t ntms)) /\
         (!j. j < 24 ==> cw' j = cw j)`,
  TAB_START_TAC pl_abs_prepare THEN REWRITE_TAC[holr_live;pl_f5] THEN ASM_REWRITE_TAC[] THEN
  TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_set] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let abs_plan_impl_goal plan =
  subst [plan,`P:(int64 list)list`]
    `!inp progs bw ctl nctl budget cfr.
       pl_progs_ok progs /\ pl_cw_range nctl P
       ==> !st. MEM st P ==>
         tab_impl (tab_rel hol_tables hol_layout inp bw ctl nctl cfr)
            hol_tables inp progs bw ctl budget cfr st`;;

let TAB_IMPL_ABS_PREPARE = prove
 (abs_plan_impl_goal `pl_abs_prepare`, TAB_PLAN_IMPL_TAC2 pl_abs_prepare);;
let TAB_SAFE_ABS_PREPARE = prove
 (tab_safe_goal `pl_abs_prepare`, TAB_SAFE_PLAN_TAC pl_abs_prepare);;

let TAB_IMPL_ABS_SUFFIX = prove
 (abs_plan_impl_goal `pl_abs_suffix`, TAB_PLAN_IMPL_TAC2 pl_abs_suffix);;

let BW_KEY_OK_HOL = prove
 (`!i row. bw_key_ok i row <=> db_key_ok i row`,
  REWRITE_TAC[FORALL_PAIR_THM;bw_key_ok;db_key_ok]);;

let PL_ABS_ROWS_VALID = prove
 (`!ctx nms tys dbs. pl_tabs_ok ctx nms tys dbs ==> bw_rows_valid nms tys dbs`,
  REWRITE_TAC[pl_tabs_ok;bw_rows_valid;BW_KEY_OK_HOL;nat_keys] THEN MESON_TAC[]);;

let FDTM_VAR_NAME = prove
 (`!nms tys ntms v x ty. fdtm nms tys ntms v (TmVar x ty)
      ==> let a = FST(SND(EL v ntms)) in a < LENGTH nms /\ EL a nms = x`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[fdtm_CASES] THEN
  REWRITE_TAC[holterm_DISTINCT;holterm_INJ;LET_DEF;LET_END_DEF] THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[FST;SND]);;

let PL_ABS_WALK_DATA = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk v t x ty tb.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     fdtm nms tys ntms v (TmVar x ty) /\ fdtm nms tys ntms t tb
     ==> bw_rows_valid nms tys dbs /\
         bw_ctx nms tys (FST(SND(EL v ntms))) (ntm_ty(EL v ntms)) ty /\
         EL (FST(SND(EL v ntms))) nms = x /\ fddb nms tys dbs (ntm_db(EL t ntms)) (hdb tb) /\
         fdty nms tys (ntm_ty(EL t ntms)) (htypeof tb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_NAMES_INJ) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_CANON) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_ABS_ROWS_VALID o MATCH_MP PL_TABS_OK) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_INV_NAT) THEN
  MAP_EVERY (fun operands ->
    MP_TAC(SPECL (pl_ns_vars @ operands) NAT_OK_TM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC)
    [[`v:num`;`TmVar x ty`];[`t:num`;`tb:holterm`]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htypeof]) THEN
  MP_TAC(SPECL [`nms:string list`;`tys:(num#num#num)list`;`ntms:(num#num#num#num#num)list`;
                `v:num`;`x:string`;`ty:holtype`] FDTM_VAR_NAME) THEN
  ASM_REWRITE_TAC[LET_DEF;LET_END_DEF] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[bw_ctx] THEN ASM_MESON_TAC[NAMES_INJ]);;

(* The two argument-list cells and the function type in the ABS suffix. *)
let PL_ABS_TYPE_CHAIN = prove
 (`!ctx nms tys dbs a b A B l1 l2 yf mt1 mt2 mt3.
     pl_tabs_ok ctx nms tys dbs /\ his_std_sig (hsigof ctx) /\
     1 < LENGTH nms /\ EL 1 nms = "fun" /\
     htype_ok (FST(hsigof ctx)) A /\ htype_ok (FST(hsigof ctx)) B /\
     fdty nms tys a A /\ fdty nms tys b B /\ fdtys nms tys 0 [] /\
     pl_interned tys (3,b,0) l1 mt1 /\
     pl_interned (APPEND tys mt1) (3,a,l1) l2 mt2 /\
     pl_interned (APPEND (APPEND tys mt1) mt2) (1,1,l2) yf mt3
     ==> let mt = APPEND mt1 (APPEND mt2 mt3) in
          pl_tabs_ok ctx nms (APPEND tys mt) dbs /\ nat_tys_ok ctx nms tys mt /\
          fdty nms (APPEND tys mt) yf (HFun A B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a < LENGTH (tys:(num#num#num)list) /\ b < LENGTH tys /\ 0 < LENGTH tys`
   STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FDTY_BOUND];ALL_TAC] THEN
  MP_TAC(SPEC `hsigof ctx` HTYPE_OK_STD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  PL_TY_STEP_TAC PL_TAB0 `(3,b:num,0)` `l1:num` `mt1:(num#num#num)list`
    (PL_CONS_OK_TAC `b:num` `0` `[B:holtype]`) THEN
  SUBGOAL_THEN `fdtys nms (APPEND tys mt1) l1 [B:holtype]` ASSUME_TAC THENL
   [PL_DEC_CONS_TAC `b:num` `0`;ALL_TAC] THEN
  PL_TY_STEP_TAC PL_TAB1 `(3,a:num,l1:num)` `l2:num` `mt2:(num#num#num)list`
    (PL_CONS_OK_TAC `a:num` `l1:num` `[A:holtype;B]`) THEN
  SUBGOAL_THEN `fdtys nms (APPEND (APPEND tys mt1) mt2) l2 [A:holtype;B]` ASSUME_TAC THENL
   [PL_DEC_CONS_TAC `a:num` `l1:num`;ALL_TAC] THEN
  PL_TY_STEP_TAC PL_TAB2 `(1,1,l2:num)` `yf:num` `mt3:(num#num#num)list`
    (PL_FUN_OK_TAC `l2:num` `[A:holtype;B]`) THEN
  REWRITE_TAC[LET_DEF;LET_END_DEF] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[APPEND_ASSOC] THEN FIRST_ASSUM ACCEPT_TAC;
    PL_TYS_OK_TAC;
    REWRITE_TAC[APPEND_ASSOC;HFun] THEN
    SUBGOAL_THEN `EL 1 nms = "fun"` (fun th -> REWRITE_TAC[GSYM th]) THENL
     [FIRST_ASSUM ACCEPT_TAC;PL_DEC_FUN_TAC `l2:num`]]);;

let PL_INTERNED_CANON = prove
 (`!rows key pay md.
     (!i. i < LENGTH rows ==> FST(EL i rows) < 8) /\ FST key < 8 /\
     pl_interned rows key pay md
     ==> !i. i < LENGTH(APPEND rows md) ==> FST(EL i (APPEND rows md)) < 8`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_interned] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[APPEND_NIL] THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[LENGTH_APPEND;LENGTH;EL_APPEND] THEN DISCH_TAC THEN
  ASM_CASES_TAC `i < LENGTH(rows:(num#num#num)list)` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `i - LENGTH(rows:(num#num#num)list) = 0` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[EL;HD]]);;

let ABS_SUFFIX_TAGS_TAC (asl,w) =
  let asms = map snd asl in
  let successor th =
    let tm = concl th in
    if not(is_const_app "pl_interned" tm) then failwith "not an intern";
    let rule = SPECL (snd(strip_comb tm)) PL_INTERNED_CANON in
    if exists (fun known -> aconv (concl known) (rand(concl rule))) asms
    then failwith "known tags";
    rule in
  match mapfilter successor asms with
  | [] -> ALL_TAC (asl,w)
  | rule::_ ->
    (SUBGOAL_THEN (rand(concl rule)) ASSUME_TAC THENL
      [MATCH_MP_TAC rule THEN ASM_SIMP_TAC[FST] THEN CONV_TAC NUM_REDUCE_CONV;ALL_TAC]) (asl,w);;

let rec ABS_SUFFIX_RUN_TAC g =
  let w = snd g in
  if is_imp w && is_const_app "tab_run" (lhand w) &&
     not (is_const(el 2 (snd(strip_comb(lhand w))))) then
    (TAB_STEP_TAC THEN ABS_SUFFIX_TAGS_TAC THEN ABS_SUFFIX_RUN_TAC) g
  else TAB_RUN_TAC g;;

let PL_ABS_SUFFIX_DATA = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp v t a b d D j0 i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     cw 8 = v /\ cw 9 = t /\ cw 29 = a /\ cw 30 = b /\ cw 32 = d /\
     tab_run hol_tables inp pl_abs_suffix j0
       (cw,(ctx,nms,tys,ntms,D,ths,nmap,ymap,drops,pol),stk) (1,i,(cw',ns',stk'))
     ==> ?l1 l2 yf mt1 mt2 mt3.
         pl_interned tys (3,b,0) l1 mt1 /\
         pl_interned (APPEND tys mt1) (3,a,l1) l2 mt2 /\
         pl_interned (APPEND (APPEND tys mt1) mt2) (1,1,l2) yf mt3 /\
         LENGTH ntms + 1 < 2 EXP 60 /\ stk' = stk /\
         ns' = (ctx,nms,APPEND (APPEND (APPEND tys mt1) mt2) mt3,
                APPEND ntms [(3,v,t,yf,d)],D,ths,nmap,ymap,drops,pol) /\
         (!j. j < 24 ==> cw' j = cw j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(W(fun (_,w) -> if is_imp w && not(is_const_app "tab_run" (lhand w)) then DISCH_TAC else NO_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_K) THEN PL_ROWS_TAC THEN
  REWRITE_TAC[pl_abs_suffix] THEN ABS_SUFFIX_RUN_TAC THEN
  REWRITE_TAC[ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
  TRY(UNDISCH_TAC `1 = 2` THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `1` && is_var(rhs(concl th)))) THEN ASM_MESON_TAC[] THEN NO_TAC) THEN
  PL_WITNESS_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  PL_SET_LOW_TAC);;

let TAB_SAFE_ABS_SUFFIX = prove
 (`!inp cw (s:nstate) stk. (!j. j <= 6 ==> cw j = j) ==>
     tab_safe hol_tables inp pl_abs_suffix (cw,s,stk)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TAB_SAFE_CONST THEN
  ASM_REWRITE_TAC[hol_tables;FST;SND] THEN
  REWRITE_TAC[pl_abs_suffix;MEM] THEN GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN CONV_TAC TAB_REDUCE_CONV);;

let PL_ABS_SUFFIX_GROWS = prove
 (`!inp cw ctx nms tys ntms D ths nmap ymap drops pol stk j0 k i cw' ns' stk'.
     (!j. j <= 6 ==> cw j = j) /\
     (!i. i < LENGTH tys ==> FST(EL i tys) < 8) /\
     tab_run hol_tables inp pl_abs_suffix j0
       (cw,(ctx,nms,tys,ntms,D,ths,nmap,ymap,drops,pol),stk) (k,i,(cw',ns',stk'))
     ==> ~(k = 0) /\ stk' = stk /\
         pl_grows (ctx,nms,tys,ntms,D,ths,nmap,ymap,drops,pol) ns' /\
         (!j. j < 24 ==> cw' j = cw j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `cw 0 = 0 /\ cw 1 = 1 /\ cw 2 = 2 /\ cw 3 = 3 /\ cw 4 = 4 /\ cw 5 = 5 /\ cw 6 = 6`
     STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[ARITH];ALL_TAC] THEN
  REWRITE_TAC[pl_abs_suffix] THEN ABS_SUFFIX_RUN_TAC THEN
  REWRITE_TAC[pl_grows;PL_APPEND_SELF;GSYM APPEND_ASSOC;ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY PL_SET_LOW_TAC THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN W(fun (_,w) ->
    let _,eq = dest_exists w in EXISTS_TAC(rand(lhs eq)) THEN REFL_TAC));;

let ABS_PLAN_CONTROL_SIZE = prove
 (`!nctl. pl_cw_range nctl pl_plan_abs ==> 39 < nctl`,
  GEN_TAC THEN REWRITE_TAC[pl_cw_range] THEN
  DISCH_THEN(MP_TAC o SPECL [`EL 15 pl_plan_abs:int64 list`;`17`]) THEN
  SIMP_TAC[MEM_EL;ABS_PLAN_LENGTH;ARITH] THEN
  REWRITE_TAC[ABS_PLAN_COMMIT_LAST;MAP] THEN CONV_TAC STEP_EL_CONV2);;

let ABS_PREPARE_LENGTH = prove
 (`LENGTH pl_abs_prepare = 8`,
  REWRITE_TAC[pl_abs_prepare;LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let ABS_PARTS_CONTROL_RANGE = prove
 (`!nctl. pl_cw_range nctl pl_plan_abs
    ==> pl_cw_range nctl pl_abs_prepare /\ pl_cw_range nctl pl_abs_suffix`,
  GEN_TAC THEN REWRITE_TAC[pl_cw_range] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ABS_PLAN_PARTS] THEN
  REWRITE_TAC[MEM_APPEND;MEM] THEN MESON_TAC[]);;

let PL_FIBRE_TYPE_OK = prove
 (`!ctx nms tys i ty.
    fibre_ty_ok ctx nms tys i /\ fdty nms tys i ty ==> htype_ok (FST(hsigof ctx)) ty`,
  REWRITE_TAC[fibre_ty_ok] THEN MESON_TAC[FDTY_FUN;FDTY_NOT_BOTH]);;

let PL_TABS_TYPE_OK = prove
 (`!ctx nms tys D i ty.
    pl_tabs_ok ctx nms tys D /\ fdty nms tys i ty ==> htype_ok (FST(hsigof ctx)) ty`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_tabs_ok] THEN STRIP_TAC THEN
  MATCH_MP_TAC PL_FIBRE_TYPE_OK THEN MAP_EVERY EXISTS_TAC
    [`nms:string list`;`tys:(num#num#num)list`;`i:num`] THEN
  ASM_MESON_TAC[FDTY_BOUND]);;

let PL_ABS_SUFFIX_FIRED = prove
 (`!inp cw ctx nms tys ntms dbs ths nmap ymap drops pol stk v t x ty body md d j0 i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     holr_live 2 v (LENGTH ntms) drops /\ holr_live 2 t (LENGTH ntms) drops /\
     fdtm nms tys ntms v (TmVar x ty) /\ fdtm nms tys ntms t body /\
     pl_tabs_ok ctx nms tys (APPEND dbs md) /\
     fddb nms tys (APPEND dbs md) d (hdbAbs ty (hbind (x,ty) 0 (hdb body))) /\
     cw 8 = v /\ cw 9 = t /\ cw 29 = ntm_ty(EL v ntms) /\ cw 30 = ntm_ty(EL t ntms) /\ cw 32 = d /\
     tab_run hol_tables inp pl_abs_suffix j0
         (cw,(ctx,nms,tys,ntms,APPEND dbs md,ths,nmap,ymap,drops,pol),stk) (1,i,(cw',ns',stk'))
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAbs v t) ns' /\
         pl_inv (cw',ns',stk') /\ (!j. j < 24 ==> cw' j = cw j) /\
         pl_grows (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) ns'`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL ([`cw:num->num`] @ pl_ns_vars @
    [`stk:num list`;`inp:num list`;`v:num`;`t:num`;`ntm_ty(EL v ntms)`;`ntm_ty(EL t ntms)`;
     `d:num`;`APPEND (dbs:(num#num#num)list) md`;`j0:num`;`i:num`;
     `cw':num->num`;`ns':nstate`;`stk':num list`]) PL_ABS_SUFFIX_DATA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL ([`cw:num->num`] @ pl_ns_vars @
    [`stk:num list`;`v:num`;`t:num`;`x:string`;`ty:holtype`;`body:holterm`]) PL_ABS_WALK_DATA) THEN
  ASM_REWRITE_TAC[bw_ctx] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  PL_INV_ASM(fun inv -> MAP_EVERY (STRIP_ASSUME_TAC o C MATCH_MP inv)
    [PL_STD_SIG;PL_BOOT_LISTS]) THEN
  PL_INV_FACTS_TAC THEN
  SUBGOAL_THEN `1 < LENGTH(nms:string list)` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  MP_TAC(SPECL [`ctx:hupdate list`;`nms:string list`;`tys:(num#num#num)list`;
    `APPEND (dbs:(num#num#num)list) md`;`ntm_ty(EL v ntms)`;`ntm_ty(EL t ntms)`;
    `ty:holtype`;`htypeof body`;`l1:num`;`l2:num`;`yf:num`;
    `mt1:(num#num#num)list`;`mt2:(num#num#num)list`;`mt3:(num#num#num)list`] PL_ABS_TYPE_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC PL_TABS_TYPE_OK THEN MAP_EVERY EXISTS_TAC
        [`nms:string list`;`tys:(num#num#num)list`;`APPEND (dbs:(num#num#num)list) md`;
         `ntm_ty(EL v ntms)`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PL_TABS_TYPE_OK THEN MAP_EVERY EXISTS_TAC
        [`nms:string list`;`tys:(num#num#num)list`;`APPEND (dbs:(num#num#num)list) md`;
         `ntm_ty(EL t ntms)`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[LET_DEF;LET_END_DEF] THEN STRIP_TAC THEN
  MP_TAC(SPECL ([`cw:num->num`] @ pl_ns_vars @
    [`stk:num list`;`v:num`;`t:num`;`x:string`;`ty:holtype`;`body:holterm`;
     `APPEND (mt1:(num#num#num)list) (APPEND mt2 mt3)`;`md:(num#num#num)list`;
     `yf:num`;`d:num`;`cw':num->num`]) PL_ABS_COMMIT) THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC(CONJUNCT1(SPEC_ALL PL_FDDB_TYS_APPEND)) THEN ASM_REWRITE_TAC[];
                    ASM_SIMP_TAC[ARITH_RULE `j <= 6 ==> j < 24`]];
    STRIP_TAC THEN ASM_REWRITE_TAC[pl_grows;PL_APPEND_SELF;GSYM APPEND_ASSOC] THEN
    REPEAT CONJ_TAC THEN W(fun (_,w) -> let _,eq = dest_exists w in EXISTS_TAC(rand(lhs eq)) THEN REFL_TAC)]);;

let tables_abs_semantics_theorems =
 ["ABS_PLAN_PARTS",ABS_PLAN_PARTS;
  "ABS_WALK_OPCODE",ABS_WALK_OPCODE;
  "PL_ABS_PREPARE_RUN",PL_ABS_PREPARE_RUN;
  "TAB_IMPL_ABS_PREPARE",TAB_IMPL_ABS_PREPARE;
  "TAB_SAFE_ABS_PREPARE",TAB_SAFE_ABS_PREPARE;
  "TAB_IMPL_ABS_SUFFIX",TAB_IMPL_ABS_SUFFIX;
  "BW_KEY_OK_HOL",BW_KEY_OK_HOL;
  "PL_ABS_ROWS_VALID",PL_ABS_ROWS_VALID;
  "FDTM_VAR_NAME",FDTM_VAR_NAME;
  "PL_ABS_WALK_DATA",PL_ABS_WALK_DATA;
  "PL_ABS_TYPE_CHAIN",PL_ABS_TYPE_CHAIN;
  "PL_INTERNED_CANON",PL_INTERNED_CANON;
  "PL_ABS_SUFFIX_DATA",PL_ABS_SUFFIX_DATA;
  "TAB_SAFE_ABS_SUFFIX",TAB_SAFE_ABS_SUFFIX;
  "PL_ABS_SUFFIX_GROWS",PL_ABS_SUFFIX_GROWS;
  "ABS_PLAN_CONTROL_SIZE",ABS_PLAN_CONTROL_SIZE;
  "ABS_PREPARE_LENGTH",ABS_PREPARE_LENGTH;
  "ABS_PARTS_CONTROL_RANGE",ABS_PARTS_CONTROL_RANGE;
  "PL_FIBRE_TYPE_OK",PL_FIBRE_TYPE_OK;
  "PL_TABS_TYPE_OK",PL_TABS_TYPE_OK;
  "PL_ABS_SUFFIX_FIRED",PL_ABS_SUFFIX_FIRED];;
