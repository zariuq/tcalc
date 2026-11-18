needs "native/hol/tables_put_domain.ml";;

(* ========================================================================= *)
(* The plans of NAME, TYVAR and VAR over the interface (tab_run), and their *)
(* analysis over HOL's tables (hol_tables): from a state satisfying pl_inv  *)
(* with the record's operands in their control words, a FIRED run is the   *)
(* record's nat_step and keeps pl_inv, and the run is REFUSED exactly when  *)
(* the clause's guards fail (PL_TYVAR, PL_VAR, PL_NAME).                     *)
(*                                                                           *)
(* The plans (PLANS.txt, section 6):                                         *)
(*   NAME   fnv INP OP0 OP1 (v1 FNVB) -> h [R: outside the input];          *)
(*          intern_name OP0 OP1 (v1 h) -> i; append_row NMR (i)              *)
(*   TYVAR  live N OP0 [R: not a name id]; MAPGET N OP0 -> a;                *)
(*          ITY(0,a,K0) -> y; append_row YMR (y)                             *)
(*   VAR    live N OP0 [R]; live Y OP1 [R: not live]; MAPGET N OP0 -> a;     *)
(*          MAPGET Y OP1 -> ty; IDB(0,a,ty) -> d; append_row TMR (K0,a,ty,ty,d) *)
(* Names are never dropped: N ids are live exactly below the N count when  *)
(* no drop names space 0 (the drops HOLR makes are of spaces 1..3).         *)
(*                                                                           *)
(* The symbolic executor TAB_RUN_TAC runs tab_run hol_tables over a concrete *)
(* plan as PL_RUN_TAC runs pl_run: each leaf's meaning over HOL's tables,   *)
(* with an intern16 into the type or de Bruijn rows kept as one fact        *)
(* (pl_interned) when the rows' tags are canonical (TAB_INTERN_HOL_TY/DB).   *)
(*                                                                           *)
(* Loaded after tables_hol_laws.ml.                                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The plans.                                                                *)
(* ------------------------------------------------------------------------- *)

let pl_FNV = 22 and pl_INAME = 23;;
let pl_INP = [54] and pl_NAMES = [54; 44; 46; 48; 50]
and pl_NMAP = [30; 32] and pl_YMAP = [24; 26]                (* row_word, append_row: rows, count *)
and pl_NLIVE = [32; 34] and pl_YLIVE = [26; 28];;           (* live: count, marks *)
let pl_FNVB = 22;;

pl_begin();;
let _ = let h = pl_emit pl_FNV pl_INP pl_OP0 pl_OP1 [pl_FNVB] in
        let i = pl_emit pl_INAME pl_NAMES pl_OP0 pl_OP1 [h] in
        pl_emit pl_APPEND pl_NMAP i 0 [1];;
let pl_plan_name = new_definition(mk_eq(`pl_plan_name:(int64 list)list`, pl_plan()));;

pl_begin();;
let _ = let _ = pl_emit pl_LIVE pl_NLIVE pl_OP0 0 [] in
        let a = pl_emit pl_ROWW pl_NMAP pl_OP0 0 [1] in
        let y = pl_ity 0 a 0 in
        pl_emit pl_APPEND pl_YMAP y 0 [1];;
let pl_plan_tyvar = new_definition(mk_eq(`pl_plan_tyvar:(int64 list)list`, pl_plan()));;

pl_begin();;
let _ = let _ = pl_emit pl_LIVE pl_NLIVE pl_OP0 0 [] in
        let _ = pl_emit pl_LIVE pl_YLIVE pl_OP1 0 [] in
        let a = pl_emit pl_ROWW pl_NMAP pl_OP0 0 [1] in
        let ty = pl_emit pl_ROWW pl_YMAP pl_OP1 0 [1] in
        let d = pl_idb 0 a ty in
        pl_emit pl_APPEND pl_TM 0 a [5; ty; ty; d];;
let pl_plan_var = new_definition(mk_eq(`pl_plan_var:(int64 list)list`, pl_plan()));;

(* ------------------------------------------------------------------------- *)
(* intern16 into HOL's keyed tables, as pl_intern's one fact.               *)
(* ------------------------------------------------------------------------- *)

let TAB_INTERN_HOL_TAC =
  REWRITE_TAC[tab_intern; hol_trow; hol_twd; hol_tn; hol_tapp] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV LIST_OF_SEQ_CONV) THEN REWRITE_TAC[hol_tw; CONS_11; LENGTH] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  ASSUM_LIST(fun ths -> REWRITE_TAC(mapfilter (MATCH_MP PL_INTERN_WORDS) ths)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];;

let TAB_INTERN_HOL_TY = prove
 (`!tys. (!i. i < LENGTH tys ==> FST(EL i tys) < 8)
         ==> !ctx nms ntms dbs ths nmap ymap drops pol a0 a1 k pay s'.
               (tab_intern hol_trow hol_tn hol_tapp 0 4 (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
                           [a0; a1] k pay s' <=>
                ?tys'. pl_intern tys a0 a1 k pay tys' /\ s' = (ctx,nms,tys',ntms,dbs,ths,nmap,ymap,drops,pol))`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN TAB_INTERN_HOL_TAC);;

let TAB_INTERN_HOL_DB = prove
 (`!dbs. (!i. i < LENGTH dbs ==> FST(EL i dbs) < 8)
         ==> !ctx nms tys ntms ths nmap ymap drops pol a0 a1 k pay s'.
               (tab_intern hol_trow hol_tn hol_tapp 6 10 (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
                           [a0; a1] k pay s' <=>
                ?dbs'. pl_intern dbs a0 a1 k pay dbs' /\ s' = (ctx,nms,tys,ntms,dbs',ths,nmap,ymap,drops,pol))`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN TAB_INTERN_HOL_TAC);;

(* ------------------------------------------------------------------------- *)
(* The symbolic executor over HOL's tables.                                  *)
(* ------------------------------------------------------------------------- *)

let TAB_LEAF_TERM t = is_const_app "tab_leaf" t;;
let TAB_LEAF_CONV =
  REWRITE_CONV[tab_leaf; hol_tables; LET_DEF; LET_END_DEF; pl_set] THENC DEPTH_CONV BETA_CONV THENC
  DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV THENC REWRITE_CONV[];;
(* A control word known in the branch (cw 1 = 1, cw 8 = n). *)
let TAB_CW_EQ th =
  let c = concl th in
  is_eq c && is_comb(lhs c) && is_var(rator(lhs c)) && is_numeral(rand(lhs c));;
(* A leaf's fact: the known control words; interning into canonical keyed   *)
(* tables as one fact; the leaves' meanings over the interface; the tables' *)
(* slots decided and rows read as words; then the remaining meanings.       *)
let TAB_FACT_RULE asl th =
  let asms = map snd asl in
  let cws = filter TAB_CW_EQ asms in
  let canon = mapfilter (MATCH_MP TAB_INTERN_HOL_TY) asms @ mapfilter (MATCH_MP TAB_INTERN_HOL_DB) asms in
  CONV_RULE (REWRITE_CONV cws THENC REWRITE_CONV canon THENC
             REWRITE_CONV[tab_live; tab_append; tab_row; tab_fnv; tab_name; tab_intern; tab_putw; tab_polmax] THENC
             REWRITE_CONV[hol_trow; hol_twd; hol_tn; hol_tdrop] THENC NUM_REDUCE_CONV THENC
             REWRITE_CONV[TAB_ROWW_SEQ] THENC
             REWRITE_CONV[pl_pack; pl_unpack; pl_eqw; pl_roww; pl_intern; hol_tw; hol_tapp; hol_tput; hol_mspace;
                          LET_DEF; LET_END_DEF] THENC
             PL_NORM_CONV THENC DEPTH_CONV LIST_OF_SEQ_CONV THENC DEPTH_CONV BETA_CONV THENC
             REWRITE_CONV[LENGTH] THENC PL_NORM_CONV) th;;
let TAB_STEP_TAC =
  GEN_REWRITE_TAC LAND_CONV [CONJUNCT2 tab_run] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV(fun t -> if TAB_LEAF_TERM t then TAB_LEAF_CONV t else failwith "TAB_HEAD"))) THEN
  CONV_TAC(LAND_CONV PL_NORM_CONV) THEN
  REWRITE_TAC[FST; SND; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    W(fun (asl,_) ->
      let raw = TAB_FACT_RULE asl (CONJUNCT1 th) in
      PL_BOUNDS_TAC (concl raw) THEN
      W(fun (asl,_) ->
        let leaf = CONV_RULE (SIMP_CONV (!PL_SIMPS @ map snd asl) THENC PL_NORM_CONV THENC
                              REWRITE_CONV[PL_COND_DISJ]) raw in
        MP_TAC(CONJUNCT2 th) THEN PL_ASM_TCL leaf))) THEN
  PL_SUBST_ALL_TAC THEN REWRITE_TAC[ARITH_EQ] THEN PL_NEG_EQ_TAC;;
let rec TAB_RUN_TAC g =
  let w = snd g in
  if not (is_imp w) then ALL_TAC g else
  let a = lhand w in
  let hname = try fst(dest_const(fst(strip_comb a))) with Failure _ -> "" in
  if hname = "tab_run" then
    let sts = el 2 (snd(strip_comb a)) in
    if is_const sts && fst(dest_const sts) = "NIL" then (GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 tab_run] THEN PL_END_TAC) g
    else (TAB_STEP_TAC THEN TAB_RUN_TAC) g
  else if is_eq a then PL_END_TAC g
  else ALL_TAC g;;

(* ------------------------------------------------------------------------- *)
(* Facts of the invariant the plans read, and the start of every proof.     *)
(* ------------------------------------------------------------------------- *)

(* The N map points at names, the Y map at rows that decode to types. *)
let TAB_HOL_MAPS = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> (!n. n < LENGTH nmap ==> EL n nmap < LENGTH nms /\ EL n nmap < 2 EXP 60) /\
         (!y. y < LENGTH ymap ==> EL y ymap < LENGTH tys /\ EL y ymap < 2 EXP 60 /\
                                  ?ty. fdty nms tys (EL y ymap) ty)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[nat_rows_ok] o CONJUNCT1 o CONJUNCT2 o MATCH_MP PL_INV_NAT) THEN
  PL_INV_FACTS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_EL]) THEN
  CONJ_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THENL
   [ASM_MESON_TAC[LT_TRANS];
    SUBGOAL_THEN `?ty. fdty nms tys (EL j ymap) ty` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `EL j ymap < LENGTH (tys:(num#num#num)list)` ASSUME_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1(SPEC_ALL FDTY_BOUND)) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[LT_TRANS]]);;

let TAB_START_TAC plan =
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(W(fun (_,w) -> if is_imp w && not(is_const_app "tab_run" (lhand w)) then DISCH_TAC else NO_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_K) THEN PL_ROWS_TAC THEN
  PL_INV_ASM(fun inv -> STRIP_ASSUME_TAC(MATCH_MP TAB_HOL_MAPS inv)) THEN
  REWRITE_TAC[plan] THEN TAB_RUN_TAC THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
  TRY(ASM_ARITH_TAC THEN NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The invariant after a step that appends rows: names, type rows, terms,   *)
(* de Bruijn rows and theorems appended, the maps, drops and policy any.    *)
(* ------------------------------------------------------------------------- *)

let pl_inv_grow_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk cw' r ctx' mn mt mtm md mth nmap' ymap' drops' pol'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) r
              (ctx',APPEND nms mn,APPEND tys mt,APPEND ntms mtm,APPEND dbs md,APPEND ths mth,
               nmap',ymap',drops',pol') /\
     (!n. n <= 6 ==> cw' n = cw n) /\
     nat_keys (APPEND tys mt) (APPEND dbs md) /\
     keys_distinct (APPEND tys mt) /\ keys_distinct (APPEND dbs md) /\
     LENGTH nms + LENGTH mn < 2 EXP 60 /\ LENGTH tys + LENGTH mt < 2 EXP 60 /\
     LENGTH ntms + LENGTH mtm < 2 EXP 60 /\ LENGTH dbs + LENGTH md < 2 EXP 60 /\
     LENGTH ths + LENGTH mth < 2 EXP 60 /\
     (!h. h < LENGTH mth ==> SND(EL h mth) < LENGTH dbs + LENGTH md /\
                             ?ids. pl_ids (APPEND dbs md) (FST(EL h mth)) ids /\ PAIRWISE (<) ids)
     ==> pl_inv (cw',(ctx',APPEND nms mn,APPEND tys mt,APPEND ntms mtm,APPEND dbs md,APPEND ths mth,
                      nmap',ymap',drops',pol'),stk)`;;

let PL_INV_GROW = prove(pl_inv_grow_goal,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_inv] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`; `r:holr_record`;
                `(ctx',APPEND nms mn,APPEND tys mt,APPEND ntms mtm,APPEND dbs md,APPEND ths mth,
                  nmap',ymap',drops',pol'):nstate`; `hr:hrstate`] NAT_STEP_SIM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH_APPEND] THEN
  REPEAT CONJ_TAC THEN FIRST (map (fun t -> t THEN NO_TAC)
   [EXISTS_TAC `hr':hrstate` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[EL_APPEND; ARITH_RULE `3 <= l ==> 0 < l /\ 1 < l /\ 2 < l`];
    ASM_SIMP_TAC[EL_APPEND; ARITH_RULE `4 <= l ==> 0 < l /\ 1 < l /\ 3 < l`];
    ASM_SIMP_TAC[EL_APPEND; ARITH_RULE `1 <= l ==> 0 < l`];
    X_GEN_TAC `h:num` THEN DISCH_TAC THEN REWRITE_TAC[EL_APPEND] THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `h:num` o check (fun th -> is_forall(concl th) &&
         can (find_term ((=) `ths:(num#num)list`)) (concl th) && can (find_term ((=) `pl_ids`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[PL_IDS_APPEND];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term ((=) `mth:(num#num)list`)) (concl th))) THEN
      ASM_ARITH_TAC]]));;

(* ------------------------------------------------------------------------- *)
(* TYVAR n: the N id's name a; the type row (0,a,0) interned; the Y map     *)
(* extended by it.                                                           *)
(* ------------------------------------------------------------------------- *)

let FDTY_TYVAR = el 0 (CONJUNCTS(SPEC_ALL fdty_RULES));;
let NAT_STEP_TYVAR = el 1 (CONJUNCTS nat_step_RULES);;

let PL_TYVAR_FIRED = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk n y mt cw'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ n < LENGTH nmap /\
     pl_interned tys (0,EL n nmap,0) y mt /\ (!m. m <= 6 ==> cw' m = cw m)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTyVar n)
                  (ctx,nms,APPEND tys mt,ntms,dbs,ths,nmap,APPEND ymap [y],drops,pol) /\
         pl_inv (cw',(ctx,nms,APPEND tys mt,ntms,dbs,ths,nmap,APPEND ymap [y],drops,pol),stk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_HOL_MAPS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_TABS_OK) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_NAMES_INJ) THEN
  SUBGOAL_THEN `EL n nmap < LENGTH (nms:string list)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  PL_TY_STEP_TAC `tys:(num#num#num)list` `(0,EL n (nmap:num list),0)` `y:num` `mt:(num#num#num)list`
    (REWRITE_TAC[fibre_ty_ok] THEN DISJ1_TAC THEN EXISTS_TAC `TyVar (EL (EL n nmap) nms)` THEN
     REWRITE_TAC[HTYPE_OK] THEN MATCH_MP_TAC FDTY_TYVAR THEN EXISTS_TAC `0` THEN
     ASM_REWRITE_TAC[PL_EL_SNOC]) THEN
  SUBGOAL_THEN `fdty nms (APPEND tys mt) y (TyVar (EL (EL n nmap) nms))` ASSUME_TAC THENL
   [MATCH_MP_TAC FDTY_TYVAR THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_const_app "pl_tabs_ok" (concl th) &&
                           can (find_term ((=) `mt:(num#num#num)list`)) (concl th)
                        then STRIP_ASSUME_TAC(REWRITE_RULE[pl_tabs_ok] th) else failwith "") THEN
  SUBGOAL_THEN `nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTyVar n)
                  (ctx,nms,APPEND tys mt,ntms,dbs,ths,nmap,APPEND ymap [y],drops,pol)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                  `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                  `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `n:num`;
                  `mt:(num#num#num)list`; `[]:(num#num#num)list`; `y:num`] NAT_STEP_TYVAR) THEN
    REWRITE_TAC[APPEND_NIL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                  `mt:(num#num#num)list`; `[]:(num#num#num)list`] NAT_KEYS_NEW_ROWS) THEN
    ASM_REWRITE_TAC[APPEND_NIL; LENGTH; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
                `cw':num->num`; `RTyVar n`; `ctx:hupdate list`; `[]:string list`; `mt:(num#num#num)list`;
                `[]:(num#num#num#num#num)list`; `[]:(num#num#num)list`; `[]:(num#num)list`;
                `nmap:num list`; `APPEND (ymap:num list) [y]`; `drops:(num#num)list`; `pol:num`] PL_INV_GROW) THEN
  REWRITE_TAC[APPEND_NIL; LENGTH; ADD_CLAUSES; CONJUNCT1 LT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN PL_INV_FACTS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
  ASM_REWRITE_TAC[]);;

let pl_tyvar_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp n k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ (!j. ~MEM (0,j) drops) /\ cw 8 = n /\
     tab_run hol_tables inp pl_plan_tyvar 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
             (k,i,(cw',ns',stk'))
     ==> (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTyVar n) ns' /\
                    pl_inv (cw',ns',stk')) /\
         (k = 0 <=> ~(n < LENGTH nmap))`;;

(* PL_TYVAR: the plan's FIRED run is TYVAR's nat_step and keeps pl_inv; it   *)
(* is REFUSED exactly when n is not an N id.                                 *)
let PL_TYVAR = prove(pl_tyvar_goal,
  TAB_START_TAC pl_plan_tyvar THEN
  MATCH_MP_TAC PL_TYVAR_FIRED THEN PL_WITNESS_TAC THEN ASM_REWRITE_TAC[] THEN PL_SET_LOW_TAC);;

(* ------------------------------------------------------------------------- *)
(* VAR n y: the N id's name a and the Y id's type row ty; the de Bruijn row *)
(* (0,a,ty) interned; the term row (0,a,ty,ty,d) appended.                  *)
(* ------------------------------------------------------------------------- *)

let FDDB_VAR = el 0 (CONJUNCTS(SPEC_ALL fddb_RULES));;
let NAT_STEP_VAR = el 3 (CONJUNCTS nat_step_RULES);;

let PL_VAR_FIRED = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk n y d md cw'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ n < LENGTH nmap /\
     y < LENGTH ymap /\ ~MEM (1,y) drops /\
     pl_interned dbs (0,EL n nmap,EL y ymap) d md /\ LENGTH ntms + 1 < 2 EXP 60 /\ (!m. m <= 6 ==> cw' m = cw m)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RVar n y)
                  (ctx,nms,tys,APPEND ntms [(0,EL n nmap,EL y ymap,EL y ymap,d)],APPEND dbs md,ths,
                   nmap,ymap,drops,pol) /\
         pl_inv (cw',(ctx,nms,tys,APPEND ntms [(0,EL n nmap,EL y ymap,EL y ymap,d)],APPEND dbs md,ths,
                      nmap,ymap,drops,pol),stk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_HOL_MAPS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_TABS_OK) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_NAMES_INJ) THEN
  SUBGOAL_THEN `EL n nmap < LENGTH (nms:string list)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?ty. fdty nms tys (EL y ymap) ty` (X_CHOOSE_TAC `ty:holtype`) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  PL_DB_STEP_TAC `tys:(num#num#num)list` `dbs:(num#num#num)list` `(0,EL n (nmap:num list),EL y (ymap:num list))` `d:num`
    `md:(num#num#num)list`
    (DISJ1_TAC THEN EXISTS_TAC `hdbVar (EL (EL n nmap) nms) ty` THEN MATCH_MP_TAC FDDB_VAR THEN
     EXISTS_TAC `EL y (ymap:num list)` THEN ASM_REWRITE_TAC[PL_EL_SNOC]) THEN
  SUBGOAL_THEN `fddb nms tys (APPEND dbs md) d (hdbVar (EL (EL n nmap) nms) ty)` ASSUME_TAC THENL
   [MATCH_MP_TAC FDDB_VAR THEN EXISTS_TAC `EL y (ymap:num list)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_const_app "pl_tabs_ok" (concl th) &&
                           can (find_term ((=) `md:(num#num#num)list`)) (concl th)
                        then STRIP_ASSUME_TAC(REWRITE_RULE[pl_tabs_ok] th) else failwith "") THEN
  SUBGOAL_THEN `nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RVar n y)
                  (ctx,nms,tys,APPEND ntms [(0,EL n nmap,EL y ymap,EL y ymap,d)],APPEND dbs md,ths,
                   nmap,ymap,drops,pol)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                  `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                  `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `n:num`; `y:num`;
                  `ty:holtype`; `[]:(num#num#num)list`; `md:(num#num#num)list`; `d:num`] NAT_STEP_VAR) THEN
    REWRITE_TAC[APPEND_NIL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND; holr_live; NAT_TYS_OK_NIL] THEN
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
                `cw':num->num`; `RVar n y`; `ctx:hupdate list`; `[]:string list`; `[]:(num#num#num)list`;
                `[(0,EL n (nmap:num list),EL y (ymap:num list),EL y ymap,d:num)]`; `md:(num#num#num)list`; `[]:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`] PL_INV_GROW) THEN
  REWRITE_TAC[APPEND_NIL; LENGTH; ADD_CLAUSES; CONJUNCT1 LT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN PL_INV_FACTS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
  ASM_REWRITE_TAC[ONE] THEN ASM_ARITH_TAC);;

let pl_var_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp n y k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ (!j. ~MEM (0,j) drops) /\
     cw 8 = n /\ cw 9 = y /\
     tab_run hol_tables inp pl_plan_var 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
             (k,i,(cw',ns',stk'))
     ==> (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RVar n y) ns' /\
                    pl_inv (cw',ns',stk')) /\
         (k = 0 <=> ~(n < LENGTH nmap /\ holr_live 1 y (LENGTH ymap) drops))`;;

(* PL_VAR: the plan's FIRED run is VAR's nat_step and keeps pl_inv; it is   *)
(* REFUSED exactly when n is not an N id or y is not a live Y id.            *)
let PL_VAR = prove(pl_var_goal,
  REWRITE_TAC[holr_live] THEN TAB_START_TAC pl_plan_var THEN
  MATCH_MP_TAC PL_VAR_FIRED THEN PL_WITNESS_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  PL_SET_LOW_TAC);;

(* ------------------------------------------------------------------------- *)
(* NAME: the name found among the names, or appended when absent; the N    *)
(* map extended by its row.                                                  *)
(* ------------------------------------------------------------------------- *)

let NAT_STEP_NAME = el 0 (CONJUNCTS nat_step_RULES);;

let PL_NAME_FIRED = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk bs i nms' cw'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     (nms' = nms /\ i < LENGTH nms /\ hname_bytes (EL i nms) = bs \/
      nms' = APPEND nms [holr_name bs] /\ i = LENGTH nms /\
      (!j. j < LENGTH nms ==> ~(hname_bytes (EL j nms) = bs)) /\
      LENGTH nms + 1 < 2 EXP 60 /\ ALL (\b. b < 256) bs) /\
     (!m. m <= 6 ==> cw' m = cw m)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RName bs)
                  (ctx,nms',tys,ntms,dbs,ths,APPEND nmap [i],ymap,drops,pol) /\
         pl_inv (cw',(ctx,nms',tys,ntms,dbs,ths,APPEND nmap [i],ymap,drops,pol),stk)`,
  let grow mn ent =
    MP_TAC(SPECL [`cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                  `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                  `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
                  `cw':num->num`; `RName bs`; `ctx:hupdate list`; mn; `[]:(num#num#num)list`;
                  `[]:(num#num#num#num#num)list`; `[]:(num#num#num)list`; `[]:(num#num)list`;
                  mk_icomb(mk_icomb(`APPEND:num list->num list->num list`, `nmap:num list`), mk_list([ent],`:num`));
                  `ymap:num list`; `drops:(num#num)list`; `pol:num`] PL_INV_GROW) THEN
    REWRITE_TAC[APPEND_NIL; LENGTH; ADD_CLAUSES; CONJUNCT1 LT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN PL_INV_FACTS_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC in
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `nms':string list`)) THENL
   [SUBGOAL_THEN `nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RName bs)
                    (ctx,nms,tys,ntms,dbs,ths,APPEND nmap [i],ymap,drops,pol)` ASSUME_TAC THENL
     [MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                    `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                    `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `bs:num list`;
                    `[]:string list`; `i:num`] NAT_STEP_NAME) THEN
      REWRITE_TAC[APPEND_NIL; NAT_NEW_NAMES_NIL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `bs:num list`)) THEN
      REWRITE_TAC[HOLR_NAME_BYTES];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN grow `[]:string list` `i:num`;
    SUBGOAL_THEN `nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RName bs)
                    (ctx,APPEND nms [holr_name bs],tys,ntms,dbs,ths,APPEND nmap [LENGTH nms],ymap,drops,pol)`
      ASSUME_TAC THENL
     [MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                    `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                    `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `bs:num list`;
                    `[holr_name bs]`; `LENGTH (nms:string list)`] NAT_STEP_NAME) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH; EL_APPEND; LT_REFL; SUB_REFL; EL; HD; nat_new_names] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`kk:num`; `j:num`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `kk = LENGTH (nms:string list)` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[LT_REFL; SUB_REFL; EL; HD] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
                      can (find_term ((=) `hname_bytes`)) (concl th))) THEN
      ASM_SIMP_TAC[HNAME_BYTES_NAME];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `i:num`)) THEN
    ASM_REWRITE_TAC[] THEN grow `[holr_name bs]` `LENGTH (nms:string list)`]);;

let pl_name_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp off len k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = off /\ cw 9 = len /\
     tab_run hol_tables inp pl_plan_name 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
             (k,i,(cw',ns',stk'))
     ==> (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RName (tab_key inp off len)) ns' /\
                    pl_inv (cw',ns',stk')) /\
         (k = 0 <=> ~(off + len <= LENGTH inp))`;;

(* PL_NAME: the plan's FIRED run is NAME's nat_step for the input's bytes    *)
(* from OP0, OP1 of them, and keeps pl_inv; it is REFUSED exactly when they *)
(* do not lie in the input.                                                  *)
let PL_NAME = prove(pl_name_goal,
  TAB_START_TAC pl_plan_name THEN
  MATCH_MP_TAC PL_NAME_FIRED THEN PL_WITNESS_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  PL_SET_LOW_TAC);;

(* ------------------------------------------------------------------------- *)
(* Safety: every leaf a run of these plans reaches is enabled. A leaf is    *)
(* enabled at every state but append_row, which needs its width word to be  *)
(* the table's width, and intern_name, which inside the input needs v1 to   *)
(* be the name's FNV-1a; for any interface (the TAB_EN lemmas).              *)
(* ------------------------------------------------------------------------- *)

let TAB_EN_TOTAL = prove
 (`!(tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
        (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) inp st s.
     val(EL 0 st) = 0 \/ val(EL 0 st) = 1 \/ val(EL 0 st) = 2 \/ val(EL 0 st) = 3 \/
     val(EL 0 st) = 4 \/ val(EL 0 st) = 5 \/ val(EL 0 st) = 20 \/ val(EL 0 st) = 22
     ==> ?k pay s'. tab_leaf tb inp st s k pay s'`,
  MESON_TAC[TAB_TOTAL_LEAF; tab_total]);;

let TAB_EN_APPEND = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput inp st cw s stk.
     val(EL 0 st) = 6 /\ cw(val(EL 12 st)) = twd (val(EL 1 st))
     ==> ?k pay s'. tab_leaf (trow,tn,twd,tdrop,tapp,tput) inp st (cw,s,stk) k pay s'`,
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`2`; `0`; `s:S`] THEN
  REWRITE_TAC[tab_leaf; tab_append; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[ARITH_EQ]);;

let TAB_EN_NAME = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput inp st cw s stk.
     val(EL 0 st) = 23 /\
     (cw(val(EL 10 st)) + cw(val(EL 11 st)) <= LENGTH inp
      ==> cw(val(EL 12 st)) = val(fnv1a fnv_offset (tab_key inp (cw(val(EL 10 st))) (cw(val(EL 11 st))))))
     ==> ?k pay s'. tab_leaf (trow,tn,twd,tdrop,tapp,tput) inp st (cw,s,stk) k pay s'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tab_leaf; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[tab_name; tab_intern] THEN
  ASM_CASES_TAC `cw(val(EL 10 (st:int64 list))) + cw(val(EL 11 st)) <= LENGTH (inp:num list)` THEN
  ASM_REWRITE_TAC[] THENL
   [MAP_EVERY EXISTS_TAC [`2`; `0`; `s:S`] THEN ASM_SIMP_TAC[ARITH_EQ];
    MESON_TAC[]]);;

(* A step's control words and words of the step, reduced. *)
let TAB_REDUCE_CONV =
  REWRITE_CONV[pl_set] THENC DEPTH_CONV BETA_CONV THENC
  DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV THENC
  REWRITE_CONV[hol_twd] THENC NUM_REDUCE_CONV;;
let TAB_ENABLED_TAC =
  REWRITE_TAC[hol_tables] THEN
  FIRST [MATCH_MP_TAC TAB_EN_TOTAL THEN CONV_TAC TAB_REDUCE_CONV THEN NO_TAC;
         MATCH_MP_TAC TAB_EN_APPEND THEN CONV_TAC TAB_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC TAB_EN_PUTW_MARK THEN CONV_TAC TAB_REDUCE_CONV THEN
          ASM_REWRITE_TAC[GSYM hol_tables;HOL_TPUT_MARK_OK;hol_twd] THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
         MATCH_MP_TAC TAB_EN_NAME THEN CONV_TAC TAB_REDUCE_CONV THEN
         ASM_REWRITE_TAC[WORD_VAL] THEN NO_TAC];;
(* A branch whose facts contradict (an outcome both 1 and another). *)
let TAB_CONTRA_TAC =
  FIRST_ASSUM(fun th -> let th' = CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[]) th in
                        if concl th' = `F` then CONTR_TAC th' else failwith "TAB_CONTRA_TAC");;
let rec TAB_SAFE_TAC g =
  let w = snd g in
  if not (is_const_app "tab_safe" w) then ALL_TAC g else
  let sts = el 2 (snd(strip_comb w)) in
  if is_const sts && fst(dest_const sts) = "NIL" then REWRITE_TAC[CONJUNCT1 tab_safe] g else
  (GEN_REWRITE_TAC I [CONJUNCT2 tab_safe] THEN REWRITE_TAC[FST; SND] THEN CONJ_TAC THENL
    [TAB_ENABLED_TAC;
     REPEAT GEN_TAC THEN
     CONV_TAC(LAND_CONV(LAND_CONV(fun t -> if TAB_LEAF_TERM t then TAB_LEAF_CONV t else failwith "TAB_HEAD"))) THEN
     DISCH_THEN(fun th ->
       W(fun (asl,_) ->
         let raw = TAB_FACT_RULE asl (CONJUNCT1 th) in
         PL_BOUNDS_TAC (concl raw) THEN
         W(fun (asl,_) ->
           let leaf = CONV_RULE (SIMP_CONV (!PL_SIMPS @ map snd asl) THENC PL_NORM_CONV THENC
                                 REWRITE_CONV[PL_COND_DISJ]) raw in
           ASSUME_TAC(CONJUNCT2 th) THEN PL_ASM_TCL leaf))) THEN
     PL_SUBST_ALL_TAC THEN (TAB_CONTRA_TAC ORELSE TAB_SAFE_TAC)]) g;;

let TAB_SAFE_TYVAR = prove
 (`!inp cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     cw 1 = 1 ==> tab_safe hol_tables inp pl_plan_tyvar (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_plan_tyvar] THEN TAB_SAFE_TAC);;

let TAB_SAFE_VAR = prove
 (`!inp cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     cw 5 = 5 ==> tab_safe hol_tables inp pl_plan_var (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_plan_var] THEN TAB_SAFE_TAC);;

let TAB_SAFE_NAME = prove
 (`!inp cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     cw 1 = 1 /\ cw 22 = val fnv_offset
     ==> tab_safe hol_tables inp pl_plan_name (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_plan_name] THEN TAB_SAFE_TAC);;

(* Every theorem this file states, for the audits. *)
let tables_kinds_theorems =
 ["TAB_INTERN_HOL_TY", TAB_INTERN_HOL_TY; "TAB_INTERN_HOL_DB", TAB_INTERN_HOL_DB; "TAB_HOL_MAPS", TAB_HOL_MAPS;
  "PL_INV_GROW", PL_INV_GROW; "PL_TYVAR_FIRED", PL_TYVAR_FIRED; "PL_TYVAR", PL_TYVAR;
  "PL_VAR_FIRED", PL_VAR_FIRED; "PL_VAR", PL_VAR; "PL_NAME_FIRED", PL_NAME_FIRED; "PL_NAME", PL_NAME;
  "TAB_EN_TOTAL", TAB_EN_TOTAL; "TAB_EN_APPEND", TAB_EN_APPEND; "TAB_EN_PUTW_MARK", TAB_EN_PUTW_MARK; "TAB_EN_NAME", TAB_EN_NAME;
  "TAB_SAFE_TYVAR", TAB_SAFE_TYVAR; "TAB_SAFE_VAR", TAB_SAFE_VAR; "TAB_SAFE_NAME", TAB_SAFE_NAME];;
