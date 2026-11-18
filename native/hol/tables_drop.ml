(* ========================================================================= *)
(* DROP_TYPE, DROP_TERM and DROP_THM over the interface (PLANS.txt, section *)
(* 6): live the id [REFUSED when it is not a live id of its space], then    *)
(* put_word 1 at its mark (stride 1, word 0). From a state satisfying       *)
(* pl_inv with the id in OP0, a FIRED run is the record's nat_step and      *)
(* keeps pl_inv; it is REFUSED exactly when the id is not live (PL_DROP_TYPE, *)
(* PL_DROP_TERM, PL_DROP_THM); so through the driver over HOL's full layout  *)
(* (PL_DROP_TYPE_TAB and the others).                                        *)
(*                                                                           *)
(* Loaded after tables_kinds_drv.ml and tables_put.ml.                       *)
(* ========================================================================= *)

let pl_PUTW = 9;;
let pl_YMARKS = [28; 26] and pl_TMMARKS = [16; 14] and pl_THMARKS = [22; 20];;   (* put_word: marks, count *)

let pl_drop_plan live marks =
  pl_begin();
  let _ = pl_emit pl_LIVE live pl_OP0 0 [] in
  let _ = pl_emit pl_PUTW marks pl_OP0 1 [1; 0] in
  pl_plan();;

let pl_plan_drop_type = new_definition(mk_eq(`pl_plan_drop_type:(int64 list)list`, pl_drop_plan pl_YLIVE pl_YMARKS));;
let pl_plan_drop_term = new_definition(mk_eq(`pl_plan_drop_term:(int64 list)list`, pl_drop_plan pl_TMLIVE pl_TMMARKS));;
let pl_plan_drop_thm = new_definition(mk_eq(`pl_plan_drop_thm:(int64 list)list`, pl_drop_plan pl_THLIVE pl_THMARKS));;

(* ------------------------------------------------------------------------- *)
(* The invariant after a drop.                                               *)
(* ------------------------------------------------------------------------- *)

let PL_DROP_FIRED = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk r (drop_space:num) (n:num) cw'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) r
              (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,CONS (drop_space,n) drops,pol) /\
     (!m. m <= 6 ==> cw' m = cw m)
     ==> pl_inv (cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,CONS (drop_space,n) drops,pol),stk)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:(hupdate)list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`;
                `cw':num->num`; `r:holr_record`; `ctx:(hupdate)list`; `[]:string list`; `[]:(num#num#num)list`;
                `[]:(num#num#num#num#num)list`; `[]:(num#num#num)list`; `[]:(num#num)list`; `nmap:num list`;
                `ymap:num list`; `CONS ((drop_space:num),(n:num)) (drops:(num#num)list)`; `pol:num`] PL_INV_GROW) THEN
  REWRITE_TAC[APPEND_NIL; LENGTH; ADD_CLAUSES; ARITH_RULE `~(h < 0)`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[pl_inv] o check (fun th -> is_const_app "pl_inv" (concl th))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The plans over HOL's tables.                                              *)
(* ------------------------------------------------------------------------- *)

let pl_drop_goal plan rcon sp count =
  let tm = `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp n k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ (!j. ~MEM (0,j) drops) /\ cw 8 = n /\
     tab_run hol_tables inp P 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) (k,i,(cw',ns',stk'))
     ==> (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (R n) ns' /\ pl_inv (cw',ns',stk')) /\
         (k = 0 <=> ~(n < C /\ ~MEM (drop_space,n) drops))` in
  let variables, body = strip_forall tm in
  let goal = list_mk_forall(variables,
    subst [plan, `P:(int64 list)list`; rcon, `R:num->holr_record`; mk_small_numeral sp, `drop_space:num`;
           count, `C:num`] body) in
  if frees goal <> [] then failwith "pl_drop_goal: free statement variable" else goal;;

let NAT_STEP_OF r = find (fun th -> can (find_term ((=) r)) (concl th)) (CONJUNCTS nat_step_RULES);;

let PL_DROP_TAC plan_def r =
  TAB_START_TAC plan_def THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC (NAT_STEP_OF r) THEN
    REWRITE_TAC[nat_ops_live; holr_operands; ALL; holr_live] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_DROP_FIRED THEN
    MAP_EVERY EXISTS_TAC [`cw:num->num`; mk_comb(r, `n:num`)] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (NAT_STEP_OF r) THEN
      REWRITE_TAC[nat_ops_live; holr_operands; ALL; holr_live] THEN ASM_REWRITE_TAC[];
      PL_SET_LOW_TAC]];;

let PL_DROP_TYPE = prove(pl_drop_goal `pl_plan_drop_type` `RDropType` 1 `LENGTH (ymap:num list)`,
  PL_DROP_TAC pl_plan_drop_type `RDropType`);;
let PL_DROP_TERM = prove(pl_drop_goal `pl_plan_drop_term` `RDropTerm` 2 `LENGTH (ntms:(num#num#num#num#num)list)`,
  PL_DROP_TAC pl_plan_drop_term `RDropTerm`);;
let PL_DROP_THM = prove(pl_drop_goal `pl_plan_drop_thm` `RDropThm` 3 `LENGTH (ths:(num#num)list)`,
  PL_DROP_TAC pl_plan_drop_thm `RDropThm`);;

(* ------------------------------------------------------------------------- *)
(* Through the driver over HOL's full layout.                                *)
(* ------------------------------------------------------------------------- *)

let tab_drop_impl_goal plan =
  subst [plan, `P:(int64 list)list`]
   `!inp progs bw ctl nctl budget cfr.
      pl_progs_ok progs /\ progs 9 = put_word /\ progs 20 = pol_max /\ progs 22 = fnv /\ progs 23 = intern_name /\
      pl_cw_range nctl P
      ==> !st. MEM st P ==> tab_impl (tab_rel hol_tables hol_layout inp bw ctl nctl cfr) hol_tables inp
                                     progs bw ctl budget cfr st`;;

let TAB_IMPL_DROP_TYPE = prove(tab_drop_impl_goal `pl_plan_drop_type`, TAB_PLAN_IMPL_TAC pl_plan_drop_type);;
let TAB_IMPL_DROP_TERM = prove(tab_drop_impl_goal `pl_plan_drop_term`, TAB_PLAN_IMPL_TAC pl_plan_drop_term);;
let TAB_IMPL_DROP_THM = prove(tab_drop_impl_goal `pl_plan_drop_thm`, TAB_PLAN_IMPL_TAC pl_plan_drop_thm);;

let tab_drop_safe_goal plan =
  subst [plan, `P:(int64 list)list`]
   `!inp cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
      cw 0 = 0 /\ cw 1 = 1 ==> tab_safe hol_tables inp P (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`;;

let TAB_SAFE_DROP_TYPE = prove(tab_drop_safe_goal `pl_plan_drop_type`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_plan_drop_type] THEN TAB_SAFE_TAC);;
let TAB_SAFE_DROP_TERM = prove(tab_drop_safe_goal `pl_plan_drop_term`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_plan_drop_term] THEN TAB_SAFE_TAC);;
let TAB_SAFE_DROP_THM = prove(tab_drop_safe_goal `pl_plan_drop_thm`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_plan_drop_thm] THEN TAB_SAFE_TAC);;

let pl_drop_tab_goal plan rcon sp count =
  let tm = `!progs bw ctl nctl budget cfr m used res inp cw ctx nms tys ntms dbs ths nmap ymap drops pol stk n.
     pl_progs_ok progs /\ progs 9 = put_word /\ progs 20 = pol_max /\ progs 22 = fnv /\ progs 23 = intern_name /\
     pl_cw_range nctl P /\ drv_sem progs bw ctl budget cfr P 0 m used res /\
     tab_rel hol_tables hol_layout inp bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ (!j. ~MEM (0,j) drops) /\ cw 8 = n
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (R n) (FST(SND s')) /\ pl_inv s') /\
                   tab_rel hol_tables hol_layout inp bw ctl nctl cfr (FST(SND(SND res))) s') /\
         (FST res = word 0 <=> ~(n < C /\ ~MEM (drop_space,n) drops))` in
  let variables, body = strip_forall tm in
  let goal = list_mk_forall(variables,
    subst [plan, `P:(int64 list)list`; rcon, `R:num->holr_record`; mk_small_numeral sp, `drop_space:num`;
           count, `C:num`] body) in
  if frees goal <> [] then failwith "pl_drop_tab_goal: free statement variable" else goal;;

let PL_DROP_TYPE_TAB = prove(pl_drop_tab_goal `pl_plan_drop_type` `RDropType` 1 `LENGTH (ymap:num list)`,
  TAB_KIND_TAC `pl_plan_drop_type` TAB_IMPL_DROP_TYPE TAB_SAFE_DROP_TYPE PL_DROP_TYPE);;
let PL_DROP_TERM_TAB = prove(pl_drop_tab_goal `pl_plan_drop_term` `RDropTerm` 2
                               `LENGTH (ntms:(num#num#num#num#num)list)`,
  TAB_KIND_TAC `pl_plan_drop_term` TAB_IMPL_DROP_TERM TAB_SAFE_DROP_TERM PL_DROP_TERM);;
let PL_DROP_THM_TAB = prove(pl_drop_tab_goal `pl_plan_drop_thm` `RDropThm` 3 `LENGTH (ths:(num#num)list)`,
  TAB_KIND_TAC `pl_plan_drop_thm` TAB_IMPL_DROP_THM TAB_SAFE_DROP_THM PL_DROP_THM);;

(* Every theorem this file states, for the audits. *)
let tables_drop_theorems =
 ["PL_DROP_FIRED", PL_DROP_FIRED; "PL_DROP_TYPE", PL_DROP_TYPE; "PL_DROP_TERM", PL_DROP_TERM;
  "PL_DROP_THM", PL_DROP_THM; "TAB_IMPL_DROP_TYPE", TAB_IMPL_DROP_TYPE; "TAB_IMPL_DROP_TERM", TAB_IMPL_DROP_TERM;
  "TAB_IMPL_DROP_THM", TAB_IMPL_DROP_THM; "TAB_SAFE_DROP_TYPE", TAB_SAFE_DROP_TYPE;
  "TAB_SAFE_DROP_TERM", TAB_SAFE_DROP_TERM; "TAB_SAFE_DROP_THM", TAB_SAFE_DROP_THM;
  "PL_DROP_TYPE_TAB", PL_DROP_TYPE_TAB; "PL_DROP_TERM_TAB", PL_DROP_TERM_TAB; "PL_DROP_THM_TAB", PL_DROP_THM_TAB];;
