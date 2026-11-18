(* ========================================================================= *)
(* The record plans of plans_abs.ml and plans_more.ml over the general      *)
(* layer: a plan of old steps runs over HOL's tables as pl_run does         *)
(* (TAB_RUN_HOL), so each abstract theorem PL_<KIND> holds of tab_run       *)
(* (tab_run_lift), and through the driver over HOL's full layout as NAME,   *)
(* TYVAR and VAR's do (tab_drv_lift): REFL, ASSUME and EMIT. Both goals are *)
(* read off PL_<KIND>'s statement.                                          *)
(*                                                                           *)
(* Loaded after tables_kinds_drv.ml.                                         *)
(* ========================================================================= *)

(* The keyed tables of a pl_inv state are canonical. *)
let TAB_CANON_INV = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> tab_canon (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PL_INV_ROWS) THEN SIMP_TAC[tab_canon]);;

(* ------------------------------------------------------------------------- *)
(* A plan's abstract theorem over tab_run.                                   *)
(* ------------------------------------------------------------------------- *)

let tab_run_goal th =
  let vs, body = strip_forall(concl th) in
  let ant, cncl = dest_imp body in
  let prems = conjuncts ant in
  let run = find (is_const_app "pl_run") prems in
  let trun = list_mk_icomb "tab_run" ([`hol_tables`; `inp:num list`] @ snd(strip_comb run)) in
  list_mk_forall(`inp:num list` :: vs,
                 mk_imp(list_mk_conj(map (fun p -> if p = run then trun else p) prems), cncl));;

(* TAB_RUN_HOL's side conditions, for a concrete plan of old steps. *)
let TAB_OLD_PLAN_TAC plan_def =
  let red = CONV_TAC(DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) in
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[plan_def; ALL; pl_old_step] THEN red;
    PL_INV_ASM(fun inv -> ACCEPT_TAC(MATCH_MP TAB_CANON_INV inv));
    FIRST_ASSUM(fun th -> ACCEPT_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(MATCH_MP PL_K th)))));
    REWRITE_TAC[plan_def; MEM] THEN GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN red];;

let tab_run_lift th plan_def =
  prove(tab_run_goal th,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th THEN PL_WITNESS_TAC THEN ASM_REWRITE_TAC[] THEN
    W(fun (asl,w) ->
      let run = find (fun t -> is_const_app "pl_run" t) (conjuncts w @ [w]) in
      let args = snd(strip_comb run) in
      let P = el 0 args and i = el 1 args and s = el 2 args and r = el 3 args in
      let cw, rest = dest_pair s in
      let ns, stk = dest_pair rest in
      MP_TAC(ISPECL [`inp:num list`; P; i; cw; ns; stk; r] TAB_RUN_HOL)) THEN
    ANTS_TAC THENL [TAB_OLD_PLAN_TAC plan_def; DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A plan's theorem through the driver over HOL's full layout.              *)
(* ------------------------------------------------------------------------- *)

let tab_drv_goal tabrun_th =
  let vs, body = strip_forall(concl tabrun_th) in
  let ant, cncl = dest_imp body in
  let prems = conjuncts ant in
  let run = find (is_const_app "tab_run") prems in
  let args = snd(strip_comb run) in
  let P = el 2 args and s = el 4 args in
  let others = filter (fun p -> not(p = run)) prems in
  let fired, refused = dest_conj cncl in
  let nstep = lhand(rand fired) and g = rand refused in
  let ns' = el 2 (snd(strip_comb nstep)) in
  let s' = `s':pstate` and res = `res:int64#num#(int64->byte)#int64` in
  let rel m st = list_mk_icomb "tab_rel" [`hol_tables`; `hol_layout`; `inp:num list`; `bw:num->int64`; `ctl:int64`;
                                          `nctl:num`; `cfr:int64`; m; st] in
  let fst_res = `FST(res:int64#num#(int64->byte)#int64)` in
  let ant' = list_mk_conj
    ([`pl_progs_ok progs`; `(progs:num->tisa_prog) 22 = fnv`; `(progs:num->tisa_prog) 23 = intern_name`;
      list_mk_icomb "pl_cw_range" [`nctl:num`; P];
      list_mk_icomb "drv_sem" [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`;
                               P; `0`; `m:int64->byte`; `used:int64`; res];
      rel `m:int64->byte` s; `~(val (budget:int64) < val (used:int64))`] @ others) in
  let cncl' = mk_conj(mk_imp(mk_eq(fst_res, `word 1:int64`),
                             mk_exists(s', mk_conj(mk_conj(subst [`FST(SND(s':pstate))`, ns'] nstep, `pl_inv s'`),
                                                   rel `FST(SND(SND(res:int64#num#(int64->byte)#int64)))` s'))),
                      mk_iff(mk_eq(fst_res, `word 0:int64`), g)) in
  let gl = mk_imp(ant', cncl') in
  let head = [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
              `m:int64->byte`; `used:int64`; res; `inp:num list`] in
  let tail = filter (fun v -> not(mem v head) && vfree_in v gl) vs in
  list_mk_forall(head @ tail, gl);;

let tab_drv_lift tabrun_th plan impl_th safe_th =
  prove(tab_drv_goal tabrun_th, TAB_KIND_TAC plan impl_th safe_th tabrun_th);;

(* ------------------------------------------------------------------------- *)
(* REFL, ASSUME, EMIT.                                                       *)
(* ------------------------------------------------------------------------- *)

let PL_REFL_TABRUN = tab_run_lift PL_REFL pl_plan_refl;;
let PL_ASSUME_TABRUN = tab_run_lift PL_ASSUME pl_plan_assume;;
let PL_EMIT_TABRUN = tab_run_lift PL_EMIT pl_plan_emit;;

let TAB_IMPL_REFL = prove(tab_plan_impl_goal `pl_plan_refl`, TAB_PLAN_IMPL_TAC pl_plan_refl);;
let TAB_IMPL_ASSUME = prove(tab_plan_impl_goal `pl_plan_assume`, TAB_PLAN_IMPL_TAC pl_plan_assume);;
let TAB_IMPL_EMIT = prove(tab_plan_impl_goal `pl_plan_emit`, TAB_PLAN_IMPL_TAC pl_plan_emit);;

(* A plan is safe when each step's leaf is enabled at every state (total)  *)
(* or is an append whose width word is a constant K0..K6 naming its table's *)
(* width, and no step writes a word below 7; for any interface.             *)
let TAB_SAFE_CONST = prove
 (`!(tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
        (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) inp P cw (s:S) stk.
     (!st. MEM st P ==> 6 < val(EL 17 st) /\
                       (val(EL 0 st) = 0 \/ val(EL 0 st) = 1 \/ val(EL 0 st) = 2 \/ val(EL 0 st) = 3 \/
                        val(EL 0 st) = 4 \/ val(EL 0 st) = 5 \/ val(EL 0 st) = 22 \/
                        val(EL 0 st) = 6 /\ val(EL 12 st) <= 6 /\
                        FST(SND(SND tb)) (val(EL 1 st)) = val(EL 12 st))) /\
     (!k. k <= 6 ==> cw k = k)
     ==> tab_safe tb inp P (cw,s,stk)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`trow:num->S->num->num list`; `tn:num->S->num`; `twd:num->num`;
                       `tdrop:num->S->num->bool`; `tapp:num->num->S->num list->S->bool`; `tput:num->num->S->num->num->num->S->bool`; `inp:num list`] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[tab_safe; MEM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[FST; SND] THEN
  FIRST_ASSUM(MP_TAC o SPEC `h:int64 list`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  (CONJ_TAC THENL
    [(MATCH_MP_TAC TAB_EN_TOTAL THEN ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
     (MATCH_MP_TAC TAB_EN_APPEND THEN ASM_SIMP_TAC[]);
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
     REWRITE_TAC[pl_set] THEN REPEAT STRIP_TAC THEN
     COND_CASES_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]]]));;

let tab_safe_goal plan =
  subst [plan, `P:(int64 list)list`]
   `!inp cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
      pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
      ==> tab_safe hol_tables inp P (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`;;
let TAB_SAFE_PLAN_TAC plan_def =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TAB_SAFE_CONST THEN PL_INV_FACTS_TAC THEN
  ASM_REWRITE_TAC[hol_tables; FST; SND] THEN
  REWRITE_TAC[plan_def; MEM] THEN GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC TAB_REDUCE_CONV;;

let TAB_SAFE_REFL = prove(tab_safe_goal `pl_plan_refl`, TAB_SAFE_PLAN_TAC pl_plan_refl);;
let TAB_SAFE_ASSUME = prove(tab_safe_goal `pl_plan_assume`, TAB_SAFE_PLAN_TAC pl_plan_assume);;
let TAB_SAFE_EMIT = prove(tab_safe_goal `pl_plan_emit`, TAB_SAFE_PLAN_TAC pl_plan_emit);;

let PL_REFL_TAB = tab_drv_lift PL_REFL_TABRUN `pl_plan_refl` TAB_IMPL_REFL TAB_SAFE_REFL;;
let PL_ASSUME_TAB = tab_drv_lift PL_ASSUME_TABRUN `pl_plan_assume` TAB_IMPL_ASSUME TAB_SAFE_ASSUME;;
let PL_EMIT_TAB = tab_drv_lift PL_EMIT_TABRUN `pl_plan_emit` TAB_IMPL_EMIT TAB_SAFE_EMIT;;

(* Every theorem this file states, for the audits. *)
let tables_old_theorems =
 ["TAB_CANON_INV", TAB_CANON_INV; "TAB_SAFE_CONST", TAB_SAFE_CONST; "PL_REFL_TABRUN", PL_REFL_TABRUN; "PL_ASSUME_TABRUN", PL_ASSUME_TABRUN;
  "PL_EMIT_TABRUN", PL_EMIT_TABRUN; "TAB_IMPL_REFL", TAB_IMPL_REFL; "TAB_IMPL_ASSUME", TAB_IMPL_ASSUME;
  "TAB_IMPL_EMIT", TAB_IMPL_EMIT; "TAB_SAFE_REFL", TAB_SAFE_REFL; "TAB_SAFE_ASSUME", TAB_SAFE_ASSUME;
  "TAB_SAFE_EMIT", TAB_SAFE_EMIT; "PL_REFL_TAB", PL_REFL_TAB; "PL_ASSUME_TAB", PL_ASSUME_TAB;
  "PL_EMIT_TAB", PL_EMIT_TAB];;
