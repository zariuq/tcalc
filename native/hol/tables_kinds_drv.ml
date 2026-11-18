(* ========================================================================= *)
(* NAME, TYVAR and VAR through the driver over HOL's full layout: the        *)
(* driver's run of the kind's plan from memory related (tab_rel hol_tables  *)
(* hol_layout) to a state satisfying pl_inv is the record's nat_step when it *)
(* FIRES, with the final memory related to a state satisfying pl_inv, and   *)
(* is REFUSED exactly when the clause's guards fail (PL_<KIND>_TAB). Every  *)
(* step's leaf implements its meaning by the generic bridges, instantiated  *)
(* at HOL's interface and layout (TAB_HOL_IMPL_TAC); every plan is safe     *)
(* (tables_kinds.ml).                                                        *)
(*                                                                           *)
(* Loaded after tables_kinds.ml.                                             *)
(* ========================================================================= *)

(* A plan's abstract theorem carries over to the driver, for any interface: *)
(* whatever the plan proves of its FIRED runs (Q) and of when it is REFUSED *)
(* (G), the driver's run from a related state has, with the final memory    *)
(* related to a state Q holds of.                                           *)
let TAB_DRV_GENERIC = prove
 (`!prel (tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
              (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) inp progs bw ctl budget cfr P m used res
    (s:(num->num)#S#num list) Q G.
     (!st. MEM st P ==> tab_impl prel tb inp progs bw ctl budget cfr st) /\ tab_safe tb inp P s /\
     drv_sem progs bw ctl budget cfr P 0 m used res /\ prel m s /\ ~(val budget < val used) /\
     (!k j s'. tab_run tb inp P 0 s (k,j,s') ==> (k = 1 ==> Q s') /\ (k = 0 <=> G))
     ==> (FST res = word 1 ==> ?s'. Q s' /\ prel (FST(SND(SND res))) s') /\ (FST res = word 0 <=> G)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`prel:(int64->byte)->(num->num)#S#num list->bool`;
                 `tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
                     (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`; `inp:num list`;
                 `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`;
                 `P:(int64 list)list`; `0`; `m:int64->byte`; `used:int64`;
                 `res:int64#num#(int64->byte)#int64`; `s:(num->num)#S#num list`] TAB_DRV_BRIDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num`
    (X_CHOOSE_THEN `s':(num->num)#S#num list` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(FST(res:int64#num#(int64->byte)#int64) = word 1 <=> k = 1) /\ (FST res = word 0 <=> k = 0)`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC PL_WORD_SMALL_EQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `j:num`; `s':(num->num)#S#num list`] o
                check (fun th -> is_forall(concl th) && can (find_term (is_const_app "tab_run")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN EXISTS_TAC `s':(num->num)#S#num list` THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* HOL's layout: its tables, its laws in the interface's tuple form.        *)
(* ------------------------------------------------------------------------- *)

let HOL_LAYOUT_MEMS = prove
 (`MEM (KeyTab 0) hol_layout /\ MEM (KeyTab 6) hol_layout /\
   MEM (RowTab 12 14 5) hol_layout /\ MEM (MarkTab 16 12 14 5) hol_layout /\
   MEM (RowTab 18 20 2) hol_layout /\ MEM (MarkTab 22 18 20 2) hol_layout /\
   MEM (RowTab 24 26 1) hol_layout /\ MEM (MarkTab 28 24 26 1) hol_layout /\
   MEM (RowTab 30 32 1) hol_layout /\ MEM (MarkTab 34 30 32 1) hol_layout /\
   MEM (NameTab 44) hol_layout /\ MEM (InTab 54) hol_layout`,
  REWRITE_TAC[hol_layout; hol_layout_old; APPEND; MEM]);;

let HOL_TB_OK = REWRITE_RULE[hol_tables] HOL_TAPP_OK;;
let HOL_TB_PUT_OK = REWRITE_RULE[hol_tables] HOL_TPUT_MARK_OK;;

(* The bridge of a concrete step's leaf over HOL's layout, its tables read   *)
(* from the step's binding words: a row table's width and the rows a count *)
(* belongs to are HOL's (hol_twd; hol_layout).                               *)
let tab_hol_width j = assoc j [12,5; 18,2; 24,1; 30,1];;
let tab_hol_rows c = assoc c [14,12; 20,18; 26,24; 32,30];;
let TAB_HOL_BRIDGE st =
  let ws = map (fun t -> dest_small_numeral(rand t)) (dest_list st) in
  let leaf = el 0 ws and b1 = el 1 ws and b2 = el 2 ws in
  let h th = ISPECL [`hol_trow`; `hol_tn`; `hol_twd`; `hol_tdrop`; `hol_tapp`; `hol_tput`; `hol_layout`] th in
  let inst th l = INST (map (fun (v,n) -> (mk_small_numeral n, mk_var(v,`:num`))) l) (SPEC_ALL (h th)) in
  match leaf with
    0 -> inst TAB_IMPL_I16 ["j",b1]
  | 1 -> inst TAB_IMPL_PACK []
  | 2 -> inst TAB_IMPL_UNPACK []
  | 3 -> inst TAB_IMPL_EQW []
  | 4 -> inst TAB_IMPL_ROWW ["j",b1; "c",b2; "wd",tab_hol_width b1]
  | 5 -> let j = tab_hol_rows b1 in inst TAB_IMPL_LIVE ["c",b1; "jm",b2; "j",j; "wd",tab_hol_width j]
  | 6 -> inst TAB_IMPL_APPEND ["j",b1; "c",b2; "wd",tab_hol_width b1]
  | 9 -> let j = tab_hol_rows b2 in inst TAB_IMPL_PUTW_MARK ["jm",b1; "c",b2; "j",j; "wd",tab_hol_width j]
  | 20 -> inst TAB_IMPL_POLMAX []
  | 22 -> inst TAB_IMPL_FNV ["ji",b1]
  | 23 -> inst TAB_IMPL_NAME ["ji",b1; "j",b2]
  | _ -> failwith "TAB_HOL_BRIDGE: a leaf without a bridge";;

(* tab_impl at a concrete step, from the leaves' programs and its control  *)
(* words' range among the assumptions.                                       *)
let TAB_HOL_IMPL_TAC : tactic = fun (asl,w) ->
  (REWRITE_TAC[hol_tables] THEN MATCH_MP_TAC (TAB_HOL_BRIDGE (rand w)) THEN
   ASM_REWRITE_TAC[HOL_LAYOUT_MEMS; HOL_LAYOUT_WF; HOL_TB_OK; HOL_TB_PUT_OK] THEN
   CONV_TAC TAB_REDUCE_CONV THEN REWRITE_TAC[HOL_TAPP_EXISTS]) (asl,w);;

(* Every step of a plan: its leaves' programs, its control words below nctl. *)
let TAB_PLAN_IMPL_TAC plan_def =
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_progs_ok] THEN STRIP_TAC THEN
  X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!f. 10 <= f /\ f < 18 ==> val(EL f (st:int64 list)) < nctl` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_cw_range]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "MEM" (concl th))) THEN
  REWRITE_TAC[plan_def; MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `st:int64 list`
                          then SUBST_ALL_TAC th else failwith "") THEN
  TAB_HOL_IMPL_TAC;;

let tab_plan_impl_goal plan =
  subst [plan, `P:(int64 list)list`]
   `!inp progs bw ctl nctl budget cfr.
      pl_progs_ok progs /\ progs 22 = fnv /\ progs 23 = intern_name /\ pl_cw_range nctl P
      ==> !st. MEM st P ==> tab_impl (tab_rel hol_tables hol_layout inp bw ctl nctl cfr) hol_tables inp
                                     progs bw ctl budget cfr st`;;

let TAB_IMPL_TYVAR = prove(tab_plan_impl_goal `pl_plan_tyvar`, TAB_PLAN_IMPL_TAC pl_plan_tyvar);;
let TAB_IMPL_VAR = prove(tab_plan_impl_goal `pl_plan_var`, TAB_PLAN_IMPL_TAC pl_plan_var);;
let TAB_IMPL_NAMEP = prove(tab_plan_impl_goal `pl_plan_name`, TAB_PLAN_IMPL_TAC pl_plan_name);;

(* ------------------------------------------------------------------------- *)
(* The kinds through the driver.                                             *)
(* ------------------------------------------------------------------------- *)

let TAB_KIND_TAC plan impl_th safe_th abs_th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_K) THEN
  W(fun (asl,w) ->
    let c1,c2 = dest_conj w in
    let g_tm = rand c2 in
    let s',b = dest_exists (rand c1) in
    let q_tm = mk_abs(s', lhand b) in
    let s0 = rand(concl(snd(find (fun (_,th) -> is_const_app "pl_inv" (concl th)) asl))) in
    let res = rand(lhand(lhand c1)) in
    MP_TAC(ISPECL [`tab_rel hol_tables hol_layout inp bw ctl nctl cfr`; `hol_tables`; `inp:num list`;
                   `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`;
                   plan; `m:int64->byte`; `used:int64`; res; s0; q_tm; g_tm] TAB_DRV_GENERIC)) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC impl_th THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC safe_th THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC abs_th THEN PL_WITNESS_TAC THEN ASM_REWRITE_TAC[]];;

(* PL_TYVAR_TAB: TYVAR's plan through the driver over HOL's layout. *)
let PL_TYVAR_TAB = prove
 (`!progs bw ctl nctl budget cfr m used res inp cw ctx nms tys ntms dbs ths nmap ymap drops pol stk n.
     pl_progs_ok progs /\ progs 22 = fnv /\ progs 23 = intern_name /\ pl_cw_range nctl pl_plan_tyvar /\
     drv_sem progs bw ctl budget cfr pl_plan_tyvar 0 m used res /\
     tab_rel hol_tables hol_layout inp bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ (!j. ~MEM (0,j) drops) /\ cw 8 = n
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTyVar n) (FST(SND s')) /\
                    pl_inv s') /\
                   tab_rel hol_tables hol_layout inp bw ctl nctl cfr (FST(SND(SND res))) s') /\
         (FST res = word 0 <=> ~(n < LENGTH nmap))`,
  TAB_KIND_TAC `pl_plan_tyvar` TAB_IMPL_TYVAR TAB_SAFE_TYVAR PL_TYVAR);;

(* PL_VAR_TAB: VAR's plan through the driver over HOL's layout. *)
let PL_VAR_TAB = prove
 (`!progs bw ctl nctl budget cfr m used res inp cw ctx nms tys ntms dbs ths nmap ymap drops pol stk n y.
     pl_progs_ok progs /\ progs 22 = fnv /\ progs 23 = intern_name /\ pl_cw_range nctl pl_plan_var /\
     drv_sem progs bw ctl budget cfr pl_plan_var 0 m used res /\
     tab_rel hol_tables hol_layout inp bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ (!j. ~MEM (0,j) drops) /\
     cw 8 = n /\ cw 9 = y
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RVar n y) (FST(SND s')) /\
                    pl_inv s') /\
                   tab_rel hol_tables hol_layout inp bw ctl nctl cfr (FST(SND(SND res))) s') /\
         (FST res = word 0 <=> ~(n < LENGTH nmap /\ holr_live 1 y (LENGTH ymap) drops))`,
  TAB_KIND_TAC `pl_plan_var` TAB_IMPL_VAR TAB_SAFE_VAR PL_VAR);;

(* PL_NAME_TAB: NAME's plan through the driver over HOL's layout, for the   *)
(* name the input's bytes from OP0 hold, OP1 of them, with FNVB holding the *)
(* FNV-1a offset basis.                                                      *)
let PL_NAME_TAB = prove
 (`!progs bw ctl nctl budget cfr m used res inp cw ctx nms tys ntms dbs ths nmap ymap drops pol stk off len.
     pl_progs_ok progs /\ progs 22 = fnv /\ progs 23 = intern_name /\ pl_cw_range nctl pl_plan_name /\
     drv_sem progs bw ctl budget cfr pl_plan_name 0 m used res /\
     tab_rel hol_tables hol_layout inp bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 22 = val fnv_offset /\
     cw 8 = off /\ cw 9 = len
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RName (tab_key inp off len))
                             (FST(SND s')) /\ pl_inv s') /\
                   tab_rel hol_tables hol_layout inp bw ctl nctl cfr (FST(SND(SND res))) s') /\
         (FST res = word 0 <=> ~(off + len <= LENGTH inp))`,
  TAB_KIND_TAC `pl_plan_name` TAB_IMPL_NAMEP TAB_SAFE_NAME PL_NAME);;

(* Every theorem this file states, for the audits. *)
let tables_kinds_drv_theorems =
 ["TAB_DRV_GENERIC", TAB_DRV_GENERIC; "HOL_LAYOUT_MEMS", HOL_LAYOUT_MEMS; "HOL_TB_OK", HOL_TB_OK;
  "TAB_IMPL_TYVAR", TAB_IMPL_TYVAR; "TAB_IMPL_VAR", TAB_IMPL_VAR; "TAB_IMPL_NAMEP", TAB_IMPL_NAMEP;
  "PL_TYVAR_TAB", PL_TYVAR_TAB; "PL_VAR_TAB", PL_VAR_TAB; "PL_NAME_TAB", PL_NAME_TAB];;
