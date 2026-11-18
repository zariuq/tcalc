(* ========================================================================= *)
(* The plans, every run, not only the FIRED ones. A step that does not fire *)
(* leaves the abstract tables as they were (PL_LEAF_UNFIRED); a run that    *)
(* does not fire extends the tables by appending and keeps the theorem rows *)
(* when its only append to them is its last step (PL_RUN_GROWS); and the   *)
(* theorem rows of a state that grows a pl_inv state are derivable          *)
(* (PL_GROWS_THMS). Through the driver: pl_impl says nothing of the memory  *)
(* after a step that does not fire, so each leaf meets a second obligation, *)
(* pl_kept (the relation kept at the same tables); with it the final memory *)
(* is related to pl_run's final state for every outcome (PL_DRV_BRIDGE_ALL).*)
(* pl_kept under plan_rel for every leaf of the host's table (the PL_KEPT  *)
(* theorems),                                                                *)
(* and plans that write no table keep plan_rel whatever their outcome       *)
(* (RD_ONLY_KEEPS_PL).                                                       *)
(*                                                                           *)
(* Loaded after reader_rel.ml.                                               *)
(* ========================================================================= *)

needs "native/hol/reader_rel.ml";;
needs "native/hol/intern16_kept.ml";;

(* ------------------------------------------------------------------------- *)
(* Growth: the same context, theorem rows, drops and policy; every other    *)
(* table extended by appending.                                              *)
(* ------------------------------------------------------------------------- *)

let pl_grows = new_definition
 `pl_grows ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate)
           ((ctx',nms',tys',ntms',dbs',ths',nmap',ymap',drops',pol'):nstate) <=>
    ctx' = ctx /\ ths' = ths /\ drops' = drops /\ pol' = pol /\
    (?a. nms' = APPEND nms a) /\ (?a. tys' = APPEND tys a) /\ (?a. ntms' = APPEND ntms a) /\
    (?a. dbs' = APPEND dbs a) /\ (?a. nmap' = APPEND nmap a) /\ (?a. ymap' = APPEND ymap a)`;;

let PL_APPEND_SELF = prove
 (`!l:A list. ?a. l = APPEND l a`,
  GEN_TAC THEN EXISTS_TAC `[]:A list` THEN REWRITE_TAC[APPEND_NIL]);;

let PL_APPEND_TRANS = prove
 (`!l1 l2 l3:A list. (?a. l2 = APPEND l1 a) /\ (?a. l3 = APPEND l2 a) ==> ?a. l3 = APPEND l1 a`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:A list`) (X_CHOOSE_TAC `b:A list`)) THEN
  EXISTS_TAC `APPEND (a:A list) b` THEN ASM_REWRITE_TAC[APPEND_ASSOC]);;

let PL_GROWS_REFL = prove
 (`!ns. pl_grows ns ns`,
  REWRITE_TAC[FORALL_PAIR_THM; pl_grows; PL_APPEND_SELF]);;

let PL_GROWS_TRANS = prove
 (`!ns1 ns2 ns3. pl_grows ns1 ns2 /\ pl_grows ns2 ns3 ==> pl_grows ns1 ns3`,
  REWRITE_TAC[FORALL_PAIR_THM; pl_grows] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC PL_APPEND_TRANS THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* One step.                                                                 *)
(* ------------------------------------------------------------------------- *)

let PL_INTERN_GROWS = prove
 (`!rows k0 k1 k pay rows'. pl_intern rows k0 k1 k pay rows' ==> ?a. rows' = APPEND rows a`,
  REWRITE_TAC[pl_intern] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[PL_APPEND_SELF]);;

let PL_INTERN_UNFIRED = prove
 (`!rows k0 k1 k pay rows'. pl_intern rows k0 k1 k pay rows' /\ ~(k = 1) ==> rows' = rows`,
  REWRITE_TAC[pl_intern] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let PL_UNION_GROWS = prove
 (`!dbs l1 l2 k pay dbs'. pl_union dbs l1 l2 k pay dbs' ==> ?a. dbs' = APPEND dbs a`,
  REWRITE_TAC[pl_union] THEN MESON_TAC[]);;

let PL_UNION_UNFIRED = prove
 (`!dbs l1 l2 k pay dbs'. pl_union dbs l1 l2 k pay dbs' /\ ~(k = 1) ==> dbs' = dbs`,
  REWRITE_TAC[pl_union] THEN MESON_TAC[]);;

let PL_APPEND_TH_UNFIRED = prove
 (`!ths a b k pay ths'. pl_append_th ths 2 a b k pay ths' /\ ~(k = 1) ==> ths' = ths`,
  REWRITE_TAC[pl_append_th] THEN MESON_TAC[]);;

(* A step that does not fire leaves the tables as they were; its append to *)
(* the theorem rows is of width 2 (control word 2 holds 2).                 *)
let PL_LEAF_UNFIRED = prove
 (`!st s k pay ns'.
     pl_leaf st s k pay ns' /\ ~(k = 1) /\ (val(EL 0 st) = 6 ==> FST s (val(EL 12 st)) = 2)
     ==> ns' = FST(SND s)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[pl_leaf; LET_DEF; LET_END_DEF; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  TRY(DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THEN
  ASM_MESON_TAC[PL_INTERN_UNFIRED; PL_UNION_UNFIRED; PL_APPEND_TH_UNFIRED]);;

(* A step grows the tables, unless it is an append to the theorem rows that *)
(* fires.                                                                    *)
let PL_LEAF_GROWS = prove
 (`!st s k pay ns'.
     pl_leaf st s k pay ns' /\ (val(EL 0 st) = 6 ==> ~(k = 1) /\ FST s (val(EL 12 st)) = 2)
     ==> pl_grows (FST(SND s)) ns'`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[pl_leaf; LET_DEF; LET_END_DEF; FST; SND] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  ASM_REWRITE_TAC[pl_grows; PL_APPEND_SELF] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  TRY(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])))) THEN
  ASM_MESON_TAC[PL_INTERN_GROWS; PL_UNION_GROWS; PL_APPEND_TH_UNFIRED; PL_APPEND_SELF]);;

(* ------------------------------------------------------------------------- *)
(* A run that does not fire. pl_th_last P: a step appending to the theorem  *)
(* rows (leaf 6) is the plan's last, with width word 2; no step writes      *)
(* control word 2.                                                           *)
(* ------------------------------------------------------------------------- *)

let pl_th_last = define
 `(pl_th_last [] <=> T) /\
  (pl_th_last (CONS (st:int64 list) sts) <=>
     ~(val(EL 17 st) = 2) /\ (val(EL 0 st) = 6 ==> sts = [] /\ val(EL 12 st) = 2) /\ pl_th_last sts)`;;

let PL_RUN_GROWS = prove
 (`!P i s k j s'.
     pl_run P i s (k,j,s') /\ ~(k = 1) /\ FST s 2 = 2 /\ pl_th_last P
     ==> pl_grows (FST(SND s)) (FST(SND s'))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[pl_run; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_run; pl_th_last] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `pay:num` (X_CHOOSE_THEN `ns1:nstate` STRIP_ASSUME_TAC)))
    STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `k1 = 1` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k1 = 1`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    ASM_CASES_TAC `val(EL 0 (h:int64 list)) = 6` THENL
     [(* the append fired: it was the last step, so the plan fired *)
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_eq(lhand(concl th)))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "pl_run" (concl th))) THEN
      ASM_REWRITE_TAC[pl_run; PAIR_EQ] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC PL_GROWS_TRANS THEN EXISTS_TAC `ns1:nstate` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_LEAF_GROWS THEN
      MAP_EVERY EXISTS_TAC [`h:int64 list`; `1`; `pay:num`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`i + 1`; `(pl_set (FST(s:pstate)) (val(EL 17 (h:int64 list))) pay,ns1,SND(SND(s:pstate))):pstate`;
       `k:num`; `j:num`; `s':pstate`] o
      check (fun th -> is_forall(concl th) && can (find_term (is_const_app "pl_th_last")) (concl th))) THEN
    REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[pl_set] THEN BETA_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  MATCH_MP_TAC PL_LEAF_GROWS THEN
  MAP_EVERY EXISTS_TAC [`h:int64 list`; `k1:num`; `pay:num`] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_eq(lhand(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The theorem rows: derivable in the state's context.                      *)
(* ------------------------------------------------------------------------- *)

let pl_thms_ok = new_definition
 `pl_thms_ok ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) <=>
    !j. j < LENGTH ths ==> fibre_thm_ok ctx nms tys dbs (EL j ths)`;;

let NAT_SIM_THMS = prove
 (`!ns hr. nat_sim ns hr ==> pl_thms_ok ns`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
    `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
    `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`;
    `hctx:hupdate list`; `hnms:string list`; `htys:holtype list`; `htms:holterm list`;
    `hths:(holterm list#holterm)list`; `hdrops:(num#num)list`; `hpol:num`] THEN
  REWRITE_TAC[nat_sim; pl_thms_ok] THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[FIBRE_THM_OK_WIT] THEN
  MAP_EVERY EXISTS_TAC [`FST(EL j (hths:(holterm list#holterm)list))`;
                        `SND(EL j (hths:(holterm list#holterm)list))`] THEN
  ASM_SIMP_TAC[PAIR]);;

let PL_INV_THMS = prove
 (`!s. pl_inv s ==> pl_thms_ok (FST(SND s))`,
  REWRITE_TAC[FORALL_PAIR_THM; pl_inv; FST; SND] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NAT_SIM_THMS THEN ASM_MESON_TAC[]);;

let PL_GROWS_THMS = prove
 (`!ns ns'. pl_thms_ok ns /\ pl_grows ns ns' ==> pl_thms_ok ns'`,
  REWRITE_TAC[FORALL_PAIR_THM; pl_thms_ok; pl_grows] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FIBRE_THM_OK_EXTEND THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Through the driver. pl_kept: when the step's leaf does not fire, the     *)
(* memory the driver keeps is related to the state with only the payload   *)
(* word changed.                                                             *)
(* ------------------------------------------------------------------------- *)

let pl_kept = new_definition
 `pl_kept (prel:(int64->byte)->pstate->bool) progs bw ctl budget cfr (st:int64 list) <=>
    !m used s t k u.
      prel m s /\ ~(val budget < val used) /\
      drv_child bw ctl budget cfr st m used t /\
      tisa_entry_ok (progs (val(EL 0 st))) t /\ tisa_run (progs (val(EL 0 st))) t = TStop k u /\
      ~(tisa_fword u 18 = word 1)
      ==> prel (drv_after ctl st u)
               (pl_set (FST s) (val(EL 17 st)) (val(tisa_fword u 19)),FST(SND s),SND(SND s))`;;

let PL_DRV_BRIDGE_ALL = prove
 (`!prel progs bw ctl budget cfr sts i m used res s.
     (!st. MEM st sts ==> pl_impl prel progs bw ctl budget cfr st /\
                          pl_kept prel progs bw ctl budget cfr st /\
                          (val(EL 0 st) = 6 ==> val(EL 12 st) = 2)) /\
     (!m s. prel m s ==> FST s 2 = 2) /\
     drv_sem progs bw ctl budget cfr sts i m used res /\ prel m s /\ ~(val budget < val used)
     ==> ?k j s'. pl_run sts i s (k,j,s') /\ k < 8 /\ FST res = word k /\ FST(SND res) = j /\
                 prel (FST(SND(SND res))) s' /\ ~(val budget < val(SND(SND(SND res))))`,
  REPLICATE_TAC 6 GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[drv_sem; MEM] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`1`; `i:num`; `s:pstate`] THEN ASM_REWRITE_TAC[pl_run] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  ASM_REWRITE_TAC[drv_sem] THEN
  DISCH_THEN(X_CHOOSE_THEN `tc:tisa_state` (X_CHOOSE_THEN `kc:num`
    (X_CHOOSE_THEN `u:tisa_state` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[] o SPEC `h:int64 list` o
              check (fun th -> is_forall(concl th) && can (find_term (is_const_app "pl_impl")) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[pl_impl] o check (fun th -> is_const_app "pl_impl" (concl th))) THEN
  DISCH_THEN(MP_TAC o SPECL [`m:int64->byte`; `used:int64`; `s:pstate`; `tc:tisa_state`;
                             `kc:num`; `u:tisa_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `ns1:nstate` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `tisa_fword u 18 = word 1 <=> k1 = 1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_WORD_SMALL_EQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k1 = 1` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k1 = 1`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`; `drv_after ctl h u`; `tisa_fword u 21`;
                    `res:int64#num#(int64->byte)#int64`;
                    `(pl_set (FST(s:pstate)) (val(EL 17 (h:int64 list))) (val(tisa_fword u 19)),ns1,SND(SND(s:pstate))):pstate`] o
                  check (fun th -> is_forall(concl th) && can (find_term (is_const_app "drv_sem")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                       can (find_term (is_const_app "pl_impl")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `j:num`; `s':pstate`] THEN ASM_REWRITE_TAC[pl_run] THEN
    MAP_EVERY EXISTS_TAC [`1`; `val(tisa_fword u 19)`; `ns1:nstate`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the step did not fire: the tables as they were *)
  SUBGOAL_THEN `ns1 = FST(SND(s:pstate))` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC PL_LEAF_UNFIRED THEN
    MAP_EVERY EXISTS_TAC [`h:int64 list`; `k1:num`; `val(tisa_fword u 19)`] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `val(EL 12 (h:int64 list)) = 2` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY EXISTS_TAC [`k1:num`; `i:num`;
                        `(pl_set (FST(s:pstate)) (val(EL 17 (h:int64 list))) (val(tisa_fword u 19)),FST(SND(s:pstate)),SND(SND(s:pstate))):pstate`] THEN
  ASM_REWRITE_TAC[pl_run; FST; SND] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`k1:num`; `val(tisa_fword u 19)`; `FST(SND(s:pstate))`] THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[pl_kept] o check (fun th -> is_const_app "pl_kept" (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`m:int64->byte`; `used:int64`; `tc:tisa_state`; `kc:num`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* pl_kept under plan_rel, leaf by leaf: a step that does not fire keeps    *)
(* the relation with the tables as they were.                                *)
(* ------------------------------------------------------------------------- *)

(* A leaf without read-write regions. *)
let PL_KEPT_RO = prove
 (`!progs bw ctl nctl budget cfr st.
     tisa_leaf_wf (progs (val(EL 0 st))) /\ (!r. ~tisa_rw (tisa_decls (progs (val(EL 0 st)))) r) /\
     val(EL 17 st) < nctl /\ 6 < val(EL 17 st)
     ==> pl_kept (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_kept; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`m:int64->byte`; `used:int64`; `cw:num->num`; `ctx:hupdate list`; `nms:string list`;
    `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`;
    `ths:(num#num)list`; `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`;
    `stk:num list`; `t:tisa_state`; `k:num`; `u:tisa_state`] THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN MATCH_MP_TAC PL_REL_RO_STEP THEN
  MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`;
                        `progs (val(EL 0 (st:int64 list))):tisa_prog`; `k:num`] THEN
  ASM_REWRITE_TAC[]);;

(* intern16 that does not fire: the interner as it was. *)
let PL_I16_STEP_KEPT = prove
 (`!bw ctl nctl budget cfr st m used t k u j rows.
     pl_layout bw ctl nctl cfr /\ (j = 0 \/ j = 6) /\ pl_itab bw j m rows /\
     drv_child bw ctl budget cfr st m used t /\
     val(EL 1 st) = j /\ val(EL 2 st) = j + 2 /\ val(EL 3 st) = j + 4 /\ val(EL 17 st) < nctl /\
     tisa_entry_ok intern16 t /\ tisa_run intern16 t = TStop k u /\ ~(k = 1)
     ==> pl_itab bw j (drv_after ctl st u) rows`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `j:num`] PL_I16_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `j:num`; `m:int64->byte`; `rows:(num#num#num)list`; `t:tisa_state`]
    PL_ITAB_STATE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] INTERN16_TISA_RUN_KEPT) THEN
  ASM_REWRITE_TAC[intern16_kept] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; `j:num`] PL_I16_AFTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[pl_itab] THEN EXISTS_TAC `u:tisa_state` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 * i < 2 * LENGTH(rows:(num#num#num)list) /\ 2 * i + 1 < 2 * LENGTH rows`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]]);;

let PL_I16_KEPT_TAC j rel_th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_kept; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`m:int64->byte`; `used:int64`; `cw:num->num`; `ctx:hupdate list`; `nms:string list`;
    `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`;
    `ths:(num#num)list`; `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`;
    `stk:num list`; `t:tisa_state`; `k:num`; `u:tisa_state`] THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [plan_rel]) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; j;
                if j = `0` then `tys:(num#num#num)list` else `dbs:(num#num#num)list`] PL_I16_STEP) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `~(k = 1)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; j;
                if j = `0` then `tys:(num#num#num)list` else `dbs:(num#num#num)list`] PL_I16_STEP_KEPT) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC rel_th THEN EXISTS_TAC `m:int64->byte` THEN
  EXISTS_TAC (if j = `0` then `tys:(num#num#num)list` else `dbs:(num#num#num)list`) THEN
  ASM_REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME] THEN REWRITE_TAC[GSYM drv_after] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC THEN NO_TAC) THEN
  X_GEN_TAC `x:int64` THEN STRIP_TAC THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
  MAP_EVERY EXISTS_TAC [`intern16`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                        `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[INTERN16_LEAF_WF; REWRITE_RULE[INTERN16_DECLS] INTERN16_REGION_KINDS; INTERN16_DECLS] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    X_GEN_TAC `r:num` THEN REWRITE_TAC[ARITH_RULE `r < 3 <=> r = 0 \/ r = 1 \/ r = 2`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]];;

let PL_KEPT_INTERN_TY = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 0 = intern16 /\ val(EL 0 st) = 0 /\ val(EL 1 st) = 0 /\ val(EL 2 st) = 2 /\ val(EL 3 st) = 4 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_kept (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_I16_KEPT_TAC `0` PL_REL_ITAB_TY);;

let PL_KEPT_INTERN_DB = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 0 = intern16 /\ val(EL 0 st) = 0 /\ val(EL 1 st) = 6 /\ val(EL 2 st) = 8 /\ val(EL 3 st) = 10 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_kept (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_I16_KEPT_TAC `6` PL_REL_ITAB_DB);;

(* append_row to the theorem rows that does not fire: the rows and their   *)
(* count as they were.                                                       *)
let PL_REL_APPEND_TH_KEPT = prove
 (`!bw ctl nctl budget cfr st m used t k u cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok append_row t /\
     tisa_run append_row t = TStop k u /\
     val(EL 1 st) = 18 /\ val(EL 2 st) = 20 /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st) /\
     val(pl_w u 1 0) = LENGTH ths /\
     (!j. j < 2 * LENGTH ths ==> pl_w u 0 j = pl_w t 0 j)
     ==> plan_rel bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),
            (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [plan_rel]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  SUBGOAL_THEN `!x. ~drv_stack cfr x /\ ~drv_in x (bw 18) (val(bw 19)) /\ ~drv_in x (bw 20) (val(bw 21)) /\
                    ~drv_in x (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8
                    ==> drv_after ctl st u x = (m:int64->byte) x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`append_row`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                          `used:int64`; `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[APPEND_ROW_LEAF_WF; APPEND_ROW_DECLS; tisa_rw; LENGTH] THEN
    X_GEN_TAC `r:num` THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `r < 2 <=> r = 0 \/ r = 1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!j x. MEM j pl_slots /\ ~(j = 18) /\ ~(j = 20) /\ drv_in x (bw j) (val(bw(j + 1)))
                     ==> drv_after ctl st u x = (m:int64->byte) x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_after`)) (concl th))) THEN
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`;
                  `val(EL 17 (st:int64 list))`; `x:int64`] PL_SLOT_ADDR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`; `18`; `x:int64`]
        PL_SLOT_APART_IN) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`; `20`; `x:int64`]
        PL_SLOT_APART_IN) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]];
    ALL_TAC]) THEN
  (MAP_EVERY PL_AGREE_SLOT_TAC [`0`; `2`; `4`; `6`; `8`; `10`; `12`; `14`; `16`; `22`; `40`] THEN
  PL_SLOT_BOUNDS_TAC THEN
  REWRITE_TAC[plan_rel] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC) THENL
   [(REWRITE_TAC[pl_set] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);
    (MATCH_MP_TAC PL_CWORDS_SET THEN EXISTS_TAC `m:int64->byte` THEN
  ASM_REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME] THEN REWRITE_TAC[GSYM drv_after] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_stack`)) (concl th) && can (find_term ((=) `drv_after`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_CTL_ADDR THEN MAP_EVERY EXISTS_TAC [`bw:num->int64`; `ctl:int64`; `nctl:num`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `18`] PL_LAYOUT_SLOT) THEN
    REWRITE_TAC[PL_SLOT_MEMS] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[drv_apart] THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_in]) THEN REWRITE_TAC[drv_in] THEN
    ASM_ARITH_TAC;
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `20`] PL_LAYOUT_SLOT) THEN
    REWRITE_TAC[PL_SLOT_MEMS] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[drv_apart] THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_in]) THEN REWRITE_TAC[drv_in] THEN
    ASM_ARITH_TAC]);
    (PL_ITAB_KEEP_TAC);
    (PL_ITAB_KEEP_TAC);
    (MATCH_MP_TAC PL_RTAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_SIMP_TAC[]);
    (MATCH_MP_TAC PL_MARKS_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_SIMP_TAC[]);
    (FIRST_ASSUM(MP_TAC o check (fun th -> is_const_app "pl_rtab" (concl th) &&
        can (find_term ((=) `pl_f2`)) (concl th))) THEN
  REWRITE_TAC[pl_rtab] THEN STRIP_TAC THEN REPEAT CONJ_TAC) THENL
     [(PL_AFTER_TAC `1` `20` `0` THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);
      (ASM_REWRITE_TAC[]);
      (REPEAT STRIP_TAC THEN
  PL_AFTER_TAC `0` `18` `2 * i + w` THEN ANTS_TAC THENL
   [MP_TAC(SPECL [`2`; `i:num`; `w:num`; `LENGTH(ths:(num#num)list)`] PL_ROW_WORD_BOUND) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `2 * i + w < 2 * LENGTH(ths:(num#num)list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `0`; `18`; `2 * i + w`] PL_CHILD_W) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS] THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`2`; `i:num`; `w:num`; `LENGTH(ths:(num#num)list)`] PL_ROW_WORD_BOUND) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  ASM_SIMP_TAC[])];
    (MATCH_MP_TAC PL_MARKS_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_SIMP_TAC[]);
    (MATCH_MP_TAC PL_STK_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_SIMP_TAC[])]);;

(* append_row on the theorem rows, width 2 in control word 2. *)
let PL_KEPT_APPEND_TH = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 6 = append_row /\ val(EL 0 st) = 6 /\ val(EL 1 st) = 18 /\ val(EL 2 st) = 20 /\
     val(EL 12 st) = 2 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_kept (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_kept; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`m:int64->byte`; `used:int64`; `cw:num->num`; `ctx:hupdate list`; `nms:string list`;
    `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`;
    `ths:(num#num)list`; `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`;
    `stk:num list`; `t:tisa_state`; `k:num`; `u:tisa_state`] THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [plan_rel]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(cw:num->num) 2 = 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `cw:num->num`)) (concl th) &&
      is_imp(snd(dest_forall(concl th))) && is_eq(rand(snd(dest_forall(concl th)))) &&
      rhs(rand(snd(dest_forall(concl th)))) = fst(dest_forall(concl th)))) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `0`; `18`] PL_CHILD_REGION) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `20`] PL_CHILD_REGION) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `20`; `0`] PL_CHILD_W) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if is_const_app "pl_rtab" (concl th) && can (find_term ((=) `pl_f2`)) (concl th)
     then STRIP_ASSUME_TAC(REWRITE_RULE[pl_rtab] th) else failwith "") THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (MP_TAC PL_APPEND_ROW_SPEC THEN REWRITE_TAC[pl_append_row_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o CONJUNCT2 o CONJUNCT2)
                             (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `8 * 2 * (LENGTH (ths:(num#num)list) + 1) <= val(bw 19:int64)` THEN ASM_REWRITE_TAC[]) THENL
   [(* the condition held: the leaf fired, against the premise *)
    DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k = 1`)) THEN ASM_MESON_TAC[];
    DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    MATCH_MP_TAC PL_REL_APPEND_TH_KEPT THEN
    MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC THEN NO_TAC) THEN
    TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `pl_w u 0`)) (concl th))) THEN ASM_ARITH_TAC]);;

(* The read-only leaves of the host's table. *)
let PL_KEPT_RO_LEAF_TAC wf rw =
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC PL_KEPT_RO THEN
  ASM_REWRITE_TAC[wf; rw] THEN FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC;;

let PL_KEPT_PACK = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 1 = pack /\ val(EL 0 st) = 1 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_kept (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_KEPT_RO_LEAF_TAC PACK_LEAF_WF PACK_RW);;

let PL_KEPT_UNPACK = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 2 = unpack /\ val(EL 0 st) = 2 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_kept (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_KEPT_RO_LEAF_TAC UNPACK_LEAF_WF UNPACK_RW);;

let PL_KEPT_EQW = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 3 = eqw /\ val(EL 0 st) = 3 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_kept (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_KEPT_RO_LEAF_TAC EQW_LEAF_WF EQW_RW);;

let PL_KEPT_ROW_WORD = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 4 = row_word /\ val(EL 0 st) = 4 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_kept (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_KEPT_RO_LEAF_TAC ROW_WORD_LEAF_WF ROW_WORD_RW);;

let PL_KEPT_LIVE = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 5 = live /\ val(EL 0 st) = 5 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_kept (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_KEPT_RO_LEAF_TAC LIVE_LEAF_WF LIVE_RW);;

(* ------------------------------------------------------------------------- *)
(* Plans that write no table: the reader's steps (the decode plan, the     *)
(* header plan, a handler's prefix) and the count's increment. Their run,  *)
(* whatever its outcome, keeps plan_rel at the same tables, the control    *)
(* words read back from memory.                                              *)
(* ------------------------------------------------------------------------- *)

(* plan_rel of a memory that agrees on every slot plan_rel reads and on     *)
(* control words 0..6, at the control words that memory holds.              *)
let PL_REL_REREAD = prove
 (`!bw ctl nctl cfr m m' cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     (!j a. MEM j pl_slots /\ drv_in a (bw j) (val(bw(j + 1))) ==> m' a = m a) /\
     (!k. k <= 6 ==> pl_mw m' ctl k = pl_mw m ctl k)
     ==> plan_rel bw ctl nctl cfr m'
           ((\k. if k < nctl then pl_mw m' ctl k else cw k),
            (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[plan_rel] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY PL_SLOT_FACTS_TAC [`12`; `14`; `16`; `18`; `20`; `22`; `40`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [pl_cwords] o check (fun th -> is_const_app "pl_cwords" (concl th))) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `k < nctl` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k < nctl` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
    REWRITE_TAC[pl_cwords] THEN BETA_TAC THEN SIMP_TAC[];
    MATCH_MP_TAC PL_ITAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_ITAB_SLOTS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_ITAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_ITAB_SLOTS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_RTAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MARKS_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_RTAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MARKS_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_STK_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[]]);;

(* The steps of P write no slot of plan_rel: each step's read-write regions *)
(* are the reader's (the input at slot 54, the state at slot 58), its      *)
(* payload word above 6.                                                     *)
let rd_only_ok = new_definition
 `rd_only_ok (progs:num->tisa_prog) nctl (P:(int64 list)list) <=>
    !st. MEM st P ==> tisa_leaf_wf (progs (val(EL 0 st))) /\ 6 < val(EL 17 st) /\ val(EL 17 st) < nctl /\
                      (!r. tisa_rw (tisa_decls (progs (val(EL 0 st)))) r
                           ==> val(EL (1 + r) st) = 54 \/ val(EL (1 + r) st) = 58)`;;

let RD_ONLY_KEEPS_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_only_ok] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout] o
              check (fun th -> is_const_app "pl_layout" (concl th))) THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `P:(int64 list)list`; `i:num`; `m:int64->byte`; `used:int64`;
                `res:int64#num#(int64->byte)#int64`] DRV_SEM_KEEPS) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC;;

(* An address the reader's regions miss, given a step's region r is one of  *)
(* them.                                                                     *)
let RD_ONLY_REGION_TAC =
  REWRITE_TAC[drv_base; drv_len] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th))) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];;

let RD_ONLY_SLOTS_KEPT = prove
 (`!progs bw ctl nctl budget cfr P i m used res j a.
     drv_sem progs bw ctl budget cfr P i m used res /\
     pl_layout bw ctl nctl cfr /\ rd_layout bw ctl nctl cfr /\ rd_only_ok progs nctl P /\
     MEM j pl_slots /\ drv_in a (bw j) (val(bw(j + 1)))
     ==> FST(SND(SND res)) a = m a`,
  RD_ONLY_KEEPS_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`; `a:int64`] RD_SLOT_NOT_RD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_SLOT_NOT_STACK THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`; `ctl:int64`; `nctl:num`; `j:num`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`st:int64 list`; `r:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `val(EL (1 + r) (st:int64 list)) = 54 \/ val(EL (1 + r) st) = 58` MP_TAC THENL
     [ASM_MESON_TAC[]; DISCH_TAC] THEN
    RD_ONLY_REGION_TAC;
    X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`;
                  `val(EL 17 (st:int64 list))`; `a:int64`] PL_SLOT_ADDR) THEN
    ASM_SIMP_TAC[]]);;

let RD_ONLY_CW_KEPT = prove
 (`!progs bw ctl nctl budget cfr P i m used res j.
     drv_sem progs bw ctl budget cfr P i m used res /\
     pl_layout bw ctl nctl cfr /\ rd_layout bw ctl nctl cfr /\ rd_only_ok progs nctl P /\
     j < nctl /\ (!st. MEM st P ==> ~(val(EL 17 st) = j))
     ==> pl_mw (FST(SND(SND res))) ctl j = pl_mw m ctl j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[pl_mw] THEN AP_TERM_TAC THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout] o
              check (fun th -> is_const_app "pl_layout" (concl th))) THEN
  SUBGOAL_THEN `val(word_add (word_add ctl (word(8 * j))) (word q):int64) = val ctl + 8 * j + q` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_ADDR_VAL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `drv_in (word_add (word_add ctl (word(8 * j))) (word q)) ctl (8 * nctl)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`;
                `word_add (word_add ctl (word(8 * j))) (word q):int64`] RD_CTL_NOT_RD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `rd_only_ok progs nctl P` THEN REWRITE_TAC[rd_only_ok] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `P:(int64 list)list`; `i:num`; `m:int64->byte`; `used:int64`;
                `res:int64#num#(int64->byte)#int64`] DRV_SEM_KEEPS) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_CTL_ADDR THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`; `ctl:int64`; `nctl:num`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`st:int64 list`; `r:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `val(EL (1 + r) (st:int64 list)) = 54 \/ val(EL (1 + r) st) = 58` MP_TAC THENL
     [ASM_MESON_TAC[]; DISCH_TAC] THEN
    RD_ONLY_REGION_TAC;
    X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(EL 17 (st:int64 list)) < nctl /\ ~(val(EL 17 st) = j)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`ctl:int64`; `8 * val(EL 17 (st:int64 list))`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ASM_REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC]);;

(* A plan that writes no table, from any outcome: plan_rel at the same      *)
(* tables, the control words those in memory.                                *)
let RD_ONLY_KEEPS_PL = prove
 (`!progs bw ctl nctl budget cfr P i m used res cw ns stk inp c.
     drv_sem progs bw ctl budget cfr P i m used res /\ rd_only_ok progs nctl P /\
     plan_rel bw ctl nctl cfr m (cw,ns,stk) /\ rd_rel bw ctl nctl cfr m inp c
     ==> plan_rel bw ctl nctl cfr (FST(SND(SND res)))
           ((\k. if k < nctl then pl_mw (FST(SND(SND res))) ctl k else cw k),ns,stk)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`ns:nstate`,`ns:nstate`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC pl_ns_vars THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_REL_LAYOUT) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [rd_rel] o
              check (fun th -> is_const_app "rd_rel" (concl th))) THEN
  MATCH_MP_TAC PL_REL_REREAD THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RD_ONLY_SLOTS_KEPT THEN
    MAP_EVERY EXISTS_TAC [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                          `cfr:int64`; `P:(int64 list)list`; `i:num`; `used:int64`; `j:num`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC RD_ONLY_CW_KEPT THEN
    MAP_EVERY EXISTS_TAC [`progs:num->tisa_prog`; `bw:num->int64`; `nctl:num`; `budget:int64`;
                          `cfr:int64`; `P:(int64 list)list`; `i:num`; `used:int64`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [plan_rel] o
                  check (fun th -> is_const_app "plan_rel" (concl th))) THEN ASM_ARITH_TAC;
      X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
      UNDISCH_TAC `rd_only_ok progs nctl P` THEN REWRITE_TAC[rd_only_ok] THEN
      DISCH_THEN(MP_TAC o SPEC `st:int64 list`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_ARITH_TAC]]);;

(* Every theorem this file states, for the audits. *)
let plans_every_theorems =
 ["PL_APPEND_SELF", PL_APPEND_SELF;
  "PL_APPEND_TRANS", PL_APPEND_TRANS;
  "PL_GROWS_REFL", PL_GROWS_REFL;
  "PL_GROWS_TRANS", PL_GROWS_TRANS;
  "PL_INTERN_GROWS", PL_INTERN_GROWS;
  "PL_INTERN_UNFIRED", PL_INTERN_UNFIRED;
  "PL_UNION_GROWS", PL_UNION_GROWS;
  "PL_UNION_UNFIRED", PL_UNION_UNFIRED;
  "PL_APPEND_TH_UNFIRED", PL_APPEND_TH_UNFIRED;
  "PL_LEAF_UNFIRED", PL_LEAF_UNFIRED;
  "PL_LEAF_GROWS", PL_LEAF_GROWS;
  "PL_RUN_GROWS", PL_RUN_GROWS;
  "NAT_SIM_THMS", NAT_SIM_THMS;
  "PL_INV_THMS", PL_INV_THMS;
  "PL_GROWS_THMS", PL_GROWS_THMS;
  "PL_DRV_BRIDGE_ALL", PL_DRV_BRIDGE_ALL;
  "PL_KEPT_RO", PL_KEPT_RO;
  "PL_I16_STEP_KEPT", PL_I16_STEP_KEPT;
  "PL_KEPT_INTERN_TY", PL_KEPT_INTERN_TY;
  "PL_KEPT_INTERN_DB", PL_KEPT_INTERN_DB;
  "PL_REL_APPEND_TH_KEPT", PL_REL_APPEND_TH_KEPT;
  "PL_KEPT_APPEND_TH", PL_KEPT_APPEND_TH;
  "PL_KEPT_PACK", PL_KEPT_PACK;
  "PL_KEPT_UNPACK", PL_KEPT_UNPACK;
  "PL_KEPT_EQW", PL_KEPT_EQW;
  "PL_KEPT_ROW_WORD", PL_KEPT_ROW_WORD;
  "PL_KEPT_LIVE", PL_KEPT_LIVE;
  "PL_REL_REREAD", PL_REL_REREAD;
  "RD_ONLY_SLOTS_KEPT", RD_ONLY_SLOTS_KEPT;
  "RD_ONLY_CW_KEPT", RD_ONLY_CW_KEPT;
  "RD_ONLY_KEEPS_PL", RD_ONLY_KEEPS_PL];;
