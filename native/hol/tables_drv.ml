(* ========================================================================= *)
(* Plans over the interface through the driver: drv_sem runs a plan as     *)
(* tab_run does, for any relation prel between the driver's memory and the *)
(* abstract state under which every step's leaf implements its meaning     *)
(* (tab_impl), from a state the plan is safe from (TAB_DRV_BRIDGE).         *)
(* tab_impl speaks of every outcome: from related states at which the     *)
(* leaf is enabled, the leaf's run is an abstract step with its outcome    *)
(* code and payload, its receipt within the allowance, and the memory the  *)
(* driver keeps after it related to the abstract state after it, with the  *)
(* payload in the step's word. A step that does not fire keeps the tables  *)
(* in every leaf's meaning, so the final memory of every run, whatever its *)
(* outcome, is related to the final abstract state.                        *)
(*                                                                           *)
(* Loaded after tables.ml and plans_drv.ml.                                  *)
(* ========================================================================= *)

let tab_impl = new_definition
 `tab_impl (prel:(int64->byte)->(num->num)#S#num list->bool)
           (tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
               (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) (inp:num list) progs bw ctl budget cfr (st:int64 list) <=>
    !m used s t k u.
      prel m s /\ ~(val budget < val used) /\ (?k0 p0 s0. tab_leaf tb inp st s k0 p0 s0) /\
      drv_child bw ctl budget cfr st m used t /\
      tisa_entry_ok (progs (val(EL 0 st))) t /\ tisa_run (progs (val(EL 0 st))) t = TStop k u
      ==> ?k' s'. tab_leaf tb inp st s k' (val(tisa_fword u 19)) s' /\ k' < 8 /\
                  tisa_fword u 18 = word k' /\ ~(val budget < val(tisa_fword u 21)) /\
                  prel (drv_after ctl st u) (pl_set (FST s) (val(EL 17 st)) (val(tisa_fword u 19)),s',SND(SND s))`;;

let TAB_DRV_BRIDGE = prove
 (`!prel tb inp progs bw ctl budget cfr sts i m used res (s:(num->num)#S#num list).
     (!st. MEM st sts ==> tab_impl prel tb inp progs bw ctl budget cfr st) /\
     tab_safe tb inp sts s /\
     drv_sem progs bw ctl budget cfr sts i m used res /\ prel m s /\ ~(val budget < val used)
     ==> ?k j s'. tab_run tb inp sts i s (k,j,s') /\ k < 8 /\ FST res = word k /\ FST(SND res) = j /\
                 prel (FST(SND(SND res))) s' /\ ~(val budget < val(SND(SND(SND res))))`,
  REPLICATE_TAC 8 GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[drv_sem; MEM] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`1`; `i:num`; `s:(num->num)#S#num list`] THEN ASM_REWRITE_TAC[tab_run] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[MEM; tab_safe] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  ASM_REWRITE_TAC[drv_sem] THEN
  DISCH_THEN(X_CHOOSE_THEN `tc:tisa_state` (X_CHOOSE_THEN `kc:num`
    (X_CHOOSE_THEN `u:tisa_state` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[tab_impl] o SPEC `h:int64 list` o
              check (fun th -> is_forall(concl th) && can (find_term (is_const_app "tab_impl")) (concl th))) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:int64->byte`; `used:int64`; `s:(num->num)#S#num list`; `tc:tisa_state`;
                             `kc:num`; `u:tisa_state`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `s1:S` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `tisa_fword u 18 = word 1 <=> k1 = 1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_WORD_SMALL_EQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k1 = 1` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k1 = 1`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`; `drv_after ctl h u`; `tisa_fword u 21`;
                    `res:int64#num#(int64->byte)#int64`;
                    `(pl_set (FST(s:(num->num)#S#num list)) (val(EL 17 (h:int64 list))) (val(tisa_fword u 19)),
                      (s1:S),SND(SND(s:(num->num)#S#num list)))`] o
                  check (fun th -> is_forall(concl th) && can (find_term (is_const_app "drv_sem")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                         can (find_term (is_const_app "tab_impl")) (concl th))) THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                         can (find_term (is_const_app "tab_safe")) (concl th))) THEN
        EXISTS_TAC `1` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `s':(num->num)#S#num list`
      STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `j:num`; `s':(num->num)#S#num list`] THEN ASM_REWRITE_TAC[tab_run] THEN
    MAP_EVERY EXISTS_TAC [`1`; `val(tisa_fword u 19)`; `s1:S`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`k1:num`; `i:num`;
                          `(pl_set (FST(s:(num->num)#S#num list)) (val(EL 17 (h:int64 list))) (val(tisa_fword u 19)),
                            (s1:S),SND(SND(s:(num->num)#S#num list)))`] THEN
    ASM_REWRITE_TAC[tab_run] THEN
    MAP_EVERY EXISTS_TAC [`k1:num`; `val(tisa_fword u 19)`; `s1:S`] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Safety: a step whose leaf is enabled at every state; plans of such steps. *)
(* ------------------------------------------------------------------------- *)

let tab_total = new_definition
 `tab_total (tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
                (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) (inp:num list) (st:int64 list) <=>
    !s. ?k pay s'. tab_leaf tb inp st s k pay s'`;;

let TAB_SAFE_TOTAL = prove
 (`!(tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
        (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) inp sts s.
     ALL (tab_total tb inp) sts ==> tab_safe tb inp sts s`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[tab_safe; ALL; tab_total] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* Every leaf but append_row (6), put_word (9) and intern_name (23) is      *)
(* enabled at every state, for every interface and input.                   *)
let TAB_TOTAL_LEAF = prove
 (`!(tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
        (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) inp st.
     (val(EL 0 st) = 0 \/ val(EL 0 st) = 1 \/ val(EL 0 st) = 2 \/ val(EL 0 st) = 3 \/
      val(EL 0 st) = 4 \/ val(EL 0 st) = 5 \/ val(EL 0 st) = 20 \/ val(EL 0 st) = 22)
     ==> tab_total tb inp st`,
  REWRITE_TAC[FORALL_PAIR_THM; tab_total] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`cw:num->num`; `s:S`; `stk:num list`] THEN
  REWRITE_TAC[tab_leaf; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[tab_intern; pl_pack; pl_unpack; pl_eqw; pl_roww; tab_live; tab_polmax; tab_fnv] THEN
  FIRST [MAP_EVERY EXISTS_TAC [`2`; `0`; `s:S`] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN NO_TAC;
         TRY COND_CASES_TAC THEN MESON_TAC[]]);;

(* Every theorem this file states, for the audits. *)
let tables_drv_theorems =
 ["TAB_DRV_BRIDGE", TAB_DRV_BRIDGE; "TAB_SAFE_TOTAL", TAB_SAFE_TOTAL; "TAB_TOTAL_LEAF", TAB_TOTAL_LEAF];;
