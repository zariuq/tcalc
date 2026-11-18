(* ========================================================================= *)
(* Every run over the general relation: whatever a run's outcome, the       *)
(* memory left is related to a state that grows the start's tables or the  *)
(* state a record's native step reached; the theorem rows are derivable.   *)
(* A step that does not fire keeps the state (TAB_LEAF_UNFIRED); one that  *)
(* fires keeps it, appends a row or writes a word (TAB_LEAF_FIRED); a run  *)
(* of HOL's tables that does not fire grows them by appending and keeps the *)
(* theorem rows and marks when only its last step may write them           *)
(* (TAB_RUN_HOL_GROWS); a plan that                                         *)
(* writes only the reader's state keeps the tables whatever its outcome    *)
(* (TAB_RD_ONLY_KEEPS).                                                      *)
(*                                                                           *)
(* Loaded after rec_induction_tab.ml and rec_every.ml.                       *)
(* ========================================================================= *)

(* A step that does not fire leaves the state as it was. *)
let TAB_LEAF_UNFIRED = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput inp st cw s stk k pay s'.
     tab_leaf (trow,tn,twd,tdrop,tapp,tput) inp st (cw,s,stk) k pay s' /\ ~(k = 1) ==> s' = s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_leaf; tab_intern; tab_append; tab_name; tab_putw; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* A step that fires keeps the state, appends a row to the table it names or *)
(* writes a word of it.                                                      *)
let TAB_LEAF_FIRED = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput inp st cw s stk pay s'.
     tab_leaf (trow,tn,twd,tdrop,tapp,tput) inp st (cw,s,stk) 1 pay s'
     ==> s' = s \/
         (?j c r. tapp j c s r s' /\
                  ((val(EL 0 st) = 0 \/ val(EL 0 st) = 6) /\ j = val(EL 1 st) \/
                   val(EL 0 st) = 23 /\ j = val(EL 2 st))) \/
         (?j c i w v. tput j c s i w v s' /\ val(EL 0 st) = 9 /\ j = val(EL 1 st))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_leaf; tab_intern; tab_append; tab_name; tab_putw; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* HOL's tables: an append to any table but the theorems' grows the state;  *)
(* a run whose only possible theorem append is its last step, and which     *)
(* does not fire, grows the state and keeps the stack.                       *)
(* ------------------------------------------------------------------------- *)

let HOL_TAPP_GROWS = prove
 (`!j c ns r ns'. hol_tapp j c ns r ns' /\ ~(j = 18) ==> pl_grows ns ns'`,
  REWRITE_TAC[FORALL_PAIR_THM; hol_tapp; pl_grows; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PL_APPEND_SELF]);;

(* Only a plan's last step may write the theorem table (slot 18) or write a *)
(* word (put_word: a drop).                                                  *)
let tab_th_last = define
 `(tab_th_last [] <=> T) /\
  (tab_th_last (CONS (st:int64 list) sts) <=>
     (~(sts = []) ==> ~((val(EL 0 st) = 0 \/ val(EL 0 st) = 6) /\ val(EL 1 st) = 18) /\
                      ~(val(EL 0 st) = 23 /\ val(EL 2 st) = 18) /\ ~(val(EL 0 st) = 9)) /\
     tab_th_last sts)`;;

let TAB_RUN_HOL_GROWS = prove
 (`!P inp i cw ns stk k j cw' ns' stk'.
     tab_run hol_tables inp P i (cw,ns,stk) (k,j,(cw',ns',stk')) /\ tab_th_last P /\ ~(k = 1)
     ==> pl_grows ns ns' /\ stk' = stk`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[tab_run; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_run; tab_th_last; FST; SND] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k0:num` (X_CHOOSE_THEN `pay:num` (X_CHOOSE_THEN `s1:nstate`
    STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `k0 = 1` THENL
   [ALL_TAC;
    (* the step did not fire: the state as it was *)
    SUBGOAL_THEN `s1:nstate = ns` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC(ISPECL [`hol_trow`; `hol_tn`; `hol_twd`; `hol_tdrop`; `hol_tapp`; `hol_tput`] TAB_LEAF_UNFIRED) THEN
      MAP_EVERY EXISTS_TAC [`inp:num list`; `h:int64 list`; `cw:num->num`; `stk:num list`; `k0:num`; `pay:num`] THEN
      ASM_REWRITE_TAC[GSYM hol_tables];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    MESON_TAC[PL_GROWS_REFL]] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `t:(int64 list)list = []` THENL
   [(* the last step fired: the run fired *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "tab_run" (concl th))) THEN
    REWRITE_TAC[tab_run; PAIR_EQ] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* a step that is not the last fired: an append to a table but the theorems' *)
  SUBGOAL_THEN `pl_grows ns (s1:nstate)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN
    MP_TAC(ISPECL [`hol_trow`; `hol_tn`; `hol_twd`; `hol_tdrop`; `hol_tapp`; `hol_tput`; `inp:num list`; `h:int64 list`;
                   `cw:num->num`; `ns:nstate`; `stk:num list`; `pay:num`; `s1:nstate`] TAB_LEAF_FIRED) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_const_app "tab_leaf" (concl th) then
        ACCEPT_TAC(REWRITE_RULE[hol_tables; ASSUME `k0 = 1`] th) else failwith "");
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th; PL_GROWS_REFL]) MP_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_neg(lhand(concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    DISCH_THEN(DISJ_CASES_THEN2
      (X_CHOOSE_THEN `jt:num` (X_CHOOSE_THEN `ct:num` (X_CHOOSE_THEN `rt:num list` STRIP_ASSUME_TAC)))
      (fun th -> STRIP_ASSUME_TAC th THEN ASM_MESON_TAC[])) THEN
    MATCH_MP_TAC HOL_TAPP_GROWS THEN MAP_EVERY EXISTS_TAC [`jt:num`; `ct:num`; `rt:num list`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`inp:num list`; `i + 1`; `pl_set cw (val(EL 17 (h:int64 list))) pay`;
                                `s1:nstate`; `stk:num list`; `k:num`; `j:num`; `cw':num->num`; `ns':nstate`;
                                `stk':num list`] o
    check (fun th -> is_forall(concl th) && can (find_term (is_const_app "tab_run")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PL_GROWS_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Plans that write only the reader's state (slot 58) and control words      *)
(* keep the tables, whatever their outcome.                                  *)
(* ------------------------------------------------------------------------- *)

let rd_only58_ok = new_definition
 `rd_only58_ok (progs:num->tisa_prog) nctl (P:(int64 list)list) <=>
    !st. MEM st P ==> tisa_leaf_wf (progs (val(EL 0 st))) /\ 6 < val(EL 17 st) /\ val(EL 17 st) < nctl /\
                      (!r. tisa_rw (tisa_decls (progs (val(EL 0 st)))) r ==> val(EL (1 + r) st) = 58)`;;

let TAB_RD_ONLY_KEEPS = prove
 (`!(tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool))
    L inp progs bw ctl nctl budget cfr P i m used res cw s stk.
     rd_only58_ok progs nctl P /\ rd_layout bw ctl nctl cfr /\ rd_tab_apart L bw /\
     drv_sem progs bw ctl budget cfr P i m used res /\ tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk)
     ==> ?cw'. tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND res))) (cw',s,stk) /\
               (!j. (!st. MEM st P ==> ~(val(EL 17 st) = j)) ==> cw' j = cw j)`,
  REPLICATE_TAC 9 GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[drv_sem] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `cw:num->num` THEN ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_sem] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `cw:num->num` THEN ASM_REWRITE_TAC[FST; SND]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:tisa_state` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `h:int64 list` o REWRITE_RULE[rd_only58_ok; MEM] o
              check (is_const_app "rd_only58_ok" o concl)) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
                 `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                 `cfr:int64`; `progs(val(EL 0 (h:int64 list))):tisa_prog`; `h:int64 list`; `m:int64->byte`;
                 `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; `cw:num->num`; `s:S`; `stk:num list`]
                TAB_RD_STEP_KEEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`; `drv_after ctl h u`; `tisa_fword u 21`;
                                  `res:int64#num#(int64->byte)#int64`;
                                  `pl_set cw (val(EL 17 (h:int64 list))) (val(tisa_fword u 19))`; `s:S`;
                                  `stk:num list`] o
      check (fun th -> is_forall(concl th) && can (find_term (is_const_app "drv_sem")) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (is_const_app "rd_only58_ok" o concl)) THEN
      REWRITE_TAC[rd_only58_ok; MEM] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `cw2:num->num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `cw2:num->num` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[MEM] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `cw2:num->num`)) (concl th)
                            then MP_TAC(SPEC `j:num` th) else failwith "") THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[pl_set] THEN COND_CASES_TAC THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN
    EXISTS_TAC `pl_set cw (val(EL 17 (h:int64 list))) (val(tisa_fword u 19))` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[MEM] THEN DISCH_TAC THEN REWRITE_TAC[pl_set] THEN COND_CASES_TAC THEN ASM_MESON_TAC[]]);;

(* The reader's plans write only its state and control words, by computation *)
(* on their data under the host's leaf table.                               *)
let RD_ONLY58_TAC_WITH facts plan_defs =
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_progs_ok] THEN STRIP_TAC THEN
  REWRITE_TAC([rd_only58_ok; MEM; MEM_APPEND] @ plan_defs) THEN REWRITE_TAC[GSYM DISJ_ASSOC] THEN
  X_GEN_TAC `st:int64 list` THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC)) THEN TRY(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC facts THEN
  REWRITE_TAC[FORALL_UNWIND_THM2] THEN CONV_TAC STEP_EL_CONV2 THEN ASM_ARITH_TAC;;

let RD58_LEAF_FACTS = RD_HDR_LEAF_FACTS @ [SKIP_LEAF_WF; SKIP_RW];;

let RD_ONLY58_DD = prove
 (`!progs nctl. rd_progs_ok progs /\ 21 < nctl ==> rd_only58_ok progs nctl pl_plan_dd`,
  RD_ONLY58_TAC_WITH RD58_LEAF_FACTS [pl_plan_dd]);;

let RD_ONLY58_PREFIX_OP0 = prove
 (`!progs nctl. progs 3 = eqw /\ rd_progs_ok progs /\ 24 < nctl ==> rd_only58_ok progs nctl pl_prefix_op0`,
  RD_ONLY58_TAC_WITH RD58_LEAF_FACTS [pl_prefix_op0]);;

let RD_ONLY58_PREFIX_OP01 = prove
 (`!progs nctl. progs 3 = eqw /\ rd_progs_ok progs /\ 24 < nctl ==> rd_only58_ok progs nctl pl_prefix_op01`,
  RD_ONLY58_TAC_WITH RD58_LEAF_FACTS [pl_prefix_op01; pl_prefix_op0]);;

let RD_ONLY58_PREFIX_NAME = prove
 (`!progs nctl. progs 3 = eqw /\ rd_progs_ok progs /\ progs 28 = skip /\ 24 < nctl
                ==> rd_only58_ok progs nctl pl_prefix_name`,
  RD_ONLY58_TAC_WITH RD58_LEAF_FACTS [pl_prefix_name]);;

let RD_ONLY58_INC_CNT = prove
 (`!progs nctl. rd_progs_ok progs /\ 17 < nctl ==> rd_only58_ok progs nctl pl_inc_cnt`,
  RD_ONLY58_TAC_WITH RD58_LEAF_FACTS [pl_inc_cnt]);;

let RD_ONLY58_END = prove
 (`!progs nctl. progs 3 = eqw /\ progs 22 = fnv /\ rd_progs_ok progs /\ progs 29 = le8_next /\
                progs 30 = at_end /\ 30 < nctl
                ==> rd_only58_ok progs nctl pl_plan_end`,
  RD_ONLY58_TAC_WITH RD58_LEAF_FACTS [pl_plan_end; pl_end_a; pl_end_b; pl_end_c; pl_end_d]);;

let RD_ONLY58_HDR = prove
 (`!progs nctl. progs 3 = eqw /\ rd_progs_ok progs /\ progs 31 = const_next /\ progs 20 = pol_max /\
                27 < nctl
                ==> rd_only58_ok progs nctl pl_plan_hdr`,
  RD_ONLY58_TAC_WITH RD58_LEAF_FACTS
    [pl_plan_hdr;pl_hdr_b;pl_hdr_a;pl_hdr_v1;pl_hdr_v0;pl_hdr_p;pl_hdr_commit;pl_hdr_g]);;

(* ------------------------------------------------------------------------- *)
(* A kind's handler over HOL's tables, every run: whatever the outcome, the  *)
(* memory left is related to a state that grows the start's tables, or      *)
(* grows the state the record's native step reached (its plan FIRED, the     *)
(* count's increment then whatever it did).                                  *)
(* ------------------------------------------------------------------------- *)

let TAB_HANDLER_EVERY_HOL = prove
 (`!R pfx (D:num list->A->bool) W Ln P Q G progs bw ctl nctl budget cfr m used res cw ns stk inp c.
     tab_prefix_rd hol_tables hol_layout R pfx D W Ln /\
     (!cw c ns stk v. hol_inv (cw,ns,stk) ==> hol_inv (W cw c v,ns,stk)) /\
     rd_only58_ok progs nctl pfx /\ rd_only58_ok progs nctl pl_inc_cnt /\
     tab_lifts hol_tables hol_layout hol_progs P Q G hol_inv /\
     (!st. MEM st P ==> tab_impl (tab_rel hol_tables hol_layout inp bw ctl nctl cfr) hol_tables inp
                                  progs bw ctl budget cfr st) /\
     (!s. hol_inv s ==> tab_safe hol_tables inp P s) /\ tab_th_last P /\
     tab_rd_plan_ok hol_layout progs nctl P /\
     (!st. MEM st P ==> ~(17 <= val(EL 17 st) /\ val(EL 17 st) < 24)) /\
     hol_progs progs /\ R progs /\ progs 3 = eqw /\ rd_progs_ok progs /\ pl_cw_range nctl P /\ 24 < nctl /\
     rd_tab_apart hol_layout bw /\
     drv_sem progs bw ctl budget cfr (APPEND pfx (APPEND P pl_inc_cnt)) 0 m used res /\
     tab_rel hol_tables hol_layout inp bw ctl nctl cfr m (cw,ns,stk) /\ hol_inv (cw,ns,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> ?s'. tab_rel hol_tables hol_layout inp bw ctl nctl cfr (FST(SND(SND res))) s' /\
              (pl_grows ns (FST(SND s')) \/
               ?v s2. cw 20 = 1 /\ D (rd_from inp c) v /\ Q inp (W cw c v,ns,stk) (FST(SND s2)) /\
                      hol_inv s2 /\ pl_grows (FST(SND s2)) (FST(SND s')))`,
  let r1 = `r1:int64#num#(int64->byte)#int64` and r2 = `r2:int64#num#(int64->byte)#int64` in
  let fstw r = mk_eq(mk_icomb(`FST:int64#num#(int64->byte)#int64->int64`, r), `word 1:int64`) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rd_layout bw ctl nctl cfr` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th)
                          then ACCEPT_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)) else failwith "");
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[DRV_SEM_APPEND] THEN DISCH_THEN(X_CHOOSE_THEN r1 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  (* the prefix keeps the tables, whatever its outcome *)
  MP_TAC(ISPECL [`hol_tables`; `hol_layout`; `inp:num list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
                 `nctl:num`; `budget:int64`; `cfr:int64`; `pfx:(int64 list)list`; `0`; `m:int64->byte`;
                 `used:int64`; r1; `cw:num->num`; `ns:nstate`; `stk:num list`] TAB_RD_ONLY_KEEPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `cw1:num->num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC (fstw r1) THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `(cw1,ns,stk):pstate` THEN ASM_REWRITE_TAC[FST; SND; PL_GROWS_REFL]] THEN
  (* the prefix FIRED: the header seen, the operands v read *)
  FIRST_ASSUM(MP_TAC o SPECL [`inp:num list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                             `budget:int64`; `cfr:int64`; `0`; `m:int64->byte`; `used:int64`; r1; `cw:num->num`;
                             `ns:nstate`; `stk:num list`; `c:num`] o
    REWRITE_RULE[tab_prefix_rd] o check (fun th -> is_const_app "tab_prefix_rd" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(fun th -> if is_conj(concl th) && lhand(concl th) = `(cw:num->num) 20 = 1`
                        then ASSUME_TAC(CONJUNCT1 th) else failwith "") THEN
  SUBGOAL_THEN `hol_inv ((W:(num->num)->num->A->num->num) cw c v,ns,stk)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[DRV_SEM_APPEND] THEN DISCH_THEN(X_CHOOSE_THEN r2 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_CASES_TAC (fstw r2) THENL
   [(* the plan FIRED: its state, then the increment, whatever its outcome *)
    MP_TAC(ISPECL [`hol_tables`; `hol_layout`; `hol_progs`; `P:(int64 list)list`;
                   `Q:num list->pstate->nstate->bool`; `G:num list->pstate->bool`; `hol_inv`; `inp:num list`;
                   `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                   `0 + LENGTH(pfx:(int64 list)list)`; `FST(SND(SND(r1:int64#num#(int64->byte)#int64)))`;
                   `used:int64`; r2; `((W:(num->num)->num->A->num->num) cw c v,ns,stk):pstate`;
                   `c + (Ln:A->num) v`] TAB_PLAN_IN_HANDLER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s2:pstate` STRIP_ASSUME_TAC) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`hol_tables`; `hol_layout`; `inp:num list`; `progs:num->tisa_prog`; `bw:num->int64`;
                   `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `pl_inc_cnt`;
                   `(0 + LENGTH(pfx:(int64 list)list)) + LENGTH(P:(int64 list)list)`;
                   `FST(SND(SND(r2:int64#num#(int64->byte)#int64)))`;
                   `SND(SND(SND(r2:int64#num#(int64->byte)#int64)))`; `res:int64#num#(int64->byte)#int64`;
                   `FST(s2:pstate)`; `FST(SND(s2:pstate))`; `SND(SND(s2:pstate))`] TAB_RD_ONLY_KEEPS) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN(X_CHOOSE_THEN `cw3:num->num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(cw3,FST(SND(s2:pstate)),SND(SND(s2:pstate))):pstate` THEN ASM_REWRITE_TAC[FST; SND] THEN
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`v:A`; `s2:pstate`] THEN ASM_REWRITE_TAC[PL_GROWS_REFL];
    ALL_TAC] THEN
  (* the plan did not fire: its run, the tables grown by appending *)
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`tab_rel hol_tables hol_layout inp bw ctl nctl cfr`; `hol_tables`; `inp:num list`;
                 `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`;
                 `P:(int64 list)list`; `0 + LENGTH(pfx:(int64 list)list)`;
                 `FST(SND(SND(r1:int64#num#(int64->byte)#int64)))`;
                 `used:int64`; r2;
                 `((W:(num->num)->num->A->num->num) cw c v,ns,stk):pstate`] TAB_DRV_BRIDGE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `s':pstate` THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
  SUBGOAL_THEN `~(k = 1)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = mk_neg(fstw r2))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:(int64 list)list`; `inp:num list`; `0 + LENGTH(pfx:(int64 list)list)`;
                 `(W:(num->num)->num->A->num->num) cw c v`; `ns:nstate`; `stk:num list`; `k:num`; `j:num`;
                 `FST(s':pstate)`; `FST(SND(s':pstate))`; `SND(SND(s':pstate))`] TAB_RUN_HOL_GROWS) THEN
  ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The every-run contract of a kind's handler over HOL's tables: whatever   *)
(* the outcome, the memory left is related to a state that grows the       *)
(* start's tables, or grows the state the record's native step reached.     *)
(* ------------------------------------------------------------------------- *)

let tab_kind_every = new_definition
 `tab_kind_every L progs bw ctl nctl budget cfr H op <=>
    !m used res cw ns stk inp c.
      drv_sem progs bw ctl budget cfr H 0 m used res /\
      tab_rel hol_tables L inp bw ctl nctl cfr m (cw,ns,stk) /\ hol_inv (cw,ns,stk) /\
      rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
      ==> ?s'. tab_rel hol_tables L inp bw ctl nctl cfr (FST(SND(SND res))) s' /\
               (pl_grows ns (FST(SND s')) \/
                cw 20 = 1 /\
                ?rec rest s0. holr_rec_enc rec = CONS op (TL (holr_rec_enc rec)) /\
                              rd_from inp c = APPEND (TL (holr_rec_enc rec)) rest /\
                              nat_step ns rec (FST(SND s0)) /\ hol_inv s0 /\
                              pl_grows (FST(SND s0)) (FST(SND s')))`;;

(* A plan's safety from HOL's invariant, its driver theorem's premises being *)
(* pl_inv or words the invariant fixes.                                      *)
let TAB_SAFE_HOL_TAC safe_th =
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; HOL_INV] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST [MATCH_ACCEPT_TAC safe_th;
         (fun gl -> (MATCH_MP_TAC safe_th THEN ASM_REWRITE_TAC[] THEN
                     TRY(PL_INV_FACTS_TAC THEN ASM_SIMP_TAC[ARITH])) gl)];;

let tab_kind_every_of name (sh:tab_shape) pfx_rd58 plan_def (lifts, rdok, payloads, nctl) impl_th safe_th op =
  let plan = lhs(concl plan_def) in
  let q, g = match snd(strip_comb(concl lifts)) with [_; _; _; _; q; g; _] -> q, g | _ -> failwith "lifts" in
  let hbody = list_mk_icomb "APPEND" [sh.ts_pfx; list_mk_icomb "APPEND" [plan; `pl_inc_cnt`]] in
  let hdef = tab_handler_def name hbody in
  let thlast = prove(mk_comb(`tab_th_last`, plan),
    REWRITE_TAC[plan_def; tab_th_last; NOT_CONS_NIL] THEN CONV_TAC STEP_EL_CONV2 THEN REWRITE_TAC[]) in
  let safe_all = prove(list_mk_forall([`inp:num list`; `s:pstate`],
                         mk_imp(`hol_inv s`, list_mk_icomb "tab_safe" [`hol_tables`; `inp:num list`; plan; `s:pstate`])),
                       TAB_SAFE_HOL_TAC safe_th) in
  let gen = SPEC_ALL(ISPECL [HOL_R; sh.ts_pfx; sh.ts_d; sh.ts_w; sh.ts_l; plan; q; g] TAB_HANDLER_EVERY_HOL) in
  let ant = fst(dest_imp(concl gen)) in
  let statics = filter (fun p -> frees p = []) (conjuncts ant) in
  let static_ths = map (fun p -> prove(p, FIRST [ACCEPT_TAC thlast; TAB_STATIC_TAC sh lifts payloads])) statics in
  let goal = list_mk_forall([`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                             `cfr:int64`],
    mk_imp(list_mk_conj [`hol_progs progs`; `(progs:num->tisa_prog) 28 = skip`; `rd_progs_ok progs`;
                         list_mk_icomb "pl_cw_range" [`nctl:num`; plan]; `rd_tab_apart hol_layout bw`],
           list_mk_icomb "tab_kind_every" [`hol_layout`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
                                           `nctl:num`; `budget:int64`; `cfr:int64`; lhs(concl hdef); op])) in
  prove(goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tab_kind_every] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC gen THEN RULE_ASSUM_TAC(REWRITE_RULE[hdef]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[hol_progs; pl_progs_ok] o check (is_const_app "hol_progs" o concl)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP nctl o check (is_const_app "pl_cw_range" o concl)) THEN
    SUBGOAL_THEN (list_mk_icomb "tab_rd_plan_ok" [`hol_layout`; `progs:num->tisa_prog`; `nctl:num`; plan]) ASSUME_TAC
    THENL [MATCH_MP_TAC rdok THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN (list_mk_icomb "rd_only58_ok" [`progs:num->tisa_prog`; `nctl:num`; sh.ts_pfx]) ASSUME_TAC
    THENL [MATCH_MP_TAC pfx_rd58 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `rd_only58_ok progs nctl pl_inc_cnt` ASSUME_TAC THENL
     [MATCH_MP_TAC RD_ONLY58_INC_CNT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC_ALL impl_th) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[pl_progs_ok]; DISCH_TAC] THEN
    ASSUME_TAC(SPEC `inp:num list` safe_all) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC static_ths; ALL_TAC] THEN
    CONV_TAC(LAND_CONV TAB_HANDLER_NORM_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `s':pstate` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> EXISTS_TAC `s':pstate` THEN ASM_REWRITE_TAC[] THEN MP_TAC th) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> DISJ1_TAC THEN ACCEPT_TAC th) MP_TAC) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN DISJ2_TAC THEN
    TRY(FIRST_ASSUM(fun th -> if is_const_app "name_fires" (concl th) then
          RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP NAME_FIRES_KEY th]) THEN
          STRIP_ASSUME_TAC(REWRITE_RULE[name_fires] th) else failwith "")) THEN
    TRY(FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [leb_fires] o
                      check (fun th -> is_const_app "leb_fires" (concl th)))) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if is_const_app "nat_step" (concl th)
                          then EXISTS_TAC (el 1 (snd(strip_comb(concl th)))) else failwith "") THEN
    MAP_EVERY EXISTS_TAC [`rest:num list`; `s2:pstate`] THEN
    REWRITE_TAC[holr_rec_enc; TL] THEN ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ASM_REWRITE_TAC[APPEND_ASSOC]);;

let KE_NAME_TAB = tab_kind_every_of "name" tab_name_shape RD_ONLY58_PREFIX_NAME pl_plan_name LF_NAME
                    TAB_IMPL_NAMEP TAB_SAFE_NAME `1`;;
let KE_TYVAR_TAB = tab_kind_every_of "tyvar" tab_op0_shape RD_ONLY58_PREFIX_OP0 pl_plan_tyvar LF_TYVAR
                     TAB_IMPL_TYVAR TAB_SAFE_TYVAR `2`;;
let KE_VAR_TAB = tab_kind_every_of "var" tab_op01_shape RD_ONLY58_PREFIX_OP01 pl_plan_var LF_VAR
                   TAB_IMPL_VAR TAB_SAFE_VAR `4`;;
let KE_COMB_TAB = tab_kind_every_of "comb" tab_op01_shape RD_ONLY58_PREFIX_OP01 pl_plan_comb LF_COMB
                    TAB_IMPL_COMB TAB_SAFE_COMB `6`;;
let KE_REFL_TAB = tab_kind_every_of "refl" tab_op0_shape RD_ONLY58_PREFIX_OP0 pl_plan_refl LF_REFL
                    TAB_IMPL_REFL TAB_SAFE_REFL `16`;;
let KE_BETA_TAB = tab_kind_every_of "beta" tab_op0_shape RD_ONLY58_PREFIX_OP0 pl_plan_beta LF_BETA
                    TAB_IMPL_BETA TAB_SAFE_BETA `20`;;
let KE_ASSUME_TAB = tab_kind_every_of "assume" tab_op0_shape RD_ONLY58_PREFIX_OP0 pl_plan_assume LF_ASSUME
                      TAB_IMPL_ASSUME TAB_SAFE_ASSUME `21`;;
let KE_LABEL_TAB = tab_kind_every_of "label" tab_op01_shape RD_ONLY58_PREFIX_OP01 pl_plan_label LF_LABEL
                     TAB_IMPL_LABEL TAB_SAFE_LABEL `49`;;
let KE_EMIT_TAB = tab_kind_every_of "emit" tab_op0_shape RD_ONLY58_PREFIX_OP0 pl_plan_emit LF_EMIT
                    TAB_IMPL_EMIT TAB_SAFE_EMIT `50`;;
let KE_DROP_TYPE_TAB = tab_kind_every_of "drop_type" tab_op0_shape RD_ONLY58_PREFIX_OP0 pl_plan_drop_type LF_DROP_TYPE
                    TAB_IMPL_DROP_TYPE TAB_SAFE_DROP_TYPE `64`;;
let KE_DROP_TERM_TAB = tab_kind_every_of "drop_term" tab_op0_shape RD_ONLY58_PREFIX_OP0 pl_plan_drop_term LF_DROP_TERM
                    TAB_IMPL_DROP_TERM TAB_SAFE_DROP_TERM `65`;;
let KE_DROP_THM_TAB = tab_kind_every_of "drop_thm" tab_op0_shape RD_ONLY58_PREFIX_OP0 pl_plan_drop_thm LF_DROP_THM
                    TAB_IMPL_DROP_THM TAB_SAFE_DROP_THM `66`;;

(* ------------------------------------------------------------------------- *)
(* The record loop over the general relation, every run: whatever the       *)
(* outcome, the loop's memory is related to a state whose tables grow those *)
(* of a state meeting HOL's invariant, which the bootstrap reaches by the   *)
(* records of a body prefix of the input, or the bootstrap state itself     *)
(* before the header (REC_EVERY_TAB). The decode, the header and END write  *)
(* no table (rd_only58_ok); a record kind's handler meets tab_kind_every.    *)
(* The call, entry to return (REC_X86_EVERY_TAB); its theorem rows          *)
(* derivable (REC_EVERY_THMS_TAB). As rec_every.ml, over tab_rel.           *)
(* ------------------------------------------------------------------------- *)

let tab_rec_entry_every = new_definition
 `tab_rec_entry_every L progs bw ctl nctl budget cfr k (H:(int64 list)list) <=>
    ((k = 127 \/ k = 72) ==> rd_only58_ok progs nctl H) /\
    (~(k = 127) /\ ~(k = 72) ==> tab_kind_every L progs bw ctl nctl budget cfr H k)`;;

let tab_rec_every_tbl_tm =
 `!k. k < val (nh:int64) /\ ~(drv_word m0 (word_add ht (word (8 * k))) = word 0)
      ==> tab_rec_entry_every L progs bw ctl nctl budget (word_sub E (word 312)) k
                          (pl (drv_word m0 (word_add ht (word (8 * k)))))`;;

let tab_rec_every = new_definition
 `tab_rec_every L bw ctl nctl E hpol inp (m:int64->byte) <=>
    ?s cw0 ns0 stk0.
      tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) m s /\
      hol_inv (cw0,ns0,stk0) /\ pl_grows ns0 (FST(SND s)) /\
      (ns0 = (hinit_ctxt,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],hpol) \/
       ?pol0 recs n. pol0 <= 2 /\ list_of_seq (\j. EL j inp) n = holr_body pol0 0 recs /\
                     tc_path nat_step recs
                       (hinit_ctxt,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],MAX hpol pol0) ns0)`;;

let ev_ns_tuple = end_itlist (curry mk_pair) pl_ns_vars;;

(* The invariant's memory meets the every-run property. *)
let REC_INV_EVERY_TAB = prove
 (`!L bw ctl nctl E ht nh m0 hpol inp m.
     tab_rec_inv L bw ctl nctl E ht nh m0 hpol inp m ==> tab_rec_every L bw ctl nctl E hpol inp m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_rec_inv; tab_rec_every; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC ([`cw:num->num`] @ RD_NS_VARS @ [`pos:num`]) THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [mk_pair(`cw:num->num`, mk_pair(ev_ns_tuple, `stk:num list`));
                        `cw:num->num`; ev_ns_tuple; `stk:num list`] THEN
  ASM_REWRITE_TAC[FST; SND; PL_GROWS_REFL] THEN
  DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`pol0:num`; `recs:holr_record list`; `pos:num`] THEN
  ASM_REWRITE_TAC[]);;

(* A plan run through its descriptor: what the run of its steps gives of the *)
(* memory they leave, under tab_rel, holds of the loop's memory after it.    *)
let REC_PLAN_REL_EVERY_TAB = prove
 (`!L progs bw ctl nctl budget E pl d m used r R cw ns stk inp c (Phi:pstate->bool).
     rec_plan progs bw ctl budget E pl d m used r /\ val d + 64 <= 2 EXP 64 /\
     tab_rel_reads hol_tables L bw ctl nctl (word_sub E (word 312)) R /\
     (!a. R a ==> ~rec_stack E a /\ ~drv_in a (word_add d (word 40)) 24) /\
     tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) m (cw,ns,stk) /\
     rd_rel bw ctl nctl (word_sub E (word 312)) m inp c /\
     (!m' res. drv_sem progs bw ctl budget (word_sub E (word 312)) (pl d) 0 m' used res /\
               tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) m' (cw,ns,stk) /\
               rd_rel bw ctl nctl (word_sub E (word 312)) m' inp c
               ==> ?s'. tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) (FST(SND(SND res))) s' /\ Phi s')
     ==> ?s'. tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) (FST(SND r)) s' /\ Phi s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `E:int64`;
                 `pl:int64->(int64 list)list`; `d:int64`; `m:int64->byte`; `used:int64`;
                 `r:int64#(int64->byte)#int64`; `R:int64->bool`] REC_PLAN_DRV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m':int64->byte` (X_CHOOSE_THEN `res:int64#num#(int64->byte)#int64`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m':int64->byte`; `res:int64#num#(int64->byte)#int64`] o
    check (fun th -> is_forall(concl th) && can (find_term (is_const_app "drv_sem")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPEC `hol_tables` TAB_REL_READS_TAB) THEN
      MAP_EVERY EXISTS_TAC [`R:int64->bool`; `m:int64->byte`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ISPECL [`hol_tables`; `L:tabdesc list`] TAB_REL_READS_RD) THEN
      MAP_EVERY EXISTS_TAC [`R:int64->bool`; `m:int64->byte`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s':pstate` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPEC `hol_tables` TAB_REL_READS_TAB) THEN
  MAP_EVERY EXISTS_TAC [`R:int64->bool`; `FST(SND(SND(res:int64#num#(int64->byte)#int64)))`] THEN
  ASM_REWRITE_TAC[]);;

(* The opcode byte and the record's other bytes: the record's encoding.     *)
let tab_rec_dec_every_goal =
  let dyn = `tab_rec_inv L bw ctl nctl E ht nh m0 hpol inp m /\ ~(val budget <= val used) /\
             rec_plan progs bw ctl budget E pl dd m (word_add used (word 1)) r1` in
  rec_order (tab_rec_static_names @ ["m"; "used"; "r1"])
    (mk_imp(mk_conj(tab_rec_static_tm, dyn),
            `tab_rec_every L bw ctl nctl E hpol inp (FST(SND(r1:int64#(int64->byte)#int64)))`));;

let TAB_REC_INV_STATE_TAC =
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[tab_rec_inv] o check (fun th -> is_const_app "tab_rec_inv" (concl th))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC ([`cw:num->num`] @ RD_NS_VARS @ [`pos:num`]) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS);;

(* tab_rec_every at a state with the invariant's tables. *)
let TAB_REC_EVERY_SAME_TAC =
  REWRITE_TAC[tab_rec_every] THEN
  MAP_EVERY EXISTS_TAC [`s':pstate`; `cw:num->num`; ev_ns_tuple; `stk:num list`] THEN
  ASM_REWRITE_TAC[PL_GROWS_REFL] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `hinit_ctxt`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`pol0:num`; `recs:holr_record list`; `pos:num`] THEN ASM_REWRITE_TAC[];;

let REC_DECODE_EVERY_TAB = prove(tab_rec_dec_every_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!d. MEM d ds ==> val(d:int64) + 64 <= 2 EXP 64` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> is_const_app "rec_layout" (concl th))) THEN
    REWRITE_TAC[rec_layout] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  TAB_REC_INV_STATE_TAC THEN
  SUBGOAL_THEN `!a. (R:int64->bool) a ==> ~rec_stack E a /\ ~drv_in a (word_add dd (word 40)) 24` ASSUME_TAC THENL
   [REC_RFACTS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(dd:int64) + 64 <= 2 EXP 64` ASSUME_TAC THENL [REC_D64_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:tabdesc list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `E:int64`;
                 `pl:int64->(int64 list)list`; `dd:int64`; `m:int64->byte`; `word_add used (word 1):int64`;
                 `r1:int64#(int64->byte)#int64`; `R:int64->bool`; `cw:num->num`; ev_ns_tuple; `stk:num list`;
                 `inp:num list`; `pos:num`; mk_abs(`s':pstate`, mk_eq(`FST(SND(s':pstate))`, ev_ns_tuple))]
                REC_PLAN_REL_EVERY_TAB) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`hol_tables`; `L:tabdesc list`; `inp:num list`; `progs:num->tisa_prog`; `bw:num->int64`;
                   `ctl:int64`; `nctl:num`; `budget:int64`; `word_sub E (word 312):int64`;
                   `(pl:int64->(int64 list)list) dd`; `0`; `m':int64->byte`; `word_add used (word 1):int64`;
                   `res:int64#num#(int64->byte)#int64`; `cw:num->num`; ev_ns_tuple; `stk:num list`]
                  TAB_RD_ONLY_KEEPS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST [MATCH_MP_TAC RD_ONLY58_DD THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th)
                          then ACCEPT_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)) else failwith "")];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `cwx:num->num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (mk_pair(`cwx:num->num`, mk_pair(ev_ns_tuple, `stk:num list`))) THEN ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC) THEN
  TAB_REC_EVERY_SAME_TAC);;

(* A handler, whatever its outcome. *)
let tab_rec_hdl_every_goal =
  let dyn = `tab_rec_inv L bw ctl nctl E ht nh m0 hpol inp m /\ ~(val budget <= val used) /\
             rec_plan progs bw ctl budget E pl dd m (word_add used (word 1)) r1 /\ FST r1 = word 1 /\
             ~rec_missing ht nh opa (FST(SND r1)) /\
             rec_plan progs bw ctl budget E pl (rec_handler ht opa (FST(SND r1))) (FST(SND r1)) (SND(SND r1)) r2` in
  rec_order (tab_rec_static_names @ ["m"; "used"; "r1"; "r2"])
    (mk_imp(list_mk_conj [tab_rec_static_tm; tab_rec_every_tbl_tm; dyn],
            `tab_rec_every L bw ctl nctl E hpol inp (FST(SND(r2:int64#(int64->byte)#int64)))`));;

let REC_HANDLER_EVERY_TAB = prove(tab_rec_hdl_every_goal,
  let r1m = `FST(SND(r1:int64#(int64->byte)#int64))`
  and used1 = `SND(SND(r1:int64#(int64->byte)#int64))`
  and r2 = `r2:int64#(int64->byte)#int64` in
  let dop = `drv_word m0 (word_add ht (word (8 * op)))` in
  let cw' = `pl_set (pl_set cw 21 pos) 18 op` and c' = `pos + LENGTH (leb_enc op)` in
  let is_tbl mt th = is_forall(concl th) && can (find_term ((=) `ht:int64`)) (concl th) &&
                     can (find_term ((=) mt)) (concl th) && can (find_term ((=) `m0:int64->byte`)) (concl th) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!d. MEM d ds ==> val(d:int64) + 64 <= 2 EXP 64` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> is_const_app "rec_layout" (concl th))) THEN
    REWRITE_TAC[rec_layout] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  TAB_REC_INV_STATE_TAC THEN
  (* the table in the decode's memory *)
  SUBGOAL_THEN `!k. k < val(nh:int64)
                    ==> drv_word (FST(SND(r1:int64#(int64->byte)#int64))) (word_add ht (word (8 * k))) =
                        drv_word m0 (word_add ht (word (8 * k)))` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(rec_spec ["d", `dd:int64`; "used", `word_add used (word 1):int64`; "rr", `r1:int64#(int64->byte)#int64`]
                    REC_PLAN_TABLE) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (is_tbl `m:int64->byte`)) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the decode's descriptor, the lookup *)
  SUBGOAL_THEN `!a. (R:int64->bool) a ==> ~rec_stack E a /\ ~drv_in a (word_add dd (word 40)) 24` ASSUME_TAC THENL
   [REC_RFACTS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(dd:int64) + 64 <= 2 EXP 64` ASSUME_TAC THENL [REC_D64_TAC; ALL_TAC] THEN
  MP_TAC(SPEC_ALL REC_LOOKUP_TAB) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `op:num` STRIP_ASSUME_TAC)) THEN
  (* the entry: in ds, and its every-run contract *)
  FIRST_ASSUM(MP_TAC o SPEC `op:num` o check (fun th -> is_forall(concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "tab_rec_entry")) (concl th))) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  FIRST_ASSUM(MP_TAC o SPEC `op:num` o check (fun th -> is_forall(concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "tab_rec_entry_every")) (concl th))) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[tab_rec_entry_every] THEN STRIP_TAC THEN
  (* the handler's run and descriptor *)
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "rec_plan" (concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "rec_handler")) (concl th))) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && is_const_app "rec_handler" (lhs(concl th))
                        then PURE_REWRITE_TAC[th] else failwith "") THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(val(budget:int64) < val(SND(SND(r1:int64#(int64->byte)#int64))))` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = used1 then PURE_REWRITE_TAC[th] else failwith "") THEN
    MATCH_MP_TAC REC_USED1 THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (subst [dop,`dd:int64`] `!a. (R:int64->bool) a ==> ~rec_stack E a /\ ~drv_in a (word_add dd (word 40)) 24`)
    ASSUME_TAC THENL [REC_RFACTS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (subst [dop,`dd:int64`] `val(dd:int64) + 64 <= 2 EXP 64`) ASSUME_TAC THENL [REC_D64_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `op < 128` ASSUME_TAC THENL
   [UNDISCH_TAC `op < val(nh:int64)` THEN UNDISCH_TAC `val(nh:int64) <= 128` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `op = 127 \/ op = 72` THENL
   [(* END or the header: no table written *)
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_disj(lhand(concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`L:tabdesc list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `E:int64`;
                   `pl:int64->(int64 list)list`; dop; r1m; used1; r2; `R:int64->bool`; cw'; ev_ns_tuple;
                   `stk:num list`; `inp:num list`; c';
                   mk_abs(`s':pstate`, mk_eq(`FST(SND(s':pstate))`, ev_ns_tuple))] REC_PLAN_REL_EVERY_TAB) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN BETA_TAC THEN
      MP_TAC(ISPECL [`hol_tables`; `L:tabdesc list`; `inp:num list`; `progs:num->tisa_prog`; `bw:num->int64`;
                     `ctl:int64`; `nctl:num`; `budget:int64`; `word_sub E (word 312):int64`;
                     mk_comb(`pl:int64->(int64 list)list`, dop); `0`; `m':int64->byte`; used1;
                     `res:int64#num#(int64->byte)#int64`; cw'; ev_ns_tuple; `stk:num list`] TAB_RD_ONLY_KEEPS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th)
                          then ACCEPT_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)) else failwith "")];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `cwx:num->num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (mk_pair(`cwx:num->num`, mk_pair(ev_ns_tuple, `stk:num list`))) THEN ASM_REWRITE_TAC[FST; SND];
      ALL_TAC] THEN
    BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC) THEN
    TAB_REC_EVERY_SAME_TAC;
    ALL_TAC] THEN
  (* a record kind: its every-run contract *)
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "tab_kind_every")) (concl th))) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[DE_MORGAN_THM] o
      check (fun th -> is_neg(concl th) && is_disj(dest_neg(concl th))));
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`L:tabdesc list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `E:int64`;
                 `pl:int64->(int64 list)list`; dop; r1m; used1; r2; `R:int64->bool`; cw'; ev_ns_tuple;
                 `stk:num list`; `inp:num list`; c';
                 mk_abs(`s':pstate`,
                   subst [cw', `cw:num->num`; ev_ns_tuple, `ns:nstate`; c', `c:num`; `op:num`, `opk:num`]
                    `pl_grows ns (FST(SND(s':pstate))) \/
                     (cw:num->num) 20 = 1 /\
                     ?rec rest s0. holr_rec_enc rec = CONS opk (TL (holr_rec_enc rec)) /\
                                   rd_from inp c = APPEND (TL (holr_rec_enc rec)) rest /\
                                   nat_step ns rec (FST(SND s0)) /\ hol_inv s0 /\
                                   pl_grows (FST(SND s0)) (FST(SND(s':pstate)))`)] REC_PLAN_REL_EVERY_TAB) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN BETA_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[tab_kind_every] o
      check (fun th -> is_const_app "tab_kind_every" (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`m':int64->byte`; used1; `stk:num list`] THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOL_INV_SET THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOL_INV_SET THEN REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ARITH_TAC; ARITH_TAC];
      ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `s':pstate` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV PL_SET_NUM_CONV)) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [REWRITE_TAC[tab_rec_every] THEN
    MAP_EVERY EXISTS_TAC [`s':pstate`; `cw:num->num`; ev_ns_tuple; `stk:num list`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `hinit_ctxt`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`pol0:num`; `recs:holr_record list`; `pos:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the record's native step happened: the state one record further *)
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `rec:holr_record` (X_CHOOSE_THEN `rest:num list`
    (X_CHOOSE_THEN `s0:pstate` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `hinit_ctxt`)) (concl th))) THENL
   [(* before the header HDR is 0 *)
    UNDISCH_TAC `(cw:num->num) 20 = 1` THEN ASM_REWRITE_TAC[ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[tab_rec_every] THEN
  MAP_EVERY EXISTS_TAC [`s':pstate`; `FST(s0:pstate)`; `FST(SND(s0:pstate))`; `SND(SND(s0:pstate))`] THEN
  ASM_REWRITE_TAC[PAIR] THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`pol0:num`; `APPEND recs [rec:holr_record]`; `pos + LENGTH (holr_rec_enc rec)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`inp:num list`; `pos:num`; `op:num`; `rec:holr_record`; `rest:num list`] REC_BYTES) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `rd_from inp pos`
                          then SUBST1_TAC(MATCH_MP LIST_OF_SEQ_RD_FROM th) else failwith "") THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && is_const_app "list_of_seq" (lhs(concl th))
                          then PURE_REWRITE_TAC[th] else failwith "") THEN
    REWRITE_TAC[HOLR_BODY_SNOC];
    MATCH_MP_TAC TC_PATH_SNOC THEN EXISTS_TAC ev_ns_tuple THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* The loop, every run. *)
let tab_rec_every_goal =
  let run = `rec_run progs bw ctl budget E pl dd ht nh opa enda m used c res` in
  let inner = list_mk_forall([`m:int64->byte`; `used:int64`; `c:num`; `res:int64#num#(int64->byte)#int64`],
                mk_imp(run, mk_imp(`tab_rec_inv L bw ctl nctl E ht nh m0 hpol inp m`,
                                   `tab_rec_every L bw ctl nctl E hpol inp (FST(SND(SND(res:int64#num#(int64->byte)#int64))))`))) in
  rec_order tab_rec_static_names (mk_imp(mk_conj(tab_rec_static_tm, tab_rec_every_tbl_tm), inner));;

let REC_EVERY_TAB = prove(tab_rec_every_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC rec_run_INDUCT THEN REWRITE_TAC[FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [(* the allowance spent: the invariant's memory *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_ACCEPT_TAC REC_INV_EVERY_TAB;
    (* the decode did not fire *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(SPEC_ALL REC_DECODE_EVERY_TAB) THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    (* no handler *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(SPEC_ALL REC_DECODE_EVERY_TAB) THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    (* the handler did not fire *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(SPEC_ALL REC_HANDLER_EVERY_TAB) THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    (* END fired *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(SPEC_ALL REC_HANDLER_EVERY_TAB) THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    (* a handler fired with ENDW 0: the invariant again, then the rest of the run *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC_ALL REC_STEP_TAB) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN FIRST_ASSUM ACCEPT_TAC]);;

(* The theorem rows the loop's memory holds are derivable, in the context of *)
(* a state the bootstrap reaches by the records of a body prefix of the     *)
(* input (or the bootstrap context itself, before the header).               *)
let REC_EVERY_THMS_TAB = prove
 (`!L bw ctl nctl E hpol inp m.
     tab_rec_every L bw ctl nctl E hpol inp m
     ==> ?s. tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) m s /\ pl_thms_ok (FST(SND s)) /\
             (FST(FST(SND s)) = hinit_ctxt \/
              ?pol0 recs n ns0. pol0 <= 2 /\ list_of_seq (\j. EL j inp) n = holr_body pol0 0 recs /\
                                tc_path nat_step recs
                                  (hinit_ctxt,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],MAX hpol pol0) ns0 /\
                                FST(FST(SND s)) = FST ns0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_rec_every; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:pstate`; `cw0:num->num`; `ns0:nstate`; `stk0:num list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  EXISTS_TAC `s:pstate` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FST(FST(SND(s:pstate))) = FST(ns0:nstate)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_grows ns0 (FST(SND(s:pstate)))` THEN
    SPEC_TAC(`FST(SND(s:pstate))`,`ns:nstate`) THEN SPEC_TAC(`ns0:nstate`,`ns0:nstate`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; pl_grows; FST] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_GROWS_THMS THEN EXISTS_TAC `ns0:nstate` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> if is_const_app "hol_inv" (concl th)
                          then ASSUME_TAC(CONJUNCT1(REWRITE_RULE[hol_inv;hol_core_inv] th)) else failwith "") THEN
    MP_TAC(ISPEC `(cw0,ns0,stk0):pstate` PL_INV_THMS) THEN ASM_REWRITE_TAC[FST; SND];
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th))) THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[FST];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`pol0:num`; `recs:holr_record list`; `n:num`; `ns0:nstate`] THEN
      ASM_REWRITE_TAC[]]]);;

(* The every-run property reads only R. *)
let REC_EVERY_AGREE_TAB = prove
 (`!L bw ctl nctl E hpol inp R M M'.
     tab_rel_reads hol_tables L bw ctl nctl (word_sub E (word 312)) R /\ (!a. R a ==> M' a = M a) /\
     tab_rec_every L bw ctl nctl E hpol inp M
     ==> tab_rec_every L bw ctl nctl E hpol inp M'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_rec_every] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:pstate`; `cw0:num->num`; `ns0:nstate`; `stk0:num list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`s:pstate`; `cw0:num->num`; `ns0:nstate`; `stk0:num list`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(ISPEC `hol_tables` TAB_REL_READS_TAB) THEN
  MAP_EVERY EXISTS_TAC [`R:int64->bool`; `M:int64->byte`] THEN ASM_REWRITE_TAC[]);;

(* The record loop's call, entry to return, every run: the memory it        *)
(* returns meets the every-run property (with REC_EVERY_THMS_TAB, its theorem  *)
(* rows are derivable). R misses the descriptor words the return writes.   *)
let tab_rec_x86_every_goal =
  let _, body = strip_forall(concl REC_CORRECT) in
  let prem, ens = dest_imp body in
  let f, frame = dest_comb ens in
  let f2, post = dest_comb f in
  let s, pb = dest_abs post in
  let ev = vsubst [s, `s:x86state`] `tab_rec_every L bw ctl nctl E hpol inp (read memory (s:x86state))` in
  let post' = mk_abs(s, mk_conj(pb, ev)) in
  let ens' = mk_comb(mk_comb(f2, post'), frame) in
  let prems = list_mk_conj [prem; tab_rec_static_tm; tab_rec_every_tbl_tm; `tab_rec_inv L bw ctl nctl E ht nh m0 hpol inp m0`;
                            `!a. (R:int64->bool) a ==> ~drv_in a (word_add r (word 56)) 16`] in
  let tm = mk_imp(prems, ens') in
  list_mk_forall(frees tm, tm);;

let REC_X86_EVERY_TAB = prove(tab_rec_x86_every_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (let _, body = strip_forall(concl REC_CORRECT) in rand(rator(rand body))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REC_EVERY_AGREE_TAB THEN
      MAP_EVERY EXISTS_TAC [`R:int64->bool`; `FST(SND(SND(res:int64#num#(int64->byte)#int64)))`] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
        SUBGOAL_THEN `~rec_stack E (a:int64)` ASSUME_TAC THENL
         [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `rec_stack`)) (concl th) && not (can (find_term ((=) `drv_in`)) (concl th)))) THEN
          FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `rec_final`)) (concl th)
                              then REWRITE_TAC[MATCH_MP (SPEC `a:int64` th) (ASSUME `~rec_stack E (a:int64)`)]
                              else failwith "") THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `a:int64` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `word_add (r:int64) (word 56)`)) (concl th))) THEN
        ASM_REWRITE_TAC[rec_final; drv_in] THEN
        FIRST_ASSUM(MP_TAC o check (fun th -> is_const_app "rec_layout" (concl th))) THEN
        REWRITE_TAC[rec_layout] THEN STRIP_TAC THEN
        SUBGOAL_THEN `val(word_add r (word 56):int64) = val(r:int64) + 56 /\
                      val(word_add r (word 64):int64) = val(r:int64) + 64` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        REFL_TAC;
        MP_TAC(rec_spec ["m", `m0:int64->byte`; "used", `used0:int64`; "c", `0`;
                         "res", `res:int64#num#(int64->byte)#int64`] REC_EVERY_TAB) THEN
        ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`m0:int64->byte`; `used0:int64`; `0`; `res:int64#num#(int64->byte)#int64`]) THEN
        ASM_REWRITE_TAC[]]];
    MP_TAC(SPEC_ALL REC_CORRECT) THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]);;

(* Every theorem this file states, for the audits. *)

(* Every theorem this file states, for the audits. *)
let every_tab_theorems =
 ["TAB_LEAF_UNFIRED", TAB_LEAF_UNFIRED; "TAB_LEAF_FIRED", TAB_LEAF_FIRED; "HOL_TAPP_GROWS", HOL_TAPP_GROWS;
  "TAB_RUN_HOL_GROWS", TAB_RUN_HOL_GROWS; "TAB_RD_ONLY_KEEPS", TAB_RD_ONLY_KEEPS; "RD_ONLY58_DD", RD_ONLY58_DD;
  "RD_ONLY58_PREFIX_OP0", RD_ONLY58_PREFIX_OP0; "RD_ONLY58_PREFIX_OP01", RD_ONLY58_PREFIX_OP01;
  "RD_ONLY58_PREFIX_NAME", RD_ONLY58_PREFIX_NAME; "RD_ONLY58_INC_CNT", RD_ONLY58_INC_CNT;
  "RD_ONLY58_END", RD_ONLY58_END; "RD_ONLY58_HDR", RD_ONLY58_HDR;
  "TAB_HANDLER_EVERY_HOL", TAB_HANDLER_EVERY_HOL; "KE_NAME_TAB", KE_NAME_TAB; "KE_TYVAR_TAB", KE_TYVAR_TAB;
  "KE_VAR_TAB", KE_VAR_TAB; "KE_COMB_TAB", KE_COMB_TAB; "KE_REFL_TAB", KE_REFL_TAB; "KE_BETA_TAB", KE_BETA_TAB;
  "KE_ASSUME_TAB", KE_ASSUME_TAB; "KE_LABEL_TAB", KE_LABEL_TAB; "KE_EMIT_TAB", KE_EMIT_TAB;
  "REC_INV_EVERY_TAB", REC_INV_EVERY_TAB; "REC_PLAN_REL_EVERY_TAB", REC_PLAN_REL_EVERY_TAB;
  "REC_DECODE_EVERY_TAB", REC_DECODE_EVERY_TAB; "REC_HANDLER_EVERY_TAB", REC_HANDLER_EVERY_TAB;
  "REC_EVERY_TAB", REC_EVERY_TAB; "REC_EVERY_THMS_TAB", REC_EVERY_THMS_TAB;
  "REC_EVERY_AGREE_TAB", REC_EVERY_AGREE_TAB; "REC_X86_EVERY_TAB", REC_X86_EVERY_TAB;
  "KE_DROP_TYPE_TAB", KE_DROP_TYPE_TAB; "KE_DROP_TERM_TAB", KE_DROP_TERM_TAB; "KE_DROP_THM_TAB", KE_DROP_THM_TAB];;
