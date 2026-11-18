(* ========================================================================= *)
(* A handler, every run: the prefix, the plan and the count's increment,    *)
(* whatever their outcomes (HANDLER_EVERY). The memory left is related to a *)
(* state whose tables grow the start's, or grow the state the plan's FIRED  *)
(* run reached. Each compiled kind's every-run contract (kind_every) from   *)
(* its handler (kind_every_of), with the plans that write no table by       *)
(* computation on their data (the RD_ONLY theorems).                         *)
(*                                                                           *)
(* Loaded after kind_contract.ml.                                            *)
(* ========================================================================= *)

needs "native/hol/kind_contract.ml";;
needs "native/hol/plans_every.ml";;

(* ------------------------------------------------------------------------- *)
(* A handler, whatever its outcome: the prefix, the plan and the count's    *)
(* increment. The memory it leaves is related to a state whose tables grow  *)
(* the start's (the prefix or the plan did not fire), or grow the state the *)
(* plan's FIRED run reached (the increment did not fire).                    *)
(* ------------------------------------------------------------------------- *)

let PL_TH_LAST_MEM = prove
 (`!P st. pl_th_last P /\ MEM st P ==> ~(val(EL 17 st) = 2) /\ (val(EL 0 st) = 6 ==> val(EL 12 st) = 2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pl_th_last; MEM] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let PL_REL_CW2 = prove
 (`!bw ctl nctl cfr m s. plan_rel bw ctl nctl cfr m s ==> FST s 2 = 2`,
  REWRITE_TAC[FORALL_PAIR_THM; plan_rel; FST] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

(* Leaf n keeps the relation, when it does not fire, in every step of P     *)
(* that calls it: the premise for a leaf not yet built.                     *)
let pl_leaf_kept = new_definition
 `pl_leaf_kept prel progs bw ctl budget cfr (P:(int64 list)list) n <=>
    !st. MEM st P /\ val(EL 0 st) = n ==> pl_kept prel progs bw ctl budget cfr st`;;

let HANDLER_EVERY = prove
 (`!pfx (D:num list->A->bool) W L P Q G pend progs bw ctl nctl budget cfr m used res cw ns stk inp c.
     prefix_reads pfx D W L /\ (!cw ns stk v. pl_inv (cw,ns,stk) ==> pl_inv (W cw v,ns,stk)) /\
     rd_only_ok progs nctl pfx /\ rd_only_ok progs nctl pl_inc_cnt /\
     plan_lifts P Q G pend /\ ALL (pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr P) pend /\
     (!st. MEM st P ==> pl_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st /\
                        pl_kept (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st) /\
     pl_th_last P /\
     rd_plan_ok progs nctl P /\ (!st. MEM st P ==> 24 <= val(EL 17 st)) /\
     pl_progs_ok progs /\ rd_progs_ok progs /\ pl_cw_range nctl P /\ 24 < nctl /\
     drv_sem progs bw ctl budget cfr (APPEND pfx (APPEND P pl_inc_cnt)) 0 m used res /\
     plan_rel bw ctl nctl cfr m (cw,ns,stk) /\ pl_inv (cw,ns,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> ?s'. plan_rel bw ctl nctl cfr (FST(SND(SND res))) s' /\
              (pl_grows ns (FST(SND s')) \/
               ?v s2. cw 20 = 1 /\ D (rd_from inp c) v /\ Q (W cw v,ns,stk) (FST(SND s2)) /\ pl_inv s2 /\
                      pl_grows (FST(SND s2)) (FST(SND s')))`,
  let r1 = `r1:int64#num#(int64->byte)#int64` and r2 = `r2:int64#num#(int64->byte)#int64` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `progs 3 = eqw` ASSUME_TAC THENL [ASM_MESON_TAC[pl_progs_ok]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[DRV_SEM_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN r1 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                             `cfr:int64`; `0`; `m:int64->byte`; `used:int64`; r1; `cw:num->num`; `ns:nstate`;
                             `stk:num list`; `inp:num list`; `c:num`] o
    REWRITE_RULE[prefix_reads] o check (fun th -> is_const_app "prefix_reads" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `FST(r1:int64#num#(int64->byte)#int64) = word 1` THENL
   [ALL_TAC;
    (* The prefix did not fire: the tables as they were. *)
    REWRITE_TAC[ASSUME `~(FST(r1:int64#num#(int64->byte)#int64) = word 1)`] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `((\k. if k < nctl then pl_mw (FST(SND(SND(r1:int64#num#(int64->byte)#int64)))) ctl k
                     else (cw:num->num) k),ns,stk):pstate` THEN
    REWRITE_TAC[FST; SND; PL_GROWS_REFL] THEN MATCH_MP_TAC RD_ONLY_KEEPS_PL THEN
    MAP_EVERY EXISTS_TAC [`progs:num->tisa_prog`; `budget:int64`; `pfx:(int64 list)list`; `0`;
                          `m:int64->byte`; `used:int64`; `inp:num list`; `c:num`] THEN
    ASM_REWRITE_TAC[]] THEN
  (* The prefix FIRED: the header seen, the operands v read. *)
  FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
                             lhand(concl th) = `FST(r1:int64#num#(int64->byte)#int64) = word 1` then
     X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC (MP th (ASSUME `FST(r1:int64#num#(int64->byte)#int64) = word 1`))
   else failwith "") THEN
  SUBGOAL_THEN `(cw:num->num) 20 = 1` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `FST(r1:int64#num#(int64->byte)#int64) = word 1`;
              ASSUME `SND(SND(SND(r1:int64#num#(int64->byte)#int64))) = used`] THEN
  DISCH_THEN(X_CHOOSE_THEN r2 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `pl_inv ((W:(num->num)->A->num->num) cw v,ns,stk)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `W:(num->num)->A->num->num`)) (concl th) &&
      can (find_term (is_const_app "pl_inv")) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`P:(int64 list)list`; `Q:pstate->nstate->bool`; `G:pstate->bool`; `pend:num list`;
                `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `0 + LENGTH (pfx:(int64 list)list)`; `FST(SND(SND(r1:int64#num#(int64->byte)#int64)))`;
                `used:int64`; r2; `((W:(num->num)->A->num->num) cw v,ns,stk):pstate`;
                `inp:num list`; `c + (L:A->num) v`] PLAN_IN_HANDLER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  ASM_CASES_TAC `FST(r2:int64#num#(int64->byte)#int64) = word 1` THENL
   [(* The plan FIRED: its state, then the increment, whatever its outcome. *)
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
                               lhand(concl th) = `FST(r2:int64#num#(int64->byte)#int64) = word 1` then
       X_CHOOSE_THEN `s2:pstate` STRIP_ASSUME_TAC (MP th (ASSUME `FST(r2:int64#num#(int64->byte)#int64) = word 1`))
     else failwith "") THEN
    REWRITE_TAC[ASSUME `FST(r2:int64#num#(int64->byte)#int64) = word 1`] THEN DISCH_TAC THEN
    EXISTS_TAC `((\k. if k < nctl then pl_mw (FST(SND(SND(res:int64#num#(int64->byte)#int64)))) ctl k
                     else FST(s2:pstate) k),FST(SND(s2:pstate)),SND(SND(s2:pstate))):pstate` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RD_ONLY_KEEPS_PL THEN
      MAP_EVERY EXISTS_TAC [`progs:num->tisa_prog`; `budget:int64`; `pl_inc_cnt`;
                            `(0 + LENGTH (pfx:(int64 list)list)) + LENGTH (P:(int64 list)list)`;
                            `FST(SND(SND(r2:int64#num#(int64->byte)#int64)))`;
                            `SND(SND(SND(r2:int64#num#(int64->byte)#int64)))`;
                            `inp:num list`; `c + (L:A->num) v`] THEN
      ASM_REWRITE_TAC[PAIR] THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[PAIR];
      REWRITE_TAC[FST; SND] THEN DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`v:A`; `s2:pstate`] THEN
      ASM_REWRITE_TAC[PL_GROWS_REFL]];
    ALL_TAC] THEN
  (* The plan did not fire: its run, the tables grown by appending. *)
  REWRITE_TAC[ASSUME `~(FST(r2:int64#num#(int64->byte)#int64) = word 1)`] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`plan_rel bw ctl nctl cfr`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
                 `budget:int64`; `cfr:int64`; `P:(int64 list)list`; `0 + LENGTH (pfx:(int64 list)list)`;
                 `FST(SND(SND(r1:int64#num#(int64->byte)#int64)))`; `used:int64`; r2;
                 `((W:(num->num)->A->num->num) cw v,ns,stk):pstate`] PL_DRV_BRIDGE_ALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      MP_TAC(SPECL [`P:(int64 list)list`; `st:int64 list`] PL_TH_LAST_MEM) THEN ASM_SIMP_TAC[];
      MESON_TAC[PL_REL_CW2]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `s':pstate` THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
  MP_TAC(ISPECL [`P:(int64 list)list`; `0 + LENGTH (pfx:(int64 list)list)`;
                 `((W:(num->num)->A->num->num) cw v,ns,stk):pstate`; `k:num`; `j:num`; `s':pstate`] PL_RUN_GROWS) THEN
  REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`;
                   `FST(SND(SND(r1:int64#num#(int64->byte)#int64)))`;
                   `((W:(num->num)->A->num->num) cw v,ns,stk):pstate`] PL_REL_CW2) THEN
    ASM_REWRITE_TAC[FST]]);;

(* ------------------------------------------------------------------------- *)
(* The plans that write no table, by computation on their data: the decode *)
(* plan, the operand prefixes, the count's increment, the header's and     *)
(* END's plans.                                                              *)
(* ------------------------------------------------------------------------- *)

let RD_LEAF_FACTS =
  [EQW_LEAF_WF; CUR_LEAF_WF; LEB_NEXT_LEAF_WF; INC_LEAF_WF; AT_END_LEAF_WF; LE8_NEXT_LEAF_WF;
   FNV_LEAF_WF; EQW_RW; CUR_RW; LEB_NEXT_RW; INC_RW; AT_END_RO; FNV_RO; LE8_NEXT_RW];;

let RD_ONLY_TAC_WITH facts plan_defs =
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_progs_ok] THEN STRIP_TAC THEN
  REWRITE_TAC([rd_only_ok; MEM; MEM_APPEND] @ plan_defs) THEN REWRITE_TAC[GSYM DISJ_ASSOC] THEN
  X_GEN_TAC `st:int64 list` THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC)) THEN TRY(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC facts THEN
  REWRITE_TAC[FORALL_UNWIND_THM2] THEN CONV_TAC STEP_EL_CONV2 THEN ASM_ARITH_TAC;;

let RD_ONLY_TAC = RD_ONLY_TAC_WITH RD_LEAF_FACTS;;

let RD_ONLY_DD = prove
 (`!progs nctl. rd_progs_ok progs /\ 21 < nctl ==> rd_only_ok progs nctl pl_plan_dd`,
  RD_ONLY_TAC [pl_plan_dd]);;

let RD_ONLY_PREFIX_OP0 = prove
 (`!progs nctl. progs 3 = eqw /\ rd_progs_ok progs /\ 24 < nctl ==> rd_only_ok progs nctl pl_prefix_op0`,
  RD_ONLY_TAC [pl_prefix_op0]);;

let RD_ONLY_PREFIX_OP01 = prove
 (`!progs nctl. progs 3 = eqw /\ rd_progs_ok progs /\ 24 < nctl ==> rd_only_ok progs nctl pl_prefix_op01`,
  RD_ONLY_TAC [pl_prefix_op01; pl_prefix_op0]);;

let RD_ONLY_INC_CNT = prove
 (`!progs nctl. rd_progs_ok progs /\ 17 < nctl ==> rd_only_ok progs nctl pl_inc_cnt`,
  RD_ONLY_TAC [pl_inc_cnt]);;

let RD_ONLY_END = prove
 (`!progs nctl. progs 3 = eqw /\ progs 22 = fnv /\ rd_progs_ok progs /\ progs 29 = le8_next /\
                progs 30 = at_end /\ 30 < nctl
                ==> rd_only_ok progs nctl pl_plan_end`,
  RD_ONLY_TAC [pl_plan_end; pl_end_a; pl_end_b; pl_end_c; pl_end_d]);;

(* ------------------------------------------------------------------------- *)
(* A table plan's steps: each leaf implements its semantics and keeps the  *)
(* relation when it does not fire, the built leaves by their bridges and   *)
(* the pending ones by premises; its append to the theorem rows last.       *)
(* ------------------------------------------------------------------------- *)

let PL_KEPTS = [PL_KEPT_INTERN_TY; PL_KEPT_INTERN_DB; PL_KEPT_PACK; PL_KEPT_UNPACK; PL_KEPT_EQW;
                PL_KEPT_ROW_WORD; PL_KEPT_LIVE; PL_KEPT_APPEND_TH];;

let PL_STEPS_TAC plan_def =
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_progs_ok; pl_cw_range; ALL; pl_leaf_impl; pl_leaf_kept] THEN
  STRIP_TAC THEN X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!f. 10 <= f /\ f < 18 ==> val(EL f (st:int64 list)) < nctl` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_const_app "MEM" (concl th))) THEN
  REWRITE_TAC[plan_def; MEM] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC)) THEN TRY(DISCH_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV)) THEN
  CONJ_TAC THEN
  FIRST(map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN
                       CONV_TAC(DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) THEN
                       ASM_REWRITE_TAC[] THEN NO_TAC) (PL_BRIDGES @ PL_KEPTS) @
        [FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN
                               CONV_TAC(DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) THEN
                               NO_TAC)]);;

let plan_steps plan_def pend =
  let plan = lhs(concl plan_def) in
  let rel = `plan_rel bw ctl nctl cfr` in
  let args = [rel; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`] in
  let impl_all = list_mk_icomb "ALL" [list_mk_icomb "pl_leaf_impl" (args @ [plan]); pend]
  and kept_all = list_mk_icomb "ALL" [list_mk_icomb "pl_leaf_kept" (args @ [plan]); pend] in
  let st = `st:int64 list` in
  let cncl = mk_forall(st, mk_imp(list_mk_icomb "MEM" [st; plan],
               mk_conj(list_mk_icomb "pl_impl" (args @ [st]), list_mk_icomb "pl_kept" (args @ [st])))) in
  let ant = list_mk_conj [`pl_progs_ok progs`; list_mk_icomb "pl_cw_range" [`nctl:num`; plan]; impl_all; kept_all] in
  prove(list_mk_forall([`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                        `cfr:int64`], mk_imp(ant, cncl)),
        PL_STEPS_TAC plan_def);;

let plan_th_last plan_def =
  let plan = lhs(concl plan_def) in
  prove(list_mk_icomb "pl_th_last" [plan],
        REWRITE_TAC[plan_def; pl_th_last] THEN CONV_TAC STEP_EL_CONV THEN REWRITE_TAC[NOT_CONS_NIL]);;

(* ------------------------------------------------------------------------- *)
(* The every-run contract of a kind's handler: whatever the outcome, the    *)
(* memory left is related to a state that grows the start's tables, or     *)
(* grows the state the record's native step reached.                        *)
(* ------------------------------------------------------------------------- *)

let kind_every = new_definition
 `kind_every progs bw ctl nctl budget cfr H op <=>
    !m used res cw ns stk inp c.
      drv_sem progs bw ctl budget cfr H 0 m used res /\
      plan_rel bw ctl nctl cfr m (cw,ns,stk) /\ pl_inv (cw,ns,stk) /\
      rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
      ==> ?s'. plan_rel bw ctl nctl cfr (FST(SND(SND res))) s' /\
               (pl_grows ns (FST(SND s')) \/
                cw 20 = 1 /\
                ?rec rest s0. holr_rec_enc rec = CONS op (TL (holr_rec_enc rec)) /\
                              rd_from inp c = APPEND (TL (holr_rec_enc rec)) rest /\
                              nat_step ns rec (FST(SND s0)) /\ pl_inv s0 /\
                              pl_grows (FST(SND s0)) (FST(SND s')))`;;

(* A kind's every-run contract from its compiled handler: HANDLER_EVERY at   *)
(* the kind's shape and plan, the static premises as KC_<KIND>'s, the       *)
(* pending leaves' keeping as premises; the native step's record as in      *)
(* CONTRACT_TAC.                                                             *)
let kind_every_of kc_th hdef (sh:op_shape) plan_def rel_th =
  let plan = lhs(concl plan_def) in
  let lifts, q, g = kind_lifts plan rel_th in
  let pend = kind_pend rel_th in
  let payloads = kind_payloads plan_def in
  let rd_ok = try Some (kind_rd_ok plan_def) with Failure _ -> None in
  let steps = plan_steps plan_def pend in
  let thlast = plan_th_last plan_def in
  let pfx_ok = if sh.sh_pfx = `pl_prefix_op0` then RD_ONLY_PREFIX_OP0 else RD_ONLY_PREFIX_OP01 in
  let vs, body = strip_forall(concl kc_th) in
  let ant, cncl = dest_imp body in
  let args = snd(strip_comb cncl) in
  let rel = `plan_rel bw ctl nctl cfr` in
  let kept = if dest_list pend = [] then [] else
    [list_mk_icomb "ALL" [list_mk_icomb "pl_leaf_kept" [rel; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
                                                       `budget:int64`; `cfr:int64`; plan]; pend]] in
  let body' = mk_imp(list_mk_conj(conjuncts ant @ kept), list_mk_icomb "kind_every" args) in
  let goal = list_mk_forall(filter (fun v -> vfree_in v body')
               [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`],
               body') in
  let ns_tuple = end_itlist (curry mk_pair) pl_ns_vars in
  let gen = ISPECL [sh.sh_pfx; sh.sh_d; sh.sh_w; sh.sh_l; plan; q; g; pend] HANDLER_EVERY in
  prove(goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN REWRITE_TAC[kind_every] THEN
    REPEAT GEN_TAC THEN SPEC_TAC(`ns:nstate`,`ns:nstate`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC pl_ns_vars THEN STRIP_TAC THEN
    MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                  `m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`;
                  ns_tuple; `stk:num list`; `inp:num list`; `c:num`] gen) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[hdef]) THEN
    ASM_REWRITE_TAC[lifts; payloads; thlast; sh.sh_reads; sh.sh_facts; ALL] THEN
    SUBGOAL_THEN `progs 3 = eqw` ASSUME_TAC THENL [ASM_MESON_TAC[pl_progs_ok]; ALL_TAC] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST [MATCH_MP_TAC pfx_ok THEN ASM_REWRITE_TAC[] THEN NO_TAC;
             MATCH_MP_TAC RD_ONLY_INC_CNT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
             MATCH_MP_TAC steps THEN ASM_REWRITE_TAC[ALL] THEN NO_TAC;
             (match rd_ok with Some th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC
                             | None -> NO_TAC);
             FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV HANDLER_NORM_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `s':pstate` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> EXISTS_TAC `s':pstate` THEN ASM_REWRITE_TAC[] THEN MP_TAC th) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> DISJ1_TAC THEN ACCEPT_TAC th) MP_TAC) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN DISJ2_TAC THEN
    TRY(FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [leb_fires] o
                      check (fun th -> is_const_app "leb_fires" (concl th)))) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if is_const_app "nat_step" (concl th)
                          then EXISTS_TAC (el 1 (snd(strip_comb(concl th)))) else failwith "") THEN
    MAP_EVERY EXISTS_TAC [`rest:num list`; `s2:pstate`] THEN
    REWRITE_TAC[holr_rec_enc; TL] THEN ASM_REWRITE_TAC[]);;

(* The header's plan writes no table (after reader_hdr.ml). *)
let RD_HDR_LEAF_FACTS = RD_LEAF_FACTS @
  [POL_MAX_LEAF_WF; CONST_NEXT_LEAF_WF; CONST_NEXT_RW; REWRITE_RULE[GSYM POL_MAX_DECLS] NO_DECLS_RW];;

let RD_ONLY_HDR = prove
 (`!progs nctl. progs 3 = eqw /\ rd_progs_ok progs /\ progs 31 = const_next /\ progs 20 = pol_max /\
                27 < nctl
                ==> rd_only_ok progs nctl pl_plan_hdr`,
  RD_ONLY_TAC_WITH RD_HDR_LEAF_FACTS
    [pl_plan_hdr;pl_hdr_b;pl_hdr_a;pl_hdr_v1;pl_hdr_v0;pl_hdr_p;pl_hdr_commit;pl_hdr_g]);;

(* The kinds with handler theorems, every run: their kind_every contracts. *)
let KE_REFL = kind_every_of KC_REFL pl_handler_refl op0_shape pl_plan_refl PL_REFL_REL;;
let KE_ASSUME = kind_every_of KC_ASSUME pl_handler_assume op0_shape pl_plan_assume PL_ASSUME_REL;;
let KE_TRANS = kind_every_of KC_TRANS pl_handler_trans op01_shape pl_plan_trans PL_TRANS_REL;;
let KE_EQMP = kind_every_of KC_EQMP pl_handler_eqmp op01_shape pl_plan_eqmp PL_EQMP_REL;;
let KE_MKCOMB = kind_every_of KC_MKCOMB pl_handler_mkcomb op01_shape pl_plan_mkcomb PL_MKCOMB_REL;;

(* Every theorem this file states, for the audits. *)
let handlers_every_theorems =
 ["PL_TH_LAST_MEM", PL_TH_LAST_MEM;
  "PL_REL_CW2", PL_REL_CW2;
  "HANDLER_EVERY", HANDLER_EVERY;
  "RD_ONLY_DD", RD_ONLY_DD;
  "RD_ONLY_PREFIX_OP0", RD_ONLY_PREFIX_OP0;
  "RD_ONLY_PREFIX_OP01", RD_ONLY_PREFIX_OP01;
  "RD_ONLY_INC_CNT", RD_ONLY_INC_CNT;
  "RD_ONLY_END", RD_ONLY_END;
  "RD_ONLY_HDR", RD_ONLY_HDR;
  "KE_REFL", KE_REFL;
  "KE_ASSUME", KE_ASSUME;
  "KE_TRANS", KE_TRANS;
  "KE_EQMP", KE_EQMP;
  "KE_MKCOMB", KE_MKCOMB];;
