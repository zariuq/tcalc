(* ========================================================================= *)
(* HOL's instance of the general record loop: the invariant its handlers    *)
(* keep (the plans' pl_inv, names never dropped, FNVB the offset basis),    *)
(* its leaf table, and the handlers of the kinds whose plans run over its   *)
(* tables (hol_layout), each an instance of TAB_HANDLER_GEN whose lifts are *)
(* read off the kind's driver theorem PL_<KIND>_TAB.                         *)
(*                                                                           *)
(* Loaded after handlers_tab.ml and the tables_* kinds files.               *)
(* ========================================================================= *)

needs "native/hol/kernel_table_handler_basis_load.ml";;
needs "native/hol/protected_value_frame.ml";;

(* ------------------------------------------------------------------------- *)
(* HOL's instance of the record loop's parameters: the invariant (the plans' *)
(* pl_inv, names never dropped, FNVB the offset basis) and the leaf table.   *)
(* ------------------------------------------------------------------------- *)

let hol_core_inv = new_definition
 `hol_core_inv (s:pstate) <=>
    pl_inv s /\ (!j. ~MEM (0,j) (FST(SND(SND(SND(SND(SND(SND(SND(SND(FST(SND s)))))))))))) /\
    FST s 22 = val fnv_offset`;;

let HOL_CORE_INV = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     hol_core_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) <=>
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ (!j. ~MEM (0,j) drops) /\
     cw 22 = val fnv_offset`,
  REWRITE_TAC[hol_core_inv; FST; SND]);;

let hol_inv = new_definition
 `hol_inv (s:pstate) <=> hol_core_inv s /\ tab_value_fact 7 nat_policy s`;;

let HOL_INV = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     hol_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) <=>
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ (!j. ~MEM (0,j) drops) /\
     cw 22 = val fnv_offset /\ cw 7 = pol`,
  REWRITE_TAC[hol_inv;HOL_CORE_INV;tab_value_fact;nat_policy;FST;SND;CONJ_ASSOC]);;

let hol_progs = new_definition
 `hol_progs (progs:num->tisa_prog) <=>
    pl_progs_ok progs /\ progs 9 = put_word /\ progs 20 = pol_max /\ progs 22 = fnv /\ progs 23 = intern_name`;;

let TAB_SLOTS_HOL = prove
 (`tab_slots hol_layout =
   [0; 2; 4; 6; 8; 10; 12; 14; 16; 18; 20; 22; 24; 26; 28; 30; 32; 34; 44; 46; 48; 50; 54; 40; 42]`,
  REWRITE_TAC[tab_slots; hol_layout; hol_layout_old; APPEND] THEN
  REWRITE_TAC[ITLIST; tab_dslots; APPEND] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[APPEND] THEN CONV_TAC NUM_REDUCE_CONV);;

let NAME_RW = prove
 (`!r. tisa_rw (tisa_decls intern_name) r <=> r = 1 \/ r = 2 \/ r = 3 \/ r = 4`,
  GEN_TAC THEN REWRITE_TAC[NAME_DECLS; tisa_rw; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `r < 5` THENL
   [FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o
      MATCH_MP(ARITH_RULE `r < 5 ==> r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[FST] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* A plan writes only described slots other than the input, by computation *)
(* on its data under HOL's leaf table.                                       *)
let TAB_RD_PLAN_OK_TAC plan_def =
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_progs; pl_progs_ok; pl_cw_range; tab_rd_plan_ok] THEN STRIP_TAC THEN
  X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(EL 17 (st:int64 list)) < nctl` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "MEM" (concl th))) THEN
  REWRITE_TAC[plan_def; MEM] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC)) THEN TRY(DISCH_THEN SUBST1_TAC) THEN
  CONV_TAC STEP_EL_CONV2 THEN
  ASM_REWRITE_TAC(PL_LEAVES_WF @ PL_LEAVES_RW @ [FNV_LEAF_WF; FNV_RO; NAME_LEAF_WF; NAME_RW; PUT_WORD_LEAF_WF;
                                                PUT_WORD_RW; POL_MAX_LEAF_WF; POL_MAX_RO]) THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`; FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  CONV_TAC STEP_EL_CONV2 THEN REWRITE_TAC[TAB_SLOTS_HOL; MEM] THEN CONV_TAC NUM_REDUCE_CONV;;

let tab_rd_plan_ok_hol plan_def =
  let plan = lhs(concl plan_def) in
  prove(list_mk_forall([`progs:num->tisa_prog`; `nctl:num`],
          mk_imp(mk_conj(`hol_progs progs`, list_mk_icomb "pl_cw_range" [`nctl:num`; plan]),
                 list_mk_icomb "tab_rd_plan_ok" [`hol_layout`; `progs:num->tisa_prog`; `nctl:num`; plan])),
        TAB_RD_PLAN_OK_TAC plan_def);;

(* A plan's control words bound nctl from below: its first step's payload  *)
(* is a temporary (24 and up).                                               *)
let plan_nctl plan_def =
  let plan = lhs(concl plan_def) in
  let st0 = hd(dest_list(rhs(concl plan_def))) in
  prove(mk_forall(`nctl:num`, mk_imp(list_mk_icomb "pl_cw_range" [`nctl:num`; plan], `24 < nctl`)),
        GEN_TAC THEN REWRITE_TAC[pl_cw_range; plan_def; MEM] THEN
        DISCH_THEN(MP_TAC o SPECL [st0; `17`]) THEN CONV_TAC STEP_EL_CONV2 THEN ARITH_TAC);;

(* Reader updates preserve the constants, the policy word and FNVB. *)
let HOL_INV_SET = prove
 (`!cw (s:nstate) stk j v. hol_inv (cw,s,stk) /\ 7 < j /\ ~(j = 22) ==> hol_inv (pl_set cw j v,s,stk)`,
  REWRITE_TAC[FORALL_PAIR_THM; HOL_INV] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PL_INV_SET;ARITH_RULE `7 < j ==> 6 < j`] THEN ASM_REWRITE_TAC[pl_set] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A kind's plan lifts (tab_lifts) under HOL's invariant, from its driver   *)
(* theorem PL_<KIND>_TAB: Q is the kind's native step from the operands in  *)
(* OP0.., G its guards' failure, read off the theorem.                       *)
(* ------------------------------------------------------------------------- *)

let hol_lift_parts kind_th =
  let _, body = strip_forall(concl kind_th) in
  let ant, cncl = dest_imp body in
  let ops = mapfilter (fun p -> let l, r = dest_eq p in
                         let f, k = dest_comb l in
                         if f = pl_cw_var && is_var r then (r, k) else failwith "not an operand") (conjuncts ant) in
  let fired, refused = dest_conj cncl in
  let s', eb = dest_exists(rand fired) in
  let s = `s:pstate` and ns' = `ns':nstate` in
  let fst_snd t = mk_icomb(`FST:A#B->A`, mk_icomb(`SND:A#B->B`, t)) in
  let tidy t = vsubst (pl_state_proj s @ map (fun (x, k) -> mk_comb(mk_icomb(`FST:A#B->A`, s), k), x) ops)
                      (subst [fst_snd s, end_itlist (curry mk_pair) pl_ns_vars] t) in
  let q = list_mk_abs([`inp:num list`; s; ns'], tidy(subst [ns', fst_snd s'] (lhand(lhand eb)))) in
  let g = list_mk_abs([`inp:num list`; s], tidy(rand refused)) in
  ops, q, g;;

let TAB_LIFTS_CORE_TAC kind_th plan rdok_th payloads_th nctl_th : tactic = fun gl ->
  let ops, _, _ = hol_lift_parts kind_th in
  let sv = pl_cw_var :: pl_ns_vars @ [pl_stk_var] in
  let st = mk_pair(pl_cw_var, mk_pair(end_itlist (curry mk_pair) pl_ns_vars, pl_stk_var)) in
  let res = `res:int64#num#(int64->byte)#int64` in
  let kth = INST (map (fun (x, k) -> (mk_comb(pl_cw_var, k), x)) ops) (SPEC_ALL kind_th) in
  (REWRITE_TAC[tab_lifts] THEN
   MAP_EVERY X_GEN_TAC [`inp:num list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                        `budget:int64`; `cfr:int64`; `m:int64->byte`; `used:int64`; res] THEN
   REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC sv THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND; HOL_CORE_INV; hol_progs] THEN STRIP_TAC THEN
   MP_TAC kth THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(TAUT `(a ==> a') ==> (a /\ b ==> a' /\ b)`) THEN
   DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC(MP th (ASSUME (mk_eq(mk_icomb(`FST:A#B->A`, res), `word 1:int64`))))) THEN
   DISCH_THEN(X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC) THEN EXISTS_TAC `s':pstate` THEN
   ASM_REWRITE_TAC[hol_core_inv] THEN CONJ_TAC THENL
    [(* names: the native step drops none *)
     FIRST_ASSUM(MP_TAC o MATCH_MP NAT_STEP_NAMES_KEPT o check (is_const_app "nat_step" o concl)) THEN
     REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[];
     (* FNVB: no step of the plan writes word 22 *)
     SUBGOAL_THEN `22 < nctl` ASSUME_TAC THENL
      [MATCH_MP_TAC(ARITH_RULE `24 < n ==> 22 < n`) THEN MATCH_MP_TAC nctl_th THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     SUBGOAL_THEN (list_mk_icomb "tab_rd_plan_ok" [`hol_layout`; `progs:num->tisa_prog`; `nctl:num`; plan])
       ASSUME_TAC THENL [MATCH_MP_TAC rdok_th THEN ASM_REWRITE_TAC[hol_progs]; ALL_TAC] THEN
     FIRST_ASSUM(fun th -> if is_const_app "tab_rel" (concl th) && rand(concl th) = st
                           then STRIP_ASSUME_TAC(MATCH_MP TAB_REL_LAYOUT th) else failwith "") THEN
     MP_TAC(ISPECL [`hol_tables`; `hol_layout`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                    `cfr:int64`; `FST(SND(SND(res:int64#num#(int64->byte)#int64)))`; `s':pstate`; `22`] TAB_REL_CW) THEN
     MP_TAC(ISPECL [`hol_tables`; `hol_layout`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                    `cfr:int64`; `m:int64->byte`; st; `22`] TAB_REL_CW) THEN
     MP_TAC(SPECL [`hol_layout`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                   `budget:int64`; `cfr:int64`; plan; `0`; `m:int64->byte`; `used:int64`; res; `22`]
                  TAB_PLAN_CW_KEPT) THEN
     ASM_REWRITE_TAC[FST] THEN
     ANTS_TAC THENL [GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP payloads_th) THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN REFL_TAC]) gl;;

let tab_lifts_hol kind_th plan_def =
  let plan = lhs(concl plan_def) in
  let _, q, g = hol_lift_parts kind_th in
  let rdok = tab_rd_plan_ok_hol plan_def and payloads = kind_payloads plan_def and nctl = plan_nctl plan_def in
  let core = prove(list_mk_icomb "tab_lifts" [`hol_tables`; `hol_layout`; `hol_progs`; plan; q; g; `hol_core_inv`],
                   TAB_LIFTS_CORE_TAC kind_th plan rdok payloads nctl) in
  let kept_goal = list_mk_forall([`inp:num list`;`before:pstate`;`following:nstate`],
    mk_imp(list_mk_comb(q,[`inp:num list`;`before:pstate`;`following:nstate`]),
      `nat_policy following = nat_policy(FST(SND(before:pstate)))`)) in
  let kept = prove(kept_goal,
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP NAT_STEP_POLICY_KEPT o check (is_const_app "nat_step" o concl)) THEN
    REWRITE_TAC[distinctness "holr_record"]) in
  let th = REWRITE_RULE[GSYM hol_inv;ETA_AX]
    (tab_lift_small_value 7 `nat_policy` core rdok nctl payloads kept) in
  th, rdok, payloads, nctl;;

(* ------------------------------------------------------------------------- *)
(* Operand shapes over the tables: one operand (OP0), two (OP0, OP1), and   *)
(* NAME's bytes; the leaf table's need beyond the reader's, skip at 28.     *)
(* ------------------------------------------------------------------------- *)

let HOL_R = `\progs:num->tisa_prog. progs 28 = skip`;;

let TAB_ENC_READS_OP0 = prove
 (list_mk_forall([`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
                  `L:tabdesc list`; `R:(num->tisa_prog)->bool`],
   list_mk_icomb "tab_enc_reads"
     [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
      `L:tabdesc list`; `R:(num->tisa_prog)->bool`; `pl_prefix_op0`; ENC_OK0; `leb_enc`; OP0_WC]),
  SUBGOAL_THEN `leb_fires = (\bs v. (\v:num. v < 2 EXP 62) v /\ ?rest. bs = APPEND (leb_enc v) rest)` MP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; leb_fires]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(REWRITE_RULE[th] TAB_PREFIX_OP0_RD)) THEN
  REWRITE_TAC[tab_enc_reads] THEN DISCH_THEN ACCEPT_TAC);;

let TAB_ENC_READS_OP01 =
  let th = ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
                   `L:tabdesc list`; `R:(num->tisa_prog)->bool`; `pl_prefix_op0`; ENC_OK0; `leb_enc`; OP0_WC; `9`]
                  TAB_ENC_READS_SNOC in
  let th = MP th (end_itlist CONJ [SPEC_ALL TAB_ENC_READS_OP0; ENC_UNIQUE_OP0; ARITH_RULE `6 < 9`; ARITH_RULE `9 < 24`]) in
  GEN_ALL(REWRITE_RULE[GSYM pl_prefix_op01] th);;

type tab_shape = { ts_pfx : term; ts_d : term; ts_w : term; ts_l : term; ts_rd : thm; ts_uniq : thm };;

let tab_op0_shape =
  { ts_pfx = `pl_prefix_op0`; ts_d = `leb_fires`; ts_w = OP0_WC; ts_l = OP0_L;
    ts_rd = ISPECL [`hol_tables`; `hol_layout`; HOL_R] TAB_PREFIX_OP0_RD; ts_uniq = LEB_FIRES_UNIQUE };;

let tab_op01_shape =
  let rd = REWRITE_RULE[tab_enc_reads] (ISPECL [`hol_tables`; `hol_layout`; HOL_R] TAB_ENC_READS_OP01) in
  let pfx, d, w, l = match snd(strip_comb(concl rd)) with [_; _; _; a; b; c; e] -> a, b, c, e | _ -> failwith "op01" in
  let uniq = MATCH_MP (ISPECL [mk_icomb(`ok_snoc:(A->bool)->A#num->bool`, ENC_OK0); `enc_snoc (leb_enc:num->num list)`]
                              ENC_D_UNIQUE) (MATCH_MP ENC_UNIQUE_SNOC ENC_UNIQUE_OP0) in
  { ts_pfx = pfx; ts_d = d; ts_w = w; ts_l = l; ts_rd = rd; ts_uniq = uniq };;

let tab_name_shape =
  { ts_pfx = `pl_prefix_name`; ts_d = `name_fires`; ts_w = NAME_WC; ts_l = NAME_L;
    ts_rd = ISPECL [`hol_tables`; `hol_layout`] TAB_PREFIX_NAME_RD; ts_uniq = NAME_FIRES_UNIQUE };;

(* ------------------------------------------------------------------------- *)
(* The handler of a kind over HOL's tables: its definition (the prefix, the *)
(* plan, the count's increment) and its theorem, an instance of             *)
(* TAB_HANDLER_GEN whose closed premises are proved here.                    *)
(* ------------------------------------------------------------------------- *)

let TAB_HANDLER_NORM_CONV =
  TOP_DEPTH_CONV BETA_CONV THENC
  REWRITE_CONV[tab_w_snoc; ok_snoc; enc_snoc; EXISTS_NUMPAIR; FORALL_NUMPAIR] THENC
  TOP_DEPTH_CONV BETA_CONV THENC REWRITE_CONV[FST; SND; PL_SET_IDX] THENC
  TOP_DEPTH_CONV PL_SET_NUM_CONV THENC REWRITE_CONV[];;

(* The closed premises: the prefix, the decoding's uniqueness, the words'   *)
(* and the count's keeping of the invariant and of CNT, the lifts, the      *)
(* payloads.                                                                  *)
let TAB_STATIC_TAC (sh:tab_shape) lifts payloads : tactic =
  let w_tac = REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[tab_w_snoc] THEN
              CONV_TAC(TOP_DEPTH_CONV BETA_CONV) in
  FIRST [ACCEPT_TAC sh.ts_rd; ACCEPT_TAC lifts; ACCEPT_TAC payloads;
         GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `st:int64 list` payloads) THEN
         ASM_REWRITE_TAC[] THEN ARITH_TAC THEN NO_TAC;
         CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MATCH_ACCEPT_TAC sh.ts_uniq;
         w_tac THEN DISCH_TAC THEN
         REPEAT(MATCH_MP_TAC HOL_INV_SET THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]) THEN
         ASM_REWRITE_TAC[] THEN NO_TAC;
         w_tac THEN CONV_TAC(TOP_DEPTH_CONV PL_SET_NUM_CONV) THEN REWRITE_TAC[] THEN NO_TAC];;

(* A kind's handler: the old loop's definition when it has one (the same  *)
(* program), else a new one.                                                 *)
let tab_handler_def name hbody =
  let nm = "pl_handler_" ^ name in
  if can get_const_type nm then
    let th = find (fun th -> try fst(dest_const(lhs(concl th))) = nm with Failure _ -> false) (definitions()) in
    if aconv (rhs(concl th)) hbody then th else failwith ("tab_handler_def: " ^ nm ^ " is another program")
  else new_definition(mk_eq(mk_var(nm, `:(int64 list)list`), hbody));;

let tab_kind_handler name (sh:tab_shape) plan_def (lifts, rdok, payloads, nctl) =
  let plan = lhs(concl plan_def) in
  let q, g = match snd(strip_comb(concl lifts)) with [_; _; _; _; q; g; _] -> q, g | _ -> failwith "lifts" in
  let hbody = list_mk_icomb "APPEND" [sh.ts_pfx; list_mk_icomb "APPEND" [plan; `pl_inc_cnt`]] in
  let hdef = tab_handler_def name hbody in
  let gen = SPEC_ALL(ISPECL [`hol_tables`; `hol_layout`; HOL_R; sh.ts_pfx; sh.ts_d; sh.ts_w; sh.ts_l;
                             `hol_progs`; plan; q; g; `hol_inv`] TAB_HANDLER_GEN) in
  let ant, cncl = dest_imp(concl gen) in
  let statics = filter (fun p -> frees p = []) (conjuncts ant) in
  let static_ths = map (fun p -> prove(p, TAB_STATIC_TAC sh lifts payloads)) statics in
  let derived p = is_const_app "tab_rd_plan_ok" p || p = `(progs:num->tisa_prog) 3 = eqw` || p = `24 < nctl` in
  let keep = filter (fun p -> frees p <> [] && not (derived p)) (conjuncts ant) in
  let keep = map (fun p -> if is_const_app "drv_sem" p then subst [lhs(concl hdef), hbody] p
                           else rhs(concl(TOP_DEPTH_CONV BETA_CONV p))) keep in
  let goal_cncl = rhs(concl(TAB_HANDLER_NORM_CONV cncl)) in
  let body = mk_imp(list_mk_conj keep, goal_cncl) in
  let order = [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
               `m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`; `s:nstate`;
               `stk:num list`; `inp:num list`; `c:num`] in
  let fv = frees body in
  let goal = list_mk_forall(filter (fun v -> mem v fv) order @ filter (fun v -> not (mem v order)) fv, body) in
  let th = prove(goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC gen THEN
    RULE_ASSUM_TAC(REWRITE_RULE[hdef]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[hol_progs; pl_progs_ok] o check (is_const_app "hol_progs" o concl)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP nctl o check (is_const_app "pl_cw_range" o concl)) THEN
    SUBGOAL_THEN (list_mk_icomb "tab_rd_plan_ok" [`hol_layout`; `progs:num->tisa_prog`; `nctl:num`; plan]) ASSUME_TAC THENL
     [MATCH_MP_TAC rdok THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC static_ths THEN
    CONV_TAC(LAND_CONV TAB_HANDLER_NORM_CONV) THEN SIMP_TAC[]) in
  hdef, th;;

(* ------------------------------------------------------------------------- *)
(* The nine kinds over HOL's tables.                                         *)
(* ------------------------------------------------------------------------- *)

let LF_TYVAR = tab_lifts_hol PL_TYVAR_TAB pl_plan_tyvar;;
let TAB_LIFTS_TYVAR, TAB_RD_PLAN_OK_TYVAR, TYVAR_PAYLOADS, TYVAR_NCTL = LF_TYVAR;;
let pl_handler_tyvar, HANDLER_TYVAR_TAB = tab_kind_handler "tyvar" tab_op0_shape pl_plan_tyvar LF_TYVAR;;
let LF_VAR = tab_lifts_hol PL_VAR_TAB pl_plan_var;;
let TAB_LIFTS_VAR, TAB_RD_PLAN_OK_VAR, VAR_PAYLOADS, VAR_NCTL = LF_VAR;;
let pl_handler_var, HANDLER_VAR_TAB = tab_kind_handler "var" tab_op01_shape pl_plan_var LF_VAR;;
let LF_NAME = tab_lifts_hol PL_NAME_TAB pl_plan_name;;
let TAB_LIFTS_NAME, TAB_RD_PLAN_OK_NAME, NAME_PAYLOADS, NAME_NCTL = LF_NAME;;
let pl_handler_name, HANDLER_NAME_TAB = tab_kind_handler "name" tab_name_shape pl_plan_name LF_NAME;;
let LF_REFL = tab_lifts_hol PL_REFL_TAB pl_plan_refl;;
let TAB_LIFTS_REFL, TAB_RD_PLAN_OK_REFL, _, REFL_NCTL = LF_REFL;;
let _, HANDLER_REFL_TAB = tab_kind_handler "refl" tab_op0_shape pl_plan_refl LF_REFL;;
let LF_ASSUME = tab_lifts_hol PL_ASSUME_TAB pl_plan_assume;;
let TAB_LIFTS_ASSUME, TAB_RD_PLAN_OK_ASSUME, ASSUME_PAYLOADS, ASSUME_NCTL = LF_ASSUME;;
let _, HANDLER_ASSUME_TAB = tab_kind_handler "assume" tab_op0_shape pl_plan_assume LF_ASSUME;;
let LF_EMIT = tab_lifts_hol PL_EMIT_TAB pl_plan_emit;;
let TAB_LIFTS_EMIT, TAB_RD_PLAN_OK_EMIT, EMIT_PAYLOADS, EMIT_NCTL = LF_EMIT;;
let pl_handler_emit, HANDLER_EMIT_TAB = tab_kind_handler "emit" tab_op0_shape pl_plan_emit LF_EMIT;;
let LF_COMB = tab_lifts_hol PL_COMB_TAB pl_plan_comb;;
let TAB_LIFTS_COMB, TAB_RD_PLAN_OK_COMB, COMB_PAYLOADS, COMB_NCTL = LF_COMB;;
let pl_handler_comb, HANDLER_COMB_TAB = tab_kind_handler "comb" tab_op01_shape pl_plan_comb LF_COMB;;
let LF_BETA = tab_lifts_hol PL_BETA_TAB pl_plan_beta;;
let TAB_LIFTS_BETA, TAB_RD_PLAN_OK_BETA, BETA_PAYLOADS, BETA_NCTL = LF_BETA;;
let pl_handler_beta, HANDLER_BETA_TAB = tab_kind_handler "beta" tab_op0_shape pl_plan_beta LF_BETA;;
let LF_LABEL = tab_lifts_hol PL_LABEL_TAB pl_plan_label;;
let TAB_LIFTS_LABEL, TAB_RD_PLAN_OK_LABEL, LABEL_PAYLOADS, LABEL_NCTL = LF_LABEL;;
let pl_handler_label, HANDLER_LABEL_TAB = tab_kind_handler "label" tab_op01_shape pl_plan_label LF_LABEL;;
let LF_DROP_TYPE = tab_lifts_hol PL_DROP_TYPE_TAB pl_plan_drop_type;;
let TAB_LIFTS_DROP_TYPE, TAB_RD_PLAN_OK_DROP_TYPE, DROP_TYPE_PAYLOADS, DROP_TYPE_NCTL = LF_DROP_TYPE;;
let pl_handler_drop_type, HANDLER_DROP_TYPE_TAB = tab_kind_handler "drop_type" tab_op0_shape pl_plan_drop_type LF_DROP_TYPE;;
let LF_DROP_TERM = tab_lifts_hol PL_DROP_TERM_TAB pl_plan_drop_term;;
let TAB_LIFTS_DROP_TERM, TAB_RD_PLAN_OK_DROP_TERM, DROP_TERM_PAYLOADS, DROP_TERM_NCTL = LF_DROP_TERM;;
let pl_handler_drop_term, HANDLER_DROP_TERM_TAB = tab_kind_handler "drop_term" tab_op0_shape pl_plan_drop_term LF_DROP_TERM;;
let LF_DROP_THM = tab_lifts_hol PL_DROP_THM_TAB pl_plan_drop_thm;;
let TAB_LIFTS_DROP_THM, TAB_RD_PLAN_OK_DROP_THM, DROP_THM_PAYLOADS, DROP_THM_NCTL = LF_DROP_THM;;
let pl_handler_drop_thm, HANDLER_DROP_THM_TAB = tab_kind_handler "drop_thm" tab_op0_shape pl_plan_drop_thm LF_DROP_THM;;

(* Every theorem this file states, for the audits. *)
let handlers_hol_theorems =
 ["HOL_CORE_INV", HOL_CORE_INV;"HOL_INV", HOL_INV; "TAB_SLOTS_HOL", TAB_SLOTS_HOL; "NAME_RW", NAME_RW; "HOL_INV_SET", HOL_INV_SET;
  "TAB_ENC_READS_OP0", TAB_ENC_READS_OP0; "TAB_ENC_READS_OP01", TAB_ENC_READS_OP01;
  "TAB_LIFTS_TYVAR", TAB_LIFTS_TYVAR; "TAB_RD_PLAN_OK_TYVAR", TAB_RD_PLAN_OK_TYVAR;
  "TYVAR_PAYLOADS", TYVAR_PAYLOADS; "TYVAR_NCTL", TYVAR_NCTL; "HANDLER_TYVAR_TAB", HANDLER_TYVAR_TAB;
  "TAB_LIFTS_VAR", TAB_LIFTS_VAR; "TAB_RD_PLAN_OK_VAR", TAB_RD_PLAN_OK_VAR; "VAR_PAYLOADS", VAR_PAYLOADS;
  "VAR_NCTL", VAR_NCTL; "HANDLER_VAR_TAB", HANDLER_VAR_TAB; "TAB_LIFTS_NAME", TAB_LIFTS_NAME;
  "TAB_RD_PLAN_OK_NAME", TAB_RD_PLAN_OK_NAME; "NAME_PAYLOADS", NAME_PAYLOADS; "NAME_NCTL", NAME_NCTL;
  "HANDLER_NAME_TAB", HANDLER_NAME_TAB; "TAB_LIFTS_REFL", TAB_LIFTS_REFL;
  "TAB_RD_PLAN_OK_REFL", TAB_RD_PLAN_OK_REFL; "REFL_NCTL", REFL_NCTL; "HANDLER_REFL_TAB", HANDLER_REFL_TAB;
  "TAB_LIFTS_ASSUME", TAB_LIFTS_ASSUME; "TAB_RD_PLAN_OK_ASSUME", TAB_RD_PLAN_OK_ASSUME;
  "ASSUME_PAYLOADS", ASSUME_PAYLOADS; "ASSUME_NCTL", ASSUME_NCTL; "HANDLER_ASSUME_TAB", HANDLER_ASSUME_TAB;
  "TAB_LIFTS_EMIT", TAB_LIFTS_EMIT; "TAB_RD_PLAN_OK_EMIT", TAB_RD_PLAN_OK_EMIT; "EMIT_PAYLOADS", EMIT_PAYLOADS;
  "EMIT_NCTL", EMIT_NCTL; "HANDLER_EMIT_TAB", HANDLER_EMIT_TAB; "TAB_LIFTS_COMB", TAB_LIFTS_COMB;
  "TAB_RD_PLAN_OK_COMB", TAB_RD_PLAN_OK_COMB; "COMB_PAYLOADS", COMB_PAYLOADS; "COMB_NCTL", COMB_NCTL;
  "HANDLER_COMB_TAB", HANDLER_COMB_TAB; "TAB_LIFTS_BETA", TAB_LIFTS_BETA;
  "TAB_RD_PLAN_OK_BETA", TAB_RD_PLAN_OK_BETA; "BETA_PAYLOADS", BETA_PAYLOADS; "BETA_NCTL", BETA_NCTL;
  "HANDLER_BETA_TAB", HANDLER_BETA_TAB; "TAB_LIFTS_LABEL", TAB_LIFTS_LABEL;
  "TAB_RD_PLAN_OK_LABEL", TAB_RD_PLAN_OK_LABEL; "LABEL_PAYLOADS", LABEL_PAYLOADS; "LABEL_NCTL", LABEL_NCTL;
  "HANDLER_LABEL_TAB", HANDLER_LABEL_TAB;
  "TAB_LIFTS_DROP_TYPE", TAB_LIFTS_DROP_TYPE; "TAB_RD_PLAN_OK_DROP_TYPE", TAB_RD_PLAN_OK_DROP_TYPE; "DROP_TYPE_PAYLOADS", DROP_TYPE_PAYLOADS;
  "DROP_TYPE_NCTL", DROP_TYPE_NCTL; "HANDLER_DROP_TYPE_TAB", HANDLER_DROP_TYPE_TAB;
  "TAB_LIFTS_DROP_TERM", TAB_LIFTS_DROP_TERM; "TAB_RD_PLAN_OK_DROP_TERM", TAB_RD_PLAN_OK_DROP_TERM; "DROP_TERM_PAYLOADS", DROP_TERM_PAYLOADS;
  "DROP_TERM_NCTL", DROP_TERM_NCTL; "HANDLER_DROP_TERM_TAB", HANDLER_DROP_TERM_TAB;
  "TAB_LIFTS_DROP_THM", TAB_LIFTS_DROP_THM; "TAB_RD_PLAN_OK_DROP_THM", TAB_RD_PLAN_OK_DROP_THM; "DROP_THM_PAYLOADS", DROP_THM_PAYLOADS;
  "DROP_THM_NCTL", DROP_THM_NCTL; "HANDLER_DROP_THM_TAB", HANDLER_DROP_THM_TAB];;
