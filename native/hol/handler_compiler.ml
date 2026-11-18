(* ========================================================================= *)
(* The handler compiler: from a kind's plan and its PL_<KIND>_REL theorem,   *)
(* the kind's handler and its theorem, by instances of HANDLER_GEN. Nothing *)
(* here is trusted: each function builds a term and HOL proves it. A leaf   *)
(* a plan calls but that is not built yet stays a premise of the kind's    *)
(* handler theorem: its implementation (pl_leaf_impl) and the plan's frame  *)
(* (rd_plan_ok) when that needs the leaf's declarations.                     *)
(*                                                                           *)
(* Loaded after handlers.ml.                                                 *)
(* ========================================================================= *)

needs "native/hol/handlers.ml";;

(* The state's twelve components and their projections from s:pstate. *)
let pl_cw_var = `cw:num->num` and pl_stk_var = `stk:num list`;;
let pl_proj_ns ns i =
  let rec snds t n = if n = 0 then t else snds (mk_icomb(`SND:A#B->B`, t)) (n - 1) in
  if i < 9 then mk_icomb(`FST:A#B->A`, snds ns i) else snds ns 9;;
let pl_state_proj s =
  let ns = mk_icomb(`SND:A#B->B`, s) in
  let ns = mk_icomb(`FST:A#B->A`, ns) in
  (mk_icomb(`FST:A#B->A`, s), pl_cw_var) ::
  (mk_icomb(`SND:A#B->B`, mk_icomb(`SND:A#B->B`, s)), pl_stk_var) ::
  List.mapi (fun i v -> pl_proj_ns ns i, v) pl_ns_vars;;

(* Q and G of a kind from its PL_<KIND>_REL theorem: the FIRED clause's      *)
(* property of the new native state and the REFUSED condition, as functions *)
(* of the state; an operand x bound by a premise cw k = x becomes FST s k.   *)
let kind_qg rel_th =
  let _, body = strip_forall(concl rel_th) in
  let ant, cncl = dest_imp body in
  let ops = mapfilter (fun p ->
      let l, r = dest_eq p in
      let f, k = dest_comb l in
      if f = pl_cw_var && is_var r then (r, k) else failwith "not an operand") (conjuncts ant) in
  let fired, refused = dest_conj cncl in
  let s' , eb = dest_exists(rand fired) in
  let qb = lhand(lhand eb) in
  let gb = rand refused in
  let s = `s:pstate` and ns' = `ns':nstate` in
  let comps = pl_state_proj s in
  let opsub = map (fun (x, k) -> mk_comb(mk_icomb(`FST:A#B->A`, s), k), x) ops in
  let fst_snd_s' = mk_icomb(`FST:A#B->A`, mk_icomb(`SND:A#B->B`, s')) in
  let q = mk_abs(s, mk_abs(ns', vsubst (comps @ opsub) (subst [ns', fst_snd_s'] qb))) in
  let g = mk_abs(s, vsubst (comps @ opsub) gb) in
  q, g;;

(* plan_lifts P Q G from PL_<KIND>_REL. *)
let PL_LIFTS_TAC rel_th =
  REWRITE_TAC[plan_lifts] THEN REPEAT GEN_TAC THEN SPEC_TAC(`s:pstate`,`s:pstate`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; ALL] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC rel_th THEN ASM_MESON_TAC[];;

(* The leaves a kind's REL theorem still assumes (pl_leaf_impl premises). *)
let kind_pend rel_th =
  let _, body = strip_forall(concl rel_th) in
  let prems = conjuncts(fst(dest_imp body)) in
  let ns = mapfilter (fun p -> if is_const_app "pl_leaf_impl" p then rand p else failwith "") prems in
  mk_list(ns, `:num`);;

let kind_lifts plan rel_th =
  let q, g = kind_qg rel_th in
  let pend = kind_pend rel_th in
  prove(list_mk_icomb "plan_lifts" [plan; q; g; pend], PL_LIFTS_TAC rel_th), q, g;;

(* A plan's payloads are temporaries (control words 24 and up). *)
let kind_payloads plan_def =
  let plan = lhs(concl plan_def) in
  prove(mk_forall(`st:int64 list`, mk_imp(list_mk_icomb "MEM" [`st:int64 list`; plan],
                                          `24 <= val(EL 17 (st:int64 list))`)),
    GEN_TAC THEN REWRITE_TAC[plan_def; MEM] THEN
    REPEAT(DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC)) THEN TRY(DISCH_THEN SUBST1_TAC) THEN
    CONV_TAC STEP_EL_CONV2);;

let kind_rd_ok plan_def =
  let plan = lhs(concl plan_def) in
  prove(list_mk_forall([`progs:num->tisa_prog`; `nctl:num`],
          mk_imp(mk_conj(`pl_progs_ok progs`, list_mk_icomb "pl_cw_range" [`nctl:num`; plan]),
                 list_mk_icomb "rd_plan_ok" [`progs:num->tisa_prog`; `nctl:num`; plan])),
    RD_PLAN_OK_TAC plan_def);;

(* An operand shape: its prefix, decoding, words, length, and the facts      *)
(* HANDLER_GEN needs of them.                                                *)
type op_shape = { sh_pfx : term; sh_d : term; sh_w : term; sh_l : term; sh_reads : thm; sh_facts : thm };;

(* The normal form of a handler theorem's conclusion: beta, projections of  *)
(* the state tuple, a control word read where it was just written.          *)
let PL_SET_IDX = prove(`!(f:num->num) n v. pl_set f n v n = v`, REWRITE_TAC[pl_set]);;
let PL_SET_PT = prove(`!(f:num->num) n v k. pl_set f n v k = if k = n then v else f k`, REWRITE_TAC[pl_set]);;
(* A control word written at numeral n, read at numeral k. *)
let PL_SET_NUM_CONV tm =
  match tm with
    Comb(Comb(Comb(Comb(Const("pl_set",_),_),n),_),k) when is_numeral n && is_numeral k ->
      (GEN_REWRITE_CONV I [PL_SET_PT] THENC ONCE_DEPTH_CONV NUM_EQ_CONV THENC REWRITE_CONV[]) tm
  | _ -> failwith "PL_SET_NUM_CONV";;
(* Operand tuples of numbers split into their components (the state stays whole). *)
let EXISTS_NUMPAIR = INST_TYPE [`:num`,`:A`; `:num`,`:B`] EXISTS_PAIR_THM;;
let FORALL_NUMPAIR = INST_TYPE [`:num`,`:A`; `:num`,`:B`] FORALL_PAIR_THM;;
let HANDLER_NORM_CONV =
  TOP_DEPTH_CONV BETA_CONV THENC
  REWRITE_CONV[FST; SND; PL_SET_IDX; ok_snoc; enc_snoc; w_snoc; EXISTS_NUMPAIR; FORALL_NUMPAIR] THENC
  TOP_DEPTH_CONV PL_SET_NUM_CONV THENC REWRITE_CONV[];;
let bnorm t = rhs(concl(DEPTH_CONV BETA_CONV t));;

(* The handler of a kind: its definition and its theorem.                    *)
let kind_handler name (sh:op_shape) plan_def rel_th =
  let plan = lhs(concl plan_def) in
  let lifts, q, g = kind_lifts plan rel_th in
  (* rd_plan_ok is proved when every leaf the plan calls is built; otherwise *)
  (* it stays a premise of the handler theorem, as the pending leaves' do.   *)
  let payloads = kind_payloads plan_def in
  let rd_ok = try Some (kind_rd_ok plan_def) with Failure _ -> None in
  let hdef = new_definition(mk_eq(mk_var("pl_handler_" ^ name, `:(int64 list)list`),
               list_mk_icomb "APPEND" [sh.sh_pfx; list_mk_icomb "APPEND" [plan; `pl_inc_cnt`]])) in
  let ns_tuple = end_itlist (curry mk_pair) pl_ns_vars in
  let gen = ISPECL [sh.sh_pfx; sh.sh_d; sh.sh_w; sh.sh_l; plan; q; g; kind_pend rel_th] HANDLER_GEN in
  let gen = SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                   `m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`;
                   ns_tuple; `stk:num list`; `inp:num list`; `c:num`] gen in
  let ant, cncl = dest_imp(concl gen) in
  (* the premises the kind's facts discharge drop out; the drv_sem premise names the handler *)
  let discharged = conjuncts(concl sh.sh_reads) @ conjuncts(concl sh.sh_facts) @
                   [concl lifts; concl payloads] in
  let keep = filter (fun p -> not (exists (fun q -> aconv (bnorm p) (bnorm q)) discharged) &&
                              not (rd_ok <> None && is_const_app "rd_plan_ok" p)) (conjuncts ant) in
  let keep = map (fun p -> if is_const_app "drv_sem" p then
                             subst [lhs(concl hdef), list_mk_icomb "APPEND" [sh.sh_pfx; list_mk_icomb "APPEND" [plan; `pl_inc_cnt`]]] p
                           else p) keep in
  let goal_cncl = rhs(concl(HANDLER_NORM_CONV cncl)) in
  let body = mk_imp(list_mk_conj keep, goal_cncl) in
  let order = [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
               `m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`] @ pl_ns_vars @
              [`stk:num list`; `inp:num list`; `c:num`] in
  let fv = frees body in
  let goal = list_mk_forall(filter (fun v -> mem v fv) order @ filter (fun v -> not (mem v order)) fv, body) in
  let th = prove(goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC gen THEN
    RULE_ASSUM_TAC(REWRITE_RULE[hdef]) THEN
    ASM_REWRITE_TAC[lifts; payloads; sh.sh_reads; sh.sh_facts] THEN
    (match rd_ok with
       Some th -> ANTS_TAC THENL [MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]; ALL_TAC]
     | None -> ALL_TAC) THEN
    CONV_TAC(LAND_CONV HANDLER_NORM_CONV) THEN SIMP_TAC[]) in
  hdef, th, (lifts, payloads, rd_ok);;

(* ------------------------------------------------------------------------- *)
(* The operand shapes: one operand (OP0), two (OP0, OP1).                    *)
(* ------------------------------------------------------------------------- *)

let op0_shape = { sh_pfx = `pl_prefix_op0`; sh_d = `leb_fires`; sh_w = OP0_W; sh_l = OP0_L;
                  sh_reads = PREFIX_OP0_READS; sh_facts = OP0_SHAPE };;

let op01_shape =
  let reads = REWRITE_RULE[enc_reads] ENC_READS_OP01 in
  let pfx, d, w, l = match snd(strip_comb(concl reads)) with [a; b; c; e] -> a, b, c, e | _ -> failwith "op01" in
  let uniq = MATCH_MP (ISPECL [mk_icomb(`ok_snoc:(A->bool)->A#num->bool`, ENC_OK0); `enc_snoc (leb_enc:num->num list)`]
                              ENC_D_UNIQUE) (MATCH_MP ENC_UNIQUE_SNOC ENC_UNIQUE_OP0) in
  let inv = MP (ISPECL [OP0_W; `9`] W_INV_SNOC) (CONJ (CONJUNCT1(CONJUNCT2 OP0_SHAPE)) (ARITH_RULE `6 < 9`)) in
  let w17 = MP (ISPECL [OP0_W; `9`] W17_SNOC) (CONJ (CONJUNCT2(CONJUNCT2 OP0_SHAPE)) (ARITH_RULE `~(9 = 17)`)) in
  { sh_pfx = pfx; sh_d = d; sh_w = w; sh_l = l; sh_reads = reads; sh_facts = end_itlist CONJ [uniq; inv; w17] };;

(* ------------------------------------------------------------------------- *)
(* The kinds whose plans are proved: their handlers.                         *)
(* ------------------------------------------------------------------------- *)

let pl_handler_assume, HANDLER_ASSUME, _ = kind_handler "assume" op0_shape pl_plan_assume PL_ASSUME_REL;;
let pl_handler_trans, HANDLER_TRANS, _ = kind_handler "trans" op01_shape pl_plan_trans PL_TRANS_REL;;
let pl_handler_eqmp, HANDLER_EQMP, _ = kind_handler "eqmp" op01_shape pl_plan_eqmp PL_EQMP_REL;;
let pl_handler_mkcomb, HANDLER_MKCOMB, _ = kind_handler "mkcomb" op01_shape pl_plan_mkcomb PL_MKCOMB_REL;;

let handler_compiler_theorems =
 ["HANDLER_ASSUME", HANDLER_ASSUME; "HANDLER_TRANS", HANDLER_TRANS; "HANDLER_EQMP", HANDLER_EQMP;
  "HANDLER_MKCOMB", HANDLER_MKCOMB];;
