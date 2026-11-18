(* ========================================================================= *)
(* Concrete runs of drv_sem. One run of a plan from a concrete memory,      *)
(* step by step, with each step's canonical child: its 24 frame words      *)
(* written at cfr over the plan's memory. Each leaf run is evaluated        *)
(* by call-by-value reduction in the logic (the t-ISA evaluator's rules,    *)
(* the leaf programs and the drv_* definitions). The result is              *)
(*   |- drv_sem progs bw ctl budget cfr steps i m used res0                 *)
(* with res0 explicit; DRV_SEM_FUN (driver_det.ml) then gives every run's   *)
(* outcome. The caller adds the leaf programs and the memory's definitions  *)
(* to the evaluator (drv_eval_compset). drv_run_eval needs every step to    *)
(* FIRE; drv_run_eval_stop also ends at a step that does not, and is meant  *)
(* to be given a named memory's reads (drv_mem_read_rules), so the memory   *)
(* stays named in every state.                                               *)
(*                                                                           *)
(* Loaded after driver.ml.                                                   *)
(* ========================================================================= *)

needs "tisa/hol/tisa_p1_eval.ml";;

(* v < k (k a numeral) as a disjunction v = k-1 \/ ... \/ v = 0, one SUC at a time. *)
let rec DRV_LT_DISJ_CONV tm =
  match tm with
    Comb(Comb(Const("<",_),v),k) when is_var v && is_numeral k ->
      if dest_small_numeral k = 0 then SPEC v (CONJUNCT1 LT)
      else (RAND_CONV num_CONV THENC REWR_CONV (CONJUNCT2 LT) THENC RAND_CONV DRV_LT_DISJ_CONV) tm
  | _ -> failwith "DRV_LT_DISJ_CONV";;
let DRV_LT_EXPAND_CONV tm =
  (DRV_LT_DISJ_CONV THENC PURE_REWRITE_CONV[OR_CLAUSES] THENC ONCE_DEPTH_CONV NUM_SUC_CONV) tm;;

let DRV_SEM_NIL = prove
 (`!progs bw ctl budget cfr i m used.
     drv_sem progs bw ctl budget cfr [] i m used (word 1,i,m,used)`,
  REWRITE_TAC[drv_sem]);;

let DRV_SEM_FIRED_STEP = prove
 (`!progs bw ctl budget cfr st sts i j m used t k u m' used' res.
     ~(val budget < val used) /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok (progs (val(EL 0 st))) t /\
     tisa_run (progs (val(EL 0 st))) t = TStop k u /\ tisa_fword u 18 = word 1 /\
     tisa_fword u 21 = used' /\ drv_after ctl st u = m' /\ i + 1 = j /\
     drv_sem progs bw ctl budget cfr sts j m' used' res
     ==> drv_sem progs bw ctl budget cfr (CONS st sts) i m used res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[drv_sem] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`t:tisa_state`; `k:num`; `u:tisa_state`] THEN ASM_REWRITE_TAC[]);;

let DRV_FRAME_WRITE_OUTSIDE = prove
 (`!cfr frame m a. val cfr + 192 <= 2 EXP 64 /\ ~drv_stack cfr a
                   ==> write (bytes(cfr,192)) frame m a = (m:int64->byte) a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_WRITE_BYTES_OUTSIDE THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~drv_stack cfr a` THEN REWRITE_TAC[drv_stack] THEN ARITH_TAC);;

(* The evaluator: the t-ISA evaluator's rules plus the given ones. *)
let drv_eval_compset extra =
  let cs = Compute.bool_compset() in
  Compute.set_skip cs `COND:bool->A->A->A` (Some 1);
  Compute.add_thms
   ([tisa_norm; tisa_bool; tisa_canonical; tisa_narrow; tisa_root; tregs; tmem;
     tisa_frame; tisa_read; tisa_fword; tisa_base; tisa_len; tisa_setreg;
     tisa_store; tisa_setfword; tisa_fail; tisa_finish; tisa_binop;
     tisa_shift32; tisa_shift64; tisa_shift; tisa_extract; tisa_compare_at;
     tisa_compare; tisa_rhs; tisa_index; tisa_inside; tisa_ea; tisa_addr_mid;
     tisa_instr; tisa_then; tisa_fund; TISA_COUNT_ITER_EVAL; tisa_early_check;
     TISA_EARLY_ITER_EVAL; tisa_exec; tisa_region_ok; tisa_pair_ok; tisa_pairs_ok;
     tisa_decls_ok; tisa_init_ok; tisa_entry_ok; tisa_run; tisa_observe;
     tisa_zero_mem; TISA_READ_ZERO; TISA_READ_WRITE; TISA_WRITE_BYTES_APPLY;
     limb; MAP; FST; SND;
     drv_regs; drv_fw; drv_cw; drv_word; drv_after; TISA_WRITE_BYTES64] @ extra) cs;
  let word_ops =
   [`word:num->N word`,1; `val:N word->num`,1; `ival:N word->int`,1;
    `word_add:N word->N word->N word`,2; `word_sub:N word->N word->N word`,2;
    `word_mul:N word->N word->N word`,2; `word_and:N word->N word->N word`,2;
    `word_or:N word->N word->N word`,2; `word_xor:N word->N word->N word`,2;
    `word_shl:N word->num->N word`,2; `word_ushr:N word->num->N word`,2;
    `word_ishr:N word->num->N word`,2; `word_zx:N word->M word`,1;
    `word_sx:N word->M word`,1; `iword:int->N word`,1] in
  List.iter (fun (c,n) -> Compute.add_conv (c,n,WORD_RED_CONV) cs) word_ops;
  let num_ops =
   [`(+):num->num->num`,2; `(-):num->num->num`,2; `( * ):num->num->num`,2;
    `(DIV):num->num->num`,2; `(MOD):num->num->num`,2; `(EXP):num->num->num`,2;
    `(<):num->num->bool`,2; `(<=):num->num->bool`,2; `SUC`,1] in
  List.iter (fun (c,n) -> Compute.add_conv (c,n,NUM_RED_CONV) cs) num_ops;
  let int_ops =
   [`(+):int->int->int`,2; `( * ):int->int->int`,2; `(<=):int->int->bool`,2;
    `(<):int->int->bool`,2; `(pow):int->num->int`,2; `(--):int->int`,1] in
  List.iter (fun (c,n) -> Compute.add_conv (c,n,INT_RED_CONV) cs) int_ops;
  Compute.add_conv (`(=):A->A->bool`,2,TISA_EQ_CONV) cs;
  Compute.add_conv (`EL:num->A list->A`,2,EL_CONV) cs;
  cs;;

(* |- tm = T, or fail. *)
let drv_eval_true conv tm =
  let th = conv tm in
  if rhs(concl th) = `T` then EQT_ELIM th else failwith ("drv_eval_true: " ^ string_of_term (rhs(concl th)));;

(* The canonical child of step st at memory m and receipt used, with |- drv_child ... t. *)
let drv_canon_child conv bw ctl budget cfr st m used =
  let fws = map (fun j -> rhs(concl(conv (list_mk_icomb "drv_fw" [bw; ctl; budget; used; st; m; mk_small_numeral j]))))
                (0--23) in
  let vals = map (fun w -> dest_numeral (rand w)) fws in
  let two64 = Num.power_num (Num.num_of_int 2) (Num.num_of_int 64) in
  let frame = itlist (fun n acc -> Num.add_num n (Num.mult_num acc two64)) vals (Num.num_of_int 0) in
  let mem = list_mk_icomb "write" [mk_comb(`bytes:int64#num->(int64->byte,num)component`, mk_pair(cfr, `192`));
                                   mk_numeral frame; m] in
  let t = list_mk_comb(`TState`, [list_mk_icomb "drv_regs" [cfr; ctl; st; m]; mem]) in
  let goal = list_mk_icomb "drv_child" [bw; ctl; budget; cfr; st; m; used; t] in
  let th = prove(goal,
    REWRITE_TAC[drv_child; tregs; tmem] THEN CONJ_TAC THENL
     [GEN_TAC THEN CONV_TAC(LAND_CONV DRV_LT_EXPAND_CONV) THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN CONV_TAC conv;
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC DRV_FRAME_WRITE_OUTSIDE THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC conv]) in
  t, th;;

(* One run of the steps from index i, memory m and receipt used; every step must be FIRED. *)
let drv_run_eval conv progs bw ctl budget cfr steps m0 used0 =
  let rec go i sts m used =
    match sts with
      [] -> ISPECL [progs; bw; ctl; budget; cfr; mk_small_numeral i; m; used] DRV_SEM_NIL
    | st :: rest ->
        let t, child = drv_canon_child conv bw ctl budget cfr st m used in
        let prog = mk_comb(progs, mk_icomb(`val:int64->num`, list_mk_icomb "EL" [`0`; st])) in
        let budget_ok = drv_eval_true conv (mk_neg(mk_binop `(<):num->num->bool`
                          (mk_icomb(`val:int64->num`, budget)) (mk_icomb(`val:int64->num`, used)))) in
        let entry = drv_eval_true conv (list_mk_icomb "tisa_entry_ok" [prog; t]) in
        let run = conv (list_mk_icomb "tisa_run" [prog; t]) in
        let k, u = dest_comb(rhs(concl run)) in
        let k = rand k in
        let s18 = conv (list_mk_icomb "tisa_fword" [u; `18`]) in
        if rhs(concl s18) <> `word 1:int64` then
          failwith (Printf.sprintf "drv_run_eval: step %d ended %s" i (string_of_term(rhs(concl s18)))) else
        let s21 = conv (list_mk_icomb "tisa_fword" [u; `21`]) in
        let after = conv (list_mk_icomb "drv_after" [ctl; st; u]) in
        let ij = NUM_ADD_CONV (mk_binop `(+):num->num->num` (mk_small_numeral i) `1`) in
        Printf.printf "DRV_EVAL step %d FIRED (leaf %s)\n%!" i (string_of_term (hd(dest_list st)));
        let rest_th = go (i + 1) rest (rhs(concl after)) (rhs(concl s21)) in
        let res = rand(concl rest_th) in
        let lem = ISPECL [progs; bw; ctl; budget; cfr; st; mk_list(rest, type_of st); mk_small_numeral i;
                          mk_small_numeral (i + 1); m; used; t; k; u; rhs(concl after); rhs(concl s21); res]
                         DRV_SEM_FIRED_STEP in
        MP lem (end_itlist CONJ [budget_ok; child; entry; run; s18; s21; after; ij; rest_th]) in
  go 0 steps m0 used0;;

(* ------------------------------------------------------------------------- *)
(* Runs that may stop: a step that does not FIRE ends the run with its      *)
(* outcome (DRV_SEM_STOP_STEP). And a memory named by a definition stays    *)
(* named in every state the run threads: the evaluator gets the memory's    *)
(* reads by the definition (drv_mem_read_rules), never the definition       *)
(* itself, which would unfold it into each state (a byte-write chain tens  *)
(* of thousands of levels deep after one plan, which no rewrite can walk).  *)
(* ------------------------------------------------------------------------- *)

let DRV_SEM_STOP_STEP = prove
 (`!progs bw ctl budget cfr st sts i m used t k u.
     ~(val budget < val used) /\ drv_child bw ctl budget cfr st m used t /\
     tisa_entry_ok (progs (val(EL 0 st))) t /\
     tisa_run (progs (val(EL 0 st))) t = TStop k u /\ ~(tisa_fword u 18 = word 1)
     ==> drv_sem progs bw ctl budget cfr (CONS st sts) i m used
                 (tisa_fword u 18, i, drv_after ctl st u, tisa_fword u 21)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[drv_sem] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`t:tisa_state`; `k:num`; `u:tisa_state`] THEN ASM_REWRITE_TAC[]);;

(* Reads of a memory constant, and of its bytes, by its definition. *)
let drv_mem_read_rules mdef =
  let d = SPEC_ALL mdef in
  let m = lhs(concl d) in
  let rd = rator(subst [m, `M:int64->byte`] `read (bytes(a:int64,n)) (M:int64->byte)`) in
  [GENL [`a:int64`; `n:num`] (AP_TERM rd d); GEN `x:int64` (AP_THM d `x:int64`)];;

(* A stopped step's result (status, i, memory, receipt), rebuilt in place   *)
(* from the evaluated status, memory and receipt.                            *)
let drv_tuple_eq s18 after s21 tup =
  let l1, r1 = dest_comb tup in
  let l2, r2 = dest_comb r1 in
  let l3, _ = dest_comb r2 in
  let e3 = MK_COMB(AP_TERM (rator l3) after, s21) in
  MK_COMB(AP_TERM (rator l1) s18, AP_TERM l2 e3);;

(* One run of the steps from memory m0 and receipt used0, to the plan's end *)
(* or to its first step that does not FIRE.                                 *)
let drv_run_eval_stop conv progs bw ctl budget cfr steps m0 used0 =
  let rec go i sts m used =
    match sts with
      [] -> ISPECL [progs; bw; ctl; budget; cfr; mk_small_numeral i; m; used] DRV_SEM_NIL
    | st :: rest ->
        let t, child = drv_canon_child conv bw ctl budget cfr st m used in
        let prog = mk_comb(progs, mk_icomb(`val:int64->num`, list_mk_icomb "EL" [`0`; st])) in
        let budget_ok = drv_eval_true conv (mk_neg(mk_binop `(<):num->num->bool`
                          (mk_icomb(`val:int64->num`, budget)) (mk_icomb(`val:int64->num`, used)))) in
        let entry = drv_eval_true conv (list_mk_icomb "tisa_entry_ok" [prog; t]) in
        let run = conv (list_mk_icomb "tisa_run" [prog; t]) in
        let k, u = dest_comb(rhs(concl run)) in
        let k = rand k in
        let s18 = conv (list_mk_icomb "tisa_fword" [u; `18`]) in
        let s21 = conv (list_mk_icomb "tisa_fword" [u; `21`]) in
        let after = conv (list_mk_icomb "drv_after" [ctl; st; u]) in
        if rhs(concl s18) <> `word 1:int64` then
          let ne = drv_eval_true conv (mk_neg(mk_eq(list_mk_icomb "tisa_fword" [u; `18`], `word 1:int64`))) in
          Printf.printf "DRV_EVAL step %d STOPPED with %s (leaf %s)\n%!" i
            (string_of_term(rhs(concl s18))) (string_of_term (hd(dest_list st)));
          let lem = ISPECL [progs; bw; ctl; budget; cfr; st; mk_list(rest, type_of st); mk_small_numeral i;
                            m; used; t; k; u] DRV_SEM_STOP_STEP in
          let th = MP lem (end_itlist CONJ [budget_ok; child; entry; run; ne]) in
          EQ_MP (AP_TERM (rator(concl th)) (drv_tuple_eq s18 after s21 (rand(concl th)))) th
        else
        let ij = NUM_ADD_CONV (mk_binop `(+):num->num->num` (mk_small_numeral i) `1`) in
        Printf.printf "DRV_EVAL step %d FIRED (leaf %s)\n%!" i (string_of_term (hd(dest_list st)));
        let rest_th = go (i + 1) rest (rhs(concl after)) (rhs(concl s21)) in
        let res = rand(concl rest_th) in
        let lem = ISPECL [progs; bw; ctl; budget; cfr; st; mk_list(rest, type_of st); mk_small_numeral i;
                          mk_small_numeral (i + 1); m; used; t; k; u; rhs(concl after); rhs(concl s21); res]
                         DRV_SEM_FIRED_STEP in
        MP lem (end_itlist CONJ [budget_ok; child; entry; run; s18; s21; after; ij; rest_th]) in
  go 0 steps m0 used0;;
