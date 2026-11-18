(* The native initializer with its step-admission obligation discharged. *)
needs "native/hol/control_init_admission.ml";;

let cinit_admitted_basis = SPEC_ALL CINIT_X86;;

let cinit_admitted_goal =
  let ant,post = dest_imp(concl cinit_admitted_basis) in
  let conditions = conjuncts ant in
  let is_admission tm =
    let head,_ = strip_comb tm in
    is_const head && fst(dest_const head) = "ALL" &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "drv_step_ok")) tm in
  let checks = filter is_admission conditions in
  if length checks <> 1 then failwith "initializer step-admission boundary changed" else
  let extra = `slot + 1 < nbw /\ ~(val(ctl:int64) = 0) /\ val ctl MOD 8 = 0` in
  mk_imp(list_mk_conj(filter (fun tm -> not(is_admission tm)) conditions @ conjuncts extra),post);;

let CINIT_ADMITTED_X86 = GEN_ALL(prove(cinit_admitted_goal,
  STRIP_TAC THEN MATCH_MP_TAC cinit_admitted_basis THEN
  ASM_REWRITE_TAC[ALL] THEN MATCH_MP_TAC CINIT_STEP_OK THEN
  EXISTS_TAC `ctl:int64` THEN ASM_REWRITE_TAC[ARITH_RULE `0 < 1`]));;

let control_init_admitted_theorems =
  driver_control_layout_theorems @ control_init_admission_theorems @
  ["CINIT_ADMITTED_X86",CINIT_ADMITTED_X86];;

leaf_audit control_init_admitted_theorems control_init_admitted_theorems;;
