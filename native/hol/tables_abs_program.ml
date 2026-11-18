(* ABS: guards, binding walk, function type, then term publication. *)
needs "native/hol/tables_abs_guards.ml";;

let pl_BIND = 10;;
let pl_BINDB = [6;8;10;42];;

(* The guard prefix uses payload words 24--27. *)
pl_buf := dest_list(rhs(concl pl_abs_guard_plan));;
pl_next := 28;;
let _ = let name = pl_f_tm pl_OP0 1 in
        let domain = pl_f_tm pl_OP0 3 in
        let codomain = pl_f_tm pl_OP1 3 in
        let body = pl_f_tm pl_OP1 4 in
        let image = pl_emit pl_BIND pl_BINDB name domain [body] in
        let tail = pl_ity 3 codomain 0 in
        let args = pl_ity 3 domain tail in
        let funty = pl_ity 1 1 args in
        pl_emit pl_APPEND pl_TM 3 pl_OP0 [5;pl_OP1;funty;image];;
let pl_plan_abs = new_definition(mk_eq(`pl_plan_abs:(int64 list)list`,pl_plan()));;

let ABS_PLAN_LENGTH = prove
 (`LENGTH pl_plan_abs = 16`,
  REWRITE_TAC[pl_plan_abs;LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let ABS_PLAN_GUARD_PREFIX = prove
 (`!i. i < 4 ==> EL i pl_plan_abs = EL i pl_abs_guard_plan`,
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[pl_plan_abs;pl_abs_guard_plan] THEN CONV_TAC STEP_EL_CONV2);;

let ABS_PLAN_BINDING = prove
 (`EL 8 pl_plan_abs =
     MAP (word:num->int64) [10;6;8;10;42;56;56;56;56;56;28;29;31;0;0;0;0;32]`,
  REWRITE_TAC[pl_plan_abs;MAP] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let ABS_PLAN_COMMIT_LAST = prove
 (`EL 15 pl_plan_abs =
     MAP (word:num->int64) [6;12;14;56;56;56;56;56;56;56;3;8;5;9;38;32;0;39] /\
   (!i. i < 15 ==> ~(val(EL 0 (EL i pl_plan_abs)) = 6))`,
  REWRITE_TAC[pl_plan_abs;MAP] THEN CONJ_TAC THENL
   [CONV_TAC(DEPTH_CONV EL_CONV) THEN REFL_TAC;
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC STEP_EL_CONV2]);;

let ABS_PLAN_ARGUMENT_RANGE = prove
 (`pl_cw_range 40 pl_plan_abs`,
  REWRITE_TAC[pl_cw_range;pl_plan_abs;MEM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN
  (SUBGOAL_THEN `f = 10 \/ f = 11 \/ f = 12 \/ f = 13 \/
                 f = 14 \/ f = 15 \/ f = 16 \/ f = 17`
     MP_TAC THENL [ASM_ARITH_TAC;ALL_TAC]) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC STEP_EL_CONV2);;

let ABS_PLAN_PRESERVES_CONTROL = prove
 (`!st. MEM st pl_plan_abs ==> 24 <= val(EL 17 st) /\ val(EL 17 st) < 40`,
  GEN_TAC THEN REWRITE_TAC[pl_plan_abs;MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN CONV_TAC STEP_EL_CONV2);;

let tables_abs_program_theorems =
 ["ABS_PLAN_LENGTH",ABS_PLAN_LENGTH;"ABS_PLAN_GUARD_PREFIX",ABS_PLAN_GUARD_PREFIX;
  "ABS_PLAN_BINDING",ABS_PLAN_BINDING;"ABS_PLAN_COMMIT_LAST",ABS_PLAN_COMMIT_LAST;
  "ABS_PLAN_ARGUMENT_RANGE",ABS_PLAN_ARGUMENT_RANGE;
  "ABS_PLAN_PRESERVES_CONTROL",ABS_PLAN_PRESERVES_CONTROL];;
