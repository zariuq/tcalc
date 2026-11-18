(* A failed clause retains its private allocation and spent fuel. *)
needs "native/procedures/procedure_rules.ml";;

let procedure_prepare_refuse = new_definition
 `procedure_prepare_refuse b (st:int64 list) (cw:num->num) (n:num) used k pay n1 used1 <=>
    if used + 2 <= b
    then k = 0 /\ pay = 0 /\ n1 = n + 1 /\ used1 = used + 2
    else k = 4 /\ pay = 4 /\ n1 = n /\ used1 = used`;;

let procedure_guard_step = new_definition
 `procedure_guard_step =
   [word 0;word 0;word 0;word 0;word 0;word 0;word 0;word 0;word 0;
    word 0;word 0;word 0;word 0;word 0;word 0;word 0;word 0;word 7]:int64 list`;;

let PROCEDURE_PREPARE_TOTAL = prove
 (`procedure_leaf_total procedure_prepare_refuse`,
  REWRITE_TAC[procedure_leaf_total;procedure_prepare_refuse] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `used + 2 <= b` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let PROCEDURE_PREPARE_RECEIPT = prove
 (`!b. procedure_leaf_receipt_ok procedure_prepare_refuse b`,
  REWRITE_TAC[procedure_leaf_receipt_ok;procedure_prepare_refuse] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `used + 2 <= b` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let PROCEDURE_REFUSAL_PREFIX_KEPT = prove
 (`!n used args.
     procedure_call 32 procedure_prepare_refuse [[[procedure_guard_step];[]]] (used + 3) 1 0 0
       args n used (1,0,n + 1,used + 3)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `used < used + 3` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC] THEN
  MATCH_MP_TAC PROCEDURE_CALL_FIRED_RULE THEN
  ASM_REWRITE_TAC[LENGTH;EL;HD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC (el 7 (CONJUNCTS procedure_RULES)) THEN
  MAP_EVERY EXISTS_TAC [`0`;
    `procedure_set (procedure_frame args) (val(EL 17 procedure_guard_step)) 0`;
    `n + 1`;`used + 3`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC (el 2 (CONJUNCTS procedure_RULES)) THEN
    REWRITE_TAC[procedure_prepare_refuse;procedure_guard_step;EL;HD;VAL_WORD_0;
                 ARITH_RULE `(u + 1) + 2 = u + 3`;LE_REFL;ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV;
    MATCH_ACCEPT_TAC PROCEDURE_CHOOSE_EMPTY_PLAN]);;

let procedure_controls_theorems =
 ["PROCEDURE_PREPARE_TOTAL",PROCEDURE_PREPARE_TOTAL;
  "PROCEDURE_PREPARE_RECEIPT",PROCEDURE_PREPARE_RECEIPT;
  "PROCEDURE_REFUSAL_PREFIX_KEPT",PROCEDURE_REFUSAL_PREFIX_KEPT];;
