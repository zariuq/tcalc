(* Derive finite control-array sizes from every argument and destination. *)
needs "Library/words.ml";;

let procedure_control_indices = new_definition
 `procedure_control_indices = [10;11;12;13;14;15;16;17]`;;

let procedure_step_control_count = new_definition
 `procedure_step_control_count (st:int64 list) =
    ITLIST (\j n. MAX (val(EL j st) + 1) n) procedure_control_indices 15`;;

let procedure_plan_control_count = new_definition
 `procedure_plan_control_count (plan:(int64 list)list) =
    ITLIST (\st n. MAX (procedure_step_control_count st) n) plan 15`;;

let procedure_body_control_count = new_definition
 `procedure_body_control_count (body:((int64 list)list)list) =
    ITLIST (\plan n. MAX (procedure_plan_control_count plan) n) body 15`;;

let procedure_program_control_count = new_definition
 `procedure_program_control_count (program:(((int64 list)list)list)list) =
    ITLIST (\body n. MAX (procedure_body_control_count body) n) program 15`;;

let PROCEDURE_MAX_FOLD_BOUND = prove
 (`!f:A->num. !xs low upper.
    ITLIST (\x n. MAX (f x) n) xs low <= upper <=>
    low <= upper /\ ALL (\x. f x <= upper) xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST;ALL;ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`] THEN
  MESON_TAC[]);;

let PROCEDURE_MAX_FOLD_LOWER = prove
 (`!f:A->num. !xs low. low <= ITLIST (\x n. MAX (f x) n) xs low`,
  MESON_TAC[PROCEDURE_MAX_FOLD_BOUND;LE_REFL]);;

let PROCEDURE_MAX_FOLD_MEMBER = prove
 (`!f:A->num. !xs low x. MEM x xs ==>
    f x <= ITLIST (\y n. MAX (f y) n) xs low`,
  MESON_TAC[PROCEDURE_MAX_FOLD_BOUND;ALL_MEM;LE_REFL]);;

let PROCEDURE_CONTROL_INDEX_MEMBER = prove
 (`!j. MEM j procedure_control_indices <=> 10 <= j /\ j < 18`,
  REWRITE_TAC[procedure_control_indices;MEM] THEN ARITH_TAC);;

let PROCEDURE_STEP_CONTROL_COUNT_BOUND = prove
 (`!st upper. procedure_step_control_count st <= upper <=>
    15 <= upper /\ (!j. 10 <= j /\ j < 18 ==> val(EL j st) < upper)`,
  REWRITE_TAC[procedure_step_control_count;PROCEDURE_MAX_FOLD_BOUND;
    GSYM ALL_MEM;PROCEDURE_CONTROL_INDEX_MEMBER;ARITH_RULE `x + 1 <= n <=> x < n`]);;

let PROCEDURE_PROGRAM_CONTROL_COUNT_MINIMUM = prove
 (`!program. 15 <= procedure_program_control_count program`,
  REWRITE_TAC[procedure_program_control_count;PROCEDURE_MAX_FOLD_LOWER]);;

let PROCEDURE_PROGRAM_CONTROL_COUNT_SLOT = prove
 (`!program body plan st j.
    MEM body program /\ MEM plan body /\ MEM st plan /\ 10 <= j /\ j < 18 ==>
    val(EL j st) < procedure_program_control_count program`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(EL j (st:int64 list)) < procedure_step_control_count st` ASSUME_TAC THENL
   [MP_TAC(SPECL [`st:int64 list`;`procedure_step_control_count st`]
      PROCEDURE_STEP_CONTROL_COUNT_BOUND) THEN REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `j:num`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `procedure_step_control_count st <= procedure_plan_control_count plan` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`procedure_step_control_count`;`plan:(int64 list)list`;`15`;`st:int64 list`]
      PROCEDURE_MAX_FOLD_MEMBER) THEN
    ASM_REWRITE_TAC[GSYM procedure_plan_control_count];ALL_TAC] THEN
  SUBGOAL_THEN `procedure_plan_control_count plan <= procedure_body_control_count body` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`procedure_plan_control_count`;`body:((int64 list)list)list`;`15`;
      `plan:(int64 list)list`] PROCEDURE_MAX_FOLD_MEMBER) THEN
    ASM_REWRITE_TAC[GSYM procedure_body_control_count];ALL_TAC] THEN
  SUBGOAL_THEN `procedure_body_control_count body <= procedure_program_control_count program` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`procedure_body_control_count`;`program:(((int64 list)list)list)list`;`15`;
      `body:((int64 list)list)list`] PROCEDURE_MAX_FOLD_MEMBER) THEN
    ASM_REWRITE_TAC[GSYM procedure_program_control_count];
    ASM_ARITH_TAC]);;

let PROCEDURE_PROGRAM_CONTROL_COUNT_LEAST = prove
 (`!program upper.
    15 <= upper /\
    (!body plan st j. MEM body program /\ MEM plan body /\ MEM st plan /\
                     10 <= j /\ j < 18 ==> val(EL j st) < upper) ==>
    procedure_program_control_count program <= upper`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[procedure_program_control_count;PROCEDURE_MAX_FOLD_BOUND] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  X_GEN_TAC `body:((int64 list)list)list` THEN DISCH_TAC THEN
  REWRITE_TAC[procedure_body_control_count;PROCEDURE_MAX_FOLD_BOUND] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  X_GEN_TAC `plan:(int64 list)list` THEN DISCH_TAC THEN
  REWRITE_TAC[procedure_plan_control_count;PROCEDURE_MAX_FOLD_BOUND] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
  REWRITE_TAC[PROCEDURE_STEP_CONTROL_COUNT_BOUND] THEN ASM_MESON_TAC[]);;

let PROCEDURE_PROGRAM_CONTROL_COUNT_EXACT = prove
 (`!program upper. procedure_program_control_count program <= upper <=>
    15 <= upper /\
    (!body plan st j. MEM body program /\ MEM plan body /\ MEM st plan /\
                     10 <= j /\ j < 18 ==> val(EL j st) < upper)`,
  MESON_TAC[PROCEDURE_PROGRAM_CONTROL_COUNT_MINIMUM;PROCEDURE_PROGRAM_CONTROL_COUNT_SLOT;
    PROCEDURE_PROGRAM_CONTROL_COUNT_LEAST;LE_TRANS;LTE_TRANS]);;

let PROCEDURE_CONTROL_COUNT_EXAMPLE_TAC =
  REWRITE_TAC[procedure_program_control_count;procedure_body_control_count;
    procedure_plan_control_count;procedure_step_control_count;procedure_control_indices;
    ITLIST;MAP] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV;;

let PROCEDURE_CONTROL_COUNT_EMPTY = prove
 (`procedure_program_control_count [] = 15`,PROCEDURE_CONTROL_COUNT_EXAMPLE_TAC);;

let PROCEDURE_CONTROL_COUNT_INHABITED = prove
 (`procedure_program_control_count
    [[[MAP (word:num->int64) [0;0;0;0;0;0;0;0;0;0;8;9;10;11;12;13;14;21]]]] = 22`,
  PROCEDURE_CONTROL_COUNT_EXAMPLE_TAC);;

let PROCEDURE_CONTROL_COUNT_FIXED48_CONTROL = prove
 (`procedure_program_control_count
    [[[MAP (word:num->int64) [0;0;0;0;0;0;0;0;0;0;8;9;10;11;12;13;14;64]]]] = 65 /\
   ~(64 < 48)`,PROCEDURE_CONTROL_COUNT_EXAMPLE_TAC);;

let PROCEDURE_CONTROL_COUNT_OVERFLOW_CONTROL = prove
 (`procedure_program_control_count
    [[[MAP (word:num->int64)
       [0;0;0;0;0;0;0;0;0;0;8;9;10;11;12;13;14;18446744073709551615]]]] = 2 EXP 64 /\
   ~(8 * 2 EXP 64 < 2 EXP 64)`,PROCEDURE_CONTROL_COUNT_EXAMPLE_TAC);;

let procedure_control_count_theorems =
 ["PROCEDURE_MAX_FOLD_BOUND",PROCEDURE_MAX_FOLD_BOUND;
  "PROCEDURE_MAX_FOLD_LOWER",PROCEDURE_MAX_FOLD_LOWER;
  "PROCEDURE_MAX_FOLD_MEMBER",PROCEDURE_MAX_FOLD_MEMBER;
  "PROCEDURE_CONTROL_INDEX_MEMBER",PROCEDURE_CONTROL_INDEX_MEMBER;
  "PROCEDURE_STEP_CONTROL_COUNT_BOUND",PROCEDURE_STEP_CONTROL_COUNT_BOUND;
  "PROCEDURE_PROGRAM_CONTROL_COUNT_MINIMUM",PROCEDURE_PROGRAM_CONTROL_COUNT_MINIMUM;
  "PROCEDURE_PROGRAM_CONTROL_COUNT_SLOT",PROCEDURE_PROGRAM_CONTROL_COUNT_SLOT;
  "PROCEDURE_PROGRAM_CONTROL_COUNT_LEAST",PROCEDURE_PROGRAM_CONTROL_COUNT_LEAST;
  "PROCEDURE_PROGRAM_CONTROL_COUNT_EXACT",PROCEDURE_PROGRAM_CONTROL_COUNT_EXACT;
  "PROCEDURE_CONTROL_COUNT_EMPTY",PROCEDURE_CONTROL_COUNT_EMPTY;
  "PROCEDURE_CONTROL_COUNT_INHABITED",PROCEDURE_CONTROL_COUNT_INHABITED;
  "PROCEDURE_CONTROL_COUNT_FIXED48_CONTROL",PROCEDURE_CONTROL_COUNT_FIXED48_CONTROL;
  "PROCEDURE_CONTROL_COUNT_OVERFLOW_CONTROL",PROCEDURE_CONTROL_COUNT_OVERFLOW_CONTROL];;
