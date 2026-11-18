(* Static call metadata and argument capture through the actual driver frame. *)
needs "native/procedures/procedure_bindings.ml";;
needs "native/procedures/procedure_call_syntax.ml";;
needs "native/leaves/procedure_call/procedure_call_view.ml";;
needs "native/driver/stack_driver_memory.ml";;

let PROCEDURE_LINKED_OVERLAY_IDENTITY = prove
 (`!bw original procedures request extent target.
    target < procedures ==>
    procedure_marker_bindings
      (procedure_linked_bindings bw original procedures request extent)
      (procedure_target_binding original target) (word target) =
    procedure_linked_bindings bw original procedures request extent`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`original:num`;`procedures:num`;`request:int64`;
    `extent:int64`;`target:num`] PROCEDURE_BINDINGS_TARGET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM;procedure_marker_bindings] THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `(n:num) = procedure_target_binding original target` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(n:num) = procedure_target_binding original target + 1` THEN
  ASM_REWRITE_TAC[]);;

let PROCEDURE_LINKED_REGION_PREFIX = prove
 (`!bw original procedures request extent st r.
    val(EL (1 + r) (st:int64 list)) + 1 < original ==>
    drv_base (procedure_linked_bindings bw original procedures request extent) st r = drv_base bw st r /\
    drv_len (procedure_linked_bindings bw original procedures request extent) st r = drv_len bw st r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[drv_base;drv_len] THEN
  ASM_SIMP_TAC[PROCEDURE_BINDINGS_PREFIX;ARITH_RULE `(n:num) + 1 < m ==> n < m`]);;

let PROCEDURE_LINKED_REQUEST_REGION = prove
 (`!bw original procedures request extent call_index st.
    procedure_binding_count original procedures <= 2 EXP 64 ==>
    drv_base (procedure_linked_bindings bw original procedures request extent)
      (procedure_linked_call_step call_index original st) 0 = request /\
    drv_len (procedure_linked_bindings bw original procedures request extent)
      (procedure_linked_call_step call_index original st) 0 = extent`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(original:num) < 2 EXP 64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[procedure_binding_count]) THEN ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[drv_base;drv_len;procedure_linked_call_step;procedure_marker_step;
    procedure_request_binding] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT;
    REWRITE_RULE[procedure_request_binding] PROCEDURE_BINDINGS_REQUEST]);;

let PROCEDURE_LINKED_TARGET_REGION = prove
 (`!bw original procedures request extent call_index st.
    procedure_binding_count original procedures <= 2 EXP 64 /\
    val(EL 1 (st:int64 list)) < procedures ==>
    drv_base (procedure_linked_bindings bw original procedures request extent)
      (procedure_linked_call_step call_index original st) 8 = word 0 /\
    drv_len (procedure_linked_bindings bw original procedures request extent)
      (procedure_linked_call_step call_index original st) 8 = EL 1 st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`original:num`;`procedures:num`;`val(EL 1 (st:int64 list))`]
    PROCEDURE_BINDINGS_TARGET_WORD_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[drv_base;drv_len;procedure_linked_call_step;procedure_marker_step] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT;PROCEDURE_BINDINGS_TARGET;WORD_VAL]);;

let PROCEDURE_REQUEST_STACK_CHILD_VALUES = prove
 (`!reserve bw ctl budget cfr st m used t.
    stack_drv_child reserve bw ctl budget cfr st m used t ==>
    [procedure_request_value t 0;procedure_request_value t 1;
     procedure_request_value t 2;procedure_request_value t 3;
     procedure_request_value t 4;procedure_request_value t 5;
     procedure_request_value t 6] =
    [drv_cw ctl m (EL 10 st);drv_cw ctl m (EL 11 st);drv_cw ctl m (EL 12 st);
     drv_cw ctl m (EL 13 st);drv_cw ctl m (EL 14 st);drv_cw ctl m (EL 15 st);
     drv_cw ctl m (EL 16 st)] /\
    procedure_request_value t 7 = drv_len bw st 8`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_drv_child] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "frame") (K ALL_TAC))) THEN
  MAP_EVERY (fun j -> USE_THEN "frame" (MP_TAC o SPEC (mk_small_numeral j)) THEN
    REWRITE_TAC[drv_fw] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [17;22;23] THEN
  REMOVE_THEN "frame" (K ALL_TAC) THEN
  ASM_REWRITE_TAC[procedure_request_value;drv_regs;drv_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let PROCEDURE_LINKED_STACK_CAPTURE = prove
 (`!reserve bw original procedures request extent ctl budget cfr call_index st m used t.
    procedure_binding_count original procedures <= 2 EXP 64 /\
    val(EL 1 (st:int64 list)) < procedures /\
    stack_drv_child reserve (procedure_linked_bindings bw original procedures request extent)
      ctl budget cfr (procedure_linked_call_step call_index original st) m used t ==>
    procedure_request_value t 7 = EL 1 st /\
    [procedure_request_value t 0;procedure_request_value t 1;
     procedure_request_value t 2;procedure_request_value t 3;
     procedure_request_value t 4;procedure_request_value t 5;
     procedure_request_value t 6] =
    [drv_cw ctl m (EL 10 st);drv_cw ctl m (EL 11 st);drv_cw ctl m (EL 12 st);
     drv_cw ctl m (EL 13 st);drv_cw ctl m (EL 14 st);drv_cw ctl m (EL 15 st);
     drv_cw ctl m (EL 16 st)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`reserve:num`;
    `procedure_linked_bindings bw original procedures request extent`;
    `ctl:int64`;`budget:int64`;`cfr:int64`;
    `procedure_linked_call_step call_index original st`;`m:int64->byte`;`used:int64`;`t:tisa_state`]
    PROCEDURE_REQUEST_STACK_CHILD_VALUES) THEN
  ASM_SIMP_TAC[PROCEDURE_LINKED_TARGET_REGION] THEN
  REWRITE_TAC[procedure_linked_call_step;procedure_marker_step] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN MESON_TAC[]);;

let PROCEDURE_WORD_ARGUMENTS_EXACT = prove
 (`!args:num list. ALL (\v. v < 2 EXP 64) args ==>
    MAP (val:int64->num) (MAP (word:num->int64) args) = args`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL;MAP] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT]);;

let procedure_bindings_driver_theorems =
 ["PROCEDURE_LINKED_CALL_FIELDS",PROCEDURE_LINKED_CALL_FIELDS;
  "PROCEDURE_LINKED_CALL_ARGUMENT_FIELD",PROCEDURE_LINKED_CALL_ARGUMENT_FIELD;
  "PROCEDURE_LINKED_OVERLAY_IDENTITY",PROCEDURE_LINKED_OVERLAY_IDENTITY;
  "PROCEDURE_LINKED_REGION_PREFIX",PROCEDURE_LINKED_REGION_PREFIX;
  "PROCEDURE_LINKED_REQUEST_REGION",PROCEDURE_LINKED_REQUEST_REGION;
  "PROCEDURE_LINKED_TARGET_REGION",PROCEDURE_LINKED_TARGET_REGION;
  "PROCEDURE_REQUEST_STACK_CHILD_VALUES",PROCEDURE_REQUEST_STACK_CHILD_VALUES;
  "PROCEDURE_LINKED_STACK_CAPTURE",PROCEDURE_LINKED_STACK_CAPTURE;
  "PROCEDURE_WORD_ARGUMENTS_EXACT",PROCEDURE_WORD_ARGUMENTS_EXACT];;
