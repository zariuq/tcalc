(* Compilation preserves call arguments and primitive memory capabilities. *)
needs "native/procedures/procedure_step_compile.ml";;
needs "native/procedures/procedure_bindings_driver.ml";;

let PROCEDURE_COMPILE_CALL_CAPABILITY = prove
 (`!catalog table original procedures st out bw request extent.
    procedure_compile_step catalog table original procedures st = SOME out /\
    val(EL 0 (st:int64 list)) = procedure_catalog_call_tag catalog ==>
    drv_base (procedure_linked_bindings bw original procedures request extent) out 0 = request /\
    drv_len (procedure_linked_bindings bw original procedures request extent) out 0 = extent /\
    drv_base (procedure_linked_bindings bw original procedures request extent) out 8 = word 0 /\
    drv_len (procedure_linked_bindings bw original procedures request extent) out 8 = EL 1 st`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PROCEDURE_COMPILE_CALL_SHAPE) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `call_index:num` SUBST1_TAC))) THEN
  ASM_SIMP_TAC[PROCEDURE_LINKED_REQUEST_REGION;PROCEDURE_LINKED_TARGET_REGION]);;

let PROCEDURE_COMPILE_CALL_CAPTURE = prove
 (`!catalog table original procedures st out reserve bw request extent ctl budget cfr m used t.
    procedure_compile_step catalog table original procedures st = SOME out /\
    val(EL 0 (st:int64 list)) = procedure_catalog_call_tag catalog /\
    stack_drv_child reserve (procedure_linked_bindings bw original procedures request extent)
      ctl budget cfr out m used t ==>
    procedure_request_value t 7 = EL 1 st /\
    [procedure_request_value t 0;procedure_request_value t 1;
     procedure_request_value t 2;procedure_request_value t 3;
     procedure_request_value t 4;procedure_request_value t 5;
     procedure_request_value t 6] =
    [drv_cw ctl m (EL 10 st);drv_cw ctl m (EL 11 st);drv_cw ctl m (EL 12 st);
     drv_cw ctl m (EL 13 st);drv_cw ctl m (EL 14 st);drv_cw ctl m (EL 15 st);
     drv_cw ctl m (EL 16 st)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`catalog:native_operation list`;`table:native_operation list`;`original:num`;
    `procedures:num`;`st:int64 list`;`out:int64 list`] PROCEDURE_COMPILE_CALL_SHAPE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `call_index:num` SUBST_ALL_TAC))) THEN
  MP_TAC(SPECL [`reserve:num`;`bw:num->int64`;`original:num`;`procedures:num`;
    `request:int64`;`extent:int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`call_index:num`;
    `st:int64 list`;`m:int64->byte`;`used:int64`;`t:tisa_state`]
    PROCEDURE_LINKED_STACK_CAPTURE) THEN ASM_REWRITE_TAC[]);;

let PROCEDURE_COMPILE_CALL_ARGUMENTS = prove
 (`!catalog table original procedures st out reserve bw request extent ctl budget cfr m used t cw.
    procedure_compile_step catalog table original procedures st = SOME out /\
    val(EL 0 (st:int64 list)) = procedure_catalog_call_tag catalog /\
    stack_drv_child reserve (procedure_linked_bindings bw original procedures request extent)
      ctl budget cfr out m used t /\
    (!j. j < 7 ==> drv_cw ctl m (EL (10 + j) st) = word(cw(val(EL (10 + j) st)))) ==>
    procedure_request_value t 7 = EL 1 st /\
    [procedure_request_value t 0;procedure_request_value t 1;
     procedure_request_value t 2;procedure_request_value t 3;
     procedure_request_value t 4;procedure_request_value t 5;
     procedure_request_value t 6] = MAP (word:num->int64) (procedure_args st cw)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`catalog:native_operation list`;`table:native_operation list`;`original:num`;
    `procedures:num`;`st:int64 list`;`out:int64 list`;`reserve:num`;`bw:num->int64`;
    `request:int64`;`extent:int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;
    `m:int64->byte`;`used:int64`;`t:tisa_state`] PROCEDURE_COMPILE_CALL_CAPTURE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[procedure_args;MAP] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `drv_cw`)) (concl th))) THEN
  CONV_TAC (LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN REFL_TAC);;

let PROCEDURE_COMPILE_CALL_ARGUMENTS_EXACT = prove
 (`!catalog table original procedures st out reserve bw request extent ctl budget cfr m used t cw.
    procedure_compile_step catalog table original procedures st = SOME out /\
    val(EL 0 (st:int64 list)) = procedure_catalog_call_tag catalog /\
    stack_drv_child reserve (procedure_linked_bindings bw original procedures request extent)
      ctl budget cfr out m used t /\
    (!j. j < 7 ==> drv_cw ctl m (EL (10 + j) st) = word(cw(val(EL (10 + j) st)))) /\
    ALL (\v. v < 2 EXP 64) (procedure_args st cw) ==>
    val(procedure_request_value t 7) = val(EL 1 st) /\
    MAP (val:int64->num)
      [procedure_request_value t 0;procedure_request_value t 1;
       procedure_request_value t 2;procedure_request_value t 3;
       procedure_request_value t 4;procedure_request_value t 5;
       procedure_request_value t 6] = procedure_args st cw`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`catalog:native_operation list`;`table:native_operation list`;`original:num`;
    `procedures:num`;`st:int64 list`;`out:int64 list`;`reserve:num`;`bw:num->int64`;
    `request:int64`;`extent:int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;
    `m:int64->byte`;`used:int64`;`t:tisa_state`;`cw:num->num`] PROCEDURE_COMPILE_CALL_ARGUMENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[PROCEDURE_WORD_ARGUMENTS_EXACT]);;

let procedure_step_compile_driver_theorems =
 ["PROCEDURE_COMPILE_CALL_SHAPE",PROCEDURE_COMPILE_CALL_SHAPE;
  "PROCEDURE_COMPILE_CALL_CAPABILITY",PROCEDURE_COMPILE_CALL_CAPABILITY;
  "PROCEDURE_COMPILE_CALL_CAPTURE",PROCEDURE_COMPILE_CALL_CAPTURE;
  "PROCEDURE_COMPILE_CALL_ARGUMENTS",PROCEDURE_COMPILE_CALL_ARGUMENTS;
  "PROCEDURE_COMPILE_CALL_ARGUMENTS_EXACT",PROCEDURE_COMPILE_CALL_ARGUMENTS_EXACT];;
