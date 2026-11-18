(* Call-step data and field equations, independent of native execution proofs. *)
needs "Library/words.ml";;
needs "native/abi/native_abi_decl_load.ml";;
needs "native/procedures/procedure_bindings.ml";;

let procedure_marker_step = new_definition
 `procedure_marker_step call_index request empty metadata (st:int64 list) =
    [word call_index;word request;word empty;word empty;word empty;word empty;
     word empty;word empty;word empty;word metadata;
     EL 10 st;EL 11 st;EL 12 st;EL 13 st;EL 14 st;EL 15 st;EL 16 st;EL 17 st]`;;

let procedure_marker_bindings = new_definition
 `procedure_marker_bindings (bw:num->int64) metadata target n =
    if n = metadata then word 0 else if n = metadata + 1 then target else bw n`;;

let PROCEDURE_MARKER_STEP_FIELDS = prove
 (`!call_index request empty metadata st.
    LENGTH(procedure_marker_step call_index request empty metadata st) = native_abi_StepWords /\
    EL native_abi_DriveStep_leaf (procedure_marker_step call_index request empty metadata st) = word call_index /\
    EL native_abi_DriveStep_region_0 (procedure_marker_step call_index request empty metadata st) = word request /\
    EL native_abi_DriveStep_region_8 (procedure_marker_step call_index request empty metadata st) = word metadata /\
    MAP (\j. EL j (procedure_marker_step call_index request empty metadata st)) [10;11;12;13;14;15;16;17] =
    MAP (\j. EL j st) [10;11;12;13;14;15;16;17]`,
  REWRITE_TAC(procedure_marker_step::LENGTH::MAP::native_abi_definitions) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

let PROCEDURE_MARKER_METADATA = prove
 (`!bw metadata target.
    procedure_marker_bindings bw metadata target metadata = word 0 /\
    procedure_marker_bindings bw metadata target (metadata + 1) = target /\
    (!n. ~(n = metadata) /\ ~(n = metadata + 1)
         ==> procedure_marker_bindings bw metadata target n = bw n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[procedure_marker_bindings] THEN
  SIMP_TAC[ARITH_RULE `~(n + 1 = n)`]);;

let procedure_linked_call_step = new_definition
 `procedure_linked_call_step call_index original (st:int64 list) =
    procedure_marker_step call_index (procedure_request_binding original)
      (procedure_empty_binding original)
      (procedure_target_binding original (val(EL 1 st))) st`;;

let PROCEDURE_LINKED_CALL_FIELDS = prove
 (`!call_index original st.
    LENGTH(procedure_linked_call_step call_index original st) = native_abi_StepWords /\
    EL native_abi_DriveStep_leaf (procedure_linked_call_step call_index original st) = word call_index /\
    EL native_abi_DriveStep_region_0 (procedure_linked_call_step call_index original st) =
      word(procedure_request_binding original) /\
    EL native_abi_DriveStep_region_8 (procedure_linked_call_step call_index original st) =
      word(procedure_target_binding original (val(EL 1 st))) /\
    MAP (\j. EL j (procedure_linked_call_step call_index original st)) [10;11;12;13;14;15;16;17] =
    MAP (\j. EL j st) [10;11;12;13;14;15;16;17]`,
  REWRITE_TAC[procedure_linked_call_step;PROCEDURE_MARKER_STEP_FIELDS]);;

let PROCEDURE_LINKED_CALL_ARGUMENT_FIELD = prove
 (`!call_index original st j. 10 <= j /\ j < 18 ==>
    EL j (procedure_linked_call_step call_index original st) = EL j st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(j:num) = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/
               j = 14 \/ j = 15 \/ j = 16 \/ j = 17` MP_TAC THENL
   [ASM_ARITH_TAC;DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)] THEN
  REWRITE_TAC[procedure_linked_call_step;procedure_marker_step] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let procedure_call_syntax_theorems =
 ["PROCEDURE_MARKER_STEP_FIELDS",PROCEDURE_MARKER_STEP_FIELDS;
  "PROCEDURE_MARKER_METADATA",PROCEDURE_MARKER_METADATA;
  "PROCEDURE_LINKED_CALL_FIELDS",PROCEDURE_LINKED_CALL_FIELDS;
  "PROCEDURE_LINKED_CALL_ARGUMENT_FIELD",PROCEDURE_LINKED_CALL_ARGUMENT_FIELD];;
