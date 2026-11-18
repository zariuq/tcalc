(* Native frame transport for the shared call-step data. *)
needs "native/procedures/procedure_call_syntax.ml";;
needs "native/procedures/procedure_call_transport.ml";;

let PROCEDURE_MARKER_TARGET = prove
 (`!bw call_index request empty metadata st.
    metadata < 2 EXP 64
    ==> drv_len (procedure_marker_bindings bw metadata (EL 1 st))
          (procedure_marker_step call_index request empty metadata st) 8 = EL 1 st`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[drv_len;procedure_marker_step] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT;PROCEDURE_MARKER_METADATA]);;

let PROCEDURE_MARKER_REQUEST_BINDING = prove
 (`!bw metadata target request.
    request + 2 <= metadata \/ metadata + 2 <= request
    ==> procedure_marker_bindings bw metadata target request = bw request /\
        procedure_marker_bindings bw metadata target (request + 1) = bw (request + 1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `~(request = metadata) /\ ~(request = metadata + 1) /\
     ~(request + 1 = metadata) /\ ~(request + 1 = metadata + 1)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;ASM_SIMP_TAC[PROCEDURE_MARKER_METADATA]]);;

let PROCEDURE_MARKER_CAPTURED_CALL = prove
 (`!bw ctl budget cfr call_index request empty metadata st m used t.
    metadata < 2 EXP 64 /\
    drv_child (procedure_marker_bindings bw metadata (EL 1 st)) ctl budget cfr
      (procedure_marker_step call_index request empty metadata st) m used t
    ==> procedure_request_value t 7 = EL 1 st /\
        [procedure_request_value t 0;procedure_request_value t 1;
         procedure_request_value t 2;procedure_request_value t 3;
         procedure_request_value t 4;procedure_request_value t 5;
         procedure_request_value t 6] =
        [drv_cw ctl m (EL 10 st);drv_cw ctl m (EL 11 st);drv_cw ctl m (EL 12 st);
         drv_cw ctl m (EL 13 st);drv_cw ctl m (EL 14 st);drv_cw ctl m (EL 15 st);
         drv_cw ctl m (EL 16 st)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL
   [`procedure_marker_bindings bw metadata (EL 1 st)`;`ctl:int64`;`budget:int64`;`cfr:int64`;
    `procedure_marker_step call_index request empty metadata st`;`m:int64->byte`;`used:int64`;`t:tisa_state`]
    PROCEDURE_REQUEST_CHILD_VALUES) THEN
  ASM_SIMP_TAC[PROCEDURE_MARKER_TARGET] THEN
  REWRITE_TAC[procedure_marker_step] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN MESON_TAC[]);;

let procedure_call_builder_theorems =
 ["PROCEDURE_MARKER_STEP_FIELDS",PROCEDURE_MARKER_STEP_FIELDS;
  "PROCEDURE_MARKER_METADATA",PROCEDURE_MARKER_METADATA;
  "PROCEDURE_MARKER_TARGET",PROCEDURE_MARKER_TARGET;
  "PROCEDURE_MARKER_REQUEST_BINDING",PROCEDURE_MARKER_REQUEST_BINDING;
  "PROCEDURE_MARKER_CAPTURED_CALL",PROCEDURE_MARKER_CAPTURED_CALL];;
