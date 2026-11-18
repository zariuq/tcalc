(* Exact-byte proof of the call request marker and its component instance. *)
needs "native/leaves/procedure_call/procedure_call.ml";;
needs "tisa/hol/tisa_x86_evidence.ml";;
needs "native/leaves/procedure_call/procedure_call.hol";;
needs "native/leaves/common/leaf_join_lib.ml";;
needs "native/driver/native_component_p1.ml";;

let PROCEDURE_CALL_MARKER_X86 =
  leaf_x86 "procedure_call_marker" PROCEDURE_CALL_MARKER_TERM PROCEDURE_CALL_MARKER_RUN;;
let PROCEDURE_CALL_MARKER_LEAF_SPEC =
  leaf_spec "procedure_call_marker" 1 PROCEDURE_CALL_MARKER_TERM PROCEDURE_CALL_MARKER_DECLS;;

let procedure_call_marker_component = new_definition
 `procedure_call_marker_component = component_of_p1 procedure_call_marker`;;

let PROCEDURE_CALL_MARKER_COMPONENT_OK = prove
 (`component_ok procedure_call_marker_component`,
  REWRITE_TAC[procedure_call_marker_component] THEN MATCH_MP_TAC COMPONENT_P1_OK THEN
  REWRITE_TAC[PROCEDURE_CALL_MARKER_LEAF_WF]);;

let PROCEDURE_CALL_MARKER_COMPONENT_IMAGE = prove
 (`!pc. component_image procedure_call_marker_component procedure_call_marker_mc pc`,
  REWRITE_TAC[procedure_call_marker_component;COMPONENT_P1_IMAGE;PROCEDURE_CALL_MARKER_LEAF_SPEC]);;

let procedure_call_marker_image_theorems = procedure_call_marker_theorems @
 ["PROCEDURE_CALL_MARKER_X86",PROCEDURE_CALL_MARKER_X86;
  "PROCEDURE_CALL_MARKER_LEAF_SPEC",PROCEDURE_CALL_MARKER_LEAF_SPEC;
  "PROCEDURE_CALL_MARKER_COMPONENT_OK",PROCEDURE_CALL_MARKER_COMPONENT_OK;
  "PROCEDURE_CALL_MARKER_COMPONENT_IMAGE",PROCEDURE_CALL_MARKER_COMPONENT_IMAGE];;

leaf_audit procedure_call_marker_image_theorems procedure_call_marker_image_theorems;;
tisa_evidence_summary();;
