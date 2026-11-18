(* Exact bytes for procedure activation and their common component contract. *)
needs "native/leaves/procedure_enter/procedure_enter.ml";;
needs "tisa/hol/tisa_x86_evidence.ml";;
needs "native/leaves/procedure_enter/procedure_enter.hol";;
needs "native/leaves/common/leaf_join_lib.ml";;
needs "native/driver/native_component_p1.ml";;

let PROCEDURE_ENTER_X86 =
  leaf_x86 "procedure_enter" PROCEDURE_ENTER_TERM PROCEDURE_ENTER_RUN;;
let PROCEDURE_ENTER_LEAF_SPEC =
  leaf_spec "procedure_enter" 0 PROCEDURE_ENTER_TERM PROCEDURE_ENTER_DECLS;;

let procedure_enter_component = new_definition
 `procedure_enter_component = component_of_p1 procedure_enter`;;

let PROCEDURE_ENTER_COMPONENT_OK = prove
 (`component_ok procedure_enter_component`,
  REWRITE_TAC[procedure_enter_component] THEN
  MATCH_MP_TAC COMPONENT_P1_OK THEN REWRITE_TAC[PROCEDURE_ENTER_LEAF_WF]);;

let PROCEDURE_ENTER_COMPONENT_IMAGE = prove
 (`!pc. component_image procedure_enter_component procedure_enter_mc pc`,
  REWRITE_TAC[procedure_enter_component;COMPONENT_P1_IMAGE;PROCEDURE_ENTER_LEAF_SPEC]);;

let procedure_enter_image_theorems = procedure_enter_theorems @
 ["PROCEDURE_ENTER_X86",PROCEDURE_ENTER_X86;
  "PROCEDURE_ENTER_LEAF_SPEC",PROCEDURE_ENTER_LEAF_SPEC;
  "PROCEDURE_ENTER_COMPONENT_OK",PROCEDURE_ENTER_COMPONENT_OK;
  "PROCEDURE_ENTER_COMPONENT_IMAGE",PROCEDURE_ENTER_COMPONENT_IMAGE];;

leaf_audit procedure_enter_image_theorems procedure_enter_image_theorems;;
tisa_evidence_summary();;
