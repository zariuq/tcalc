(* Exact bytes for the masked unsigned relation guard. *)
needs "native/leaves/relw/relw.ml";;
needs "tisa/hol/tisa_x86_evidence.ml";;
needs "native/leaves/relw/relw.hol";;
needs "native/leaves/common/leaf_join_lib.ml";;
needs "native/driver/native_component_p1.ml";;

let RELW_X86 = leaf_x86 "relw" RELW_TERM RELW_RUN;;
let RELW_LEAF_SPEC = leaf_spec "relw" 0 RELW_TERM RELW_DECLS;;

let relw_component = new_definition `relw_component = component_of_p1 relw`;;
let RELW_COMPONENT_OK = prove
 (`component_ok relw_component`,
  REWRITE_TAC[relw_component] THEN MATCH_MP_TAC COMPONENT_P1_OK THEN REWRITE_TAC[RELW_LEAF_WF]);;
let RELW_COMPONENT_IMAGE = prove
 (`!pc. component_image relw_component relw_mc pc`,
  REWRITE_TAC[relw_component;COMPONENT_P1_IMAGE;RELW_LEAF_SPEC]);;

let relw_image_theorems = relw_theorems @
 ["RELW_X86",RELW_X86;"RELW_LEAF_SPEC",RELW_LEAF_SPEC;
  "RELW_COMPONENT_OK",RELW_COMPONENT_OK;"RELW_COMPONENT_IMAGE",RELW_COMPONENT_IMAGE];;

leaf_audit relw_image_theorems relw_image_theorems;;
tisa_evidence_summary();;
