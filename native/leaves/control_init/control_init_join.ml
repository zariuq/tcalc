(* Exact native image and functional meaning of the control initializer. *)
needs "native/leaves/control_init/control_init.ml";;
needs "tisa/hol/tisa_x86_evidence.ml";;
needs "native/leaves/control_init/control_init.hol";;
needs "native/leaves/common/leaf_join_lib.ml";;

let CONTROL_INIT_X86 = leaf_x86 "control_init" CONTROL_INIT_TERM CONTROL_INIT_RUN;;
let CONTROL_INIT_LEAF_SPEC = leaf_spec "control_init" 1 CONTROL_INIT_TERM CONTROL_INIT_DECLS;;

let control_init_image_theorems = control_init_theorems @
 ["CONTROL_INIT_X86",CONTROL_INIT_X86;"CONTROL_INIT_LEAF_SPEC",CONTROL_INIT_LEAF_SPEC];;
leaf_audit control_init_image_theorems control_init_image_theorems;;
tisa_evidence_summary();;
