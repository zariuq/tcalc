(* Native component admission for the independent operation-name table. *)
needs "native/procedures/procedure_operation_names.ml";;
needs "native/driver/native_component.ml";;

let NATIVE_OPERATION_COMPONENT_OK = prove
 (`!table op components.
    MEM op table /\ LENGTH(components:native_component list) = LENGTH table /\ ALL component_ok components
    ==> component_ok (EL (native_operation_offset table op) components)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_EL] THEN
  MESON_TAC[NATIVE_OPERATION_OFFSET_BOUND]);;

let procedure_operation_theorems = procedure_operation_name_theorems @
 ["NATIVE_OPERATION_COMPONENT_OK",NATIVE_OPERATION_COMPONENT_OK];;
