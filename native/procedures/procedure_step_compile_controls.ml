(* Concrete admission and operation-table permutation controls. *)
needs "native/procedures/procedure_step_compile.ml";;

let procedure_compile_example = new_definition
 `procedure_compile_example opcode target =
    MAP (word:num->int64)
      [opcode;target;0;0;0;0;0;0;0;0;8;9;10;11;12;13;14;8]`;;

let PROCEDURE_COMPILE_EXAMPLE_TAC =
  REPEAT(CHANGED_TAC(REWRITE_TAC[procedure_compile_step;procedure_compile_lowered;
    procedure_catalog_lower;procedure_catalog_apply;procedure_catalog_operation;
    procedure_catalog_ok;procedure_catalog_call_tag;native_operation_lower;
    native_operation_unique;native_operation_offset;procedure_compile_example;
    procedure_primitive_bindings_ok;procedure_linked_call_step;procedure_marker_step;
    procedure_binding_count;procedure_request_binding;procedure_empty_binding;
    procedure_target_binding;NATIVE_OPERATION_DISTINCT;NATIVE_OPERATION_INJECTIVE;
    ALL;MAP;MEM;LENGTH;TL;EL;HD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]));;

let PROCEDURE_COMPILE_REORDERED_PRIMITIVE = prove
 (`procedure_compile_step [ReaderOperation 32;KernelOperation 32]
     [ProcedureCallMarker;KernelOperation 32;ReaderOperation 32]
     18 10 (procedure_compile_example 0 0) =
   SOME(procedure_compile_example 2 0)`,
  PROCEDURE_COMPILE_EXAMPLE_TAC);;

let PROCEDURE_COMPILE_REORDERED_CALL = prove
 (`procedure_compile_step [ReaderOperation 32;KernelOperation 32]
     [ProcedureCallMarker;KernelOperation 32;ReaderOperation 32]
     18 10 (procedure_compile_example 2 9) =
   SOME(MAP (word:num->int64)
     [0;18;20;20;20;20;20;20;20;40;8;9;10;11;12;13;14;8])`,
  PROCEDURE_COMPILE_EXAMPLE_TAC);;

let PROCEDURE_COMPILE_RUNTIME_ORDER_CONTROL = prove
 (`procedure_catalog_call_tag [ReaderOperation 32;KernelOperation 32] = 2 /\
   native_operation_offset [ProcedureCallMarker;KernelOperation 32;ReaderOperation 32]
     ProcedureCallMarker = 0 /\
   val(EL 0 (procedure_compile_example 2 0)) = 2 /\
   ~(val(EL 0 (procedure_compile_example 2 0)) <
     native_operation_offset [ProcedureCallMarker;KernelOperation 32;ReaderOperation 32]
       ProcedureCallMarker) /\
   ~(val(EL 0 (procedure_compile_example 2 0)) =
     native_operation_offset [ProcedureCallMarker;KernelOperation 32;ReaderOperation 32]
       ProcedureCallMarker)`,
  PROCEDURE_COMPILE_EXAMPLE_TAC);;

let PROCEDURE_COMPILE_BAD_TARGET_CONTROL = prove
 (`procedure_compile_step [ReaderOperation 32;KernelOperation 32]
     [ProcedureCallMarker;KernelOperation 32;ReaderOperation 32]
     18 10 (procedure_compile_example 2 10) = NONE`,
  PROCEDURE_COMPILE_EXAMPLE_TAC);;

let PROCEDURE_COMPILE_PRIVATE_BINDING_CONTROL = prove
 (`procedure_compile_step [ReaderOperation 32;KernelOperation 32]
     [ProcedureCallMarker;KernelOperation 32;ReaderOperation 32]
     18 10 (procedure_compile_example 0 18) = NONE /\
   18 + 1 < procedure_binding_count 18 10`,
  PROCEDURE_COMPILE_EXAMPLE_TAC);;

let PROCEDURE_COMPILE_DUPLICATE_RUNTIME_CONTROL = prove
 (`procedure_compile_step [ReaderOperation 32]
     [ReaderOperation 32;ReaderOperation 32;ProcedureCallMarker]
     18 10 (procedure_compile_example 0 0) = NONE`,
  PROCEDURE_COMPILE_EXAMPLE_TAC);;

let PROCEDURE_COMPILE_CAPACITY_CONTROL = prove
 (`procedure_compile_step [ReaderOperation 32] [ProcedureCallMarker]
     (2 EXP 64) 1 (procedure_compile_example 1 0) = NONE`,
  PROCEDURE_COMPILE_EXAMPLE_TAC);;

let PROCEDURE_COMPILE_MISSING_MARKER_CONTROL = prove
 (`procedure_compile_step [ReaderOperation 32] [ReaderOperation 32]
     18 10 (procedure_compile_example 1 0) = NONE`,
  PROCEDURE_COMPILE_EXAMPLE_TAC);;

let procedure_step_compile_control_theorems =
 ["PROCEDURE_COMPILE_REORDERED_PRIMITIVE",PROCEDURE_COMPILE_REORDERED_PRIMITIVE;
  "PROCEDURE_COMPILE_REORDERED_CALL",PROCEDURE_COMPILE_REORDERED_CALL;
  "PROCEDURE_COMPILE_RUNTIME_ORDER_CONTROL",PROCEDURE_COMPILE_RUNTIME_ORDER_CONTROL;
  "PROCEDURE_COMPILE_BAD_TARGET_CONTROL",PROCEDURE_COMPILE_BAD_TARGET_CONTROL;
  "PROCEDURE_COMPILE_PRIVATE_BINDING_CONTROL",PROCEDURE_COMPILE_PRIVATE_BINDING_CONTROL;
  "PROCEDURE_COMPILE_DUPLICATE_RUNTIME_CONTROL",PROCEDURE_COMPILE_DUPLICATE_RUNTIME_CONTROL;
  "PROCEDURE_COMPILE_CAPACITY_CONTROL",PROCEDURE_COMPILE_CAPACITY_CONTROL;
  "PROCEDURE_COMPILE_MISSING_MARKER_CONTROL",PROCEDURE_COMPILE_MISSING_MARKER_CONTROL];;
