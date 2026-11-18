(* Procedure compilation data, admission and operation-table controls. *)
needs "native/procedures/procedure_step_compile_controls.ml";;

let procedure_compile_math_theorems = procedure_call_syntax_theorems @
  procedure_step_compile_theorems @ procedure_step_compile_control_theorems;;
