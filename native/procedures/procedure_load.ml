(* Resource-indexed procedures, physical frames and the native activation. *)
needs "native/procedures/procedure_enter_link.ml";;
needs "native/procedures/procedure_stack.ml";;
needs "native/procedures/procedure_controls.ml";;

let procedure_theorems = procedure_enter_link_theorems @ procedure_stack_theorems @
  procedure_controls_theorems;;
leaf_audit procedure_theorems procedure_theorems;;
