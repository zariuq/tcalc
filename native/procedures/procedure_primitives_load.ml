(* Procedure comparison and typed operation-table lowering. *)
needs "native/leaves/relw/relw_join.ml";;
needs "native/procedures/procedure_operations.ml";;

let procedure_primitive_theorems = relw_image_theorems @ procedure_operation_theorems;;
