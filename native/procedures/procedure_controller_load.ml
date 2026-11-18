(* Total procedure semantics, concrete controls and physical result transport. *)
needs "native/procedures/procedure_controller_math_load.ml";;
needs "native/procedures/procedure_work_controls.ml";;

let procedure_controller_library_theorems =
  procedure_controller_math_theorems @ procedure_work_controls_theorems;;
