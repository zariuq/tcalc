(* Source procedure semantics and controller refinement, without a CPU model. *)
needs "native/procedures/procedure_controller_controls.ml";;

let procedure_controller_math_theorems =
  procedure_eval_theorems @ procedure_eval_controls_theorems @
  procedure_controller_theorems @ procedure_controller_runs_theorems @
  procedure_controller_controls_theorems;;
