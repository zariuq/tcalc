(* Catalog-bound procedures, qualified independently of a native CPU model. *)
needs "native/procedures/procedure_catalog_controller_controls.ml";;

let procedure_catalog_math_theorems =
  procedure_rules_theorems @ procedure_controls_theorems @
  procedure_controller_math_theorems @ procedure_operation_name_theorems @
  procedure_catalog_theorems @ procedure_catalog_controller_theorems @
  procedure_catalog_controller_controls_theorems;;
