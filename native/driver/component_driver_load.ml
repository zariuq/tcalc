(* The common component interface and the existing initializer client. *)
needs "native/driver/component_driver_clients.ml";;
needs "native/driver/component_driver_fuel.ml";;
needs "native/leaves/procedure_enter/procedure_enter_join.ml";;

let component_driver_acceptance_theorems =
  native_component_theorems @ native_component_p1_theorems @
  component_driver_theorems @ component_driver_p1_theorems @
  component_driver_client_theorems @ component_driver_fuel_theorems @
  procedure_enter_image_theorems @
  ["TISA_RUN_FUEL",TISA_RUN_FUEL;"TISA_FAILST_FINST",TISA_FAILST_FINST;
   "TISA_TREGS_SETFWORD",TISA_TREGS_SETFWORD];;

leaf_audit component_driver_acceptance_theorems component_driver_acceptance_theorems;;
