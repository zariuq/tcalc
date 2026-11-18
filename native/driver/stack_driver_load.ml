(* The actual driver image with an explicit private callee stack bound. *)
needs "native/driver/component_stack_driver.ml";;

let stack_driver_theorems =
  stack_driver_memory_theorems @ stack_driver_call_memory_theorems @
  component_stack_driver_theorems;;
