(* Generated layouts and their independent native/source consumer checks. *)
needs "native/abi/native_abi_core.ml";;
needs "native/abi/native_abi_driver.ml";;
needs "native/driver/native_component_stack_p1.ml";;

let native_abi_theorems = native_abi_core_theorems @ native_abi_driver_theorems @
  native_component_stack_p1_theorems;;
