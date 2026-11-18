(* Compiled calls, the shared stack-bounded driver and exact marker bytes. *)
needs "native/procedures/procedure_compile_math_load.ml";;
needs "native/driver/stack_driver_load.ml";;
needs "native/procedures/procedure_call_load.ml";;
needs "native/procedures/procedure_call_builder.ml";;
needs "native/procedures/procedure_step_compile_driver.ml";;

let procedure_compile_native_theorems = List.sort_uniq
  (fun (a,_) (b,_) -> compare a b)
  (procedure_compile_math_theorems @ procedure_call_native_theorems @
   procedure_call_builder_theorems @ procedure_bindings_driver_theorems @
   procedure_step_compile_driver_theorems);;
leaf_audit procedure_compile_native_theorems procedure_compile_native_theorems;;
