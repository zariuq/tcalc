(* Typed compiler input contracts and their checked-entry source adapter. *)
needs "native/driver/native_component_typed_clients.ml";;
needs "native/driver/native_component_guard.ml";;

let MM_SUB1_GUARDED_SOURCE_OK = prove
 (`component_ok (component_guarded (component_of_p1 mm_sub1_component_program))`,
  MATCH_MP_TAC COMPONENT_GUARDED_OK THEN MATCH_ACCEPT_TAC MM_SUB1_COMPONENT_TYPED_OK);;

let native_component_guard_client_theorems = native_component_typed_client_theorems @
  native_component_guard_theorems @ ["MM_SUB1_GUARDED_SOURCE_OK",MM_SUB1_GUARDED_SOURCE_OK];;
