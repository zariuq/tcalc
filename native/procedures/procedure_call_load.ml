(* Native call capture, source argument transport and publication frames. *)
needs "native/leaves/procedure_call/procedure_call_join.ml";;
needs "native/procedures/procedure_call_transport.ml";;

let procedure_call_native_theorems = procedure_call_marker_image_theorems @
  procedure_call_transport_theorems;;
