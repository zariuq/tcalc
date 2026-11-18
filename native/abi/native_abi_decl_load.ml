(* Load the selected generated declaration artifact through the real graph. *)
let native_abi_declaration_file =
  try Sys.getenv "TCALC_NATIVE_ABI_FILE" with Not_found ->
    tcalc_path "native/abi/generated/native_abi.ml";;
needs native_abi_declaration_file;;
