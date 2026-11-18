(* Exact compiled image and the driver leaf contract. *)

needs "native/leaves/ids_next/ids_next.ml";;
needs "tisa/hol/tisa_x86_evidence.ml";;
needs "native/leaves/ids_next/ids_next.hol";;
needs "native/leaves/common/leaf_join_lib.ml";;

let IDS_NEXT_CURRENT_IMAGE = assoc "ids_next" !tisa_entry_thms;;
leaf_check_program "ids_next" IDS_NEXT_TERM;;
let IDS_NEXT_LEAF_SPEC = leaf_spec "ids_next" 3 IDS_NEXT_TERM IDS_NEXT_DECLS;;

let IDS_NEXT_X86 = leaf_x86 "ids_next" IDS_NEXT_TERM IDS_NEXT_RUN;;
