(* ========================================================================= *)
(* Joins the x86 image theorem of unpack (from the t-ISA generator, proved in *)
(* the same process from unpack.hol) with UNPACK_RUN (unpack.ml), and gives the  *)
(* uniform image theorem the driver takes of a leaf (leaf_join_lib.ml):     *)
(*   UNPACK_X86        the native code's run ends in a state whose p1 run      *)
(*                  satisfies unpack_post;                                        *)
(*   UNPACK_LEAF_SPEC  !pc. tisa_leaf_spec unpack unpack_mc pc.                   *)
(* UNPACK_LEAF_WF is proved in unpack.ml. Run by tcalc/tisa/hol/                 *)
(* run_x86_evidence.sh as its DRIVER, after the record (leaves/evidence.sh); *)
(* also the audit of unpack.ml and leaf_lib.ml in that process, and the      *)
(* evidence gate (every loaded file with its digest).                       *)
(* ========================================================================= *)

loadt "native/leaves/common/leaf_join_lib.ml";;
loadt "native/leaves/unpack/unpack.ml";;

let UNPACK_X86 = leaf_x86 "unpack" UNPACK_TERM UNPACK_RUN;;
let UNPACK_LEAF_SPEC = leaf_spec "unpack" 0 UNPACK_TERM UNPACK_DECLS;;

leaf_audit (leaf_lib_theorems @ unpack_theorems @
            ["UNPACK_X86", UNPACK_X86; "UNPACK_LEAF_SPEC", UNPACK_LEAF_SPEC])
           ["unpack_post", unpack_post; "UNPACK_RUN", UNPACK_RUN; "UNPACK_DECLS", UNPACK_DECLS;
            "UNPACK_LEAF_WF", UNPACK_LEAF_WF; "UNPACK_X86", UNPACK_X86; "UNPACK_LEAF_SPEC", UNPACK_LEAF_SPEC];;

loadt "native/hol/evidence_gate.ml";;
