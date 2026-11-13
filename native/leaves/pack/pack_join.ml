(* ========================================================================= *)
(* Joins the x86 image theorem of pack (from the t-ISA generator, proved in *)
(* the same process from pack.hol) with PACK_RUN (pack.ml), and gives the  *)
(* uniform image theorem the driver takes of a leaf (leaf_join_lib.ml):     *)
(*   PACK_X86        the native code's run ends in a state whose p1 run      *)
(*                  satisfies pack_post;                                        *)
(*   PACK_LEAF_SPEC  !pc. tisa_leaf_spec pack pack_mc pc.                   *)
(* PACK_LEAF_WF is proved in pack.ml. Run by tcalc/tisa/hol/                 *)
(* run_x86_evidence.sh as its DRIVER, after the record (leaves/evidence.sh); *)
(* also the audit of pack.ml and leaf_lib.ml in that process, and the      *)
(* evidence gate (every loaded file with its digest).                       *)
(* ========================================================================= *)

loadt "native/leaves/common/leaf_join_lib.ml";;
loadt "native/leaves/pack/pack.ml";;

let PACK_X86 = leaf_x86 "pack" PACK_TERM PACK_RUN;;
let PACK_LEAF_SPEC = leaf_spec "pack" 0 PACK_TERM PACK_DECLS;;

leaf_audit (leaf_lib_theorems @ pack_theorems @
            ["PACK_X86", PACK_X86; "PACK_LEAF_SPEC", PACK_LEAF_SPEC])
           ["pack_post", pack_post; "PACK_RUN", PACK_RUN; "PACK_DECLS", PACK_DECLS;
            "PACK_LEAF_WF", PACK_LEAF_WF; "PACK_X86", PACK_X86; "PACK_LEAF_SPEC", PACK_LEAF_SPEC];;

loadt "native/hol/evidence_gate.ml";;
