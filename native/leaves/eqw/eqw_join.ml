(* ========================================================================= *)
(* Joins the x86 image theorem of eqw (from the t-ISA generator, proved in *)
(* the same process from eqw.hol) with EQW_RUN (eqw.ml), and gives the  *)
(* uniform image theorem the driver takes of a leaf (leaf_join_lib.ml):     *)
(*   EQW_X86        the native code's run ends in a state whose p1 run      *)
(*                  satisfies eqw_post;                                        *)
(*   EQW_LEAF_SPEC  !pc. tisa_leaf_spec eqw eqw_mc pc.                   *)
(* EQW_LEAF_WF is proved in eqw.ml. Run by tcalc/tisa/hol/                 *)
(* run_x86_evidence.sh as its DRIVER, after the record (leaves/evidence.sh); *)
(* also the audit of eqw.ml and leaf_lib.ml in that process, and the      *)
(* evidence gate (every loaded file with its digest).                       *)
(* ========================================================================= *)

loadt "native/leaves/common/leaf_join_lib.ml";;
loadt "native/leaves/eqw/eqw.ml";;

let EQW_X86 = leaf_x86 "eqw" EQW_TERM EQW_RUN;;
let EQW_LEAF_SPEC = leaf_spec "eqw" 0 EQW_TERM EQW_DECLS;;

leaf_audit (leaf_lib_theorems @ eqw_theorems @
            ["EQW_X86", EQW_X86; "EQW_LEAF_SPEC", EQW_LEAF_SPEC])
           ["eqw_post", eqw_post; "EQW_RUN", EQW_RUN; "EQW_DECLS", EQW_DECLS;
            "EQW_LEAF_WF", EQW_LEAF_WF; "EQW_X86", EQW_X86; "EQW_LEAF_SPEC", EQW_LEAF_SPEC];;

loadt "native/hol/evidence_gate.ml";;
