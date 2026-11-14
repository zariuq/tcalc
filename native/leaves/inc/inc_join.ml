(* ========================================================================= *)
(* Joins the x86 image theorem of inc (from the t-ISA generator, proved in  *)
(* the same process from inc.hol) with INC_RUN (inc.ml), and gives the      *)
(* uniform image theorem the driver takes of a leaf (leaf_join_lib.ml):     *)
(*   INC_X86        the native code's run ends in a state whose p1 run      *)
(*                  satisfies inc_post;                                       *)
(*   INC_LEAF_SPEC  !pc. tisa_leaf_spec inc inc_mc pc.                     *)
(* INC_LEAF_WF is proved in inc.ml. Run by tcalc/tisa/hol/                  *)
(* run_x86_evidence.sh as its DRIVER, after the record (leaves/evidence.sh); *)
(* also the audit of inc.ml and leaf_lib.ml in that process, and the        *)
(* evidence gate (every loaded file with its digest).                        *)
(* ========================================================================= *)

loadt "native/leaves/common/leaf_join_lib.ml";;
loadt "native/leaves/inc/inc.ml";;

let INC_X86 = leaf_x86 "inc" INC_TERM INC_RUN;;
let INC_LEAF_SPEC = leaf_spec "inc" 0 INC_TERM INC_DECLS;;

leaf_audit (leaf_lib_theorems @ inc_theorems @
            ["INC_X86", INC_X86; "INC_LEAF_SPEC", INC_LEAF_SPEC])
           ["inc_post", inc_post; "INC_RUN", INC_RUN; "INC_DECLS", INC_DECLS;
            "INC_LEAF_WF", INC_LEAF_WF; "INC_X86", INC_X86; "INC_LEAF_SPEC", INC_LEAF_SPEC];;

loadt "native/hol/evidence_gate.ml";;
