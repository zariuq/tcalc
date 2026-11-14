(* ========================================================================= *)
(* Joins the x86 image theorem of leb_next (from the t-ISA generator, proved in  *)
(* the same process from leb_next.hol) with LEB_NEXT_RUN (leb_next.ml), and gives the      *)
(* uniform image theorem the driver takes of a leaf (leaf_join_lib.ml):     *)
(*   LEB_NEXT_X86        the native code's run ends in a state whose p1 run      *)
(*                  satisfies leb_next_post;                                       *)
(*   LEB_NEXT_LEAF_SPEC  !pc. tisa_leaf_spec leb_next leb_next_mc pc.                     *)
(* LEB_NEXT_LEAF_WF is proved in leb_next.ml. Run by tcalc/tisa/hol/                  *)
(* run_x86_evidence.sh as its DRIVER, after the record (leaves/evidence.sh); *)
(* also the audit of leb_next.ml and leaf_lib.ml in that process, and the        *)
(* evidence gate (every loaded file with its digest).                        *)
(* ========================================================================= *)

loadt "native/leaves/common/leaf_join_lib.ml";;
loadt "native/leaves/leb_next/leb_next.ml";;

let LEB_NEXT_X86 = leaf_x86 "leb_next" LEB_NEXT_TERM LEB_NEXT_RUN;;
let LEB_NEXT_LEAF_SPEC = leaf_spec "leb_next" 2 LEB_NEXT_TERM LEB_NEXT_DECLS;;

leaf_audit (leaf_lib_theorems @ leb_next_theorems @
            ["LEB_NEXT_X86", LEB_NEXT_X86; "LEB_NEXT_LEAF_SPEC", LEB_NEXT_LEAF_SPEC])
           ["leb_next_post", leb_next_post; "LEB_NEXT_RUN", LEB_NEXT_RUN; "LEB_NEXT_DECLS", LEB_NEXT_DECLS;
            "LEB_NEXT_LEAF_WF", LEB_NEXT_LEAF_WF; "LEB_NEXT_X86", LEB_NEXT_X86; "LEB_NEXT_LEAF_SPEC", LEB_NEXT_LEAF_SPEC];;

loadt "native/hol/evidence_gate.ml";;
