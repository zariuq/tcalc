(* ========================================================================= *)
(* Joins the x86 image theorem of skip (from the t-ISA generator, proved     *)
(* in the same process from skip.hol) with SKIP_RUN (skip.ml), and           *)
(* gives the uniform image theorem the driver takes of a leaf                *)
(* (leaf_join_lib.ml):                                                       *)
(*   SKIP_X86  the native code's run ends in a state whose p1 run            *)
(*             satisfies skip_post;                                          *)
(*   SKIP_LEAF_SPEC  !pc. tisa_leaf_spec skip skip_mc pc.                    *)
(* SKIP_LEAF_WF is proved in skip.ml. Run by tcalc/tisa/hol/                 *)
(* run_x86_evidence.sh as its DRIVER, after the record (leaves/evidence.sh); *)
(* also the audit of skip.ml and leaf_lib.ml in that process, and the        *)
(* evidence gate (every loaded file with its digest).                        *)
(* ========================================================================= *)

loadt "native/leaves/common/leaf_join_lib.ml";;
loadt "native/leaves/skip/skip.ml";;

let SKIP_X86 = leaf_x86 "skip" SKIP_TERM SKIP_RUN;;
let SKIP_LEAF_SPEC = leaf_spec "skip" 2 SKIP_TERM SKIP_DECLS;;

leaf_audit (leaf_lib_theorems @ skip_theorems @
            ["SKIP_X86", SKIP_X86; "SKIP_LEAF_SPEC", SKIP_LEAF_SPEC])
           ["skip_post", skip_post; "SKIP_RUN", SKIP_RUN; "SKIP_DECLS", SKIP_DECLS;
            "SKIP_LEAF_WF", SKIP_LEAF_WF; "SKIP_X86", SKIP_X86; "SKIP_LEAF_SPEC", SKIP_LEAF_SPEC];;

loadt "native/hol/evidence_gate.ml";;
