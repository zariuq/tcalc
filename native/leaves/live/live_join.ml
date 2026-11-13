(* ========================================================================= *)
(* Joins the x86 image theorem of live (from the t-ISA generator, proved in *)
(* the same process from live.hol) with LIVE_RUN (live.ml), and gives the  *)
(* uniform image theorem the driver takes of a leaf (leaf_join_lib.ml):     *)
(*   LIVE_X86        the native code's run ends in a state whose p1 run      *)
(*                  satisfies live_post;                                        *)
(*   LIVE_LEAF_SPEC  !pc. tisa_leaf_spec live live_mc pc.                   *)
(* LIVE_LEAF_WF is proved in live.ml. Run by tcalc/tisa/hol/                 *)
(* run_x86_evidence.sh as its DRIVER, after the record (leaves/evidence.sh); *)
(* also the audit of live.ml and leaf_lib.ml in that process, and the      *)
(* evidence gate (every loaded file with its digest).                       *)
(* ========================================================================= *)

loadt "native/leaves/common/leaf_join_lib.ml";;
loadt "native/leaves/live/live.ml";;

let LIVE_X86 = leaf_x86 "live" LIVE_TERM LIVE_RUN;;
let LIVE_LEAF_SPEC = leaf_spec "live" 2 LIVE_TERM LIVE_DECLS;;

leaf_audit (leaf_lib_theorems @ live_theorems @
            ["LIVE_X86", LIVE_X86; "LIVE_LEAF_SPEC", LIVE_LEAF_SPEC])
           ["live_post", live_post; "LIVE_RUN", LIVE_RUN; "LIVE_DECLS", LIVE_DECLS;
            "LIVE_LEAF_WF", LIVE_LEAF_WF; "LIVE_X86", LIVE_X86; "LIVE_LEAF_SPEC", LIVE_LEAF_SPEC];;

loadt "native/hol/evidence_gate.ml";;
