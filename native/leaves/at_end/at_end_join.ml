(* ========================================================================= *)
(* Joins the x86 image theorem of at_end (from the t-ISA generator, proved  *)
(* in the same process from at_end.hol) with AT_END_RUN (at_end.ml), and    *)
(* gives the uniform image theorem the driver takes of a leaf                *)
(* (leaf_join_lib.ml):                                                       *)
(*   AT_END_X86        the native code's run ends in a state whose p1 run   *)
(*                     satisfies at_end_post;                                *)
(*   AT_END_LEAF_SPEC  !pc. tisa_leaf_spec at_end at_end_mc pc.             *)
(* AT_END_LEAF_WF is proved in at_end.ml. Run by tcalc/tisa/hol/            *)
(* run_x86_evidence.sh as its DRIVER, after the record (leaves/evidence.sh); *)
(* also the audit of at_end.ml and leaf_lib.ml in that process, and the     *)
(* evidence gate (every loaded file with its digest).                        *)
(* ========================================================================= *)

loadt "native/leaves/common/leaf_join_lib.ml";;
loadt "native/leaves/at_end/at_end.ml";;

let AT_END_X86 = leaf_x86 "at_end" AT_END_TERM AT_END_RUN;;
let AT_END_LEAF_SPEC = leaf_spec "at_end" 2 AT_END_TERM AT_END_DECLS;;

leaf_audit (leaf_lib_theorems @ at_end_theorems @
            ["AT_END_X86", AT_END_X86; "AT_END_LEAF_SPEC", AT_END_LEAF_SPEC])
           ["at_end_post", at_end_post; "AT_END_RUN", AT_END_RUN; "AT_END_DECLS", AT_END_DECLS;
            "AT_END_LEAF_WF", AT_END_LEAF_WF; "AT_END_X86", AT_END_X86; "AT_END_LEAF_SPEC", AT_END_LEAF_SPEC];;

loadt "native/hol/evidence_gate.ml";;
