(* ========================================================================= *)
(* Joins the x86 image theorem of le8_next (from the t-ISA generator, proved *)
(* in the same process from le8_next.hol) with LE8_NEXT_RUN (le8_next.ml),   *)
(* and gives the uniform image theorem the driver takes of a leaf            *)
(* (leaf_join_lib.ml):                                                       *)
(*   LE8_NEXT_X86  the native code's run ends in a state whose p1 run        *)
(*                 satisfies le8_next_post;                                  *)
(*   LE8_NEXT_LEAF_SPEC  !pc. tisa_leaf_spec le8_next le8_next_mc pc.        *)
(* LE8_NEXT_LEAF_WF is proved in le8_next.ml. Run by tcalc/tisa/hol/         *)
(* run_x86_evidence.sh as its DRIVER, after the record (leaves/evidence.sh); *)
(* also the audit of le8_next.ml and leaf_lib.ml in that process, and the    *)
(* evidence gate (every loaded file with its digest).                        *)
(* ========================================================================= *)

loadt "native/leaves/common/leaf_join_lib.ml";;
loadt "native/leaves/le8_next/le8_next.ml";;

let LE8_NEXT_X86 = leaf_x86 "le8_next" LE8_NEXT_TERM LE8_NEXT_RUN;;
let LE8_NEXT_LEAF_SPEC = leaf_spec "le8_next" 2 LE8_NEXT_TERM LE8_NEXT_DECLS;;

leaf_audit (leaf_lib_theorems @ le8_next_theorems @
            ["LE8_NEXT_X86", LE8_NEXT_X86; "LE8_NEXT_LEAF_SPEC", LE8_NEXT_LEAF_SPEC])
           ["le8_next_post", le8_next_post; "LE8_NEXT_RUN", LE8_NEXT_RUN; "LE8_NEXT_DECLS", LE8_NEXT_DECLS;
            "LE8_NEXT_LEAF_WF", LE8_NEXT_LEAF_WF; "LE8_NEXT_X86", LE8_NEXT_X86; "LE8_NEXT_LEAF_SPEC", LE8_NEXT_LEAF_SPEC];;

loadt "native/hol/evidence_gate.ml";;
