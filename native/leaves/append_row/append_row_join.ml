(* ========================================================================= *)
(* Joins the x86 image theorem of append_row (from the t-ISA generator, proved in *)
(* the same process from append_row.hol) with APPEND_ROW_RUN (append_row.ml), and gives the  *)
(* uniform image theorem the driver takes of a leaf (leaf_join_lib.ml):     *)
(*   APPEND_ROW_X86        the native code's run ends in a state whose p1 run      *)
(*                  satisfies append_row_post;                                        *)
(*   APPEND_ROW_LEAF_SPEC  !pc. tisa_leaf_spec append_row append_row_mc pc.                   *)
(* APPEND_ROW_LEAF_WF is proved in append_row.ml. Run by tcalc/tisa/hol/                 *)
(* run_x86_evidence.sh as its DRIVER, after the record (leaves/evidence.sh); *)
(* also the audit of append_row.ml and leaf_lib.ml in that process, and the      *)
(* evidence gate (every loaded file with its digest).                       *)
(* ========================================================================= *)

loadt "native/leaves/common/leaf_join_lib.ml";;
loadt "native/leaves/append_row/append_row.ml";;

let APPEND_ROW_X86 = leaf_x86 "append_row" APPEND_ROW_TERM APPEND_ROW_RUN;;
let APPEND_ROW_LEAF_SPEC = leaf_spec "append_row" 2 APPEND_ROW_TERM APPEND_ROW_DECLS;;

leaf_audit (leaf_lib_theorems @ append_row_theorems @
            ["APPEND_ROW_X86", APPEND_ROW_X86; "APPEND_ROW_LEAF_SPEC", APPEND_ROW_LEAF_SPEC])
           ["append_row_post", append_row_post; "APPEND_ROW_RUN", APPEND_ROW_RUN; "APPEND_ROW_DECLS", APPEND_ROW_DECLS;
            "APPEND_ROW_LEAF_WF", APPEND_ROW_LEAF_WF; "APPEND_ROW_X86", APPEND_ROW_X86; "APPEND_ROW_LEAF_SPEC", APPEND_ROW_LEAF_SPEC];;

loadt "native/hol/evidence_gate.ml";;
