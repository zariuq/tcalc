(* ========================================================================= *)
(* Joins the x86 image theorem of row_word (from the t-ISA generator, proved in *)
(* the same process from row_word.hol) with ROW_WORD_RUN (row_word.ml), and gives the  *)
(* uniform image theorem the driver takes of a leaf (leaf_join_lib.ml):     *)
(*   ROW_WORD_X86        the native code's run ends in a state whose p1 run      *)
(*                  satisfies row_word_post;                                        *)
(*   ROW_WORD_LEAF_SPEC  !pc. tisa_leaf_spec row_word row_word_mc pc.                   *)
(* ROW_WORD_LEAF_WF is proved in row_word.ml. Run by tcalc/tisa/hol/                 *)
(* run_x86_evidence.sh as its DRIVER, after the record (leaves/evidence.sh); *)
(* also the audit of row_word.ml and leaf_lib.ml in that process, and the      *)
(* evidence gate (every loaded file with its digest).                       *)
(* ========================================================================= *)

loadt "native/leaves/common/leaf_join_lib.ml";;
loadt "native/leaves/row_word/row_word.ml";;

let ROW_WORD_X86 = leaf_x86 "row_word" ROW_WORD_TERM ROW_WORD_RUN;;
let ROW_WORD_LEAF_SPEC = leaf_spec "row_word" 2 ROW_WORD_TERM ROW_WORD_DECLS;;

leaf_audit (leaf_lib_theorems @ row_word_theorems @
            ["ROW_WORD_X86", ROW_WORD_X86; "ROW_WORD_LEAF_SPEC", ROW_WORD_LEAF_SPEC])
           ["row_word_post", row_word_post; "ROW_WORD_RUN", ROW_WORD_RUN; "ROW_WORD_DECLS", ROW_WORD_DECLS;
            "ROW_WORD_LEAF_WF", ROW_WORD_LEAF_WF; "ROW_WORD_X86", ROW_WORD_X86; "ROW_WORD_LEAF_SPEC", ROW_WORD_LEAF_SPEC];;

loadt "native/hol/evidence_gate.ml";;
