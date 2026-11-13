(* ========================================================================= *)
(* Joins the x86 image theorem of put_word (from the t-ISA generator, proved in *)
(* the same process from put_word.hol) with PUT_WORD_RUN (put_word.ml), and gives the  *)
(* uniform image theorem the driver takes of a leaf (leaf_join_lib.ml):     *)
(*   PUT_WORD_X86        the native code's run ends in a state whose p1 run      *)
(*                  satisfies put_word_post;                                        *)
(*   PUT_WORD_LEAF_SPEC  !pc. tisa_leaf_spec put_word put_word_mc pc.                   *)
(* PUT_WORD_LEAF_WF is proved in put_word.ml. Run by tcalc/tisa/hol/                 *)
(* run_x86_evidence.sh as its DRIVER, after the record (leaves/evidence.sh); *)
(* also the audit of put_word.ml and leaf_lib.ml in that process, and the      *)
(* evidence gate (every loaded file with its digest).                       *)
(* ========================================================================= *)

loadt "native/leaves/common/leaf_join_lib.ml";;
loadt "native/leaves/put_word/put_word.ml";;

let PUT_WORD_X86 = leaf_x86 "put_word" PUT_WORD_TERM PUT_WORD_RUN;;
let PUT_WORD_LEAF_SPEC = leaf_spec "put_word" 2 PUT_WORD_TERM PUT_WORD_DECLS;;

leaf_audit (leaf_lib_theorems @ put_word_theorems @
            ["PUT_WORD_X86", PUT_WORD_X86; "PUT_WORD_LEAF_SPEC", PUT_WORD_LEAF_SPEC])
           ["put_word_post", put_word_post; "PUT_WORD_RUN", PUT_WORD_RUN; "PUT_WORD_DECLS", PUT_WORD_DECLS;
            "PUT_WORD_LEAF_WF", PUT_WORD_LEAF_WF; "PUT_WORD_X86", PUT_WORD_X86; "PUT_WORD_LEAF_SPEC", PUT_WORD_LEAF_SPEC];;

loadt "native/hol/evidence_gate.ml";;
