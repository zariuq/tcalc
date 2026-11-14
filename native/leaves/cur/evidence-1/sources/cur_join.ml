(* ========================================================================= *)
(* Joins the x86 image theorem of cur (from the t-ISA generator, proved in  *)
(* the same process from cur.hol) with CUR_RUN (cur.ml), and gives the      *)
(* uniform image theorem the driver takes of a leaf (leaf_join_lib.ml):     *)
(*   CUR_X86        the native code's run ends in a state whose p1 run      *)
(*                  satisfies cur_post;                                       *)
(*   CUR_LEAF_SPEC  !pc. tisa_leaf_spec cur cur_mc pc.                     *)
(* CUR_LEAF_WF is proved in cur.ml. Run by tcalc/tisa/hol/                  *)
(* run_x86_evidence.sh as its DRIVER, after the record (leaves/evidence.sh); *)
(* also the audit of cur.ml and leaf_lib.ml in that process, and the        *)
(* evidence gate (every loaded file with its digest).                        *)
(* ========================================================================= *)

loadt "native/leaves/common/leaf_join_lib.ml";;
loadt "native/leaves/cur/cur.ml";;

let CUR_X86 = leaf_x86 "cur" CUR_TERM CUR_RUN;;
let CUR_LEAF_SPEC = leaf_spec "cur" 2 CUR_TERM CUR_DECLS;;

leaf_audit (leaf_lib_theorems @ cur_theorems @
            ["CUR_X86", CUR_X86; "CUR_LEAF_SPEC", CUR_LEAF_SPEC])
           ["cur_post", cur_post; "CUR_RUN", CUR_RUN; "CUR_DECLS", CUR_DECLS;
            "CUR_LEAF_WF", CUR_LEAF_WF; "CUR_X86", CUR_X86; "CUR_LEAF_SPEC", CUR_LEAF_SPEC];;

loadt "native/hol/evidence_gate.ml";;
