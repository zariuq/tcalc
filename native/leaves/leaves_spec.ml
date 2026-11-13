(* ========================================================================= *)
(* The plan leaves against their specifications (tcalc/native/hol/          *)
(* plans_leaves.ml): PL_<LEAF>_SPEC is pl_<leaf>_spec <leaf>, from the      *)
(* leaf's run theorem (<LEAF>_RUN: every run's post), its declarations and  *)
(* its static well-formedness. pl_w t r i, word i of region r, is the read  *)
(* each post writes out.                                                    *)
(*                                                                           *)
(* Loaded after the Model world (plans_abs.ml) and plans_leaves.ml, in a     *)
(* session on s2n-bignum's base (leaves/audit.sh).                          *)
(*                                                                           *)
(* put_word's UNSUPPORTED case keeps every word inside the table: words past *)
(* it can be the frame's status word, which every stop writes (put_word.ml). *)
(* ========================================================================= *)

needs "native/hol/plans_leaves.ml";;
needs "native/leaves/pack/pack.ml";;
needs "native/leaves/unpack/unpack.ml";;
needs "native/leaves/eqw/eqw.ml";;
needs "native/leaves/row_word/row_word.ml";;
needs "native/leaves/live/live.ml";;
needs "native/leaves/append_row/append_row.ml";;
needs "native/leaves/put_word/put_word.ml";;

(* pl_<leaf>_spec <leaf>: pl_leaf_ok's status and fuel words and the       *)
(* specification's clause, both from the run theorem's post.               *)
let LEAF_BRIDGE_TAC spec_def run_th post_def wf_th decls_th =
  REWRITE_TAC[spec_def; pl_leaf_ok; wf_th; decls_th] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] run_th) THEN
  ASM_REWRITE_TAC[post_def; pl_w] THEN SIMP_TAC[];;

let PL_PACK_SPEC = prove
 (`pl_pack_spec pack`,
  LEAF_BRIDGE_TAC pl_pack_spec PACK_RUN pack_post PACK_LEAF_WF PACK_DECLS);;

let PL_UNPACK_SPEC = prove
 (`pl_unpack_spec unpack`,
  LEAF_BRIDGE_TAC pl_unpack_spec UNPACK_RUN unpack_post UNPACK_LEAF_WF UNPACK_DECLS);;

let PL_EQW_SPEC = prove
 (`pl_eqw_spec eqw`,
  LEAF_BRIDGE_TAC pl_eqw_spec EQW_RUN eqw_post EQW_LEAF_WF EQW_DECLS);;

let PL_ROW_WORD_SPEC = prove
 (`pl_row_word_spec row_word`,
  LEAF_BRIDGE_TAC pl_row_word_spec ROW_WORD_RUN row_word_post ROW_WORD_LEAF_WF ROW_WORD_DECLS);;

let PL_LIVE_SPEC = prove
 (`pl_live_spec live`,
  LEAF_BRIDGE_TAC pl_live_spec LIVE_RUN live_post LIVE_LEAF_WF LIVE_DECLS);;

let PL_APPEND_ROW_SPEC = prove
 (`pl_append_row_spec append_row`,
  LEAF_BRIDGE_TAC pl_append_row_spec APPEND_ROW_RUN append_row_post APPEND_ROW_LEAF_WF
                  APPEND_ROW_DECLS);;

let PL_PUT_WORD_SPEC = prove
 (`pl_put_word_spec put_word`,
  LEAF_BRIDGE_TAC pl_put_word_spec PUT_WORD_RUN put_word_post PUT_WORD_LEAF_WF PUT_WORD_DECLS);;

(* Every theorem this file states, for the audits. *)
let leaves_spec_theorems =
 ["PL_PACK_SPEC", PL_PACK_SPEC;
  "PL_UNPACK_SPEC", PL_UNPACK_SPEC;
  "PL_EQW_SPEC", PL_EQW_SPEC;
  "PL_ROW_WORD_SPEC", PL_ROW_WORD_SPEC;
  "PL_LIVE_SPEC", PL_LIVE_SPEC;
  "PL_APPEND_ROW_SPEC", PL_APPEND_ROW_SPEC;
  "PL_PUT_WORD_SPEC", PL_PUT_WORD_SPEC];;
