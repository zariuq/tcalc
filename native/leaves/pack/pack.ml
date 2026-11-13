(* ========================================================================= *)
(* pack, the record plans' leaf 1 (tcalc/native/PLANS.txt): the packed key  *)
(* word tag + 8a. The program is tcalc/native/leaves/pack/pack.metta's text  *)
(* (pack_prog.txt; image record pack.hol). No regions; arg0 a, arg1 the tag.*)
(*                                                                           *)
(* PACK_RUN: every run from a state entry validation accepts ends in        *)
(* pack_post: the status word is the outcome, the fuel receipt is kept, and *)
(*   FIRED with ret_val tag + 8a when a < 2^60 and tag < 8;                 *)
(*   UNSUPPORTED otherwise.                                                 *)
(* With PACK_DECLS and PACK_LEAF_WF that is pl_pack_spec pack               *)
(* (tcalc/native/leaves/leaves_spec.ml, over plans_leaves.ml).              *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

(* The program, as its text pack_prog.txt. *)
let PACK_TERM = new_definition
 `pack = (TProg [] [] (TSeq (TInstr (TLoadFrame TyU64 1 22)) (TSeq (TInstr (TLoadFrame TyU64 2 23)) (TSeq (TInstr (TCmp CondUlt TyU64 3 1 (OpImm (word 1152921504606846976)))) (TSeq (TIf 3 (TSeq (TInstr (TCmp CondUlt TyU64 3 2 (OpImm (word 8)))) (TIf 3 (TSeq (TInstr (TShift ShiftLeft TyU64 4 1 3)) (TSeq (TInstr (TBin BinAdd TyU64 4 4 2)) (TReturn 1 4))) TSkip)) TSkip) (TReturn 2 3))))))`;;

let PACK_DECLS = prove(`tisa_decls pack = []`, REWRITE_TAC[PACK_TERM; tisa_decls]);;

let PACK_LEAF_WF = prove(`tisa_leaf_wf pack`, LEAF_WF_TAC PACK_DECLS PACK_TERM);;

(* What every run leaves. *)
let pack_post = new_definition
 `pack_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    (if val(tisa_fword t 22) < 2 EXP 60 /\ val(tisa_fword t 23) < 8
     then k = 1 /\ tisa_fword u 19 = word(val(tisa_fword t 23) + 8 * val(tisa_fword t 22))
     else k = 2)`;;

(* The key word: the shift and the add, as one word. *)
let PACK_KEY = prove
 (`!a tag:int64. word_add (word_shl a 3) tag = word(val tag + 8 * val a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_shl] THEN CONV_TAC NUM_REDUCE_CONV THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM WORD_VAL] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC);;

let PACK_WP = prove
 (`!t. tisa_entry_ok pack t ==> tisa_wp (tisa_root pack) (\s. F) (pack_post t) t`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP LEAF_ENTRY_FRAME) THEN
  REWRITE_TAC[PACK_TERM; tisa_root] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[pack_post] THEN LEAF_VAL_NUMERALS_TAC THEN TISA_STATE_NORM_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[PACK_KEY]);;

let PACK_RUN = prove
 (`!t k u. tisa_entry_ok pack t /\ tisa_run pack t = TStop k u ==> pack_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; PACK_WP]);;

(* Every theorem this file states, for the audits. *)
let pack_theorems =
 ["PACK_TERM", PACK_TERM;
  "PACK_DECLS", PACK_DECLS;
  "PACK_LEAF_WF", PACK_LEAF_WF;
  "pack_post", pack_post;
  "PACK_KEY", PACK_KEY;
  "PACK_WP", PACK_WP;
  "PACK_RUN", PACK_RUN];;
