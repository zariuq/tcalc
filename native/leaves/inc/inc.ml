(* ========================================================================= *)
(* inc, the reader's leaf 32 (tcalc/native/PLANS.txt, sections 2 and 10): a *)
(* count plus one. The program is tcalc/native/leaves/inc/inc.metta's text  *)
(* (inc_prog.txt; image record inc.hol). No regions; arg0 a.                *)
(*                                                                           *)
(* INC_RUN: every run from a state entry validation accepts ends in         *)
(* inc_post: the status word is the outcome, the fuel receipt is kept, and  *)
(*   FIRED with ret_val a + 1 when a + 1 < 2^62;                            *)
(*   UNSUPPORTED otherwise.                                                 *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

(* The program, as its text inc_prog.txt. *)
let INC_TERM = new_definition
 `inc = (TProg [] [] (TSeq (TInstr (TLoadFrame TyU64 1 22)) (TSeq (TInstr (TCmp CondUlt TyU64 2 1 (OpImm (word 4611686018427387903)))) (TSeq (TIf 2 (TSeq (TInstr (TImm TyU64 3 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 3 1 3)) (TReturn 1 3))) TSkip) (TReturn 2 2)))))`;;

let INC_DECLS = prove(`tisa_decls inc = []`, REWRITE_TAC[INC_TERM; tisa_decls]);;

let INC_LEAF_WF = prove(`tisa_leaf_wf inc`, LEAF_WF_TAC INC_DECLS INC_TERM);;

(* What every run leaves. *)
let inc_post = new_definition
 `inc_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    (if val(tisa_fword t 22) + 1 < 2 EXP 62
     then k = 1 /\ tisa_fword u 19 = word(val(tisa_fword t 22) + 1)
     else k = 2)`;;

(* The sum, as one word. *)
let INC_SUM = prove
 (`!a:int64. word_add a (word 1) = word(val a + 1)`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM WORD_VAL] THEN
  REWRITE_TAC[GSYM WORD_ADD]);;

let INC_WP = prove
 (`!t. tisa_entry_ok inc t ==> tisa_wp (tisa_root inc) (\s. F) (inc_post t) t`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP LEAF_ENTRY_FRAME) THEN
  REWRITE_TAC[INC_TERM; tisa_root] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[inc_post] THEN LEAF_VAL_NUMERALS_TAC THEN TISA_STATE_NORM_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[INC_SUM] THEN ASM_ARITH_TAC);;

let INC_RUN = prove
 (`!t k u. tisa_entry_ok inc t /\ tisa_run inc t = TStop k u ==> inc_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; INC_WP]);;

(* Every theorem this file states, for the audits. *)
let inc_theorems =
 ["INC_TERM", INC_TERM;
  "INC_DECLS", INC_DECLS;
  "INC_LEAF_WF", INC_LEAF_WF;
  "inc_post", inc_post;
  "INC_SUM", INC_SUM;
  "INC_WP", INC_WP;
  "INC_RUN", INC_RUN];;
