(* ========================================================================= *)
(* live, the record plans' leaf 5 (tcalc/native/PLANS.txt): an id is live   *)
(* when it is below its space's count and its dropped mark is 0. The        *)
(* program is tcalc/native/leaves/live/live.metta's text (live_prog.txt;    *)
(* image record live.hol). Regions: 0 the count (RO, word 0), 1 the marks   *)
(* (RO, one word per id); arg0 the id.                                       *)
(*                                                                           *)
(* LIVE_RUN: every run from a state entry validation accepts ends in        *)
(* live_post: the status word is the outcome, the fuel receipt is kept, and *)
(*   UNSUPPORTED when the marks are shorter than 8 c bytes;                 *)
(*   else FIRED with ret_val the id when id < c and its mark is 0;          *)
(*   else REFUSED.                                                          *)
(* With LIVE_DECLS and LIVE_LEAF_WF that is pl_live_spec live               *)
(* (tcalc/native/leaves/leaves_spec.ml, over plans_leaves.ml).              *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

(* The program, as its text live_prog.txt. *)
let LIVE_TERM = new_definition
 `live = (TProg [(1,8,8); (1,0,8)] [] (TSeq (TInstr (TLoadFrame TyU64 1 22)) (TSeq (TInstr (TLoadFrame TyPtr 5 0)) (TSeq (TInstr (TLoad TyU64 8 0 2 5 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 3 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 3 3 3)) (TSeq (TInstr (TCmp CondUlt TyU64 4 3 (OpReg 2))) (TSeq (TIf 4 (TReturn 2 4) TSkip) (TSeq (TInstr (TCmp CondUlt TyU64 4 1 (OpReg 2))) (TSeq (TIf 4 (TSeq (TInstr (TLoadFrame TyPtr 5 2)) (TSeq (TInstr (TAddr 1 5 5 (SOME 1) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 1 6 5 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 4 6 (OpImm (word 0)))) (TIf 4 (TReturn 1 1) TSkip))))) TSkip) (TReturn 0 4)))))))))))`;;

let LIVE_DECLS = prove(`tisa_decls live = [(1,8,8); (1,0,8)]`, REWRITE_TAC[LIVE_TERM; tisa_decls]);;

let LIVE_LEAF_WF = prove(`tisa_leaf_wf live`, LEAF_WF_TAC LIVE_DECLS LIVE_TERM);;

(* What every run leaves (pl_w t r i written out: word i of region r). *)
let live_post = new_definition
 `live_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    (if 8 * val(tisa_read t (word_add (tisa_base t 0) (word(8 * 0))) 8) <= val(tisa_len t 1)
     then (if val(tisa_fword t 22) < val(tisa_read t (word_add (tisa_base t 0) (word(8 * 0))) 8) /\
              tisa_read t (word_add (tisa_base t 1) (word(8 * val(tisa_fword t 22)))) 8 = word 0
           then k = 1 /\ tisa_fword u 19 = tisa_fword t 22
           else k = 0)
     else k = 2)`;;

(* Entry validation: the frame, the count word, the regions below 2^64. *)
let LIVE_ENTRY = prove
 (`!t. tisa_entry_ok live t
       ==> val(tregs t 0) + 192 <= 2 EXP 64 /\
           8 <= val(tisa_len t 0) /\ val(tisa_base t 0) + val(tisa_len t 0) < 2 EXP 64 /\
           val(tisa_base t 1) + val(tisa_len t 1) < 2 EXP 64`,
  GEN_TAC THEN
  REWRITE_TAC[LIVE_TERM; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok;
              tisa_region_ok; tisa_pair_ok; tisa_frame; tisa_base; tisa_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[]);;

let LIVE_WP = prove
 (`!t. tisa_entry_ok live t ==> tisa_wp (tisa_root live) (\s. F) (live_post t) t`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP LIVE_ENTRY) THEN
  REWRITE_TAC[LIVE_TERM; tisa_root] THEN TISA_VCG_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LEAF_DIV8_LT]) THEN REWRITE_TAC[live_post] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN TISA_STATE_NORM_TAC THEN
  ASM_REWRITE_TAC[]);;

let LIVE_RUN = prove
 (`!t k u. tisa_entry_ok live t /\ tisa_run live t = TStop k u ==> live_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; LIVE_WP]);;

(* Every theorem this file states, for the audits. *)
let live_theorems =
 ["LIVE_TERM", LIVE_TERM;
  "LIVE_DECLS", LIVE_DECLS;
  "LIVE_LEAF_WF", LIVE_LEAF_WF;
  "live_post", live_post;
  "LIVE_ENTRY", LIVE_ENTRY;
  "LIVE_WP", LIVE_WP;
  "LIVE_RUN", LIVE_RUN];;
