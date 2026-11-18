(* ========================================================================= *)
(* pol_max, the record plans' leaf 20 (tcalc/native/PLANS.txt, sections 2   *)
(* and 5): the policy raised to a stream's policy. The program is           *)
(* tcalc/native/leaves/pol_max/pol_max.metta's text (pol_max_prog.txt; image *)
(* record pol_max.hol). No regions; arg0 pol, arg1 p.                       *)
(*                                                                           *)
(* POL_MAX_RUN: every run from a state entry validation accepts ends in     *)
(* pol_max_post: the status word is the outcome, the fuel receipt is kept,  *)
(* and                                                                       *)
(*   FIRED with ret_val MAX pol p when p <= 2;                              *)
(*   REFUSED otherwise.                                                      *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

(* The program, as its text pol_max_prog.txt. *)
let POL_MAX_TERM = new_definition
 `pol_max = (TProg [] [] (TSeq (TInstr (TLoadFrame TyU64 1 22)) (TSeq (TInstr (TLoadFrame TyU64 2 23)) (TSeq (TInstr (TCmp CondUle TyU64 3 2 (OpImm (word 2)))) (TSeq (TIf 3 (TSeq (TInstr (TCmp CondUle TyU64 3 2 (OpReg 1))) (TSeq (TIf 3 (TReturn 1 1) TSkip) (TReturn 1 2))) TSkip) (TReturn 0 3))))))`;;

let POL_MAX_DECLS = prove(`tisa_decls pol_max = []`, REWRITE_TAC[POL_MAX_TERM; tisa_decls]);;

let POL_MAX_LEAF_WF = prove(`tisa_leaf_wf pol_max`, LEAF_WF_TAC POL_MAX_DECLS POL_MAX_TERM);;

(* What every run leaves. *)
let pol_max_post = new_definition
 `pol_max_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    (if val(tisa_fword t 23) <= 2
     then k = 1 /\ tisa_fword u 19 = word(MAX (val(tisa_fword t 22)) (val(tisa_fword t 23)))
     else k = 0)`;;

(* The larger of two words, as the word of the larger value. *)
let POL_MAX_WORD = prove
 (`!a b:int64. (if val b <= val a then a else b) = word(MAX (val a) (val b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAX] THEN
  ASM_CASES_TAC `val(b:int64) = val(a:int64)` THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[th; LE_REFL; WORD_VAL]) THEN
    ASM_MESON_TAC[VAL_EQ];
    ASM_CASES_TAC `val(b:int64) <= val(a:int64)` THEN ASM_REWRITE_TAC[WORD_VAL] THENL
     [SUBGOAL_THEN `~(val(a:int64) <= val(b:int64))` (fun th -> REWRITE_TAC[th; WORD_VAL]) THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `val(a:int64) <= val(b:int64)` (fun th -> REWRITE_TAC[th; WORD_VAL]) THEN ASM_ARITH_TAC]]);;

let POL_MAX_WP = prove
 (`!t. tisa_entry_ok pol_max t ==> tisa_wp (tisa_root pol_max) (\s. F) (pol_max_post t) t`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP LEAF_ENTRY_FRAME) THEN
  REWRITE_TAC[POL_MAX_TERM; tisa_root] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[pol_max_post] THEN LEAF_VAL_NUMERALS_TAC THEN TISA_STATE_NORM_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[GSYM POL_MAX_WORD]);;

let POL_MAX_RUN = prove
 (`!t k u. tisa_entry_ok pol_max t /\ tisa_run pol_max t = TStop k u ==> pol_max_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; POL_MAX_WP]);;

(* Every theorem this file states, for the audits. *)
let pol_max_theorems =
 ["POL_MAX_TERM", POL_MAX_TERM;
  "POL_MAX_DECLS", POL_MAX_DECLS;
  "POL_MAX_LEAF_WF", POL_MAX_LEAF_WF;
  "pol_max_post", pol_max_post;
  "POL_MAX_WORD", POL_MAX_WORD;
  "POL_MAX_WP", POL_MAX_WP;
  "POL_MAX_RUN", POL_MAX_RUN];;
