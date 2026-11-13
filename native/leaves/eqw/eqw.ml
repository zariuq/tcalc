(* ========================================================================= *)
(* eqw, the record plans' leaf 3 (tcalc/native/PLANS.txt): a guard that two *)
(* control words are equal. The program is tcalc/native/leaves/eqw/        *)
(* eqw.metta's text (eqw_prog.txt; image record eqw.hol). No regions; arg0  *)
(* and arg1.                                                                 *)
(*                                                                           *)
(* EQW_RUN: every run from a state entry validation accepts ends in         *)
(* eqw_post: the status word is the outcome, the fuel receipt is kept, and  *)
(*   FIRED with ret_val arg0 when arg0 = arg1;                              *)
(*   REFUSED otherwise.                                                     *)
(* With EQW_DECLS and EQW_LEAF_WF that is pl_eqw_spec eqw                   *)
(* (tcalc/native/leaves/leaves_spec.ml, over plans_leaves.ml).              *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

(* The program, as its text eqw_prog.txt. *)
let EQW_TERM = new_definition
 `eqw = (TProg [] [] (TSeq (TInstr (TLoadFrame TyU64 1 22)) (TSeq (TInstr (TLoadFrame TyU64 2 23)) (TSeq (TInstr (TCmp CondEq TyU64 3 1 (OpReg 2))) (TSeq (TIf 3 (TReturn 1 1) TSkip) (TReturn 0 3))))))`;;

let EQW_DECLS = prove(`tisa_decls eqw = []`, REWRITE_TAC[EQW_TERM; tisa_decls]);;

let EQW_LEAF_WF = prove(`tisa_leaf_wf eqw`, LEAF_WF_TAC EQW_DECLS EQW_TERM);;

(* What every run leaves. *)
let eqw_post = new_definition
 `eqw_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    (if tisa_fword t 22 = tisa_fword t 23
     then k = 1 /\ tisa_fword u 19 = tisa_fword t 22
     else k = 0)`;;

let EQW_WP = prove
 (`!t. tisa_entry_ok eqw t ==> tisa_wp (tisa_root eqw) (\s. F) (eqw_post t) t`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP LEAF_ENTRY_FRAME) THEN
  REWRITE_TAC[EQW_TERM; tisa_root] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[eqw_post] THEN TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[]);;

let EQW_RUN = prove
 (`!t k u. tisa_entry_ok eqw t /\ tisa_run eqw t = TStop k u ==> eqw_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; EQW_WP]);;

(* Every theorem this file states, for the audits. *)
let eqw_theorems =
 ["EQW_TERM", EQW_TERM;
  "EQW_DECLS", EQW_DECLS;
  "EQW_LEAF_WF", EQW_LEAF_WF;
  "eqw_post", eqw_post;
  "EQW_WP", EQW_WP;
  "EQW_RUN", EQW_RUN];;
