(* ========================================================================= *)
(* at_end, the reader's leaf 30 (tcalc/native/PLANS.txt, sections 2 and 10): *)
(* the input fully read. The program is tcalc/native/leaves/at_end/          *)
(* at_end.metta's text (at_end_prog.txt; image record at_end.hol). Region 0  *)
(* the input, region 1 the reader's state (RO, at least 16 bytes; word 0 the *)
(* cursor). No arguments.                                                    *)
(*                                                                           *)
(* AT_END_RUN: every run from a state entry validation accepts ends in      *)
(* at_end_post: FIRED exactly when the cursor is the input's length, else   *)
(* REFUSED; the fuel receipt kept.                                           *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

(* The program, as its text at_end_prog.txt. *)
let AT_END_TERM = new_definition
 `at_end = (TProg [(1,0,1); (1,16,8)] [] (TSeq (TInstr (TLoadFrame TyPtr 1 2)) (TSeq (TInstr (TLoad TyU64 8 1 2 1 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 3 1)) (TSeq (TInstr (TCmp CondEq TyU64 4 2 (OpReg 3))) (TSeq (TIf 4 (TReturn 1 4) TSkip) (TReturn 0 4)))))))`;;

let AT_END_DECLS = prove(`tisa_decls at_end = [(1,0,1); (1,16,8)]`, REWRITE_TAC[AT_END_TERM; tisa_decls]);;

let AT_END_LEAF_WF = prove(`tisa_leaf_wf at_end`, LEAF_WF_TAC AT_END_DECLS AT_END_TERM);;

(* What every run leaves: FIRED exactly when word 0 of region 1, the        *)
(* cursor, is the length of region 0.                                        *)
let at_end_post = new_definition
 `at_end_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    k = (if tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8 = tisa_len t 0 then 1 else 0)`;;

(* Entry validation: the frame, the state's 16 bytes, below 2^64. *)
let AT_END_ENTRY = prove
 (`!t. tisa_entry_ok at_end t
       ==> val(tregs t 0) + 192 <= 2 EXP 64 /\
           16 <= val(tisa_len t 1) /\ val(tisa_base t 1) + val(tisa_len t 1) < 2 EXP 64`,
  GEN_TAC THEN
  REWRITE_TAC[AT_END_TERM; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok;
              tisa_region_ok; tisa_pair_ok; tisa_frame; tisa_base; tisa_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[]);;

let AT_END_WP = prove
 (`!t. tisa_entry_ok at_end t ==> tisa_wp (tisa_root at_end) (\s. F) (at_end_post t) t`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP AT_END_ENTRY) THEN
  REWRITE_TAC[AT_END_TERM; tisa_root] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[at_end_post] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN TISA_STATE_NORM_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let AT_END_RUN = prove
 (`!t k u. tisa_entry_ok at_end t /\ tisa_run at_end t = TStop k u ==> at_end_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; AT_END_WP]);;

(* Every theorem this file states, for the audits. *)
let at_end_theorems =
 ["AT_END_TERM", AT_END_TERM;
  "AT_END_DECLS", AT_END_DECLS;
  "AT_END_LEAF_WF", AT_END_LEAF_WF;
  "at_end_post", at_end_post;
  "AT_END_ENTRY", AT_END_ENTRY;
  "AT_END_WP", AT_END_WP;
  "AT_END_RUN", AT_END_RUN];;
