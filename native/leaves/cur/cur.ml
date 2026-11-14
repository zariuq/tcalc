(* ========================================================================= *)
(* cur, the reader's leaf 25 (tcalc/native/PLANS.txt, sections 2 and 10):   *)
(* the cursor. The program is tcalc/native/leaves/cur/cur.metta's text      *)
(* (cur_prog.txt; image record cur.hol). Region 0 the input, region 1 the   *)
(* reader's state (RO, at least 16 bytes; word 0 the cursor). No arguments.  *)
(*                                                                           *)
(* CUR_RUN: every run from a state entry validation accepts ends in         *)
(* cur_post: FIRED, the fuel receipt kept, ret_val word 0 of the state.     *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

(* The program, as its text cur_prog.txt. *)
let CUR_TERM = new_definition
 `cur = (TProg [(1,0,1); (1,16,8)] [] (TSeq (TInstr (TLoadFrame TyPtr 1 2)) (TSeq (TInstr (TLoad TyU64 8 1 2 1 (&0:int))) (TReturn 1 2))))`;;

let CUR_DECLS = prove(`tisa_decls cur = [(1,0,1); (1,16,8)]`, REWRITE_TAC[CUR_TERM; tisa_decls]);;

let CUR_LEAF_WF = prove(`tisa_leaf_wf cur`, LEAF_WF_TAC CUR_DECLS CUR_TERM);;

(* What every run leaves (word 0 of region 1, the cursor, written out). *)
let cur_post = new_definition
 `cur_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    k = 1 /\ tisa_fword u 19 = tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8`;;

(* Entry validation: the frame, the state's 16 bytes, below 2^64. *)
let CUR_ENTRY = prove
 (`!t. tisa_entry_ok cur t
       ==> val(tregs t 0) + 192 <= 2 EXP 64 /\
           16 <= val(tisa_len t 1) /\ val(tisa_base t 1) + val(tisa_len t 1) < 2 EXP 64`,
  GEN_TAC THEN
  REWRITE_TAC[CUR_TERM; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok;
              tisa_region_ok; tisa_pair_ok; tisa_frame; tisa_base; tisa_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[]);;

let CUR_WP = prove
 (`!t. tisa_entry_ok cur t ==> tisa_wp (tisa_root cur) (\s. F) (cur_post t) t`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP CUR_ENTRY) THEN
  REWRITE_TAC[CUR_TERM; tisa_root] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[cur_post] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN TISA_STATE_NORM_TAC THEN
  ASM_REWRITE_TAC[]);;

let CUR_RUN = prove
 (`!t k u. tisa_entry_ok cur t /\ tisa_run cur t = TStop k u ==> cur_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; CUR_WP]);;

(* Every theorem this file states, for the audits. *)
let cur_theorems =
 ["CUR_TERM", CUR_TERM;
  "CUR_DECLS", CUR_DECLS;
  "CUR_LEAF_WF", CUR_LEAF_WF;
  "cur_post", cur_post;
  "CUR_ENTRY", CUR_ENTRY;
  "CUR_WP", CUR_WP;
  "CUR_RUN", CUR_RUN];;
