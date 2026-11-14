(* ========================================================================= *)
(* skip, the reader's leaf 28 (tcalc/native/PLANS.txt, sections 2 and 10):  *)
(* the cursor advanced past n bytes. The program is tcalc/native/leaves/    *)
(* skip/skip.metta's text (skip_prog.txt; image record skip.hol). Region 0  *)
(* the input, region 1 the reader's state (RW, at least 16 bytes; word 0 the *)
(* cursor). Argument: arg0 n.                                                *)
(*                                                                           *)
(* SKIP_RUN: every run from a state entry validation accepts ends in        *)
(* skip_post: FIRED with c + n, written to the state's word 0, when c + n is *)
(* at most the input's length; else REFUSED; the fuel receipt kept.         *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

(* The program, as its text skip_prog.txt. *)
let SKIP_TERM = new_definition
 `skip = (TProg [(1,0,1); (2,16,8)] [] (TSeq (TInstr (TLoadFrame TyPtr 1 2)) (TSeq (TInstr (TLoad TyU64 8 1 2 1 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 3 1)) (TSeq (TInstr (TLoadFrame TyU64 4 22)) (TSeq (TInstr (TCmp CondUle TyU64 5 2 (OpReg 3))) (TSeq (TIf 5 (TSeq (TInstr (TBin BinSub TyU64 6 3 2)) (TSeq (TInstr (TCmp CondUle TyU64 5 4 (OpReg 6))) (TIf 5 (TSeq (TInstr (TBin BinAdd TyU64 2 2 4)) (TSeq (TInstr (TStore 8 1 1 (&0:int) 2)) (TReturn 1 2))) TSkip))) TSkip) (TSeq (TInstr (TImm TyU64 5 (word 0))) (TReturn 0 5)))))))))`;;

let SKIP_DECLS = prove(`tisa_decls skip = [(1,0,1); (2,16,8)]`, REWRITE_TAC[SKIP_TERM; tisa_decls]);;

let SKIP_LEAF_WF = prove(`tisa_leaf_wf skip`, LEAF_WF_TAC SKIP_DECLS SKIP_TERM);;

(* What every run leaves: the cursor c, word 0 of region 1, and n, arg0. *)
let skip_post = new_definition
 `skip_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    (if val(tisa_read t (tisa_base t 1) 8) + val(tisa_fword t 22) <= val(tisa_len t 0)
     then k = 1 /\
          tisa_fword u 19 = word(val(tisa_read t (tisa_base t 1) 8) + val(tisa_fword t 22)) /\
          tisa_read u (tisa_base t 1) 8 = tisa_fword u 19
     else k = 0)`;;

(* Entry validation: the frame, both regions below 2^64 and apart. *)
let SKIP_ENTRY = prove
 (`!st. tisa_entry_ok skip st
        ==> val(tregs st 0) + 192 <= 2 EXP 64 /\
            val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64 /\
            (val(tisa_len st 0) = 0 \/
             val(tisa_base st 0) + val(tisa_len st 0) <= val(tregs st 0) + 144 \/
             val(tregs st 0) + 192 <= val(tisa_base st 0)) /\
            16 <= val(tisa_len st 1) /\
            val(tisa_base st 1) + val(tisa_len st 1) < 2 EXP 64 /\
            (val(tisa_base st 1) + val(tisa_len st 1) <= val(tregs st 0) \/
             val(tregs st 0) + 192 <= val(tisa_base st 1)) /\
            (val(tisa_len st 0) = 0 \/
             val(tisa_base st 0) + val(tisa_len st 0) <= val(tisa_base st 1) \/
             val(tisa_base st 1) + val(tisa_len st 1) <= val(tisa_base st 0))`,
  GEN_TAC THEN
  REWRITE_TAC[SKIP_TERM; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok;
              tisa_region_ok; tisa_pair_ok; tisa_frame; tisa_base; tisa_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(val(tisa_fword st 3) = 0)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `val(tisa_fword st 1) = 0` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* A sum of words, as one word. *)
let SKIP_SUM = prove(`!a b:int64. word_add a b = word(val a + val b)`,
  REWRITE_TAC[WORD_ADD; WORD_VAL]);;

(* Each path's end: the frame's words and the state's word 0 read off, the  *)
(* branch conditions as arithmetic on the cursor, the length and n.         *)
let SKIP_CASE_TAC =
  REWRITE_TAC[skip_post] THEN TISA_STATE_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_CASES]) THEN REWRITE_TAC[SKIP_SUM] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term is_cond) (concl th)))) THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;;

let SKIP_WP = prove
 (`!t. tisa_entry_ok skip t ==> tisa_wp (tisa_root skip) (\s. F) (skip_post t) t`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP SKIP_ENTRY) THEN
  REWRITE_TAC[SKIP_TERM; tisa_root] THEN TISA_VCG_TAC THEN SKIP_CASE_TAC);;

let SKIP_RUN = prove
 (`!t k u. tisa_entry_ok skip t /\ tisa_run skip t = TStop k u ==> skip_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; SKIP_WP]);;

(* Every theorem this file states, for the audits. *)
let skip_theorems =
 ["SKIP_TERM", SKIP_TERM;
  "SKIP_DECLS", SKIP_DECLS;
  "SKIP_LEAF_WF", SKIP_LEAF_WF;
  "skip_post", skip_post;
  "SKIP_ENTRY", SKIP_ENTRY;
  "SKIP_SUM", SKIP_SUM;
  "SKIP_WP", SKIP_WP;
  "SKIP_RUN", SKIP_RUN];;
