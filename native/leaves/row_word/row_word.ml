(* ========================================================================= *)
(* row_word, the record plans' leaf 4 (tcalc/native/PLANS.txt): word w of   *)
(* row i of a table of rows of s words. The program is                       *)
(* tcalc/native/leaves/row_word/row_word.metta's text (row_word_prog.txt;   *)
(* image record row_word.hol). Regions: 0 the rows (RO), 1 the count (RO,   *)
(* word 0 the row count c); v1 the stride s, arg0 the row i, arg1 the word w.*)
(*                                                                           *)
(* ROW_WORD_RUN: every run from a state entry validation accepts ends in    *)
(* row_word_post: the status word is the outcome, the fuel receipt is kept, *)
(* and                                                                       *)
(*   FIRED with ret_val word s i + w of the rows when i < c, w < s and      *)
(*   8 s c <= the rows' length;                                             *)
(*   UNSUPPORTED otherwise.                                                 *)
(* The program is a checks block (row_word_checks: i < c, w < s and the     *)
(* exact product test, LEAF_PRODUCT_GUARD) and an access block              *)
(* (row_word_access), proved apart and joined at row_word_mid.              *)
(* With ROW_WORD_DECLS and ROW_WORD_LEAF_WF that is pl_row_word_spec        *)
(* row_word (tcalc/native/leaves/leaves_spec.ml, over plans_leaves.ml).     *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

(* The program: its two blocks, and its text row_word_prog.txt. *)
let row_word_checks = new_definition
 `row_word_checks = (TSeq (TInstr (TLoadFrame TyU64 2 22)) (TSeq (TInstr (TLoadFrame TyU64 3 23)) (TSeq (TInstr (TLoadFrame TyPtr 10 2)) (TSeq (TInstr (TLoad TyU64 8 1 4 10 (&0:int))) (TSeq (TInstr (TCmp CondUlt TyU64 10 2 (OpReg 4))) (TSeq (TIf 10 TSkip (TReturn 2 10)) (TSeq (TInstr (TCmp CondUlt TyU64 10 3 (OpReg 1))) (TSeq (TIf 10 TSkip (TReturn 2 10)) (TSeq (TInstr (TLoadFrame TyU64 5 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 5 5 3)) (TSeq (TInstr (TCmp CondUlt TyU64 10 5 (OpReg 1))) (TSeq (TIf 10 (TReturn 2 10) TSkip) (TSeq (TInstr (TCmp CondUlt TyU64 10 5 (OpReg 4))) (TSeq (TIf 10 (TReturn 2 10) TSkip) (TSeq (TInstr (TShift ShiftRightU TyU64 6 1 32)) (TSeq (TInstr (TShift ShiftRightU TyU64 7 4 32)) (TSeq (TInstr (TCmp CondNe TyU64 10 6 (OpImm (word 0)))) (TSeq (TInstr (TCmp CondNe TyU64 11 7 (OpImm (word 0)))) (TSeq (TInstr (TBin BinAnd TyBool 10 10 11)) (TSeq (TIf 10 (TReturn 2 10) TSkip) (TSeq (TInstr (TImm TyU64 11 (word 4294967295))) (TSeq (TInstr (TBin BinAnd TyU64 8 1 11)) (TSeq (TInstr (TBin BinAnd TyU64 9 4 11)) (TSeq (TInstr (TBin BinMulLo TyU64 10 6 9)) (TSeq (TInstr (TBin BinMulLo TyU64 11 7 8)) (TSeq (TInstr (TBin BinAdd TyU64 10 10 11)) (TSeq (TInstr (TCmp CondUlt TyU64 11 10 (OpImm (word 536870912)))) (TSeq (TIf 11 TSkip (TReturn 2 11)) (TSeq (TInstr (TShift ShiftLeft TyU64 10 10 32)) (TSeq (TInstr (TBin BinMulLo TyU64 11 8 9)) (TSeq (TInstr (TCmp CondUlt TyU64 6 5 (OpReg 11))) (TSeq (TIf 6 (TReturn 2 6) TSkip) (TSeq (TInstr (TBin BinAdd TyU64 10 10 11)) (TSeq (TInstr (TCmp CondUlt TyU64 6 5 (OpReg 10))) (TIf 6 (TReturn 2 6) TSkip)))))))))))))))))))))))))))))))))))`;;

let row_word_access = new_definition
 `row_word_access = (TSeq (TInstr (TBin BinMulLo TyU64 10 1 2)) (TSeq (TInstr (TBin BinAdd TyU64 10 10 3)) (TSeq (TInstr (TLoadFrame TyPtr 11 0)) (TSeq (TInstr (TAddr 0 11 11 (SOME 10) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 10 11 (&0:int))) (TReturn 1 10))))))`;;

let row_word = new_definition
 `row_word = TProg [(1,0,8); (1,8,8)] [(1,TyU64,0)] (TSeq row_word_checks row_word_access)`;;

let ROW_WORD_TERM = prove
 (`row_word = (TProg [(1,0,8); (1,8,8)] [(1,TyU64,0)] (TSeq (TSeq (TInstr (TLoadFrame TyU64 2 22)) (TSeq (TInstr (TLoadFrame TyU64 3 23)) (TSeq (TInstr (TLoadFrame TyPtr 10 2)) (TSeq (TInstr (TLoad TyU64 8 1 4 10 (&0:int))) (TSeq (TInstr (TCmp CondUlt TyU64 10 2 (OpReg 4))) (TSeq (TIf 10 TSkip (TReturn 2 10)) (TSeq (TInstr (TCmp CondUlt TyU64 10 3 (OpReg 1))) (TSeq (TIf 10 TSkip (TReturn 2 10)) (TSeq (TInstr (TLoadFrame TyU64 5 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 5 5 3)) (TSeq (TInstr (TCmp CondUlt TyU64 10 5 (OpReg 1))) (TSeq (TIf 10 (TReturn 2 10) TSkip) (TSeq (TInstr (TCmp CondUlt TyU64 10 5 (OpReg 4))) (TSeq (TIf 10 (TReturn 2 10) TSkip) (TSeq (TInstr (TShift ShiftRightU TyU64 6 1 32)) (TSeq (TInstr (TShift ShiftRightU TyU64 7 4 32)) (TSeq (TInstr (TCmp CondNe TyU64 10 6 (OpImm (word 0)))) (TSeq (TInstr (TCmp CondNe TyU64 11 7 (OpImm (word 0)))) (TSeq (TInstr (TBin BinAnd TyBool 10 10 11)) (TSeq (TIf 10 (TReturn 2 10) TSkip) (TSeq (TInstr (TImm TyU64 11 (word 4294967295))) (TSeq (TInstr (TBin BinAnd TyU64 8 1 11)) (TSeq (TInstr (TBin BinAnd TyU64 9 4 11)) (TSeq (TInstr (TBin BinMulLo TyU64 10 6 9)) (TSeq (TInstr (TBin BinMulLo TyU64 11 7 8)) (TSeq (TInstr (TBin BinAdd TyU64 10 10 11)) (TSeq (TInstr (TCmp CondUlt TyU64 11 10 (OpImm (word 536870912)))) (TSeq (TIf 11 TSkip (TReturn 2 11)) (TSeq (TInstr (TShift ShiftLeft TyU64 10 10 32)) (TSeq (TInstr (TBin BinMulLo TyU64 11 8 9)) (TSeq (TInstr (TCmp CondUlt TyU64 6 5 (OpReg 11))) (TSeq (TIf 6 (TReturn 2 6) TSkip) (TSeq (TInstr (TBin BinAdd TyU64 10 10 11)) (TSeq (TInstr (TCmp CondUlt TyU64 6 5 (OpReg 10))) (TIf 6 (TReturn 2 6) TSkip))))))))))))))))))))))))))))))))))) (TSeq (TInstr (TBin BinMulLo TyU64 10 1 2)) (TSeq (TInstr (TBin BinAdd TyU64 10 10 3)) (TSeq (TInstr (TLoadFrame TyPtr 11 0)) (TSeq (TInstr (TAddr 0 11 11 (SOME 10) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 10 11 (&0:int))) (TReturn 1 10))))))))`,
  REWRITE_TAC[row_word; row_word_checks; row_word_access]);;

let ROW_WORD_DECLS = prove(`tisa_decls row_word = [(1,0,8); (1,8,8)]`, REWRITE_TAC[row_word; tisa_decls]);;

let ROW_WORD_LEAF_WF = prove(`tisa_leaf_wf row_word`, LEAF_WF_TAC ROW_WORD_DECLS ROW_WORD_TERM);;

(* What every run leaves (pl_w t r i written out: word i of region r). *)
let row_word_post = new_definition
 `row_word_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    (if val(tisa_fword t 22) < val(tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8) /\
        val(tisa_fword t 23) < val(tregs t 1) /\
        8 * val(tregs t 1) * val(tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8) <=
        val(tisa_len t 0)
     then k = 1 /\
          tisa_fword u 19 =
          tisa_read t (word_add (tisa_base t 0)
                        (word(8 * (val(tregs t 1) * val(tisa_fword t 22) + val(tisa_fword t 23))))) 8
     else k = 2)`;;

(* Entry validation: the frame, the count word, the regions below 2^64. *)
let ROW_WORD_ENTRY = prove
 (`!t. tisa_entry_ok row_word t
       ==> val(tregs t 0) + 192 <= 2 EXP 64 /\
           val(tisa_base t 0) + val(tisa_len t 0) < 2 EXP 64 /\
           8 <= val(tisa_len t 1) /\ val(tisa_base t 1) + val(tisa_len t 1) < 2 EXP 64`,
  GEN_TAC THEN
  REWRITE_TAC[row_word; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok;
              tisa_region_ok; tisa_pair_ok; tisa_frame; tisa_base; tisa_len; tisa_canonical; tisa_norm] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* After the checks: the frame, the memory, s, i and w in place, and the   *)
(* checks passed.                                                           *)
let row_word_mid = new_definition
 `row_word_mid t s <=>
    tregs s 0 = tregs t 0 /\ tmem s = tmem t /\
    tregs s 1 = tregs t 1 /\ tregs s 2 = tisa_fword t 22 /\ tregs s 3 = tisa_fword t 23 /\
    val(tisa_fword t 22) < val(tisa_read t (tisa_base t 1) 8) /\
    val(tisa_fword t 23) < val(tregs t 1) /\
    8 * val(tregs t 1) * val(tisa_read t (tisa_base t 1) 8) <= val(tisa_len t 0)`;;

(* The product test against the specification's guard. *)
let ROW_WORD_GUARD_TAC =
  MP_TAC(ISPECL [`tregs t 1`; `tisa_read t (tisa_base t 1) 8`; `val(tisa_len t 0)`;
                 `val(tisa_fword t 22)`; `val(tisa_fword t 23)`] LEAF_PRODUCT_GUARD) THEN
  ASM_REWRITE_TAC[VAL_BOUND_64];;

(* A check that failed: UNSUPPORTED, and the guard is false. *)
let ROW_WORD_STOP_TAC =
  REWRITE_TAC[row_word_post] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  LEAF_VAL_NUMERALS_TAC THEN TISA_STATE_NORM_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  FIRST [ASM_ARITH_TAC; ROW_WORD_GUARD_TAC];;

(* Every check passed. *)
let ROW_WORD_CONT_TAC =
  REWRITE_TAC[row_word_mid] THEN LEAF_VAL_NUMERALS_TAC THEN TISA_STATE_NORM_TAC THEN
  ROW_WORD_GUARD_TAC;;

let ROW_WORD_CHECKS_WP = prove
 (`!t. tisa_entry_ok row_word t
       ==> tisa_wp row_word_checks (row_word_mid t) (row_word_post t) t`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP ROW_WORD_ENTRY) THEN
  REWRITE_TAC[row_word_checks] THEN TISA_VCG_TAC THEN
  FIRST [ROW_WORD_STOP_TAC THEN NO_TAC; ROW_WORD_CONT_TAC THEN NO_TAC]);;

(* The access: the word, at s i + w, inside the rows. *)
let ROW_WORD_ACCESS_WP = prove
 (`!t s. val(tregs t 0) + 192 <= 2 EXP 64 /\
         val(tisa_base t 0) + val(tisa_len t 0) < 2 EXP 64 /\ row_word_mid t s
         ==> tisa_wp row_word_access (\s. F) (row_word_post t) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[row_word_mid] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:tisa_state`; `t:tisa_state`] TISA_SAME_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`val(tregs t 1)`; `val(tisa_fword t 22)`; `val(tisa_fword t 23)`;
                `val(tisa_read t (tisa_base t 1) 8)`; `val(tisa_len t 0)`] LEAF_ROW_INDEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_mul (tregs t 1) (tisa_fword t 22)) = val(tregs t 1) * val(tisa_fword t 22)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LEAF_VAL_MUL_EXACT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add (word_mul (tregs t 1) (tisa_fword t 22)) (tisa_fword t 23)) =
                val(tregs t 1) * val(tisa_fword t 22) + val(tisa_fword t 23)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD_ADD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[row_word_access] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[row_word_post] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[]);;

let ROW_WORD_WP = prove
 (`!t. tisa_entry_ok row_word t ==> tisa_wp (tisa_root row_word) (\s. F) (row_word_post t) t`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[row_word; tisa_root; TISA_WP_SEQ] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  MAP_EVERY EXISTS_TAC [`row_word_mid t`; `row_word_post t`] THEN
  ASM_SIMP_TAC[ROW_WORD_CHECKS_WP] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ROW_WORD_ENTRY) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ROW_WORD_ACCESS_WP THEN ASM_REWRITE_TAC[]);;

let ROW_WORD_RUN = prove
 (`!t k u. tisa_entry_ok row_word t /\ tisa_run row_word t = TStop k u ==> row_word_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; ROW_WORD_WP]);;

(* Every theorem this file states, for the audits. *)
let row_word_theorems =
 ["row_word_checks", row_word_checks;
  "row_word_access", row_word_access;
  "row_word", row_word;
  "ROW_WORD_TERM", ROW_WORD_TERM;
  "ROW_WORD_DECLS", ROW_WORD_DECLS;
  "ROW_WORD_LEAF_WF", ROW_WORD_LEAF_WF;
  "row_word_post", row_word_post;
  "ROW_WORD_ENTRY", ROW_WORD_ENTRY;
  "row_word_mid", row_word_mid;
  "ROW_WORD_CHECKS_WP", ROW_WORD_CHECKS_WP;
  "ROW_WORD_ACCESS_WP", ROW_WORD_ACCESS_WP;
  "ROW_WORD_WP", ROW_WORD_WP;
  "ROW_WORD_RUN", ROW_WORD_RUN];;
