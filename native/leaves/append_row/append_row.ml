(* ========================================================================= *)
(* append_row, the record plans' leaf 6 (tcalc/native/PLANS.txt): append a  *)
(* row of w words to a table and count it. The program is                   *)
(* tcalc/native/leaves/append_row/append_row.metta's text                    *)
(* (append_row_prog.txt; image record append_row.hol). Regions: 0 the rows  *)
(* (RW), 1 the count (RW, word 0 the row count c); v1 the width w, the row's *)
(* words arg0, arg1, v2, v3, v4.                                            *)
(*                                                                           *)
(* APPEND_ROW_RUN: every run from a state entry validation accepts ends in  *)
(* append_row_post: the status word is the outcome, the fuel receipt is     *)
(* kept, and                                                                 *)
(*   FIRED with ret_val c when 1 <= w <= 5 and 8 w (c + 1) <= the rows'     *)
(*   length: the row's words at words w c + j (j < w), the count c + 1, the *)
(*   rows below w c kept;                                                   *)
(*   UNSUPPORTED otherwise: the count and every word of the rows kept.      *)
(* The program is a checks block (append_row_checks, APPEND_ROW_GUARD) and *)
(* an access block (append_row_access), proved apart and joined at          *)
(* append_row_mid. With APPEND_ROW_DECLS and APPEND_ROW_LEAF_WF that is     *)
(* pl_append_row_spec append_row (tcalc/native/leaves/leaves_spec.ml, over  *)
(* plans_leaves.ml).                                                        *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

(* The program: its two blocks, and its text append_row_prog.txt. *)
let append_row_checks = new_definition
 `append_row_checks = (TSeq (TInstr (TLoadFrame TyPtr 8 2)) (TSeq (TInstr (TLoad TyU64 8 1 5 8 (&0:int))) (TSeq (TInstr (TCmp CondUlt TyU64 7 1 (OpImm (word 1)))) (TSeq (TIf 7 (TReturn 2 7) TSkip) (TSeq (TInstr (TCmp CondUlt TyU64 7 1 (OpImm (word 6)))) (TSeq (TIf 7 TSkip (TReturn 2 7)) (TSeq (TInstr (TLoadFrame TyU64 6 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 6 6 3)) (TSeq (TInstr (TCmp CondUlt TyU64 7 5 (OpReg 6))) (TSeq (TIf 7 TSkip (TReturn 2 7)) (TSeq (TInstr (TImm TyU64 7 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 10 5 7)) (TSeq (TInstr (TBin BinMulLo TyU64 10 10 1)) (TSeq (TInstr (TCmp CondUlt TyU64 7 6 (OpReg 10))) (TIf 7 (TReturn 2 7) TSkip)))))))))))))))`;;

let append_row_access = new_definition
 `append_row_access = (TSeq (TInstr (TBin BinMulLo TyU64 10 1 5)) (TSeq (TInstr (TLoadFrame TyPtr 8 0)) (TSeq (TInstr (TAddr 0 8 8 (SOME 10) 3 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 9 22)) (TSeq (TInstr (TStore 8 0 8 (&0:int) 9)) (TSeq (TInstr (TCmp CondUlt TyU64 7 1 (OpImm (word 2)))) (TSeq (TIf 7 TSkip (TSeq (TInstr (TLoadFrame TyU64 9 23)) (TInstr (TStore 8 0 8 (&8:int) 9)))) (TSeq (TInstr (TCmp CondUlt TyU64 7 1 (OpImm (word 3)))) (TSeq (TIf 7 TSkip (TInstr (TStore 8 0 8 (&16:int) 2))) (TSeq (TInstr (TCmp CondUlt TyU64 7 1 (OpImm (word 4)))) (TSeq (TIf 7 TSkip (TInstr (TStore 8 0 8 (&24:int) 3))) (TSeq (TInstr (TCmp CondUlt TyU64 7 1 (OpImm (word 5)))) (TSeq (TIf 7 TSkip (TInstr (TStore 8 0 8 (&32:int) 4))) (TSeq (TInstr (TImm TyU64 7 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 7 5 7)) (TSeq (TInstr (TLoadFrame TyPtr 8 2)) (TSeq (TInstr (TStore 8 1 8 (&0:int) 7)) (TReturn 1 5))))))))))))))))))`;;

let append_row = new_definition
 `append_row = TProg [(2,0,8); (2,8,8)] [(1,TyU64,0); (2,TyU64,0); (3,TyU64,0); (4,TyU64,0)] (TSeq append_row_checks append_row_access)`;;

let APPEND_ROW_TERM = prove
 (`append_row = (TProg [(2,0,8); (2,8,8)] [(1,TyU64,0); (2,TyU64,0); (3,TyU64,0); (4,TyU64,0)] (TSeq (TSeq (TInstr (TLoadFrame TyPtr 8 2)) (TSeq (TInstr (TLoad TyU64 8 1 5 8 (&0:int))) (TSeq (TInstr (TCmp CondUlt TyU64 7 1 (OpImm (word 1)))) (TSeq (TIf 7 (TReturn 2 7) TSkip) (TSeq (TInstr (TCmp CondUlt TyU64 7 1 (OpImm (word 6)))) (TSeq (TIf 7 TSkip (TReturn 2 7)) (TSeq (TInstr (TLoadFrame TyU64 6 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 6 6 3)) (TSeq (TInstr (TCmp CondUlt TyU64 7 5 (OpReg 6))) (TSeq (TIf 7 TSkip (TReturn 2 7)) (TSeq (TInstr (TImm TyU64 7 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 10 5 7)) (TSeq (TInstr (TBin BinMulLo TyU64 10 10 1)) (TSeq (TInstr (TCmp CondUlt TyU64 7 6 (OpReg 10))) (TIf 7 (TReturn 2 7) TSkip))))))))))))))) (TSeq (TInstr (TBin BinMulLo TyU64 10 1 5)) (TSeq (TInstr (TLoadFrame TyPtr 8 0)) (TSeq (TInstr (TAddr 0 8 8 (SOME 10) 3 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 9 22)) (TSeq (TInstr (TStore 8 0 8 (&0:int) 9)) (TSeq (TInstr (TCmp CondUlt TyU64 7 1 (OpImm (word 2)))) (TSeq (TIf 7 TSkip (TSeq (TInstr (TLoadFrame TyU64 9 23)) (TInstr (TStore 8 0 8 (&8:int) 9)))) (TSeq (TInstr (TCmp CondUlt TyU64 7 1 (OpImm (word 3)))) (TSeq (TIf 7 TSkip (TInstr (TStore 8 0 8 (&16:int) 2))) (TSeq (TInstr (TCmp CondUlt TyU64 7 1 (OpImm (word 4)))) (TSeq (TIf 7 TSkip (TInstr (TStore 8 0 8 (&24:int) 3))) (TSeq (TInstr (TCmp CondUlt TyU64 7 1 (OpImm (word 5)))) (TSeq (TIf 7 TSkip (TInstr (TStore 8 0 8 (&32:int) 4))) (TSeq (TInstr (TImm TyU64 7 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 7 5 7)) (TSeq (TInstr (TLoadFrame TyPtr 8 2)) (TSeq (TInstr (TStore 8 1 8 (&0:int) 7)) (TReturn 1 5))))))))))))))))))))`,
  REWRITE_TAC[append_row; append_row_checks; append_row_access]);;

let APPEND_ROW_DECLS = prove(`tisa_decls append_row = [(2,0,8); (2,8,8)]`, REWRITE_TAC[append_row; tisa_decls]);;

let APPEND_ROW_LEAF_WF = prove(`tisa_leaf_wf append_row`, LEAF_WF_TAC APPEND_ROW_DECLS APPEND_ROW_TERM);;

(* What every run leaves (pl_w t r i written out: word i of region r). *)
let append_row_post = new_definition
 `append_row_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    (if 1 <= val(tregs t 1) /\ val(tregs t 1) <= 5 /\
        8 * val(tregs t 1) * (val(tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8) + 1) <=
        val(tisa_len t 0)
     then k = 1 /\ tisa_fword u 19 = tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8 /\
          tisa_read u (word_add (tisa_base u 1) (word(8 * 0))) 8 =
          word(val(tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8) + 1) /\
          (!j. j < val(tregs t 1)
               ==> tisa_read u (word_add (tisa_base u 0)
                     (word(8 * (val(tregs t 1) *
                                val(tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8) + j)))) 8 =
                   EL j [tisa_fword t 22; tisa_fword t 23; tregs t 2; tregs t 3; tregs t 4]) /\
          (!j. j < val(tregs t 1) * val(tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8)
               ==> tisa_read u (word_add (tisa_base u 0) (word(8 * j))) 8 =
                   tisa_read t (word_add (tisa_base t 0) (word(8 * j))) 8)
     else k = 2 /\
          tisa_read u (word_add (tisa_base u 1) (word(8 * 0))) 8 =
          tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8 /\
          (!j. 8 * j + 8 <= val(tisa_len t 0)
               ==> tisa_read u (word_add (tisa_base u 0) (word(8 * j))) 8 =
                   tisa_read t (word_add (tisa_base t 0) (word(8 * j))) 8))`;;

(* Entry validation: the frame, the regions below 2^64, apart from the     *)
(* frame and from each other, the count word.                             *)
let APPEND_ROW_ENTRY = prove
 (`!t. tisa_entry_ok append_row t
       ==> val(tregs t 0) + 192 <= 2 EXP 64 /\
           val(tisa_base t 0) + val(tisa_len t 0) < 2 EXP 64 /\
           (val(tisa_len t 0) = 0 \/
            val(tisa_base t 0) + val(tisa_len t 0) <= val(tregs t 0) \/
            val(tregs t 0) + 192 <= val(tisa_base t 0)) /\
           8 <= val(tisa_len t 1) /\ val(tisa_base t 1) + val(tisa_len t 1) < 2 EXP 64 /\
           (val(tisa_base t 1) + val(tisa_len t 1) <= val(tregs t 0) \/
            val(tregs t 0) + 192 <= val(tisa_base t 1)) /\
           (val(tisa_len t 0) = 0 \/
            val(tisa_base t 0) + val(tisa_len t 0) <= val(tisa_base t 1) \/
            val(tisa_base t 1) + val(tisa_len t 1) <= val(tisa_base t 0))`,
  GEN_TAC THEN
  REWRITE_TAC[append_row; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok;
              tisa_region_ok; tisa_pair_ok; tisa_frame; tisa_base; tisa_len; tisa_canonical; tisa_norm] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TISA_FOCUS_ARITH_TAC);;

(* The checks against the specification's guard: w*(c+1) is formed only   *)
(* once c < len/8, so it is exact.                                         *)
let APPEND_ROW_GUARD = prove
 (`!w c:int64 l.
     l < 2 EXP 64
     ==> (1 <= val w /\ val w <= 5 /\ 8 * val w * (val c + 1) <= l <=>
          ~(val w < 1) /\ val w < 6 /\ val c < l DIV 8 /\
          ~(l DIV 8 < val(word_mul (word_add c (word 1)) w)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `1 <= val(w:int64) /\ val w <= 5` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `~(val(w:int64) < 1) /\ val w < 6` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 * val(w:int64) * (val(c:int64) + 1) <= l <=> (val c + 1) * val w <= l DIV 8`
    SUBST1_TAC THENL
   [SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN REWRITE_TAC[MULT_AC]; ALL_TAC] THEN
  SUBGOAL_THEN `l DIV 8 < 2 EXP 61` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(c:int64) + 1 <= (val c + 1) * val(w:int64)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = x * 1`] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `val(c:int64) < l DIV 8` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `val(word_add c (word 1):int64) = val c + 1` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_mul (word_add c (word 1)) (w:int64)) = (val c + 1) * val w` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`word_add c (word 1):int64`; `w:int64`] LEAF_VAL_MUL_EXACT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `2 EXP 61 * 5` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ARITH_TAC];
    ARITH_TAC]);;

(* After the checks: the frame, the memory, w, the row's register words    *)
(* and the count in place, and the checks passed.                          *)
let append_row_mid = new_definition
 `append_row_mid t s <=>
    tregs s 0 = tregs t 0 /\ tmem s = tmem t /\
    tregs s 1 = tregs t 1 /\ tregs s 2 = tregs t 2 /\ tregs s 3 = tregs t 3 /\
    tregs s 4 = tregs t 4 /\ tregs s 5 = tisa_read t (tisa_base t 1) 8 /\
    1 <= val(tregs t 1) /\ val(tregs t 1) <= 5 /\
    8 * val(tregs t 1) * (val(tisa_read t (tisa_base t 1) 8) + 1) <= val(tisa_len t 0)`;;

let APPEND_ROW_GUARD_TAC =
  MP_TAC(ISPECL [`tregs t 1`; `tisa_read t (tisa_base t 1) 8`; `val(tisa_len t 0)`]
                APPEND_ROW_GUARD) THEN
  ASM_REWRITE_TAC[VAL_BOUND_64];;

let APPEND_ROW_KEPT_TAC =
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN TISA_STATE_NORM_TAC;;

(* A check that failed: UNSUPPORTED, the guard false, nothing written. *)
let APPEND_ROW_STOP_TAC =
  REWRITE_TAC[append_row_post] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  LEAF_VAL_NUMERALS_TAC THEN TISA_STATE_NORM_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  W(fun (asl,w) ->
    if is_forall w then APPEND_ROW_KEPT_TAC
    else FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
         FIRST [ASM_ARITH_TAC; APPEND_ROW_GUARD_TAC]);;

(* Every check passed. *)
let APPEND_ROW_CONT_TAC =
  REWRITE_TAC[append_row_mid] THEN LEAF_VAL_NUMERALS_TAC THEN TISA_STATE_NORM_TAC THEN
  APPEND_ROW_GUARD_TAC;;

let APPEND_ROW_CHECKS_WP = prove
 (`!t. tisa_entry_ok append_row t
       ==> tisa_wp append_row_checks (append_row_mid t) (append_row_post t) t`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP APPEND_ROW_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[append_row_checks] THEN TISA_VCG_TAC THEN
  FIRST [APPEND_ROW_STOP_TAC THEN NO_TAC; APPEND_ROW_CONT_TAC THEN NO_TAC]);;

(* The writes: the row's words, then the count. *)
(* Word j of the new row, j below the width (at most 5). *)
let APPEND_ROW_ROWJ_TAC =
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4` MP_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
  FIRST [SUBGOAL_THEN `F` CONTR_TAC THEN TISA_FOCUS_ARITH_TAC;
         CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN TISA_STATE_NORM_TAC];;

let APPEND_ROW_ACCESS_WP = prove
 (`!t s. val(tregs t 0) + 192 <= 2 EXP 64 /\
         val(tisa_base t 0) + val(tisa_len t 0) < 2 EXP 64 /\
         (val(tisa_len t 0) = 0 \/
          val(tisa_base t 0) + val(tisa_len t 0) <= val(tregs t 0) \/
          val(tregs t 0) + 192 <= val(tisa_base t 0)) /\
         8 <= val(tisa_len t 1) /\ val(tisa_base t 1) + val(tisa_len t 1) < 2 EXP 64 /\
         (val(tisa_base t 1) + val(tisa_len t 1) <= val(tregs t 0) \/
          val(tregs t 0) + 192 <= val(tisa_base t 1)) /\
         (val(tisa_len t 0) = 0 \/
          val(tisa_base t 0) + val(tisa_len t 0) <= val(tisa_base t 1) \/
          val(tisa_base t 1) + val(tisa_len t 1) <= val(tisa_base t 0)) /\
         append_row_mid t s
         ==> tisa_wp append_row_access (\s. F) (append_row_post t) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[append_row_mid] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:tisa_state`; `t:tisa_state`] TISA_SAME_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `8 * (val(tregs t 1) * val(tisa_read t (tisa_base t 1) 8)) + 8 * val(tregs t 1) <=
                val(tisa_len t 0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `val(tisa_len t 0)`)) (concl th) &&
                                     can (find_term ((=) `8`)) (concl th) && not(is_disj(concl th)))) THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; MULT_AC] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_mul (tregs t 1) (tisa_read t (tisa_base t 1) 8)) =
                val(tregs t 1) * val(tisa_read t (tisa_base t 1) 8)` ASSUME_TAC THENL
   [MATCH_MP_TAC LEAF_VAL_MUL_EXACT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[append_row_access] THEN LEAF_FOCUS_TAC TISA_VCG_TAC THEN
  LEAF_VAL_NUMERALS_TAC THEN
  REWRITE_TAC[append_row_post] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[LEAF_WORD_ADD_1] THEN
  (CONJ_TAC THENL
    [APPEND_ROW_ROWJ_TAC;
     X_GEN_TAC `j:num` THEN DISCH_TAC THEN TISA_STATE_NORM_TAC]));;

let APPEND_ROW_WP = prove
 (`!t. tisa_entry_ok append_row t
       ==> tisa_wp (tisa_root append_row) (\s. F) (append_row_post t) t`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[append_row; tisa_root; TISA_WP_SEQ] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  MAP_EVERY EXISTS_TAC [`append_row_mid t`; `append_row_post t`] THEN
  ASM_SIMP_TAC[APPEND_ROW_CHECKS_WP] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP APPEND_ROW_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC APPEND_ROW_ACCESS_WP THEN ASM_REWRITE_TAC[]);;

let APPEND_ROW_RUN = prove
 (`!t k u. tisa_entry_ok append_row t /\ tisa_run append_row t = TStop k u
           ==> append_row_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; APPEND_ROW_WP]);;

(* Every theorem this file states, for the audits. *)
let append_row_theorems =
 ["append_row_checks", append_row_checks;
  "append_row_access", append_row_access;
  "append_row", append_row;
  "APPEND_ROW_TERM", APPEND_ROW_TERM;
  "APPEND_ROW_DECLS", APPEND_ROW_DECLS;
  "APPEND_ROW_LEAF_WF", APPEND_ROW_LEAF_WF;
  "append_row_post", append_row_post;
  "APPEND_ROW_ENTRY", APPEND_ROW_ENTRY;
  "APPEND_ROW_GUARD", APPEND_ROW_GUARD;
  "append_row_mid", append_row_mid;
  "APPEND_ROW_CHECKS_WP", APPEND_ROW_CHECKS_WP;
  "APPEND_ROW_ACCESS_WP", APPEND_ROW_ACCESS_WP;
  "APPEND_ROW_WP", APPEND_ROW_WP;
  "APPEND_ROW_RUN", APPEND_ROW_RUN];;
