(* ========================================================================= *)
(* put_word, the record plans' leaf 9 (tcalc/native/PLANS.txt): set word w *)
(* of row i of a table of rows of s words. The program is                    *)
(* tcalc/native/leaves/put_word/put_word.metta's text (put_word_prog.txt;   *)
(* image record put_word.hol). Regions: 0 the table (RW), 1 its count (RO,  *)
(* word 0 the row count c); v1 the stride s, v2 the word w, arg0 the row i, *)
(* arg1 the value.                                                          *)
(*                                                                           *)
(* PUT_WORD_RUN: every run from a state entry validation accepts ends in    *)
(* put_word_post: the status word is the outcome, the fuel receipt is kept, *)
(* and                                                                       *)
(*   FIRED with ret_val the value, now word s i + w of the table, every     *)
(*   other word below s c kept, when i < c, w < s and 8 s c <= the table's  *)
(*   length;                                                                *)
(*   UNSUPPORTED otherwise, every word of the table kept.                   *)
(*                                                                           *)
(* pl_put_word_spec (plans_leaves.ml) states the UNSUPPORTED case as "every *)
(* word below s c kept". When 8 s c exceeds the table, words below s c lie  *)
(* past the table and can be the frame's status and return words, which    *)
(* every stop writes (a table just below the frame, word (f + 144 - b) / 8  *)
(* is the status word), so no program meets that clause. put_word_post     *)
(* keeps every word inside the table (8 j + 8 <= its length), as            *)
(* pl_append_row_spec states its UNSUPPORTED case.                          *)
(*                                                                           *)
(* The program is a checks block (put_word_checks: i < c, w < s and the     *)
(* exact product test, LEAF_PRODUCT_GUARD) and an access block              *)
(* (put_word_access), proved apart and joined at put_word_mid.              *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

(* The program: its two blocks, and its text put_word_prog.txt. *)
let put_word_checks = new_definition
 `put_word_checks = (TSeq (TInstr (TLoadFrame TyU64 3 22)) (TSeq (TInstr (TLoadFrame TyPtr 10 2)) (TSeq (TInstr (TLoad TyU64 8 1 4 10 (&0:int))) (TSeq (TInstr (TCmp CondUlt TyU64 10 3 (OpReg 4))) (TSeq (TIf 10 TSkip (TReturn 2 10)) (TSeq (TInstr (TCmp CondUlt TyU64 10 2 (OpReg 1))) (TSeq (TIf 10 TSkip (TReturn 2 10)) (TSeq (TInstr (TLoadFrame TyU64 5 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 5 5 3)) (TSeq (TInstr (TCmp CondUlt TyU64 10 5 (OpReg 1))) (TSeq (TIf 10 (TReturn 2 10) TSkip) (TSeq (TInstr (TCmp CondUlt TyU64 10 5 (OpReg 4))) (TSeq (TIf 10 (TReturn 2 10) TSkip) (TSeq (TInstr (TShift ShiftRightU TyU64 6 1 32)) (TSeq (TInstr (TShift ShiftRightU TyU64 7 4 32)) (TSeq (TInstr (TCmp CondNe TyU64 10 6 (OpImm (word 0)))) (TSeq (TInstr (TCmp CondNe TyU64 11 7 (OpImm (word 0)))) (TSeq (TInstr (TBin BinAnd TyBool 10 10 11)) (TSeq (TIf 10 (TReturn 2 10) TSkip) (TSeq (TInstr (TImm TyU64 11 (word 4294967295))) (TSeq (TInstr (TBin BinAnd TyU64 8 1 11)) (TSeq (TInstr (TBin BinAnd TyU64 9 4 11)) (TSeq (TInstr (TBin BinMulLo TyU64 10 6 9)) (TSeq (TInstr (TBin BinMulLo TyU64 11 7 8)) (TSeq (TInstr (TBin BinAdd TyU64 10 10 11)) (TSeq (TInstr (TCmp CondUlt TyU64 11 10 (OpImm (word 536870912)))) (TSeq (TIf 11 TSkip (TReturn 2 11)) (TSeq (TInstr (TShift ShiftLeft TyU64 10 10 32)) (TSeq (TInstr (TBin BinMulLo TyU64 11 8 9)) (TSeq (TInstr (TCmp CondUlt TyU64 6 5 (OpReg 11))) (TSeq (TIf 6 (TReturn 2 6) TSkip) (TSeq (TInstr (TBin BinAdd TyU64 10 10 11)) (TSeq (TInstr (TCmp CondUlt TyU64 6 5 (OpReg 10))) (TIf 6 (TReturn 2 6) TSkip))))))))))))))))))))))))))))))))))`;;

let put_word_access = new_definition
 `put_word_access = (TSeq (TInstr (TBin BinMulLo TyU64 10 1 3)) (TSeq (TInstr (TBin BinAdd TyU64 10 10 2)) (TSeq (TInstr (TLoadFrame TyPtr 11 0)) (TSeq (TInstr (TAddr 0 11 11 (SOME 10) 3 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 6 23)) (TSeq (TInstr (TStore 8 0 11 (&0:int) 6)) (TReturn 1 6)))))))`;;

let put_word = new_definition
 `put_word = TProg [(2,0,8); (1,8,8)] [(1,TyU64,0); (2,TyU64,0)] (TSeq put_word_checks put_word_access)`;;

let PUT_WORD_TERM = prove
 (`put_word = (TProg [(2,0,8); (1,8,8)] [(1,TyU64,0); (2,TyU64,0)] (TSeq (TSeq (TInstr (TLoadFrame TyU64 3 22)) (TSeq (TInstr (TLoadFrame TyPtr 10 2)) (TSeq (TInstr (TLoad TyU64 8 1 4 10 (&0:int))) (TSeq (TInstr (TCmp CondUlt TyU64 10 3 (OpReg 4))) (TSeq (TIf 10 TSkip (TReturn 2 10)) (TSeq (TInstr (TCmp CondUlt TyU64 10 2 (OpReg 1))) (TSeq (TIf 10 TSkip (TReturn 2 10)) (TSeq (TInstr (TLoadFrame TyU64 5 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 5 5 3)) (TSeq (TInstr (TCmp CondUlt TyU64 10 5 (OpReg 1))) (TSeq (TIf 10 (TReturn 2 10) TSkip) (TSeq (TInstr (TCmp CondUlt TyU64 10 5 (OpReg 4))) (TSeq (TIf 10 (TReturn 2 10) TSkip) (TSeq (TInstr (TShift ShiftRightU TyU64 6 1 32)) (TSeq (TInstr (TShift ShiftRightU TyU64 7 4 32)) (TSeq (TInstr (TCmp CondNe TyU64 10 6 (OpImm (word 0)))) (TSeq (TInstr (TCmp CondNe TyU64 11 7 (OpImm (word 0)))) (TSeq (TInstr (TBin BinAnd TyBool 10 10 11)) (TSeq (TIf 10 (TReturn 2 10) TSkip) (TSeq (TInstr (TImm TyU64 11 (word 4294967295))) (TSeq (TInstr (TBin BinAnd TyU64 8 1 11)) (TSeq (TInstr (TBin BinAnd TyU64 9 4 11)) (TSeq (TInstr (TBin BinMulLo TyU64 10 6 9)) (TSeq (TInstr (TBin BinMulLo TyU64 11 7 8)) (TSeq (TInstr (TBin BinAdd TyU64 10 10 11)) (TSeq (TInstr (TCmp CondUlt TyU64 11 10 (OpImm (word 536870912)))) (TSeq (TIf 11 TSkip (TReturn 2 11)) (TSeq (TInstr (TShift ShiftLeft TyU64 10 10 32)) (TSeq (TInstr (TBin BinMulLo TyU64 11 8 9)) (TSeq (TInstr (TCmp CondUlt TyU64 6 5 (OpReg 11))) (TSeq (TIf 6 (TReturn 2 6) TSkip) (TSeq (TInstr (TBin BinAdd TyU64 10 10 11)) (TSeq (TInstr (TCmp CondUlt TyU64 6 5 (OpReg 10))) (TIf 6 (TReturn 2 6) TSkip)))))))))))))))))))))))))))))))))) (TSeq (TInstr (TBin BinMulLo TyU64 10 1 3)) (TSeq (TInstr (TBin BinAdd TyU64 10 10 2)) (TSeq (TInstr (TLoadFrame TyPtr 11 0)) (TSeq (TInstr (TAddr 0 11 11 (SOME 10) 3 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 6 23)) (TSeq (TInstr (TStore 8 0 11 (&0:int) 6)) (TReturn 1 6)))))))))`,
  REWRITE_TAC[put_word; put_word_checks; put_word_access]);;

let PUT_WORD_DECLS = prove(`tisa_decls put_word = [(2,0,8); (1,8,8)]`, REWRITE_TAC[put_word; tisa_decls]);;

let PUT_WORD_LEAF_WF = prove(`tisa_leaf_wf put_word`, LEAF_WF_TAC PUT_WORD_DECLS PUT_WORD_TERM);;

(* What every run leaves (pl_w t r i written out: word i of region r). *)
let put_word_post = new_definition
 `put_word_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    (if val(tisa_fword t 22) < val(tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8) /\
        val(tregs t 2) < val(tregs t 1) /\
        8 * val(tregs t 1) * val(tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8) <=
        val(tisa_len t 0)
     then k = 1 /\ tisa_fword u 19 = tisa_fword t 23 /\
          tisa_read u (word_add (tisa_base u 0)
                        (word(8 * (val(tregs t 1) * val(tisa_fword t 22) + val(tregs t 2))))) 8 =
          tisa_fword t 23 /\
          (!j. j < val(tregs t 1) * val(tisa_read t (word_add (tisa_base t 1) (word(8 * 0))) 8) /\
               ~(j = val(tregs t 1) * val(tisa_fword t 22) + val(tregs t 2))
               ==> tisa_read u (word_add (tisa_base u 0) (word(8 * j))) 8 =
                   tisa_read t (word_add (tisa_base t 0) (word(8 * j))) 8)
     else k = 2 /\
          (!j. 8 * j + 8 <= val(tisa_len t 0)
               ==> tisa_read u (word_add (tisa_base u 0) (word(8 * j))) 8 =
                   tisa_read t (word_add (tisa_base t 0) (word(8 * j))) 8))`;;

(* Entry validation: the frame, the count word, the regions below 2^64, the *)
(* table apart from the frame.                                              *)
let PUT_WORD_ENTRY = prove
 (`!t. tisa_entry_ok put_word t
       ==> val(tregs t 0) + 192 <= 2 EXP 64 /\
           val(tisa_base t 0) + val(tisa_len t 0) < 2 EXP 64 /\
           (val(tisa_len t 0) = 0 \/
            val(tisa_base t 0) + val(tisa_len t 0) <= val(tregs t 0) \/
            val(tregs t 0) + 192 <= val(tisa_base t 0)) /\
           8 <= val(tisa_len t 1) /\ val(tisa_base t 1) + val(tisa_len t 1) < 2 EXP 64`,
  GEN_TAC THEN
  REWRITE_TAC[put_word; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok;
              tisa_region_ok; tisa_pair_ok; tisa_frame; tisa_base; tisa_len; tisa_canonical; tisa_norm] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* After the checks: the frame, the memory, s, w and i in place, and the   *)
(* checks passed.                                                           *)
let put_word_mid = new_definition
 `put_word_mid t s <=>
    tregs s 0 = tregs t 0 /\ tmem s = tmem t /\
    tregs s 1 = tregs t 1 /\ tregs s 2 = tregs t 2 /\ tregs s 3 = tisa_fword t 22 /\
    val(tisa_fword t 22) < val(tisa_read t (tisa_base t 1) 8) /\
    val(tregs t 2) < val(tregs t 1) /\
    8 * val(tregs t 1) * val(tisa_read t (tisa_base t 1) 8) <= val(tisa_len t 0)`;;

(* The product test against the specification's guard. *)
let PUT_WORD_GUARD_TAC =
  MP_TAC(ISPECL [`tregs t 1`; `tisa_read t (tisa_base t 1) 8`; `val(tisa_len t 0)`;
                 `val(tisa_fword t 22)`; `val(tregs t 2)`] LEAF_PRODUCT_GUARD) THEN
  ASM_REWRITE_TAC[VAL_BOUND_64];;

(* A read of word j of the table, j inside it, through the run's finish. *)
let PUT_WORD_KEPT_TAC =
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN TISA_STATE_NORM_TAC;;

(* A check that failed: UNSUPPORTED, the guard false, the table kept. *)
let PUT_WORD_STOP_TAC =
  REWRITE_TAC[put_word_post] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  LEAF_VAL_NUMERALS_TAC THEN TISA_STATE_NORM_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  W(fun (asl,w) ->
    if is_forall w then PUT_WORD_KEPT_TAC
    else FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
         FIRST [ASM_ARITH_TAC; PUT_WORD_GUARD_TAC]);;

(* Every check passed. *)
let PUT_WORD_CONT_TAC =
  REWRITE_TAC[put_word_mid] THEN LEAF_VAL_NUMERALS_TAC THEN TISA_STATE_NORM_TAC THEN
  PUT_WORD_GUARD_TAC;;

let PUT_WORD_CHECKS_WP = prove
 (`!t. tisa_entry_ok put_word t
       ==> tisa_wp put_word_checks (put_word_mid t) (put_word_post t) t`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PUT_WORD_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[put_word_checks] THEN TISA_VCG_TAC THEN
  FIRST [PUT_WORD_STOP_TAC THEN NO_TAC; PUT_WORD_CONT_TAC THEN NO_TAC]);;

(* The access: the value stored at word s i + w, inside the table. *)
let PUT_WORD_ACCESS_WP = prove
 (`!t s. val(tregs t 0) + 192 <= 2 EXP 64 /\
         val(tisa_base t 0) + val(tisa_len t 0) < 2 EXP 64 /\
         (val(tisa_len t 0) = 0 \/
          val(tisa_base t 0) + val(tisa_len t 0) <= val(tregs t 0) \/
          val(tregs t 0) + 192 <= val(tisa_base t 0)) /\
         put_word_mid t s
         ==> tisa_wp put_word_access (\s. F) (put_word_post t) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[put_word_mid] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:tisa_state`; `t:tisa_state`] TISA_SAME_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`val(tregs t 1)`; `val(tisa_fword t 22)`; `val(tregs t 2)`;
                `val(tisa_read t (tisa_base t 1) 8)`; `val(tisa_len t 0)`] LEAF_ROW_INDEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_mul (tregs t 1) (tisa_fword t 22)) = val(tregs t 1) * val(tisa_fword t 22)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LEAF_VAL_MUL_EXACT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add (word_mul (tregs t 1) (tisa_fword t 22)) (tregs t 2)) =
                val(tregs t 1) * val(tisa_fword t 22) + val(tregs t 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD_ADD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[put_word_access] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[put_word_post] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * j + 8 <= val(tisa_len t 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 * j + 8 <= 8 * (val(tregs t 1) * val(tisa_fword t 22) + val(tregs t 2)) \/
                8 * (val(tregs t 1) * val(tisa_fword t 22) + val(tregs t 2)) + 8 <= 8 * j`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  TISA_STATE_NORM_TAC);;

let PUT_WORD_WP = prove
 (`!t. tisa_entry_ok put_word t ==> tisa_wp (tisa_root put_word) (\s. F) (put_word_post t) t`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[put_word; tisa_root; TISA_WP_SEQ] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  MAP_EVERY EXISTS_TAC [`put_word_mid t`; `put_word_post t`] THEN
  ASM_SIMP_TAC[PUT_WORD_CHECKS_WP] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PUT_WORD_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PUT_WORD_ACCESS_WP THEN ASM_REWRITE_TAC[]);;

let PUT_WORD_RUN = prove
 (`!t k u. tisa_entry_ok put_word t /\ tisa_run put_word t = TStop k u ==> put_word_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; PUT_WORD_WP]);;

(* Every theorem this file states, for the audits. *)
let put_word_theorems =
 ["put_word_checks", put_word_checks;
  "put_word_access", put_word_access;
  "put_word", put_word;
  "PUT_WORD_TERM", PUT_WORD_TERM;
  "PUT_WORD_DECLS", PUT_WORD_DECLS;
  "PUT_WORD_LEAF_WF", PUT_WORD_LEAF_WF;
  "put_word_post", put_word_post;
  "PUT_WORD_ENTRY", PUT_WORD_ENTRY;
  "put_word_mid", put_word_mid;
  "PUT_WORD_CHECKS_WP", PUT_WORD_CHECKS_WP;
  "PUT_WORD_ACCESS_WP", PUT_WORD_ACCESS_WP;
  "PUT_WORD_WP", PUT_WORD_WP;
  "PUT_WORD_RUN", PUT_WORD_RUN];;
