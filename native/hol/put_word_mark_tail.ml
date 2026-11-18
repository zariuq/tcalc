(* The mark-word profile keeps the entire unpublished tail on every stop. *)
needs "native/hol/put_word_frame.ml";;

let PUT_WORD_TABLE_KEPT = prove
 (`!t k u.
     tisa_entry_ok put_word t /\ tisa_run put_word t = TStop k u
     ==> !j. 8 * j + 8 <= val(tisa_len t 0) /\
             ~(j = val(tregs t 1) * val(tisa_fword t 22) + val(tregs t 2))
              ==> tisa_read u (word_add (tisa_base u 0) (word(8 * j))) 8 =
                  tisa_read t (word_add (tisa_base t 0) (word(8 * j))) 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] PUT_WORD_FRAME_RUN) THEN
  ASM_REWRITE_TAC[put_word_frame_post] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_SIMP_TAC[]);;

let PUT_WORD_MARK_UNPUBLISHED = prove
 (`!t k u n.
     tisa_entry_ok put_word t /\ tisa_run put_word t = TStop k u /\
     tregs t 1 = word 1 /\ tregs t 2 = word 0 /\
     n = val(tisa_read t (tisa_base t 1) 8)
     ==> !j. n <= j /\ 8 * j + 8 <= val(tisa_len t 0)
              ==> tisa_read u (word_add (tisa_base u 0) (word(8 * j))) 8 =
                  tisa_read t (word_add (tisa_base t 0) (word(8 * j))) 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] PUT_WORD_FRAME_RUN) THEN
  ASM_REWRITE_TAC[put_word_frame_post] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  LEAF_VAL_NUMERALS_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let PUT_WORD_MARK_ZERO_TAIL = prove
 (`!t k u n.
     tisa_entry_ok put_word t /\ tisa_run put_word t = TStop k u /\
     tregs t 1 = word 1 /\ tregs t 2 = word 0 /\
     n = val(tisa_read t (tisa_base t 1) 8) /\
     (!j. n <= j /\ 8 * j + 8 <= val(tisa_len t 0)
           ==> tisa_read t (word_add (tisa_base t 0) (word(8 * j))) 8 = word 0)
     ==> !j. n <= j /\ 8 * j + 8 <= val(tisa_len t 0)
              ==> tisa_read u (word_add (tisa_base u 0) (word(8 * j))) 8 = word 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`;`n:num`] PUT_WORD_MARK_UNPUBLISHED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_SIMP_TAC[]);;

let PUT_WORD_MARK_EXACT = prove
 (`!t k u n.
     tisa_entry_ok put_word t /\ tisa_run put_word t = TStop k u /\
     tregs t 1 = word 1 /\ tregs t 2 = word 0 /\
     n = val(tisa_read t (tisa_base t 1) 8) /\ 8 * n <= val(tisa_len t 0)
     ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
         (k = 1 <=> val(tisa_fword t 22) < n) /\
         (k = 2 <=> n <= val(tisa_fword t 22)) /\
         (k = 1 ==> tisa_fword u 19 = tisa_fword t 23 /\
            tisa_read u (word_add (tisa_base u 0) (word(8 * val(tisa_fword t 22)))) 8 =
              tisa_fword t 23)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] PUT_WORD_FRAME_RUN) THEN
  ASM_REWRITE_TAC[put_word_frame_post] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  LEAF_VAL_NUMERALS_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES;ADD_CLAUSES]) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES;ADD_CLAUSES] THEN ASM_ARITH_TAC);;

let PUT_WORD_MARK_PAST_COUNT = prove
 (`!t k u n.
     tisa_entry_ok put_word t /\ tisa_run put_word t = TStop k u /\
     tregs t 1 = word 1 /\ tregs t 2 = word 0 /\
     n = val(tisa_read t (tisa_base t 1) 8) /\ 8 * n <= val(tisa_len t 0) /\
     n <= val(tisa_fword t 22)
     ==> k = 2 /\ ~(k = 1)`,
  MESON_TAC[PUT_WORD_MARK_EXACT;ARITH_RULE `~(2 = 1)`]);;

let put_word_mark_post = new_definition
 `put_word_mark_post t k u <=>
    put_word_frame_post t k u /\
    (tregs t 1 = word 1 /\ tregs t 2 = word 0
     ==> !j. val(tisa_read t (tisa_base t 1) 8) <= j /\ 8 * j + 8 <= val(tisa_len t 0)
              ==> tisa_read u (word_add (tisa_base u 0) (word(8 * j))) 8 =
                  tisa_read t (word_add (tisa_base t 0) (word(8 * j))) 8)`;;

let PUT_WORD_MARK_RUN = prove
 (`!t k u. tisa_entry_ok put_word t /\ tisa_run put_word t = TStop k u
     ==> put_word_mark_post t k u`,
  REWRITE_TAC[put_word_mark_post] THEN
  MESON_TAC[PUT_WORD_FRAME_RUN;PUT_WORD_MARK_UNPUBLISHED]);;

let put_word_mark_tail_theorems =
 ["PUT_WORD_TABLE_KEPT",PUT_WORD_TABLE_KEPT;
  "PUT_WORD_MARK_UNPUBLISHED",PUT_WORD_MARK_UNPUBLISHED;
  "PUT_WORD_MARK_ZERO_TAIL",PUT_WORD_MARK_ZERO_TAIL;
  "PUT_WORD_MARK_EXACT",PUT_WORD_MARK_EXACT;
  "PUT_WORD_MARK_PAST_COUNT",PUT_WORD_MARK_PAST_COUNT;
  "PUT_WORD_MARK_RUN",PUT_WORD_MARK_RUN];;
