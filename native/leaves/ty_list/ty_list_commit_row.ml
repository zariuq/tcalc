(* Replay one prepared entry into the rows and slots. The count is
   published by the caller after every entry has been written. *)

needs "native/leaves/ty_list/ty_list_program.ml";;
needs "native/leaves/ty_list/ty_list_commit_words.ml";;

let ty_list_word = new_definition
 `ty_list_word st r offset =
    tisa_read st (word_add (tisa_base st r) (word offset)) 8`;;

let ty_list_commit_row_memory = new_definition
 `ty_list_commit_row_memory st old i slot =
    tmem(tisa_store (word_add (tisa_base st 1) (word(8 * slot))) 8
          (word(SUC(old + i)))
          (tisa_store (word_add (tisa_base st 0) (word(16 * (old + i) + 8))) 8
            (ty_list_word st 7 (128 + 32 * i + 8))
            (tisa_store (word_add (tisa_base st 0) (word(16 * (old + i)))) 8
              (ty_list_word st 7 (128 + 32 * i)) st)))`;;

let TY_LIST_COMMIT_ROW_WP = prove
 (`!st old i slot.
     val(tregs st 0) + 192 <= 2 EXP 64 /\
     val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64 /\
     val(tisa_base st 1) + val(tisa_len st 1) < 2 EXP 64 /\
     val(tisa_base st 7) + val(tisa_len st 7) < 2 EXP 64 /\
     (val(tisa_base st 0) + val(tisa_len st 0) <= val(tregs st 0) \/
      val(tregs st 0) + 192 <= val(tisa_base st 0)) /\
     (val(tisa_base st 0) + val(tisa_len st 0) <= val(tisa_base st 7) \/
      val(tisa_base st 7) + val(tisa_len st 7) <= val(tisa_base st 0)) /\
     16 * (old + i) + 16 <= val(tisa_len st 0) /\
     8 * slot + 8 <= val(tisa_len st 1) /\
     128 + 32 * i + 24 <= val(tisa_len st 7) /\
     tregs st 5 = word i /\ ty_list_word st 7 24 = word old /\
     ty_list_word st 7 (128 + 32 * i + 16) = word slot
     ==> tisa_wp ty_list_commit_row
           (\u. tregs u 0 = tregs st 0 /\ tregs u 5 = word i /\
                tregs u 6 = tregs st 6 /\
                tmem u = ty_list_commit_row_memory st old i slot)
           (\k u. F) st`,
  REWRITE_TAC[ty_list_word] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`old:num`; `i:num`; `slot:num`; `val(tisa_len st 0)`;
                `val(tisa_len st 1)`; `val(tisa_len st 7)`] TY_LIST_COMMIT_WORDS) THEN
  ASM_REWRITE_TAC[VAL_BOUND_64] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `tisa_read st
      (word_add (tisa_base st 7) (word((8 * val(word_shl (word i:int64) 2) + 128) + 16)))
      8 = word slot` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `(8 * 4 * i + 128) + 16 = 128 + 32 * i + 16`];
    ALL_TAC] THEN
  REWRITE_TAC[ty_list_commit_row] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[ty_list_commit_row_memory; ty_list_word; TISA_TMEM_STORE; ADD1] THEN
  TISA_STATE_NORM_TAC THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE `8 * 2 * j = 16 * j`;
                    ARITH_RULE `8 * 4 * i + 128 = 128 + 32 * i`] THEN
  REWRITE_TAC[ADD_ASSOC]);;

let TY_LIST_COMMIT_WRITE_OUTSIDE = prove
 (`!(base:int64) off len a value m.
      val base + len <= 2 EXP 64 /\ off + 8 <= len /\
      (val a < val base \/ val base + len <= val a)
      ==> write (bytes(word_add base (word off),8)) value m a = m a`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC TISA_WRITE_BYTES_OUTSIDE THEN
  SUBGOAL_THEN `val(word_add (base:int64) (word off)) = val base + off` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let TY_LIST_COMMIT_ROW_FRAME = prove
 (`!st old i slot (a:int64).
      val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64 /\
      val(tisa_base st 1) + val(tisa_len st 1) < 2 EXP 64 /\
      16 * (old + i) + 16 <= val(tisa_len st 0) /\
      8 * slot + 8 <= val(tisa_len st 1) /\
      (val a < val(tisa_base st 0) \/ val(tisa_base st 0) + val(tisa_len st 0) <= val a) /\
      (val a < val(tisa_base st 1) \/ val(tisa_base st 1) + val(tisa_len st 1) <= val a)
      ==> ty_list_commit_row_memory st old i slot a = tmem st a`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[ty_list_commit_row_memory; TISA_TMEM_STORE] THEN
  ASM_SIMP_TAC
   [SPECL [`tisa_base st 0`; `16 * (old + i):num`; `val(tisa_len st 0)`]
           TY_LIST_COMMIT_WRITE_OUTSIDE;
    SPECL [`tisa_base st 0`; `16 * (old + i) + 8:num`; `val(tisa_len st 0)`]
           TY_LIST_COMMIT_WRITE_OUTSIDE;
    SPECL [`tisa_base st 1`; `8 * slot:num`; `val(tisa_len st 1)`]
           TY_LIST_COMMIT_WRITE_OUTSIDE;
    ARITH_RULE `x < y ==> x <= y`;
    ARITH_RULE `x + 16 <= y ==> x + 8 <= y /\ (x + 8) + 8 <= y`]);;
