(* Word arithmetic in the publication loop. The byte bounds come from the
   reservations, and each intermediate index is represented without wrap. *)

needs "Library/words.ml";;
needs "native/leaves/ty_list/ty_list_log.ml";;

let TY_LIST_COMMIT_WORDS = prove
 (`!old i slot nr nh nw.
      nr < 2 EXP 64 /\ nh < 2 EXP 64 /\ nw < 2 EXP 64 /\
      16 * (old + i) + 16 <= nr /\ 8 * slot + 8 <= nh /\
      128 + 32 * i + 24 <= nw
      ==> val(word_shl (word i:int64) 2) = 4 * i /\
          val(word_add (word old) (word i):int64) = old + i /\
          val(word_shl (word_add (word old) (word i):int64) 1) = 2 * (old + i) /\
          val(word slot:int64) = slot /\
          val(word_add (word_add (word old) (word i)) (word 1):int64) = SUC(old + i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_SHL_WORD; VAL_WORD; DIMINDEX_64; ADD1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_ARITH_TAC);;

let TY_LIST_COMMIT_LOG_WORDS = prove
 (`!(log:(A#num)list) slots old nr nh nw.
      ty_log_ok log (nh DIV 8) slots /\ nh DIV 8 <= 16777216 /\
      old + LENGTH log <= nr DIV 16 /\ 128 <= nw /\ LENGTH log <= (nw - 128) DIV 32 /\
      nr < 2 EXP 64 /\ nh < 2 EXP 64 /\ nw < 2 EXP 64
      ==> LENGTH log <= 16777216 /\
          (!i. i < LENGTH log
               ==> val(word_shl (word i:int64) 2) = 4 * i /\
                   val(word_add (word old) (word i):int64) = old + i /\
                   val(word_shl (word_add (word old) (word i):int64) 1) = 2 * (old + i) /\
                   val(word(SND(EL i log)):int64) = SND(EL i log) /\
                   val(word_add (word_add (word old) (word i)) (word 1):int64) = SUC(old + i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`log:(A#num)list`; `slots:num->num`; `old:num`; `nr:num`;
                `nh:num`; `nw:num`] TY_LOG_COMMIT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC TY_LIST_COMMIT_WORDS THEN
  MAP_EVERY EXISTS_TAC [`nr:num`; `nh:num`; `nw:num`] THEN ASM_SIMP_TAC[]);;
