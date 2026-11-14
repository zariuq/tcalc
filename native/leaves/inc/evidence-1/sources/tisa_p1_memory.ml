(* ========================================================================= *)
(* Reading memory through a byte-range write: a read inside the write sees   *)
(* the written number, a read outside it sees the memory before. Used by the *)
(* evaluator and by the native-code proofs.                                  *)
(* ========================================================================= *)

needs "tisa/hol/tisa_p1.ml";;

let TISA_READ_INSIDE_WRITE = prove
 (`!(a:int64) k c j n (m:int64->byte).
        val(word_sub a c) + k <= j /\ j <= 2 EXP 64
        ==> read (bytes(a,k)) (write (bytes(c,j)) n m) =
            ((n MOD 2 EXP (8 * j)) DIV 2 EXP (8 * val(word_sub a c))) MOD
            2 EXP (8 * k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:int64`; `j:num`; `n:num`; `m:int64->byte`] READ_WRITE_BYTES) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[WORD_VAL] THEN CONV_TAC WORD_RULE; ASM_ARITH_TAC]);;

let TISA_READ_OUTSIDE_WRITE = prove
 (`!(a:int64) k c j n (m:int64->byte).
        j <= val(word_sub a c) /\ val(word_sub a c) + k <= 2 EXP 64
        ==> read (bytes(a,k)) (write (bytes(c,j)) n m) = read (bytes(a,k)) m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[READ_BYTES_EQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[WRITE_BYTES] THEN
  SUBGOAL_THEN
   `val(word_sub (word_add a (word i)) c:int64) = val(word_sub a c) + i`
  SUBST1_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add a (word i)) c:int64 = word_add (word_sub a c) (word i)`] THEN
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `i MOD 2 EXP 64 = i` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

