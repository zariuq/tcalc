(* Memory agreement at byte, word and code observations. *)
needs "native/driver/driver.ml";;

let DRV_IN_OFFSET = prove
 (`!(b:int64) n k i. val b + n <= 2 EXP 64 /\ k + 8 <= n /\ i < 8
                     ==> drv_in (word_add (word_add b (word k)) (word i)) b n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[drv_in] THEN
  SUBGOAL_THEN `val(word_add (word_add b (word k)) (word i):int64) = val b + k + i` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let DRV_IN_BASE = prove
 (`!(b:int64) n i. val b + n <= 2 EXP 64 /\ 8 <= n /\ i < 8 ==> drv_in (word_add b (word i)) b n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:int64`; `n:num`; `0`; `i:num`] DRV_IN_OFFSET) THEN
  ASM_REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES]);;

let DRV_WORD_AREA = prove
 (`!m1 m2 (b:int64) n k.
     val b + n <= 2 EXP 64 /\ k + 8 <= n /\ (!a. drv_in a b n ==> m1 a = m2 a)
     ==> drv_word m1 (word_add b (word k)) = drv_word m2 (word_add b (word k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_WORD_AGREE THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC DRV_IN_OFFSET THEN ASM_REWRITE_TAC[]);;

let DRV_WORD_AREA0 = prove
 (`!m1 m2 (b:int64) n.
     val b + n <= 2 EXP 64 /\ 8 <= n /\ (!a. drv_in a b n ==> m1 a = m2 a)
     ==> drv_word m1 b = drv_word m2 b`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`m1:int64->byte`; `m2:int64->byte`; `b:int64`; `n:num`; `0`]
    DRV_WORD_AREA) THEN ASM_REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES]);;

let DRV_CODE_AREA = prove
 (`!m1 m2 p mc.
     p + LENGTH mc <= 2 EXP 64 /\ drv_code m2 p mc /\
     (!a. drv_in a (word p) (LENGTH mc) ==> m1 a = m2 a)
     ==> drv_code m1 p mc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_code] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REWRITE_TAC[DRV_READ_BYTELIST] THEN AP_TERM_TAC THEN
  REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[drv_in] THEN
  SUBGOAL_THEN `val(word p:int64) = p` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `p + LENGTH(mc:byte list) <= 2 EXP 64` THEN
    UNDISCH_TAC `i < LENGTH(mc:byte list)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add (word p) (word i):int64) = p + i` SUBST1_TAC THENL
   [ASM_MESON_TAC[TISA_VAL_OFFSET; ARITH_RULE `i < l /\ p + l <= 2 EXP 64 ==> p + i < 2 EXP 64`];
    ASM_ARITH_TAC]);;

let driver_memory_theorems =
 ["DRV_IN_OFFSET",DRV_IN_OFFSET;
  "DRV_IN_BASE",DRV_IN_BASE;
  "DRV_WORD_AREA",DRV_WORD_AREA;
  "DRV_WORD_AREA0",DRV_WORD_AREA0;
  "DRV_CODE_AREA",DRV_CODE_AREA];;
