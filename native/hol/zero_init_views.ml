(* Complete-word clearing views of parent byte regions. *)
needs "native/hol/zero_init.ml";;

let zinit_round = new_definition
 `zinit_round (length:int64) = word(8 * (val length DIV 8)):int64`;;

let zinit_word_view = new_definition
 `zinit_word_view (bw:num->int64) k = if EVEN k then bw k else zinit_round(bw k)`;;

let ZINIT_ROUND_VALUE = prove
 (`!length:int64. val(zinit_round length) = 8 * (val length DIV 8) /\
                  val(zinit_round length) <= val length`,
  GEN_TAC THEN
  SUBGOAL_THEN `8 * (val(length:int64) DIV 8) < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ISPEC `length:int64` VAL_BOUND_64) THEN
    MP_TAC(SPECL [`val(length:int64)`;`8`] DIVISION) THEN ARITH_TAC;
    ASM_SIMP_TAC[zinit_round;VAL_WORD;DIMINDEX_64;MOD_LT] THEN
    MP_TAC(SPECL [`val(length:int64)`;`8`] DIVISION) THEN ARITH_TAC]);;

let ZINIT_ROUND_DIV = prove
 (`!length:int64. val(zinit_round length) DIV 8 = val length DIV 8 /\
                  8 * (val(zinit_round length) DIV 8) = val(zinit_round length)`,
  SIMP_TAC[ZINIT_ROUND_VALUE;DIV_MULT;ARITH_EQ]);;

let ZINIT_ROUND_WORDS = prove
 (`!length:int64 i.
     (8 * i + 8 <= val(zinit_round length) <=> 8 * i + 8 <= val length)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * i + 8 = 8 * (i + 1)`] THEN
  SIMP_TAC[GSYM LDIV_LT_EQ;ARITH_EQ;ZINIT_ROUND_DIV]);;

let ZINIT_VIEW_PAIR = prove
 (`!bw slot. EVEN slot
       ==> zinit_word_view bw slot = bw slot /\
           zinit_word_view bw (slot + 1) = zinit_round(bw(slot + 1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[zinit_word_view;EVEN_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let ZINIT_VIEW_SUPPORTED = prove
 (`!bw slot. EVEN slot
       ==> (zinit_supported (zinit_word_view bw) slot <=> val(bw(slot + 1)) DIV 8 <= 4294967295)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`slot:num`] ZINIT_VIEW_PAIR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[zinit_supported] THEN
  REWRITE_TAC[ZINIT_ROUND_DIV] THEN REWRITE_TAC[ZINIT_ROUND_VALUE]);;

let ZINIT_APART_SHRINK = prove
 (`!a n small b m. small <= n /\ drv_apart a n b m ==> drv_apart a small b m`,
  REWRITE_TAC[drv_apart] THEN ARITH_TAC);;

let ZINIT_VIEW_RANGE = prove
 (`!bw ctl cfr slot. EVEN slot /\ zinit_range_ok bw ctl cfr slot
       ==> zinit_range_ok (zinit_word_view bw) ctl cfr slot`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[zinit_range_ok] o
    check (fun th -> zinit_app "zinit_range_ok" (concl th))) THEN
  MP_TAC(SPECL [`bw:num->int64`;`slot:num`] ZINIT_VIEW_PAIR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(bw:num->int64)(slot + 1)` ZINIT_ROUND_VALUE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[zinit_range_ok] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC ZINIT_APART_SHRINK THEN EXISTS_TAC `val((bw:num->int64)(slot + 1))` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC ZINIT_APART_SHRINK THEN EXISTS_TAC `val((bw:num->int64)(slot + 1))` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let ZINIT_VIEW_ZERO_PARENT = prove
 (`!bw slots m. ALL EVEN slots /\ zinit_zero (zinit_word_view bw) slots m
       ==> zinit_zero bw slots m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM ALL_MEM] o
    check (fun th -> zinit_app "ALL" (concl th))) THEN
  REWRITE_TAC[zinit_zero] THEN MAP_EVERY X_GEN_TAC [`slot:num`;`i:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `EVEN slot` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`slot:num`;`i:num`] o REWRITE_RULE[zinit_zero] o
    check (fun th -> zinit_app "zinit_zero" (concl th))) THEN
  ASM_SIMP_TAC[ZINIT_VIEW_PAIR;ZINIT_ROUND_WORDS]);;

let ZINIT_APART_SHRINK_BOTH = prove
 (`!a n small b m short. small <= n /\ short <= m /\ drv_apart a n b m
       ==> drv_apart a small b short`,
  REWRITE_TAC[drv_apart] THEN ARITH_TAC);;

let ZINIT_VIEW_APART = prove
 (`!bw a b. EVEN a /\ EVEN b /\ drv_apart (bw a) (val(bw(a + 1))) (bw b) (val(bw(b + 1)))
       ==> drv_apart (zinit_word_view bw a) (val(zinit_word_view bw (a + 1)))
                     (zinit_word_view bw b) (val(zinit_word_view bw (b + 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(bw:num->int64)(a + 1)` ZINIT_ROUND_VALUE) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(bw:num->int64)(b + 1)` ZINIT_ROUND_VALUE) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ZINIT_VIEW_PAIR] THEN
  MATCH_MP_TAC ZINIT_APART_SHRINK_BOTH THEN
  MAP_EVERY EXISTS_TAC [`val((bw:num->int64)(a + 1))`;`val((bw:num->int64)(b + 1))`] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
