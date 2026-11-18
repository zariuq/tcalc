(* Byte and word observations of regions outside a native driver's writes. *)
needs "native/hol/driver_control_layout.ml";;
needs "native/hol/memory_words.ml";;

let DRV_MEMORY_FRAME_REGION = prove
 (`!cfr d ctl nctl before after base length.
     (!a. ~drv_stack cfr a /\ ~drv_in a d 64 /\ ~drv_in a ctl (8 * nctl)
          ==> (after:int64->byte) a = before a) /\
     48 <= val cfr /\ drv_apart (word_sub cfr (word 48)) 304 base length /\
     drv_apart d 64 base length /\ drv_apart ctl (8 * nctl) base length
     ==> !a. drv_in a base length ==> after a = before a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `drv_stack`)) (concl th))) THEN CONJ_TAC THENL
   [MATCH_MP_TAC DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [`base:int64`;`length:num`] THEN
    ASM_REWRITE_TAC[];
    CONJ_TAC THEN MATCH_MP_TAC DRV_APART_EXCLUDES THEN
    MAP_EVERY EXISTS_TAC [`base:int64`;`length:num`] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[DRV_APART_SYM] THEN ASM_REWRITE_TAC[];ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[DRV_APART_SYM] THEN ASM_REWRITE_TAC[];ASM_REWRITE_TAC[]]]);;

let DRV_REGION_WORD_AGREE = prove
 (`!base length before after i.
     val(base:int64) + length < 2 EXP 64 /\ 8 * i + 8 <= length /\
     (!a. drv_in a base length ==> (after:int64->byte) a = before a)
     ==> pl_mw after base i = pl_mw before base i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_mw] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `byte:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `val(word_add (word_add base (word(8 * i))) (word byte):int64) = val base + 8 * i + byte`
   ASSUME_TAC THENL
   [REWRITE_TAC[DRV_ADDR_ASSOC] THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC]);;

let driver_region_frame_theorems =
 ["DRV_MEMORY_FRAME_REGION",DRV_MEMORY_FRAME_REGION;"DRV_REGION_WORD_AGREE",DRV_REGION_WORD_AGREE];;
