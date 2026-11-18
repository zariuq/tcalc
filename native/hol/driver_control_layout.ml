(* Mutable control arrays are disjoint from a driver's static footprint. *)
needs "native/driver/driver.ml";;

let DRV_APART_EXCLUDES = prove
 (`!a m b n x. drv_apart a m b n /\ drv_in x a m ==> ~drv_in x b n`,
  REWRITE_TAC[drv_apart;drv_in] THEN ARITH_TAC);;

let DRV_RETURN_WINDOW = prove
 (`!cfr a. 48 <= val cfr /\ val(cfr:int64) + 256 <= 2 EXP 64 /\
           drv_in a (word_add cfr (word 248)) 8
     ==> drv_in a (word_sub cfr (word 48)) 304`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cfr:int64`;`48`] TISA_VAL_SP_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word_add cfr (word 248):int64) = val cfr + 248` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [drv_in] o
    check (fun th -> fst(strip_comb(concl th)) = `drv_in`)) THEN
  ASM_REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC);;

let DRV_CONTROL_NOT_STATIC = prove
 (`!pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc a.
     drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     drv_in a ctl (8 * nctl)
     ==> ~drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[drv_layout] o
    check (fun th -> fst(strip_comb(concl th)) = `drv_layout`)) THEN
  SUBGOAL_THEN `!base length. drv_apart ctl (8 * nctl) base length ==> ~drv_in a base length`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC DRV_APART_EXCLUDES THEN
    MAP_EVERY EXISTS_TAC [`ctl:int64`;`8 * nctl`] THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `~drv_in a (word_add cfr (word 248)) 8` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `drv_in a (word_sub cfr (word 48)) 304` ASSUME_TAC THENL
     [MATCH_MP_TAC DRV_RETURN_WINDOW THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
    MP_TAC(SPECL [`word_sub cfr (word 48):int64`;`304`;`ctl:int64`;`8 * nctl`;`a:int64`]
                 DRV_APART_EXCLUDES) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  ASM_SIMP_TAC[drv_static;DE_MORGAN_THM;NOT_EXISTS_THM;
               TAUT `~(a /\ b) <=> a ==> ~b`]);;

let driver_control_layout_theorems =
 ["DRV_APART_EXCLUDES",DRV_APART_EXCLUDES;"DRV_RETURN_WINDOW",DRV_RETURN_WINDOW;
  "DRV_CONTROL_NOT_STATIC",DRV_CONTROL_NOT_STATIC];;
