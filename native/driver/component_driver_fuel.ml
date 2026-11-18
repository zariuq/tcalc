(* Fuel receipts compose through every completed component and every exit. *)
needs "native/driver/component_driver.ml";;

let COMPONENT_DRV_CHILD_RECEIPT = prove
 (`!bw ctl budget cfr st m used t.
     drv_child bw ctl budget cfr st m used t
     ==> tisa_fword t 20 = budget /\ tisa_fword t 21 = used`,
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_child] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `20` o check (fun th -> is_forall(concl th) &&
       can (find_term ((=) `drv_fw`)) (concl th)));
    FIRST_X_ASSUM(MP_TAC o SPEC `21` o check (fun th -> is_forall(concl th) &&
       can (find_term ((=) `drv_fw`)) (concl th)))] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[drv_fw] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let COMPONENT_DRV_SEM_FUEL = prove
 (`!progs bw ctl budget cfr sts i m used res.
     component_drv_sem progs bw ctl budget cfr sts i m used res /\
     val used <= val budget /\
     ALL (\st. component_ok (progs (val(EL 0 st)))) sts
     ==> val used <= val(SND(SND(SND res))) /\
         val(SND(SND(SND res))) <= val budget`,
  MAP_EVERY X_GEN_TAC [`progs:num->native_component`;`bw:num->int64`;`ctl:int64`;
                      `budget:int64`;`cfr:int64`] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[component_drv_sem;ALL] THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[component_drv_sem;ALL] THEN
  COND_CASES_TAC THENL
   [STRIP_TAC THEN ASM_ARITH_TAC;ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `tc:tisa_state` (X_CHOOSE_THEN `k:num`
      (X_CHOOSE_THEN `u:tisa_state` STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `tisa_fword tc 20 = budget /\ tisa_fword tc 21 = used`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC COMPONENT_DRV_CHILD_RECEIPT THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`;`ctl:int64`;`cfr:int64`;
                          `h:int64 list`;`m:int64->byte`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(used:int64) <= val(tisa_fword u 21) /\
                val(tisa_fword u 21) <= val(budget:int64)` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`progs (val(EL 0 (h:int64 list))):native_component`;
                  `tc:tisa_state`;`k:num`;`u:tisa_state`] COMPONENT_RUN_FUEL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`;`drv_after ctl (h:int64 list) u`;
                                  `tisa_fword u 21`;`res:int64#num#(int64->byte)#int64`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `component_drv_sem`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let component_driver_fuel_theorems =
 ["COMPONENT_DRV_CHILD_RECEIPT",COMPONENT_DRV_CHILD_RECEIPT;
  "COMPONENT_DRV_SEM_FUEL",COMPONENT_DRV_SEM_FUEL];;
