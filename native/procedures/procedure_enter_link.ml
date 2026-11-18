(* The mathematical activation step realized by the checked p1 component. *)
needs "native/procedures/procedure_rules.ml";;
needs "native/leaves/procedure_enter/procedure_enter_join.ml";;

let PROCEDURE_ENTER_ACTIVATION = prove
 (`!t k u. tisa_entry_ok procedure_enter t /\ tisa_run procedure_enter t = TStop k u
       ==> procedure_activation (val(tisa_fword t 20)) (val(tisa_fword t 23))
             (val(tisa_fword t 22)) (val(tisa_fword t 21)) =
           (k,(if k = 1 then val(tisa_fword u 19) else val(tisa_fword t 22)),
              val(tisa_fword u 21))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PROCEDURE_ENTER_RECEIPT_VALID o
    check (fun th -> fst(strip_comb(concl th)) = `tisa_entry_ok`)) THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] PROCEDURE_ENTER_OUTCOMES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(tisa_fword t 20) < val(tisa_fword t 21))` ASSUME_TAC THENL
   [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_CASES_TAC `val(tisa_fword t 22) < val(tisa_fword t 23)` THENL
   [SUBGOAL_THEN `~(val(tisa_fword t 23) <= val(tisa_fword t 22))` ASSUME_TAC THENL
     [ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_CASES_TAC `val(tisa_fword t 21) = val(tisa_fword t 20)` THENL
     [SUBGOAL_THEN `k = 4` ASSUME_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
      ASM_REWRITE_TAC[procedure_activation;ARITH_EQ] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `val(tisa_fword t 21) < val(tisa_fword t 20)` ASSUME_TAC THENL
       [ASM_ARITH_TAC;ALL_TAC] THEN
      SUBGOAL_THEN `k = 1` ASSUME_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
      ASM_REWRITE_TAC[procedure_activation;ARITH_EQ] THEN ASM_MESON_TAC[]];
    SUBGOAL_THEN `val(tisa_fword t 23) <= val(tisa_fword t 22)` ASSUME_TAC THENL
     [ASM_ARITH_TAC;ALL_TAC] THEN
    SUBGOAL_THEN `k = 2` ASSUME_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    ASM_REWRITE_TAC[procedure_activation;ARITH_EQ] THEN ASM_MESON_TAC[]]);;

let procedure_enter_link_theorems = procedure_rules_theorems @
 ["PROCEDURE_ENTER_ACTIVATION",PROCEDURE_ENTER_ACTIVATION];;
