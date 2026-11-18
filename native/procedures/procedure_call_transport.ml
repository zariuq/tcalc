(* A yielded call captures its operands before the driver's result write. *)
needs "native/leaves/procedure_call/procedure_call.ml";;
needs "native/procedures/procedure_sem.ml";;
needs "native/procedures/procedure_stack.ml";;

let PROCEDURE_REQUEST_CHILD_VALUES = prove
 (`!bw ctl budget cfr st m used t.
    drv_child bw ctl budget cfr st m used t
    ==> [procedure_request_value t 0;procedure_request_value t 1;
         procedure_request_value t 2;procedure_request_value t 3;
         procedure_request_value t 4;procedure_request_value t 5;
         procedure_request_value t 6] =
        [drv_cw ctl m (EL 10 st);drv_cw ctl m (EL 11 st);drv_cw ctl m (EL 12 st);
         drv_cw ctl m (EL 13 st);drv_cw ctl m (EL 14 st);drv_cw ctl m (EL 15 st);
         drv_cw ctl m (EL 16 st)] /\
        procedure_request_value t 7 = drv_len bw st 8`,
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_child] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "frame") (K ALL_TAC))) THEN
  MAP_EVERY (fun j -> USE_THEN "frame" (MP_TAC o SPEC (mk_small_numeral j)) THEN
    REWRITE_TAC[drv_fw] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [17;22;23] THEN
  REMOVE_THEN "frame" (K ALL_TAC) THEN
  ASM_REWRITE_TAC[procedure_request_value;drv_regs;drv_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let PROCEDURE_REQUEST_SOURCE_ARGUMENTS = prove
 (`!bw ctl budget cfr st m used t cw.
    drv_child bw ctl budget cfr st m used t /\
    (!j. j < 7 ==> drv_cw ctl m (EL (10 + j) st) = word(cw(val(EL (10 + j) st))))
    ==> [procedure_request_value t 0;procedure_request_value t 1;
         procedure_request_value t 2;procedure_request_value t 3;
         procedure_request_value t 4;procedure_request_value t 5;
         procedure_request_value t 6] = MAP (word:num->int64) (procedure_args st cw)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`st:int64 list`;
                `m:int64->byte`;`used:int64`;`t:tisa_state`] PROCEDURE_REQUEST_CHILD_VALUES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[procedure_args;MAP] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `drv_cw`)) (concl th))) THEN
  CONV_TAC (LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN REFL_TAC);;

let PROCEDURE_REQUEST_PUBLICATION_KEEPS = prove
 (`!ctl nctl st t k u j.
    tisa_entry_ok procedure_call_marker t /\ tisa_run procedure_call_marker t = TStop k u /\
    j < 8 /\ val(EL 17 st) < nctl /\ val(ctl:int64) + 8 * nctl < 2 EXP 64 /\
    drv_apart (tisa_base t 0) (val(tisa_len t 0)) ctl (8 * nctl)
    ==> drv_word (drv_after ctl st u) (word_add (tisa_base t 0) (word(8 * j))) =
        procedure_request_value t j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o MATCH_MP PROCEDURE_CALL_MARKER_ENTRY o
    check (fun th -> fst(strip_comb(concl th)) = `tisa_entry_ok`)) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `drv_word (tmem u) (word_add (tisa_base t 0) (word(8 * j)))` THEN CONJ_TAC THENL
   [REWRITE_TAC[drv_after] THEN MATCH_MP_TAC PROCEDURE_WRITE_WORD_APART THEN
    SUBGOAL_THEN
     `val(word_add (tisa_base t 0) (word(8 * j)):int64) = val(tisa_base t 0) + 8 * j /\
      val(word_add ctl (word(8 * val(EL 17 (st:int64 list)))):int64) = val ctl + 8 * val(EL 17 st)`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_REWRITE_TAC[drv_apart] THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_apart]) THEN ASM_ARITH_TAC;
    MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`;`j:num`] PROCEDURE_CALL_MARKER_WORD) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let PROCEDURE_RESULT_ARGUMENT_ALIAS = prove
 (`!cw st. val(EL 17 st) = val(EL 10 st)
     ==> HD(procedure_args st (procedure_set cw (val(EL 17 st)) 0)) = 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[procedure_args;HD;procedure_set]);;

let procedure_call_transport_theorems =
 ["PROCEDURE_REQUEST_CHILD_VALUES",PROCEDURE_REQUEST_CHILD_VALUES;
  "PROCEDURE_REQUEST_SOURCE_ARGUMENTS",PROCEDURE_REQUEST_SOURCE_ARGUMENTS;
  "PROCEDURE_REQUEST_PUBLICATION_KEEPS",PROCEDURE_REQUEST_PUBLICATION_KEEPS;
  "PROCEDURE_RESULT_ARGUMENT_ALIAS",PROCEDURE_RESULT_ARGUMENT_ALIAS];;
