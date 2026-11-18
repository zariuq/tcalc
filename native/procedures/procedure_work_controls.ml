(* Physical control words during a yielded call and final result publication. *)
needs "native/procedures/procedure_call_transport.ml";;

let procedure_control_word = new_definition
 `procedure_control_word (ctl:int64) j = word_add ctl (word(8 * j))`;;

let procedure_work_controls = new_definition
 `procedure_work_controls m ctl nctl (cw:num->num) <=>
    !j. j < nctl ==> cw j < 2 EXP 64 /\ drv_word m (procedure_control_word ctl j) = word(cw j)`;;

(* The marker captures arguments before the driver writes its payload. The
   suspended caller's destination need not retain its former physical value. *)
let procedure_work_waiting = new_definition
 `procedure_work_waiting m ctl nctl (cw:num->num) dst <=>
    dst < nctl /\
    !j. j < nctl ==> cw j < 2 EXP 64 /\
      (j = dst \/ drv_word m (procedure_control_word ctl j) = word(cw j))`;;

let PROCEDURE_CONTROL_ADDRESS = prove
 (`!ctl nctl j. val(ctl:int64) + 8 * nctl < 2 EXP 64 /\ j < nctl ==>
    val(procedure_control_word ctl j) = val ctl + 8 * j /\
    val(procedure_control_word ctl j) + 8 <= val ctl + 8 * nctl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(ctl:int64) + 8 * j < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[procedure_control_word;TISA_VAL_OFFSET] THEN ASM_ARITH_TAC);;

let PROCEDURE_CONTROL_WORDS_APART = prove
 (`!ctl nctl i j. val(ctl:int64) + 8 * nctl < 2 EXP 64 /\
    i < nctl /\ j < nctl /\ ~(i = j) ==>
    drv_apart (procedure_control_word ctl i) 8 (procedure_control_word ctl j) 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ctl:int64`;`nctl:num`;`i:num`] PROCEDURE_CONTROL_ADDRESS) THEN
  MP_TAC(SPECL [`ctl:int64`;`nctl:num`;`j:num`] PROCEDURE_CONTROL_ADDRESS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[drv_apart] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let PROCEDURE_CONTROL_WRITE_OTHER = prove
 (`!ctl nctl i dst value m. val(ctl:int64) + 8 * nctl < 2 EXP 64 /\
    i < nctl /\ dst < nctl /\ ~(i = dst) ==>
    drv_word (write (bytes64(procedure_control_word ctl dst)) value m)
      (procedure_control_word ctl i) = drv_word m (procedure_control_word ctl i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC PROCEDURE_WRITE_WORD_APART THEN
  MP_TAC(SPECL [`ctl:int64`;`nctl:num`;`i:num`] PROCEDURE_CONTROL_ADDRESS) THEN
  MP_TAC(SPECL [`ctl:int64`;`nctl:num`;`dst:num`] PROCEDURE_CONTROL_ADDRESS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;ASM_ARITH_TAC;
    MATCH_MP_TAC PROCEDURE_CONTROL_WORDS_APART THEN EXISTS_TAC `nctl:num` THEN
    ASM_REWRITE_TAC[]]);;

let PROCEDURE_WORK_YIELD = prove
 (`!ctl nctl cw dst value m. val(ctl:int64) + 8 * nctl < 2 EXP 64 /\
    dst < nctl /\ procedure_work_controls m ctl nctl cw ==>
    procedure_work_waiting (write (bytes64(procedure_control_word ctl dst)) value m)
      ctl nctl cw dst`,
  REPEAT GEN_TAC THEN REWRITE_TAC[procedure_work_controls;procedure_work_waiting] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(j:num) = dst` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ctl:int64`;`nctl:num`;`j:num`;`dst:num`;`value:int64`;
    `m:int64->byte`] PROCEDURE_CONTROL_WRITE_OTHER) THEN ASM_REWRITE_TAC[]);;

let PROCEDURE_WORK_RETURN = prove
 (`!ctl nctl cw dst value m. val(ctl:int64) + 8 * nctl < 2 EXP 64 /\
    value < 2 EXP 64 /\ procedure_work_waiting m ctl nctl cw dst ==>
    procedure_work_controls
      (write (bytes64(procedure_control_word ctl dst)) (word value) m)
      ctl nctl (procedure_set cw dst value)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[procedure_work_waiting;procedure_work_controls] THEN
  STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(j:num) = dst` THEN
  ASM_SIMP_TAC[procedure_set;DRV_WORD_WRITE_SAME] THEN
  MP_TAC(SPECL [`ctl:int64`;`nctl:num`;`j:num`;`dst:num`;`word value:int64`;
    `m:int64->byte`] PROCEDURE_CONTROL_WRITE_OTHER) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let PROCEDURE_WORK_CALL_PUBLICATION = prove
 (`!ctl nctl cw st u. val(ctl:int64) + 8 * nctl < 2 EXP 64 /\
    val(EL 17 st) < nctl /\ procedure_work_controls (tmem u) ctl nctl cw ==>
    procedure_work_waiting (drv_after ctl st u) ctl nctl cw (val(EL 17 st))`,
  REWRITE_TAC[drv_after;GSYM procedure_control_word] THEN
  MESON_TAC[PROCEDURE_WORK_YIELD]);;

let PROCEDURE_WORK_SAVED_ARGUMENTS = prove
 (`!saved ctl nctl dst value m. val(saved:int64) + 56 < 2 EXP 64 /\
    val(ctl:int64) + 8 * nctl < 2 EXP 64 /\ dst < nctl /\
    drv_apart saved 56 ctl (8 * nctl) ==>
    !j. j < 7 ==>
      drv_word (write (bytes64(procedure_control_word ctl dst)) value m)
        (procedure_control_word saved j) = drv_word m (procedure_control_word saved j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`saved:int64`;`7`;`j:num`] PROCEDURE_CONTROL_ADDRESS) THEN
  MP_TAC(SPECL [`ctl:int64`;`nctl:num`;`dst:num`] PROCEDURE_CONTROL_ADDRESS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PROCEDURE_WRITE_WORD_APART THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;ASM_ARITH_TAC;
    REWRITE_TAC[drv_apart] THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[drv_apart]) THEN ASM_ARITH_TAC]);;

let PROCEDURE_WORK_RETURN_REJOINS = prove
 (`!ctl nctl cw dst temporary value m.
    val(ctl:int64) + 8 * nctl < 2 EXP 64 /\ dst < nctl /\ value < 2 EXP 64 /\
    procedure_work_controls m ctl nctl cw ==>
    procedure_work_controls
      (write (bytes64(procedure_control_word ctl dst)) (word value)
        (write (bytes64(procedure_control_word ctl dst)) temporary m))
      ctl nctl (procedure_set cw dst value)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC PROCEDURE_WORK_RETURN THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PROCEDURE_WORK_YIELD THEN ASM_REWRITE_TAC[]);;

let PROCEDURE_WORK_YIELD_NOT_EXACT = prove
 (`!ctl nctl cw dst temporary m.
    dst < nctl /\ ~(temporary = word(cw dst):int64) ==>
    ~procedure_work_controls
      (write (bytes64(procedure_control_word ctl dst)) temporary m) ctl nctl cw`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[procedure_work_controls] THEN
  DISCH_THEN(MP_TAC o SPEC `dst:num`) THEN
  ASM_REWRITE_TAC[DRV_WORD_WRITE_SAME] THEN ASM_MESON_TAC[]);;

let procedure_work_controls_theorems =
 ["PROCEDURE_CONTROL_ADDRESS",PROCEDURE_CONTROL_ADDRESS;
  "PROCEDURE_CONTROL_WORDS_APART",PROCEDURE_CONTROL_WORDS_APART;
  "PROCEDURE_CONTROL_WRITE_OTHER",PROCEDURE_CONTROL_WRITE_OTHER;
  "PROCEDURE_WORK_YIELD",PROCEDURE_WORK_YIELD;
  "PROCEDURE_WORK_RETURN",PROCEDURE_WORK_RETURN;
  "PROCEDURE_WORK_CALL_PUBLICATION",PROCEDURE_WORK_CALL_PUBLICATION;
  "PROCEDURE_WORK_SAVED_ARGUMENTS",PROCEDURE_WORK_SAVED_ARGUMENTS;
  "PROCEDURE_WORK_RETURN_REJOINS",PROCEDURE_WORK_RETURN_REJOINS;
  "PROCEDURE_WORK_YIELD_NOT_EXACT",PROCEDURE_WORK_YIELD_NOT_EXACT];;
