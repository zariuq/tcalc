(* Control values established by the initializer, independent of a logic. *)
needs "native/hol/control_init_words.ml";;

let CONTROL_INIT_VALUE_FIELDS = prove
 (`!policy:int64.
     control_init_value policy 7 = policy /\
     control_init_value policy 17 = word 0 /\ control_init_value policy 19 = word 0 /\
     control_init_value policy 20 = word 0 /\
     control_init_value policy 22 = word 14695981039346656037`,
  REWRITE_TAC[control_init_value] THEN CONV_TAC NUM_REDUCE_CONV);;

let CONTROL_INIT_CONTROL_VALUES = prove
 (`!t k u nctl.
     tisa_entry_ok control_init t /\ tisa_run control_init t = TStop k u /\
     24 <= nctl /\ val(tisa_len t 0) = 8 * nctl /\ val(tisa_fword t 22) <= 2
     ==> k = 1 /\
         ?cw. (!i. i < nctl ==> pl_mw (tmem u) (tisa_base t 0) i = cw i) /\
              (!i. i <= 6 ==> cw i = i) /\ cw 7 = val(tisa_fword t 22) /\
              cw 17 = 0 /\ cw 19 = 0 /\ cw 20 = 0 /\ cw 22 = val(control_init_value (tisa_fword t 22) 22) /\
              (!i. i < nctl
                   ==> cw i = if i < 24 then val(control_init_value (tisa_fword t 22) i)
                               else pl_mw (tmem t) (tisa_base t 0) i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `k = 1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] CONTROL_INIT_RUN) THEN
    ASM_REWRITE_TAC[control_init_post] THEN SIMP_TAC[];ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i. i < nctl ==> pl_mw (tmem u) (tisa_base t 0) i =
      if i < 24 then val(control_init_value (tisa_fword t 22) i)
      else pl_mw (tmem t) (tisa_base t 0) i` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`;`i:num`] CONTROL_INIT_RUN_NUMBER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;ASM_REWRITE_TAC[]];ALL_TAC] THEN
  EXISTS_TAC `\i. pl_mw (tmem u) (tisa_base t 0) i` THEN BETA_TAC THEN
  REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `24 <= n ==> 7 < n /\ 17 < n /\ 19 < n /\ 20 < n /\ 22 < n`;
               ARITH_RULE `7 < 24 /\ 17 < 24 /\ 19 < 24 /\ 20 < 24 /\ 22 < 24`;
               CONTROL_INIT_VALUE_FIELDS;VAL_WORD_0] THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < nctl /\ i < 24` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[control_init_value;VAL_WORD;DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let control_init_value_theorems =
 ["CONTROL_INIT_VALUE_FIELDS",CONTROL_INIT_VALUE_FIELDS;
  "CONTROL_INIT_CONTROL_VALUES",CONTROL_INIT_CONTROL_VALUES];;
