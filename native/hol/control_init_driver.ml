(* The existing plan driver calls the initializer on its control array. *)
needs "native/hol/control_init_frame.ml";;
needs "native/hol/control_init_values.ml";;

let cinit_step = new_definition
 `cinit_step slot =
    [word 0;word slot;word slot;word slot;word slot;word slot;word slot;
     word slot;word slot;word slot;word 7;word 0;word 0;word 0;word 0;word 0;word 0;word 24]:int64 list`;;

let CINIT_STEP_FIELDS = prove
 (`!slot. slot < 2 EXP 64
     ==> LENGTH(cinit_step slot) = 18 /\ val(EL 0 (cinit_step slot)) = 0 /\
         val(EL 1 (cinit_step slot)) = slot /\ val(EL 17 (cinit_step slot)) = 24`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[cinit_step;LENGTH] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV);;

let CINIT_BINDINGS = prove
 (`!bw slot. slot < 2 EXP 64
     ==> drv_base bw (cinit_step slot) 0 = bw slot /\
         drv_len bw (cinit_step slot) 0 = bw(slot + 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `slot:num` CINIT_STEP_FIELDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[drv_base;drv_len;ARITH_RULE `1 + 0 = 1`]);;

let CINIT_CHILD = prove
 (`!bw ctl budget cfr slot m used t.
     slot < 2 EXP 64 /\ drv_child bw ctl budget cfr (cinit_step slot) m used t
     ==> tregs t 0 = cfr /\ tisa_base t 0 = bw slot /\ tisa_len t 0 = bw(slot + 1) /\
         tisa_fword t 22 = drv_word m (word_add ctl (word 56)) /\
         tisa_fword t 20 = budget /\ tisa_fword t 21 = used`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `0`)) THEN
  ASM_SIMP_TAC[CINIT_BINDINGS;ARITH_RULE `0 < 9`] THEN STRIP_TAC THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o REWRITE_RULE[drv_child] o
    check (fun th -> fst(strip_comb(concl th)) = `drv_child`)) THEN
  ASM_SIMP_TAC[drv_fw;
               ARITH_RULE `20 < 24 /\ 21 < 24 /\ 22 < 24`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[drv_cw;cinit_step] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let CINIT_AFTER_WORD = prove
 (`!ctl slot u nctl j.
     val(ctl:int64) + 8 * nctl < 2 EXP 64 /\ 24 < nctl /\ j < nctl
     ==> drv_word (drv_after ctl (cinit_step slot) u) (word_add ctl (word(8 * j))) =
         if j = 24 then tisa_fword u 19
         else drv_word (tmem u) (word_add ctl (word(8 * j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[drv_after;cinit_step] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[TISA_WRITE_BYTES64] THEN
  MP_TAC(SPECL [`ctl:int64`;`8 * nctl`;`24`;`j:num`;`tisa_fword u 19`;`tmem u`]
               CONTROL_WORD_WRITE) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC;CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EQ_SYM_EQ]]);;

let DRV_CHILD_CONTROL_WORD = prove
 (`!bw ctl budget cfr st m used t nctl j.
     drv_child bw ctl budget cfr st m used t /\ 48 <= val cfr /\
     val(ctl:int64) + 8 * nctl < 2 EXP 64 /\
     drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl) /\ j < nctl
     ==> drv_word (tmem t) (word_add ctl (word(8 * j))) =
         drv_word m (word_add ctl (word(8 * j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  X_GEN_TAC `byte:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
    check (fun th -> fst(strip_comb(concl th)) = `drv_child`)) THEN
  MATCH_MP_TAC DRV_IN_NOT_STACK THEN
  MAP_EVERY EXISTS_TAC [`ctl:int64`;`8 * nctl`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[drv_in] THEN
  SUBGOAL_THEN
   `val(word_add (word_add ctl (word(8 * j))) (word byte):int64) = val ctl + 8 * j + byte`
   SUBST1_TAC THENL
   [REWRITE_TAC[DRV_ADDR_ASSOC] THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let CINIT_CALL = prove
 (`!bw ctl budget cfr slot m used t k u.
     slot < 2 EXP 64 /\ drv_child bw ctl budget cfr (cinit_step slot) m used t /\
     tisa_entry_ok control_init t /\ tisa_run control_init t = TStop k u
     ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = used /\
         tisa_fword u 19 =
           (if val(drv_word m (word_add ctl (word 56))) <= 2
            then drv_word m (word_add ctl (word 56)) else word 0) /\
         k = (if val(drv_word m (word_add ctl (word 56))) <= 2 then 1 else 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`slot:num`;
                `m:int64->byte`;`used:int64`;`t:tisa_state`] CINIT_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] CONTROL_INIT_FRAME_RESULT) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let CINIT_CALL_WORD = prove
 (`!bw ctl budget cfr slot m used t k u nctl j.
     slot < 2 EXP 64 /\ drv_child bw ctl budget cfr (cinit_step slot) m used t /\
     tisa_entry_ok control_init t /\ tisa_run control_init t = TStop k u /\
     bw slot = ctl /\ val(bw(slot + 1)) = 8 * nctl /\
     48 <= val cfr /\ val(ctl:int64) + 8 * nctl < 2 EXP 64 /\
     drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl) /\ 24 < nctl /\ j < nctl
     ==> drv_word (drv_after ctl (cinit_step slot) u) (word_add ctl (word(8 * j))) =
         if j = 24 then
           (if val(drv_word m (word_add ctl (word 56))) <= 2
            then drv_word m (word_add ctl (word 56)) else word 0)
         else if val(drv_word m (word_add ctl (word 56))) <= 2 /\ j < 24
              then control_init_value (drv_word m (word_add ctl (word 56))) j
              else drv_word m (word_add ctl (word(8 * j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`slot:num`;
                `m:int64->byte`;`used:int64`;`t:tisa_state`] CINIT_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`slot:num`;
                `m:int64->byte`;`used:int64`;`t:tisa_state`;`k:num`;`u:tisa_state`] CINIT_CALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`cinit_step slot`;
                `m:int64->byte`;`used:int64`;`t:tisa_state`;`nctl:num`;`j:num`] DRV_CHILD_CONTROL_WORD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`;`j:num`] CONTROL_INIT_RUN_WORD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`ctl:int64`;`slot:num`;`u:tisa_state`;`nctl:num`;`j:num`] CINIT_AFTER_WORD) THEN
  ASM_REWRITE_TAC[]);;

let cinit_post = new_definition
 `cinit_post (ctl:int64) nctl i used (old:int64->byte)
             (res:int64#num#(int64->byte)#int64) <=>
    let policy = drv_word old (word_add ctl (word 56)) in
    FST res = word(if val policy <= 2 then 1 else 0) /\
    FST(SND res) = (if val policy <= 2 then i + 1 else i) /\
    SND(SND(SND res)) = used /\
    (!j. j < nctl
         ==> drv_word (FST(SND(SND res))) (word_add ctl (word(8 * j))) =
             if j = 24 then (if val policy <= 2 then policy else word 0)
             else if val policy <= 2 /\ j < 24 then control_init_value policy j
                  else drv_word old (word_add ctl (word(8 * j))))`;;

let CINIT_RUN = prove
 (`!bw ctl budget cfr slot nctl i m used res.
     drv_sem (\j. control_init) bw ctl budget cfr [cinit_step slot] i m used res /\
     ~(val budget < val used) /\ slot < 2 EXP 64 /\
     bw slot = ctl /\ val(bw(slot + 1)) = 8 * nctl /\
     48 <= val cfr /\ val(ctl:int64) + 8 * nctl < 2 EXP 64 /\
     drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl) /\ 24 < nctl
     ==> cinit_post ctl nctl i used m res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [drv_sem] o
    check (fun th -> fst(strip_comb(concl th)) = `drv_sem`)) THEN
  ASM_SIMP_TAC[CINIT_STEP_FIELDS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:tisa_state` (X_CHOOSE_THEN `k:num`
    (X_CHOOSE_THEN `u:tisa_state` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`slot:num`;
                `m:int64->byte`;`used:int64`;`t:tisa_state`;`k:num`;`u:tisa_state`] CINIT_CALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `val(drv_word m (word_add ctl (word 56))) <= 2` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th) &&
    can (find_term ((=) `drv_sem`)) (concl th))) THEN
  ASM_REWRITE_TAC[drv_sem;WORD_NE_10] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[cinit_post;LET_DEF;LET_END_DEF;FST;SND] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`slot:num`;
                `m:int64->byte`;`used:int64`;`t:tisa_state`;`k:num`;`u:tisa_state`;
                `nctl:num`;`j:num`] CINIT_CALL_WORD) THEN ASM_REWRITE_TAC[]);;

let CINIT_RUN_ALL = prove
 (`!bw ctl budget cfr slot nctl i m used res.
     drv_sem (\j. control_init) bw ctl budget cfr [cinit_step slot] i m used res /\
     slot < 2 EXP 64 /\ bw slot = ctl /\ val(bw(slot + 1)) = 8 * nctl /\
     48 <= val cfr /\ val(ctl:int64) + 8 * nctl < 2 EXP 64 /\
     drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl) /\ 24 < nctl
     ==> if val budget < val used then res = (word 3,i,m,used)
         else cinit_post ctl nctl i used m res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [drv_sem] o
     check (fun th -> fst(strip_comb(concl th)) = `drv_sem`)) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CINIT_RUN THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`;`budget:int64`;`cfr:int64`;`slot:num`] THEN
    ASM_REWRITE_TAC[]]);;

let control_init_driver_theorems =
 ["CINIT_STEP_FIELDS",CINIT_STEP_FIELDS;"CINIT_BINDINGS",CINIT_BINDINGS;
  "CINIT_CHILD",CINIT_CHILD;"CINIT_AFTER_WORD",CINIT_AFTER_WORD;
  "DRV_CHILD_CONTROL_WORD",DRV_CHILD_CONTROL_WORD;"CINIT_CALL",CINIT_CALL;
  "CINIT_CALL_WORD",CINIT_CALL_WORD;"CINIT_RUN",CINIT_RUN;"CINIT_RUN_ALL",CINIT_RUN_ALL];;
