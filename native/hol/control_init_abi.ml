(* Control initialization as observed after the plan driver's ABI return. *)
needs "native/hol/control_init_driver.ml";;
needs "native/hol/zero_init.ml";;

let CINIT_ABI_WORD = prove
 (`!ctl nctl cfr d plan res m j.
     48 <= val cfr /\ val(ctl:int64) + 8 * nctl < 2 EXP 64 /\ j < nctl /\
     drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl) /\
     drv_apart ctl (8 * nctl) d 64 /\ val(d:int64) + 64 <= 2 EXP 64 /\
     (!a. ~drv_stack cfr a ==> m a = drv_final d plan res a)
     ==> drv_word m (word_add ctl (word(8 * j))) =
         drv_word (FST(SND(SND res))) (word_add ctl (word(8 * j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  X_GEN_TAC `byte:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `val(word_add (word_add ctl (word(8 * j))) (word byte):int64) = val ctl + 8 * j + byte`
   ASSUME_TAC THENL
   [REWRITE_TAC[DRV_ADDR_ASSOC] THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN
   `drv_in (word_add (word_add ctl (word(8 * j))) (word byte)) ctl (8 * nctl)`
   ASSUME_TAC THENL [ASM_REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `~drv_stack cfr (word_add (word_add ctl (word(8 * j))) (word byte))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [`ctl:int64`;`8 * nctl`] THEN
    ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `~drv_in (word_add (word_add ctl (word(8 * j))) (word byte)) d 64`
   ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [drv_apart] o
     check (fun th -> concl th = `drv_apart ctl (8 * nctl) d 64`)) THEN
    ASM_REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[ZINIT_FINAL_BYTE]]);;

let cinit_abi_post = new_definition
 `cinit_abi_post (ctl:int64) nctl d plan used (old:int64->byte) (status:int64) m <=>
    let policy = drv_word old (word_add ctl (word 56)) in
    status = word(if val policy <= 2 then 1 else 0) /\
    drv_word m (word_add d (word 48)) = used /\
    drv_word m (word_add d (word 56)) =
      (if val policy <= 2 then word_add plan (word 144) else plan) /\
    (!j. j < nctl
         ==> drv_word m (word_add ctl (word(8 * j))) =
             if j = 24 then (if val policy <= 2 then policy else word 0)
             else if val policy <= 2 /\ j < 24 then control_init_value policy j
                  else drv_word old (word_add ctl (word(8 * j))))`;;

let CINIT_ABI_FROM_POST = prove
 (`!ctl nctl cfr d plan used old res m.
     cinit_post ctl nctl 0 used old res /\
     48 <= val cfr /\ val(ctl:int64) + 8 * nctl < 2 EXP 64 /\
     drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl) /\
     drv_apart (word_sub cfr (word 48)) 304 d 64 /\
     drv_apart ctl (8 * nctl) d 64 /\ val(d:int64) + 64 <= 2 EXP 64 /\
     (!a. ~drv_stack cfr a ==> m a = drv_final d plan res a)
     ==> cinit_abi_post ctl nctl d plan used old (FST res) m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[cinit_post;LET_DEF;LET_END_DEF] o
    check (fun th -> fst(strip_comb(concl th)) = `cinit_post`)) THEN
  MP_TAC(SPECL [`d:int64`;`plan:int64`;`res:int64#num#(int64->byte)#int64`] ZINIT_FINAL_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `drv_word m (word_add d (word 48)) = drv_word (drv_final d plan res) (word_add d (word 48)) /\
    drv_word m (word_add d (word 56)) = drv_word (drv_final d plan res) (word_add d (word 56))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ZINIT_DESCRIPTOR_AGREE THEN EXISTS_TAC `cfr:int64` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;ALL_TAC] THEN
  ASM_REWRITE_TAC[cinit_abi_post;LET_DEF;LET_END_DEF] THEN
  CONJ_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`ctl:int64`;`nctl:num`;`cfr:int64`;`d:int64`;`plan:int64`;
                  `res:int64#num#(int64->byte)#int64`;`m:int64->byte`;`j:num`] CINIT_ABI_WORD) THEN
    ASM_SIMP_TAC[]]);;

let CINIT_ABI_EXACT = prove
 (`!ctl nctl d plan used old status m.
     cinit_abi_post ctl nctl d plan used old status m
     ==> (status = word 1 <=> val(drv_word old (word_add ctl (word 56))) <= 2) /\
         (status = word 0 \/ status = word 1) /\
         drv_word m (word_add d (word 48)) = used`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cinit_abi_post;LET_DEF;LET_END_DEF] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

let CINIT_ABI_REFUSED_FRAME = prove
 (`!ctl nctl d plan used old status m.
     cinit_abi_post ctl nctl d plan used old status m /\ 24 < nctl /\
     ~(val(drv_word old (word_add ctl (word 56))) <= 2)
     ==> status = word 0 /\
         (!j. j < 24 ==> drv_word m (word_add ctl (word(8 * j))) =
                         drv_word old (word_add ctl (word(8 * j))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cinit_abi_post;LET_DEF;LET_END_DEF] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `j < nctl /\ ~(j = 24)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;ASM_SIMP_TAC[]]);;

let cinit_invalid_post = new_definition
 `cinit_invalid_post (ctl:int64) nctl d plan used (old:int64->byte) status m <=>
    status = word 3 /\ drv_word m (word_add d (word 48)) = used /\
    drv_word m (word_add d (word 56)) = plan /\
    (!j. j < nctl ==> drv_word m (word_add ctl (word(8 * j))) =
                      drv_word old (word_add ctl (word(8 * j))))`;;

let CINIT_INVALID_ABI = prove
 (`!ctl nctl cfr d plan used old res m.
     res = (word 3,0,old,used) /\
     48 <= val cfr /\ val(ctl:int64) + 8 * nctl < 2 EXP 64 /\
     drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl) /\
     drv_apart (word_sub cfr (word 48)) 304 d 64 /\
     drv_apart ctl (8 * nctl) d 64 /\ val(d:int64) + 64 <= 2 EXP 64 /\
     (!a. ~drv_stack cfr a ==> m a = drv_final d plan res a)
     ==> cinit_invalid_post ctl nctl d plan used old (FST res) m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:int64`;`plan:int64`;`res:int64#num#(int64->byte)#int64`] ZINIT_FINAL_FIELDS) THEN
  ASM_REWRITE_TAC[FST;SND;MULT_CLAUSES;WORD_ADD_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `drv_word m (word_add d (word 48)) = drv_word (drv_final d plan res) (word_add d (word 48)) /\
    drv_word m (word_add d (word 56)) = drv_word (drv_final d plan res) (word_add d (word 56))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ZINIT_DESCRIPTOR_AGREE THEN EXISTS_TAC `cfr:int64` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;ALL_TAC] THEN
  ASM_REWRITE_TAC[cinit_invalid_post;FST;SND] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`ctl:int64`;`nctl:num`;`cfr:int64`;`d:int64`;`plan:int64`;
                `res:int64#num#(int64->byte)#int64`;`m:int64->byte`;`j:num`] CINIT_ABI_WORD) THEN
  ASM_REWRITE_TAC[FST;SND]);;

let CINIT_ABI_FROM_RUN = prove
 (`!bw ctl budget cfr slot nctl d plan old used res m.
     drv_sem (\j. control_init) bw ctl budget cfr [cinit_step slot] 0 old used res /\
     slot < 2 EXP 64 /\ bw slot = ctl /\ val(bw(slot + 1)) = 8 * nctl /\
     48 <= val cfr /\ val(ctl:int64) + 8 * nctl < 2 EXP 64 /\
     drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl) /\ 24 < nctl /\
     drv_apart (word_sub cfr (word 48)) 304 d 64 /\
     drv_apart ctl (8 * nctl) d 64 /\ val(d:int64) + 64 <= 2 EXP 64 /\
     (!a. ~drv_stack cfr a ==> m a = drv_final d plan res a)
     ==> if val budget < val used
         then cinit_invalid_post ctl nctl d plan used old (FST res) m
         else cinit_abi_post ctl nctl d plan used old (FST res) m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`slot:num`;
                `nctl:num`;`0`;`old:int64->byte`;`used:int64`;
                `res:int64#num#(int64->byte)#int64`] CINIT_RUN_ALL) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[COND_CLAUSES] THENL
   [MATCH_MP_TAC CINIT_INVALID_ABI;
    MATCH_MP_TAC CINIT_ABI_FROM_POST] THEN
  EXISTS_TAC `cfr:int64` THEN ASM_REWRITE_TAC[]);;

let CINIT_ABI_BOOT_VALUES = prove
 (`!ctl nctl d plan used old status m.
     cinit_abi_post ctl nctl d plan used old status m /\ 24 < nctl /\ status = word 1
     ==> ?cw. (!i. i < nctl ==> pl_mw m ctl i = cw i) /\
              (!i. i <= 6 ==> cw i = i) /\
              cw 7 = val(drv_word old (word_add ctl (word 56))) /\
              cw 17 = 0 /\ cw 19 = 0 /\ cw 20 = 0 /\ cw 22 = 14695981039346656037`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CINIT_ABI_EXACT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[cinit_abi_post;LET_DEF;LET_END_DEF] o
    check (fun th -> fst(strip_comb(concl th)) = `cinit_abi_post`)) THEN
  EXISTS_TAC `\i. pl_mw m ctl i` THEN BETA_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[pl_mw;ARITH_RULE `24 < n ==> 7 < n /\ 17 < n /\ 19 < n /\ 20 < n /\ 22 < n`;
               ARITH_RULE `~(7 = 24) /\ ~(17 = 24) /\ ~(19 = 24) /\ ~(20 = 24) /\ ~(22 = 24)`;
               ARITH_RULE `7 < 24 /\ 17 < 24 /\ 19 < 24 /\ 20 < 24 /\ 22 < 24`;
               CONTROL_INIT_VALUE_FIELDS;VAL_WORD_0] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < nctl /\ i < 24 /\ ~(i = 24)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[pl_mw;control_init_value;VAL_WORD;DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let control_init_abi_theorems =
 ["CINIT_ABI_WORD",CINIT_ABI_WORD;"CINIT_ABI_FROM_POST",CINIT_ABI_FROM_POST;
  "CINIT_ABI_EXACT",CINIT_ABI_EXACT;"CINIT_ABI_REFUSED_FRAME",CINIT_ABI_REFUSED_FRAME;
  "CINIT_INVALID_ABI",CINIT_INVALID_ABI;"CINIT_ABI_FROM_RUN",CINIT_ABI_FROM_RUN;
  "CINIT_ABI_BOOT_VALUES",CINIT_ABI_BOOT_VALUES];;
