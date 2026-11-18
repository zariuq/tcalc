(* Initialization plans over the proved driver and whole-word zero leaf. *)
needs "native/driver/driver.ml";;
needs "native/driver/driver_seq.ml";;
needs "native/leaves/zero_words/zero_words.ml";;

let zinit_app name tm =
  try fst(dest_const(fst(strip_comb tm))) = name with Failure _ -> false;;

(* A private one-entry leaf table holds zero_words. Unused bindings and
   input control indices are zero; control word zero receives the payload. *)
let zinit_step = new_definition
 `zinit_step slot =
    [word 0;word slot;word 0;word 0;word 0;word 0;word 0;word 0;word 0;
     word 0;word 0;word 0;word 0;word 0;word 0;word 0;word 0;word 0]:int64 list`;;

let zinit_plan = new_definition
 `zinit_plan slots = MAP zinit_step slots`;;

let zinit_supported = new_definition
 `zinit_supported (bw:num->int64) slot <=>
    8 * (val(bw(slot + 1)) DIV 8) = val(bw(slot + 1)) /\
    val(bw(slot + 1)) DIV 8 <= 4294967295`;;

let zinit_zero = new_definition
 `zinit_zero (bw:num->int64) slots (m:int64->byte) <=>
    !slot i. MEM slot slots /\ 8 * i + 8 <= val(bw(slot + 1))
       ==> drv_word m (word_add (bw slot) (word(8 * i))) = word 0`;;

let ZINIT_STEP_FIELDS = prove
 (`!slot. slot < 2 EXP 64
       ==> LENGTH(zinit_step slot) = 18 /\ val(EL 0 (zinit_step slot)) = 0 /\
           val(EL 1 (zinit_step slot)) = slot /\ val(EL 17 (zinit_step slot)) = 0`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[zinit_step;LENGTH] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV);;

let ZINIT_BINDINGS = prove
 (`!bw slot. slot < 2 EXP 64
       ==> drv_base bw (zinit_step slot) 0 = bw slot /\
           drv_len bw (zinit_step slot) 0 = bw(slot + 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `slot:num` ZINIT_STEP_FIELDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[drv_base;drv_len;ARITH_RULE `1 + 0 = 1`]);;

let ZINIT_CHILD = prove
 (`!bw ctl budget cfr slot m used t.
     slot < 2 EXP 64 /\ drv_child bw ctl budget cfr (zinit_step slot) m used t
     ==> tregs t 0 = cfr /\ tisa_base t 0 = bw slot /\ tisa_len t 0 = bw(slot + 1) /\
         tisa_fword t 20 = budget /\ tisa_fword t 21 = used`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `0`)) THEN
  ASM_SIMP_TAC[ZINIT_BINDINGS;ARITH_RULE `0 < 9`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[drv_child] o
    check (fun th -> tisa_has_tm `drv_child` th)) THEN
  ASM_SIMP_TAC[drv_fw;ARITH_RULE `20 < 24 /\ 21 < 24`;ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let ZINIT_RW = prove
 (`!r. tisa_rw (tisa_decls zero_words) r <=> r = 0`,
  GEN_TAC THEN REWRITE_TAC[ZERO_WORDS_DECLS;tisa_rw;LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[EL;HD;FST] THEN ASM_ARITH_TAC);;

let ZINIT_ZERO_NIL = prove
 (`!bw m. zinit_zero bw [] m`,REWRITE_TAC[zinit_zero;MEM]);;

let ZINIT_ZERO_CONS = prove
 (`!bw slot slots m. zinit_zero bw (CONS slot slots) m <=>
     zinit_zero bw [slot] m /\ zinit_zero bw slots m`,
  REWRITE_TAC[zinit_zero;MEM] THEN MESON_TAC[]);;

let ZINIT_ENTRY_SEP = prove
 (`!t. tisa_entry_ok zero_words t ==> tisa_frame_sep [(2,0,8)] t`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tisa_decls zero_words`;`tisa_inits zero_words`;
                `tisa_root zero_words`;`t:tisa_state`] TISA_ENTRY_FRAME_SEP) THEN
  REWRITE_TAC[GSYM TISA_PROG_CASES] THEN
  ASM_REWRITE_TAC[ZERO_WORDS_DECLS;LENGTH;ARITH_RULE `1 <= 9`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let ZINIT_RUN_REGIONS = prove
 (`!t k u. tisa_entry_ok zero_words t /\ tisa_run zero_words t = TStop k u
       ==> tisa_base u 0 = tisa_base t 0 /\ tisa_len u 0 = tisa_len t 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`[(2,0,8)]`;`t:tisa_state`;`u:tisa_state`;`0`] TISA_KEEPS_REGIONS) THEN
  ASM_SIMP_TAC[ZINIT_ENTRY_SEP] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC ZERO_WORDS_FRAME THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[tisa_readable;LENGTH;EL;HD;FST] THEN CONV_TAC NUM_REDUCE_CONV];
    REWRITE_TAC[]]);;

let ZINIT_CALL = prove
 (`!bw ctl budget cfr slot m used t k u.
     slot < 2 EXP 64 /\ drv_child bw ctl budget cfr (zinit_step slot) m used t /\
     tisa_entry_ok zero_words t /\ tisa_run zero_words t = TStop k u
     ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = used /\
         (if zinit_supported bw slot
          then k = 1 /\
               (!i. 8 * i + 8 <= val(bw(slot + 1))
                    ==> drv_word (tmem u) (word_add (bw slot) (word(8 * i))) = word 0)
          else k = 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`slot:num`;
                `m:int64->byte`;`used:int64`;`t:tisa_state`] ZINIT_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] ZINIT_RUN_REGIONS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] ZERO_WORDS_RUN) THEN
  ASM_REWRITE_TAC[zero_words_post;zero_words_supported;zero_words_count;GSYM zinit_supported] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[drv_word;GSYM tisa_read] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SIMP_TAC[LDIV_LT_EQ;ARITH_EQ] THEN ASM_ARITH_TAC);;

let zinit_range_ok = new_definition
 `zinit_range_ok (bw:num->int64) ctl cfr slot <=>
    slot < 2 EXP 64 /\ val(bw slot) + val(bw(slot + 1)) < 2 EXP 64 /\
    drv_apart (bw slot) (val(bw(slot + 1))) (word_sub cfr (word 48)) 304 /\
    drv_apart (bw slot) (val(bw(slot + 1))) ctl 8`;;

let ZINIT_AFTER_WORD = prove
 (`!ctl slot u a. val(ctl:int64) + 8 <= 2 EXP 64 /\ val(a:int64) + 8 <= 2 EXP 64 /\
                  drv_apart a 8 ctl 8
       ==> drv_word (drv_after ctl (zinit_step slot) u) a = drv_word (tmem u) a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[drv_after;zinit_step] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[VAL_WORD_0;MULT_CLAUSES;WORD_ADD_0;drv_word;TISA_WRITE_BYTES64] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC TISA_READ_DISJOINT_WRITE THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[drv_apart]) THEN ARITH_TAC);;

let ZINIT_AFTER_ZERO = prove
 (`!bw ctl budget cfr slot m used t k u.
     zinit_range_ok bw ctl cfr slot /\ val ctl + 8 <= 2 EXP 64 /\
     zinit_supported bw slot /\ drv_child bw ctl budget cfr (zinit_step slot) m used t /\
     tisa_entry_ok zero_words t /\ tisa_run zero_words t = TStop k u
     ==> zinit_zero bw [slot] (drv_after ctl (zinit_step slot) u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[zinit_range_ok] o
    check (fun th -> tisa_has_tm `zinit_range_ok` th)) THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`slot:num`;
                `m:int64->byte`;`used:int64`;`t:tisa_state`;`k:num`;`u:tisa_state`] ZINIT_CALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[zinit_zero;MEM] THEN MAP_EVERY X_GEN_TAC [`j:num`;`i:num`] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT2 th) THEN SUBST_ALL_TAC(CONJUNCT1 th)) THEN
  SUBGOAL_THEN `val(word_add ((bw:num->int64) slot) (word(8 * i)):int64) = val(bw slot) + 8 * i`
    ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `drv_word (tmem u) (word_add ((bw:num->int64) slot) (word(8 * i)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ZINIT_AFTER_WORD THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[drv_apart]) THEN REWRITE_TAC[drv_apart] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[]]);;

let ZINIT_RANGE_BYTE = prove
 (`!bw ctl cfr slot i byte.
     zinit_range_ok bw ctl cfr slot /\ 48 <= val cfr /\
     8 * i + 8 <= val(bw(slot + 1)) /\ byte < 8
     ==> drv_in (word_add (word_add (bw slot) (word(8 * i))) (word byte))
                (bw slot) (val(bw(slot + 1))) /\
         ~drv_stack cfr (word_add (word_add (bw slot) (word(8 * i))) (word byte)) /\
         ~drv_in (word_add (word_add (bw slot) (word(8 * i))) (word byte)) ctl 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[zinit_range_ok] o
    check (fun th -> tisa_has_tm `zinit_range_ok` th)) THEN
  SUBGOAL_THEN
   `val(word_add (word_add ((bw:num->int64) slot) (word(8 * i))) (word byte):int64) =
      val(bw slot) + 8 * i + byte` ASSUME_TAC THENL
   [REWRITE_TAC[DRV_ADDR_ASSOC] THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cfr:int64`;`48`] TISA_VAL_SP_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[drv_apart]) THEN
  ASM_REWRITE_TAC[drv_in;drv_stack] THEN ASM_ARITH_TAC);;

let ZINIT_STEP_ZERO = prove
 (`!slot. EL 0 (zinit_step slot) = word 0 /\ EL 17 (zinit_step slot) = word 0`,
  GEN_TAC THEN REWRITE_TAC[zinit_step] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

let ZINIT_SEM_FRAME = prove
 (`!bw ctl budget cfr slots i m used res.
     drv_sem (\j. zero_words) bw ctl budget cfr (zinit_plan slots) i m used res /\
     val ctl + 8 <= 2 EXP 64 /\ (!slot. MEM slot slots ==> slot < 2 EXP 64)
     ==> !a. ~drv_stack cfr a /\
             (!slot. MEM slot slots ==> ~drv_in a (bw slot) (val(bw(slot + 1)))) /\
             ~drv_in a ctl 8
             ==> FST(SND(SND res)) a = m a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\j:num. zero_words`;`bw:num->int64`;`ctl:int64`;`1`;`budget:int64`;
                `cfr:int64`;`zinit_plan slots`;`i:num`;`m:int64->byte`;`used:int64`;
                `res:int64#num#(int64->byte)#int64`] DRV_SEM_KEEPS) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN ANTS_TAC THENL
   [X_GEN_TAC `st:int64 list` THEN REWRITE_TAC[zinit_plan;MEM_MAP] THEN
    DISCH_THEN(X_CHOOSE_THEN `slot:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    REWRITE_TAC[ZERO_WORDS_LEAF_WF;ZINIT_STEP_ZERO;VAL_WORD_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`st:int64 list`;`r:num`] THEN REWRITE_TAC[ZINIT_RW] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `slot:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) o
      REWRITE_RULE[zinit_plan;MEM_MAP] o
      check (fun th -> zinit_app "MEM" (concl th))) THEN
    SUBGOAL_THEN `slot < 2 EXP 64` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[ZINIT_BINDINGS];
    X_GEN_TAC `st:int64 list` THEN REWRITE_TAC[zinit_plan;MEM_MAP] THEN
    DISCH_THEN(X_CHOOSE_THEN `slot:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[ZINIT_STEP_ZERO;VAL_WORD_0;MULT_CLAUSES;WORD_ADD_0]]);;

let ZINIT_KEEP_RANGE = prove
 (`!bw ctl budget cfr slots i m used res saved.
     drv_sem (\j. zero_words) bw ctl budget cfr (zinit_plan slots) i m used res /\
     val ctl + 8 <= 2 EXP 64 /\ 48 <= val cfr /\ zinit_range_ok bw ctl cfr saved /\
     (!slot. MEM slot slots ==> slot < 2 EXP 64) /\
     (!slot. MEM slot slots ==> drv_apart (bw saved) (val(bw(saved + 1)))
                                        (bw slot) (val(bw(slot + 1))))
     ==> !ix. 8 * ix + 8 <= val(bw(saved + 1))
                 ==> drv_word (FST(SND(SND res))) (word_add (bw saved) (word(8 * ix))) =
                     drv_word m (word_add (bw saved) (word(8 * ix)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `ix:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `byte:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`cfr:int64`;`saved:num`;`ix:num`;`byte:num`]
               ZINIT_RANGE_BYTE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`slots:num list`;
               `i:num`;`m:int64->byte`;`used:int64`;`res:int64#num#(int64->byte)#int64`]
               ZINIT_SEM_FRAME) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `slot:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `slot:num` o check (fun th -> is_forall(concl th) &&
    tisa_has_tm `drv_apart` th)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[drv_in] o check (fun th -> zinit_app "drv_in" (concl th))) THEN
  REWRITE_TAC[drv_apart;drv_in] THEN ARITH_TAC);;

let zinit_post = new_definition
 `zinit_post (bw:num->int64) slots i (used:int64) (res:int64#num#(int64->byte)#int64) <=>
    ?done rest. slots = APPEND done rest /\ ALL (zinit_supported bw) done /\
                FST(SND res) = i + LENGTH done /\ SND(SND(SND res)) = used /\
                zinit_zero bw done (FST(SND(SND res))) /\
                (if rest = [] then FST res = word 1
                 else FST res = word 2 /\ ~zinit_supported bw (HD rest))`;;

let ZINIT_NE12 = prove
 (`~(word 1:int64 = word 2) /\ ~(word 2:int64 = word 1)`,
  CONV_TAC WORD_REDUCE_CONV);;

let ZINIT_RANGE_BOUND = prove
 (`!bw ctl cfr slots.
     (!slot. MEM slot slots ==> zinit_range_ok bw ctl cfr slot)
     ==> !slot. MEM slot slots ==> slot < 2 EXP 64`,
  REWRITE_TAC[zinit_range_ok] THEN MESON_TAC[]);;

let ZINIT_RUN = prove
 (`!bw ctl budget cfr slots i m used res.
     drv_sem (\j. zero_words) bw ctl budget cfr (zinit_plan slots) i m used res /\
     ~(val budget < val used) /\ val ctl + 8 <= 2 EXP 64 /\ 48 <= val cfr /\
     (!slot. MEM slot slots ==> zinit_range_ok bw ctl cfr slot) /\
     PAIRWISE (\a b. drv_apart (bw a) (val(bw(a + 1))) (bw b) (val(bw(b + 1)))) slots
     ==> zinit_post bw slots i used res`,
  REPLICATE_TAC 4 GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[zinit_plan;MAP;drv_sem] o
      check (fun th -> zinit_app "drv_sem" (concl th))) THEN
    REWRITE_TAC[zinit_post] THEN EXISTS_TAC `[]:num list` THEN EXISTS_TAC `[]:num list` THEN
    REWRITE_TAC[APPEND;ALL;LENGTH;FST;SND;ADD_CLAUSES;ZINIT_ZERO_NIL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `zinit_range_ok bw ctl cfr h` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `!slot. MEM slot t ==> zinit_range_ok bw ctl cfr slot` ASSUME_TAC THENL
   [X_GEN_TAC `slot:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[zinit_range_ok] o
    check (fun th -> concl th = `zinit_range_ok bw ctl cfr h`)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[PAIRWISE;GSYM ALL_MEM] o
    check (fun th -> zinit_app "PAIRWISE" (concl th))) THEN
  SUBGOAL_THEN `!slot. MEM slot t ==> slot < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC ZINIT_RANGE_BOUND THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`;`ctl:int64`;`cfr:int64`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[zinit_plan;MAP;drv_sem] o
    check (fun th -> zinit_app "drv_sem" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tc:tisa_state` (X_CHOOSE_THEN `k:num`
    (X_CHOOSE_THEN `u:tisa_state` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`h:num`;
                `m:int64->byte`;`used:int64`;`tc:tisa_state`;`k:num`;`u:tisa_state`] ZINIT_CALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `zinit_supported bw h` THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `zinit_supported bw h`] o
      check (fun th -> is_cond(concl th) && tisa_has_tm `zinit_supported` th)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th) && tisa_has_tm `drv_sem` th)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o REWRITE_RULE[GSYM zinit_plan]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`;`drv_after ctl (zinit_step h) u`;`used:int64`;
                                 `res:int64#num#(int64->byte)#int64`] o
      check (fun th -> is_forall(concl th) && tisa_has_tm `zinit_post` th)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[zinit_post]) THEN
    DISCH_THEN(X_CHOOSE_THEN `done:num list` (X_CHOOSE_THEN `rest:num list` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `zinit_zero bw [h] (drv_after ctl (zinit_step h) u)` ASSUME_TAC THENL
     [MATCH_MP_TAC ZINIT_AFTER_ZERO THEN
      MAP_EVERY EXISTS_TAC [`budget:int64`;`cfr:int64`;`m:int64->byte`;`used:int64`;
                            `tc:tisa_state`;`k:num`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`t:num list`;
                  `i + 1`;`drv_after ctl (zinit_step h) u`;`used:int64`;
                  `res:int64#num#(int64->byte)#int64`;`h:num`] ZINIT_KEEP_RANGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `zinit_zero bw [h] (FST(SND(SND(res:int64#num#(int64->byte)#int64))))`
      ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[zinit_zero;MEM]) THEN
      REWRITE_TAC[zinit_zero;MEM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[zinit_post] THEN
    EXISTS_TAC `CONS (h:num) done` THEN EXISTS_TAC `rest:num list` THEN
    ASM_REWRITE_TAC[APPEND;ALL;LENGTH;ZINIT_ZERO_CONS] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[ASSUME `~zinit_supported bw h`] o
      check (fun th -> is_cond(concl th) && tisa_has_tm `zinit_supported` th)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th) && tisa_has_tm `drv_sem` th)) THEN
    ASM_REWRITE_TAC[ZINIT_NE12] THEN DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[zinit_post] THEN EXISTS_TAC `[]:num list` THEN EXISTS_TAC `CONS (h:num) t` THEN
    ASM_REWRITE_TAC[APPEND;ALL;LENGTH;FST;SND;ADD_CLAUSES;ZINIT_ZERO_NIL;NOT_CONS_NIL;HD]]);;

let ZINIT_POST_EXACT = prove
 (`!bw slots i used res. zinit_post bw slots i used res
     ==> (FST res = word 1 <=> ALL (zinit_supported bw) slots) /\
         (FST res = word 1 \/ FST res = word 2) /\ SND(SND(SND res)) = used /\
         (FST res = word 1 ==> FST(SND res) = i + LENGTH slots /\
                               zinit_zero bw slots (FST(SND(SND res))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zinit_post] THEN
  DISCH_THEN(X_CHOOSE_THEN `done:num list` (X_CHOOSE_THEN `rest:num list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `slots:num list`)) THEN
  MP_TAC(ISPEC `rest:num list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `h:num` (X_CHOOSE_THEN `t:num list` SUBST_ALL_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  ASM_REWRITE_TAC[ALL_APPEND;ALL;APPEND_NIL;HD;NOT_CONS_NIL;ZINIT_NE12] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ALL_APPEND;ALL;APPEND_NIL;ZINIT_NE12]);;

let ZINIT_FINAL_BYTE = prove
 (`!d plan res a. val(d:int64) + 64 <= 2 EXP 64 /\ ~drv_in a d 64
     ==> drv_final d plan res a = FST(SND(SND res)) a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add d (word 48):int64) = val d + 48 /\
                val(word_add d (word 56):int64) = val d + 56` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word_add d (word 48):int64) + 8 <= 2 EXP 64 /\
    ~(val(word_add d (word 48):int64) <= val(a:int64) /\ val a < val(word_add d (word 48):int64) + 8) /\
    val(word_add d (word 56):int64) + 8 <= 2 EXP 64 /\
    ~(val(word_add d (word 56):int64) <= val(a:int64) /\ val a < val(word_add d (word 56):int64) + 8)`
    STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[drv_in]) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[drv_final;DRV_WRITE64_OUTSIDE]]);;

let ZINIT_FINAL_FIELDS = prove
 (`!d plan res. val(d:int64) + 64 <= 2 EXP 64
     ==> drv_word (drv_final d plan res) (word_add d (word 48)) = SND(SND(SND res)) /\
         drv_word (drv_final d plan res) (word_add d (word 56)) =
           word_add plan (word(144 * FST(SND res)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[drv_final;DRV_WORD_WRITE_SAME] THEN
  SUBGOAL_THEN `val(word_add d (word 48):int64) = val d + 48 /\
                val(word_add d (word 56):int64) = val d + 56` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `drv_word (write (bytes64 (word_add d (word 48)))
             (SND(SND(SND(res:int64#num#(int64->byte)#int64)))) (FST(SND(SND res))))
             (word_add d (word 48))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[drv_word;TISA_WRITE_BYTES64] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC TISA_READ_DISJOINT_WRITE THEN ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_ARITH_TAC;
    REWRITE_TAC[DRV_WORD_WRITE_SAME]]);;

let ZINIT_ACTUAL_ZERO = prove
 (`!bw ctl cfr d plan done res m.
     val(d:int64) + 64 <= 2 EXP 64 /\ 48 <= val cfr /\
     zinit_zero bw done (FST(SND(SND res))) /\
     (!slot. MEM slot done ==> zinit_range_ok bw ctl cfr slot /\
                drv_apart (bw slot) (val(bw(slot + 1))) d 64) /\
     (!a. ~drv_stack cfr a ==> m a = drv_final d plan res a)
     ==> zinit_zero bw done m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[zinit_zero] THEN
  MAP_EVERY X_GEN_TAC [`slot:num`;`i:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `zinit_range_ok bw ctl cfr slot /\ drv_apart (bw slot) (val(bw(slot + 1))) d 64`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `drv_word (FST(SND(SND(res:int64#num#(int64->byte)#int64))))
             (word_add ((bw:num->int64) slot) (word(8 * i)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `byte:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`cfr:int64`;`slot:num`;`i:num`;`byte:num`]
                 ZINIT_RANGE_BYTE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `~drv_in (word_add (word_add ((bw:num->int64) slot) (word(8 * i))) (word byte)) d 64`
      ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[drv_apart;drv_in]) THEN REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[ZINIT_FINAL_BYTE]];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[zinit_zero] o
      check (fun th -> zinit_app "zinit_zero" (concl th))) THEN ASM_SIMP_TAC[]]);;

let ZINIT_DESCRIPTOR_AGREE = prove
 (`!d plan res cfr m off.
     val(d:int64) + 64 <= 2 EXP 64 /\ 48 <= val cfr /\
     drv_apart (word_sub cfr (word 48)) 304 d 64 /\ off + 8 <= 64 /\
     (!a. ~drv_stack cfr a ==> m a = drv_final d plan res a)
     ==> drv_word m (word_add d (word off)) = drv_word (drv_final d plan res) (word_add d (word off))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add d (word off):int64) = val d + off` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `byte:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC DRV_IN_NOT_STACK THEN
  MAP_EVERY EXISTS_TAC [`d:int64`;`64`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`word_add d (word off):int64`;`d:int64`;`64`;`off:num`] DRV_BYTES_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let zinit_abi_post = new_definition
 `zinit_abi_post (bw:num->int64) slots d plan used (status:int64) m <=>
    ?done rest. slots = APPEND done rest /\ ALL (zinit_supported bw) done /\
                drv_word m (word_add d (word 56)) = word_add plan (word(144 * LENGTH done)) /\
                drv_word m (word_add d (word 48)) = used /\ zinit_zero bw done m /\
                (if rest = [] then status = word 1
                 else status = word 2 /\ ~zinit_supported bw (HD rest))`;;

let ZINIT_ABI_FROM_POST = prove
 (`!bw ctl cfr d plan slots used res m.
     zinit_post bw slots 0 used res /\ val(d:int64) + 64 <= 2 EXP 64 /\ 48 <= val cfr /\
     drv_apart (word_sub cfr (word 48)) 304 d 64 /\
     (!slot. MEM slot slots ==> zinit_range_ok bw ctl cfr slot /\
                drv_apart (bw slot) (val(bw(slot + 1))) d 64) /\
     (!a. ~drv_stack cfr a ==> m a = drv_final d plan res a)
     ==> zinit_abi_post bw slots d plan used (FST res) m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `done:num list` (X_CHOOSE_THEN `rest:num list` STRIP_ASSUME_TAC) o
    REWRITE_RULE[zinit_post] o check (fun th -> zinit_app "zinit_post" (concl th))) THEN
  SUBGOAL_THEN `zinit_zero bw done m` ASSUME_TAC THENL
   [MATCH_MP_TAC ZINIT_ACTUAL_ZERO THEN
    MAP_EVERY EXISTS_TAC [`ctl:int64`;`cfr:int64`;`d:int64`;`plan:int64`;
                          `res:int64#num#(int64->byte)#int64`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `slot:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[MEM_APPEND];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:int64`;`plan:int64`;`res:int64#num#(int64->byte)#int64`] ZINIT_FINAL_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `drv_word m (word_add d (word 48)) = drv_word (drv_final d plan res) (word_add d (word 48)) /\
    drv_word m (word_add d (word 56)) = drv_word (drv_final d plan res) (word_add d (word 56))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ZINIT_DESCRIPTOR_AGREE THEN EXISTS_TAC `cfr:int64` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[zinit_abi_post] THEN EXISTS_TAC `done:num list` THEN EXISTS_TAC `rest:num list` THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;

let ZINIT_ABI_EXACT = prove
 (`!bw slots d plan used status m.
     zinit_abi_post bw slots d plan used status m
     ==> drv_word m (word_add d (word 48)) = used /\
         (status = word 1 <=> ALL (zinit_supported bw) slots) /\
         (status = word 1 \/ status = word 2) /\
         (status = word 1 ==> zinit_zero bw slots m /\
             drv_word m (word_add d (word 56)) = word_add plan (word(144 * LENGTH slots)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zinit_abi_post] THEN
  DISCH_THEN(X_CHOOSE_THEN `done:num list` (X_CHOOSE_THEN `rest:num list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `slots:num list`)) THEN
  MP_TAC(ISPEC `rest:num list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `h:num` (X_CHOOSE_THEN `t:num list` SUBST_ALL_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  ASM_REWRITE_TAC[ALL_APPEND;ALL;APPEND_NIL;HD;NOT_CONS_NIL;ZINIT_NE12] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ALL_APPEND;ALL;APPEND_NIL;ZINIT_NE12]);;

let ZINIT_SIZE_CONTROLS = prove
 (`zinit_supported (\j. word 16) 0 /\
   ~zinit_supported (\j. word 17) 0 /\
   ~zinit_supported (\j. word 34359738368) 0`,
  REWRITE_TAC[zinit_supported;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let zero_init_theorems =
 ["ZINIT_STEP_FIELDS",ZINIT_STEP_FIELDS;"ZINIT_BINDINGS",ZINIT_BINDINGS;
  "ZINIT_CHILD",ZINIT_CHILD;"ZINIT_RW",ZINIT_RW;"ZINIT_ZERO_NIL",ZINIT_ZERO_NIL;
  "ZINIT_ZERO_CONS",ZINIT_ZERO_CONS;"ZINIT_ENTRY_SEP",ZINIT_ENTRY_SEP;
  "ZINIT_RUN_REGIONS",ZINIT_RUN_REGIONS;"ZINIT_CALL",ZINIT_CALL;
  "ZINIT_AFTER_WORD",ZINIT_AFTER_WORD;"ZINIT_AFTER_ZERO",ZINIT_AFTER_ZERO;
  "ZINIT_RANGE_BYTE",ZINIT_RANGE_BYTE;"ZINIT_STEP_ZERO",ZINIT_STEP_ZERO;
  "ZINIT_SEM_FRAME",ZINIT_SEM_FRAME;"ZINIT_KEEP_RANGE",ZINIT_KEEP_RANGE;
  "ZINIT_NE12",ZINIT_NE12;"ZINIT_RANGE_BOUND",ZINIT_RANGE_BOUND;
  "ZINIT_RUN",ZINIT_RUN;"ZINIT_POST_EXACT",ZINIT_POST_EXACT;
  "ZINIT_FINAL_BYTE",ZINIT_FINAL_BYTE;"ZINIT_FINAL_FIELDS",ZINIT_FINAL_FIELDS;
  "ZINIT_ACTUAL_ZERO",ZINIT_ACTUAL_ZERO;"ZINIT_DESCRIPTOR_AGREE",ZINIT_DESCRIPTOR_AGREE;
  "ZINIT_ABI_FROM_POST",ZINIT_ABI_FROM_POST;"ZINIT_ABI_EXACT",ZINIT_ABI_EXACT;
  "ZINIT_SIZE_CONTROLS",ZINIT_SIZE_CONTROLS];;
