(* The initializer's plan admission follows from concrete layout conditions. *)
needs "native/hol/control_init_driver_join.ml";;
needs "native/hol/driver_control_layout.ml";;

let CINIT_READABLE = prove
 (`!r. tisa_readable (tisa_decls control_init) r <=> r = 0`,
  GEN_TAC THEN REWRITE_TAC[CONTROL_INIT_DECLS;tisa_readable;LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[EL;HD;FST] THEN ASM_ARITH_TAC);;

let CINIT_WRITABLE = prove
 (`!r. tisa_rw (tisa_decls control_init) r <=> r = 0`,
  GEN_TAC THEN REWRITE_TAC[CONTROL_INIT_DECLS;tisa_rw;LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[EL;HD;FST] THEN ASM_ARITH_TAC);;

let CINIT_BINDING_INDICES = prove
 (`!slot. !r. r < 9 ==> EL (1 + r) (cinit_step slot) = word slot`,
  GEN_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[cinit_step] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

let CINIT_CONTROL_INDICES = prove
 (`!slot nctl. 24 < nctl
     ==> !f. 10 <= f /\ f < 18 ==> val(EL f (cinit_step slot)) < nctl`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[TAUT `(a /\ b ==> c) <=> (b ==> a ==> c)`] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[cinit_step] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN ASM_ARITH_TAC);;

let CINIT_STEP_OK = prove
 (`!pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc bw slot.
     drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     0 < nl /\ slot < 2 EXP 64 /\ slot + 1 < nbw /\
     bw slot = ctl /\ val(bw(slot + 1)) = 8 * nctl /\ 24 < nctl /\
     ~(val(ctl:int64) = 0) /\ val ctl MOD 8 = 0 /\ val ctl + 8 * nctl < 2 EXP 64
     ==> drv_step_ok (\j. control_init) pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw
                     (cinit_step slot)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[drv_layout] o
    check (fun th -> fst(strip_comb(concl th)) = `drv_layout`)) THEN
  SUBGOAL_THEN `drv_apart ctl (8 * nctl) (word_sub cfr (word 48)) 304`
    ASSUME_TAC THENL [ASM_MESON_TAC[DRV_APART_SYM];ALL_TAC] THEN
  ASM_SIMP_TAC[drv_step_ok;CINIT_STEP_FIELDS;CINIT_BINDING_INDICES;
    VAL_WORD;DIMINDEX_64;MOD_LT;CINIT_CONTROL_INDICES;CINIT_READABLE;CINIT_WRITABLE;
    FORALL_UNWIND_THM2;CINIT_BINDINGS] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:tisa_state` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_base`)) (concl th))) THEN
    ASM_SIMP_TAC[CINIT_BINDINGS;ARITH_RULE `0 < 9`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CONTROL_INIT_DECLS;tisa_decls_ok;tisa_pairs_ok;tisa_region_ok;tisa_frame] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(SPECL [`cfr:int64`;`48`] TISA_VAL_SP_SUB) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [drv_apart] o
      check (fun th -> concl th = `drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl)`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`r:num`;`a:int64`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CINIT_BINDINGS] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`pc:num`;`cfr:int64`;`d:int64`;`plan:int64`;`ns:num`;`ctl:int64`;
                  `nctl:num`;`bind:int64`;`nbw:num`;`leaves:int64`;`nl:num`;
                  `lpc:num->num`;`lmc:num->byte list`;`a:int64`] DRV_CONTROL_NOT_STATIC) THEN
    ASM_REWRITE_TAC[]]);;

let control_init_admission_theorems =
 ["CINIT_READABLE",CINIT_READABLE;"CINIT_WRITABLE",CINIT_WRITABLE;
  "CINIT_BINDING_INDICES",CINIT_BINDING_INDICES;"CINIT_CONTROL_INDICES",CINIT_CONTROL_INDICES;
  "CINIT_STEP_OK",CINIT_STEP_OK];;
