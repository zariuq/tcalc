(* The native seed preserves tables and constants outside its control array. *)
needs "native/hol/control_init_admitted_join.ml";;

let DRV_CONTROL_WORD_SUBSET = prove
 (`!ctl nctl j a.
     val(ctl:int64) + 8 * nctl < 2 EXP 64 /\ j < nctl /\
     drv_in a (word_add ctl (word(8 * j))) 8
     ==> drv_in a ctl (8 * nctl)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add ctl (word(8 * j)):int64) = val ctl + 8 * j`
   ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [drv_in] o
    check (fun th -> fst(strip_comb(concl th)) = `drv_in`)) THEN
  ASM_REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC);;

let CINIT_SEM_FRAME = prove
 (`!bw ctl nctl budget cfr slot i m0 used res.
     drv_sem (\j. control_init) bw ctl budget cfr [cinit_step slot] i m0 used res /\
     slot < 2 EXP 64 /\ bw slot = ctl /\ val(bw(slot + 1)) = 8 * nctl /\
     24 < nctl /\ val(ctl:int64) + 8 * nctl < 2 EXP 64
     ==> !a. ~drv_stack cfr a /\ ~drv_in a ctl (8 * nctl)
             ==> FST(SND(SND res)) a = m0 a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\j:num. control_init`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;
                `cfr:int64`;`[cinit_step slot]`;`i:num`;`m0:int64->byte`;`used:int64`;
                `res:int64#num#(int64->byte)#int64`] DRV_SEM_KEEPS) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_ARITH_TAC;
      X_GEN_TAC `st:int64 list` THEN REWRITE_TAC[MEM] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[CONTROL_INIT_LEAF_WF;CINIT_STEP_FIELDS]];
    ALL_TAC] THEN DISCH_TAC THEN
  X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `drv_stack`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`st:int64 list`;`r:num`] THEN
    REWRITE_TAC[MEM;CINIT_WRITABLE] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CINIT_BINDINGS];
    X_GEN_TAC `st:int64 list` THEN REWRITE_TAC[MEM] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPEC `slot:num` CINIT_STEP_FIELDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[ASSUME `val(EL 17 (cinit_step slot)) = 24`]) THEN
    MP_TAC(SPECL [`ctl:int64`;`nctl:num`;`24`;`a:int64`] DRV_CONTROL_WORD_SUBSET) THEN
    ASM_REWRITE_TAC[]]);;

let CINIT_ACTUAL_FRAME = prove
 (`!bw ctl nctl budget cfr slot i m0 used res d plan m.
     drv_sem (\j. control_init) bw ctl budget cfr [cinit_step slot] i m0 used res /\
     slot < 2 EXP 64 /\ bw slot = ctl /\ val(bw(slot + 1)) = 8 * nctl /\
     24 < nctl /\ val(ctl:int64) + 8 * nctl < 2 EXP 64 /\
     val(d:int64) + 64 <= 2 EXP 64 /\
     (!a. ~drv_stack cfr a ==> m a = drv_final d plan res a)
     ==> !a. ~drv_stack cfr a /\ ~drv_in a d 64 /\ ~drv_in a ctl (8 * nctl)
             ==> m a = m0 a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;
                `slot:num`;`i:num`;`m0:int64->byte`;`used:int64`;
                `res:int64#num#(int64->byte)#int64`] CINIT_SEM_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ZINIT_FINAL_BYTE]);;

let cinit_preserve_basis = SPEC_ALL CINIT_ADMITTED_X86;;
let cinit_preserve_goal =
  let ant,ens = dest_imp(concl cinit_preserve_basis) in
  let h,args = strip_comb ens in
  let state = `s:x86state` in
  let post = mk_abs(state,mk_conj(mk_comb(el 2 args,state),
    `!a. ~drv_stack (word_sub stackpointer (word 248)) a /\
         ~drv_in a d 64 /\ ~drv_in a ctl (8 * nctl)
         ==> read memory (s:x86state) a = m0 a`)) in
  mk_imp(ant,list_mk_comb(h,[el 0 args;el 1 args;post;el 3 args]));;

let CINIT_X86_PRESERVES = GEN_ALL(prove(cinit_preserve_goal,
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[drv_layout] o
    check (fun th -> fst(strip_comb(concl th)) = `drv_layout`)) THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (el 2 (snd(strip_comb(rand(concl cinit_preserve_basis))))) THEN CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> tisa_has_tm `drv_sem` th)) THEN
    MATCH_MP_TAC CINIT_ACTUAL_FRAME THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`;`budget:int64`;`slot:num`;`0`;`used0:int64`;
                          `res:int64#num#(int64->byte)#int64`;`plan:int64`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC cinit_preserve_basis THEN ASM_REWRITE_TAC[]]));;

let control_init_preserve_theorems =
 ["DRV_CONTROL_WORD_SUBSET",DRV_CONTROL_WORD_SUBSET;"CINIT_SEM_FRAME",CINIT_SEM_FRAME;
  "CINIT_ACTUAL_FRAME",CINIT_ACTUAL_FRAME;"CINIT_X86_PRESERVES",CINIT_X86_PRESERVES];;
leaf_audit control_init_preserve_theorems control_init_preserve_theorems;;
