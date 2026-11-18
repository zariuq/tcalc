(* The exact initializer image called through the proved plan driver. *)
needs "native/hol/control_init_driver_basis_load.ml";;
needs "native/hol/control_init_abi.ml";;

let cinit_driver_correct =
  REWRITE_RULE[CONTROL_INIT_LEAF_WF;CONTROL_INIT_LEAF_SPEC;
               ARITH_RULE `j < 1 <=> j = 0`;FORALL_UNWIND_THM2;MULT_CLAUSES]
   (ISPECL [`\j:num. control_init`;`\j:num. cpc:num`;`\j:num. control_init_mc`;`1`;
            `pc:num`;`stackpointer:int64`;`d:int64`;`plan:int64`;`1`;
            `ctl:int64`;`nctl:num`;`bind:int64`;`nbw:num`;`leaves:int64`;`bw:num->int64`;
            `[cinit_step slot]`;`budget:int64`;`used0:int64`;`m0:int64->byte`;`ret:int64`;
            `rbxv:int64`;`rbpv:int64`;`r12v:int64`;`r13v:int64`;`r14v:int64`;`r15v:int64`]
           DRV_CORRECT);;

let cinit_x86_goal =
  let ant,ens = dest_imp(concl cinit_driver_correct) in
  let h,args = strip_comb ens in
  let state = `s:x86state` in
  let extra =
   `slot < 2 EXP 64 /\ (bw:num->int64) slot = ctl /\ val(bw(slot + 1)) = 8 * nctl /\
    val(ctl:int64) + 8 * nctl < 2 EXP 64 /\ 24 < nctl /\
    drv_apart ctl (8 * nctl) d 64` in
  let post = mk_abs(state,mk_conj(mk_comb(el 2 args,state),
    `if val(budget:int64) < val(used0:int64)
     then cinit_invalid_post ctl nctl d plan used0 m0 (read RAX (s:x86state)) (read memory s)
     else cinit_abi_post ctl nctl d plan used0 m0 (read RAX (s:x86state)) (read memory s)`)) in
  mk_imp(mk_conj(ant,extra),list_mk_comb(h,[el 0 args;el 1 args;post;el 3 args]));;

let CINIT_X86 = GEN_ALL(prove(cinit_x86_goal,
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[drv_layout;MULT_CLAUSES] o
    check (fun th -> fst(strip_comb(concl th)) = `drv_layout`)) THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (el 2 (snd(strip_comb(rand(concl cinit_driver_correct))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> tisa_has_tm `drv_sem` th)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CINIT_ABI_FROM_RUN THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`;`word_sub stackpointer (word 248):int64`;
                          `slot:num`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC cinit_driver_correct THEN ASM_REWRITE_TAC[]]));;

let control_init_driver_join_theorems =
  control_init_frame_theorems @ control_init_driver_theorems @ control_init_abi_theorems @
  ["CINIT_X86",CINIT_X86];;

leaf_audit control_init_driver_join_theorems
 ["CONTROL_INIT_FRAME_RESULT",CONTROL_INIT_FRAME_RESULT;"CINIT_RUN_ALL",CINIT_RUN_ALL;
  "CINIT_ABI_EXACT",CINIT_ABI_EXACT;"CINIT_ABI_FROM_RUN",CINIT_ABI_FROM_RUN;"CINIT_X86",CINIT_X86];;
