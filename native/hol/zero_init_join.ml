(* Native initialization through the unchanged plan driver and zero leaf. *)
needs "native/hol/zero_init.ml";;
needs "native/leaves/zero_words/zero_words_join.ml";;

let zinit_driver_correct =
  REWRITE_RULE[ZERO_WORDS_LEAF_WF;ZERO_WORDS_LEAF_SPEC;
               ARITH_RULE `j < 1 <=> j = 0`;FORALL_UNWIND_THM2;MULT_CLAUSES]
   (ISPECL [`\j:num. zero_words`;`\j:num. zpc:num`;`\j:num. zero_words_mc`;`1`;
            `pc:num`;`stackpointer:int64`;`d:int64`;`plan:int64`;`LENGTH(slots:num list)`;
            `ctl:int64`;`1`;`bind:int64`;`nbw:num`;`leaves:int64`;`bw:num->int64`;
            `zinit_plan slots`;`budget:int64`;`used0:int64`;`m0:int64->byte`;`ret:int64`;
            `rbxv:int64`;`rbpv:int64`;`r12v:int64`;`r13v:int64`;`r14v:int64`;`r15v:int64`]
           DRV_CORRECT);;

let zinit_x86_goal =
  let ant,ens = dest_imp(concl zinit_driver_correct) in
  let h,args = strip_comb ens in
  let state = `s:x86state` in
  let extra =
   `val(used0:int64) <= val(budget:int64) /\
    (!slot. MEM slot (slots:num list)
       ==> zinit_range_ok bw ctl (word_sub stackpointer (word 248)) slot /\
           drv_apart (bw slot) (val(bw(slot + 1))) d 64) /\
    PAIRWISE (\a b. drv_apart (bw a) (val(bw(a + 1))) (bw b) (val(bw(b + 1)))) slots` in
  let post = mk_abs(state,mk_conj(mk_comb(el 2 args,state),
    `zinit_abi_post bw slots d plan used0 (read RAX (s:x86state)) (read memory s)`)) in
  mk_imp(mk_conj(ant,extra),list_mk_comb(h,[el 0 args;el 1 args;post;el 3 args]));;

let ZINIT_X86 = GEN_ALL(prove(zinit_x86_goal,
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[drv_layout;MULT_CLAUSES] o
    check (fun th -> zinit_app "drv_layout" (concl th))) THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (el 2 (snd(strip_comb(rand(concl zinit_driver_correct))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> tisa_has_tm `drv_sem` th)) THEN
    SUBGOAL_THEN `zinit_post bw slots 0 used0 (res:int64#num#(int64->byte)#int64)` ASSUME_TAC THENL
     [MATCH_MP_TAC ZINIT_RUN THEN
      MAP_EVERY EXISTS_TAC [`ctl:int64`;`budget:int64`;`word_sub stackpointer (word 248):int64`;
                            `m0:int64->byte`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ZINIT_ABI_FROM_POST THEN
      MAP_EVERY EXISTS_TAC [`ctl:int64`;`word_sub stackpointer (word 248):int64`] THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC zinit_driver_correct THEN ASM_REWRITE_TAC[]]));;

let zero_init_join_theorems = zero_init_theorems @ ["ZINIT_X86",ZINIT_X86];;
leaf_audit zero_init_join_theorems
 ["ZINIT_RUN",ZINIT_RUN;"ZINIT_POST_EXACT",ZINIT_POST_EXACT;
  "ZINIT_ABI_EXACT",ZINIT_ABI_EXACT;"ZINIT_X86",ZINIT_X86];;
