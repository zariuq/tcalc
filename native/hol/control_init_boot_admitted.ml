(* A successful native initializer establishes the bootstrap control view. *)
needs "native/hol/kernel_entry_init_basis_load.ml";;

let CONTROL_INIT_FNV_NUMBER = prove
 (`val(fnv_offset:int64) = 14695981039346656037`,
  REWRITE_TAC[fnv_offset;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let CINIT_ABI_BOOT_CONTROLS =
  REWRITE_RULE[GSYM pl_cwords;GSYM CONTROL_INIT_FNV_NUMBER] CINIT_ABI_BOOT_VALUES;;

let cinit_boot_basis = SPEC_ALL CINIT_ADMITTED_X86;;
let cinit_boot_goal =
  let ant,ens = dest_imp(concl cinit_boot_basis) in
  let h,args = strip_comb ens in
  let state = `s:x86state` in
  let post = mk_abs(state,mk_conj(mk_comb(el 2 args,state),
    `read RAX (s:x86state) = word 1
     ==> ?cw. pl_cwords ctl nctl (read memory s) cw /\
              (!i. i <= 6 ==> cw i = i) /\
              cw 7 = val(drv_word m0 (word_add ctl (word 56))) /\
              cw 17 = 0 /\ cw 19 = 0 /\ cw 20 = 0 /\ cw 22 = val fnv_offset`)) in
  mk_imp(ant,list_mk_comb(h,[el 0 args;el 1 args;post;el 3 args]));;

let CINIT_BOOT_CONTROLS_X86 = GEN_ALL(prove(cinit_boot_goal,
  STRIP_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (el 2 (snd(strip_comb(rand(concl cinit_boot_basis))))) THEN CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> tisa_has_tm `cinit_abi_post` th)) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `FST(res:int64#num#(int64->byte)#int64) = word 1` ASSUME_TAC THENL
     [ASM_MESON_TAC[];ALL_TAC] THEN
    ASM_CASES_TAC `val(budget:int64) < val(used0:int64)` THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th) &&
       tisa_has_tm `cinit_abi_post` th)) THEN
      ASM_REWRITE_TAC[cinit_invalid_post;
        EQT_ELIM(WORD_REDUCE_CONV `~(word 1:int64 = word 3)`)];
      MATCH_MP_TAC CINIT_ABI_BOOT_CONTROLS THEN
      MAP_EVERY EXISTS_TAC [`d:int64`;`plan:int64`;`used0:int64`;
                            `read RAX (s:x86state)`] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th) &&
       tisa_has_tm `cinit_abi_post` th)) THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC cinit_boot_basis THEN ASM_REWRITE_TAC[]]));;

let control_init_boot_admitted_theorems =
 ["CONTROL_INIT_FNV_NUMBER",CONTROL_INIT_FNV_NUMBER;
  "CINIT_ABI_BOOT_CONTROLS",CINIT_ABI_BOOT_CONTROLS;
  "CINIT_BOOT_CONTROLS_X86",CINIT_BOOT_CONTROLS_X86];;
leaf_audit control_init_boot_admitted_theorems control_init_boot_admitted_theorems;;
