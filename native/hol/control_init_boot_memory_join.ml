(* The native seed carries prepared bootstrap memory facts to its caller. *)
needs "native/hol/control_init_preserve.ml";;
needs "native/hol/boot_memory_frame.ml";;

let cinit_boot_memory_basis = SPEC_ALL CINIT_X86_PRESERVES;;
let cinit_boot_memory_goal =
  let ant,ens = dest_imp(concl cinit_boot_memory_basis) in
  let h,args = strip_comb ens in
  let state = `s:x86state` in
  let extra =
   `hol_boot_frame_regions parent (word_sub stackpointer (word 248)) d ctl nctl /\
    hol_boot_lengths parent /\ hol_boot_zero parent m0 /\ hol_boot_bytes_at parent m0` in
  let post = mk_abs(state,mk_conj(mk_comb(el 2 args,state),
    `hol_boot_zero parent (read memory (s:x86state)) /\
     hol_boot_bytes_at parent (read memory s)`)) in
  mk_imp(mk_conj(ant,extra),list_mk_comb(h,[el 0 args;el 1 args;post;el 3 args]));;

let CINIT_BOOT_MEMORY_X86 = GEN_ALL(prove(cinit_boot_memory_goal,
  STRIP_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (el 2 (snd(strip_comb(rand(concl cinit_boot_memory_basis))))) THEN CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> tisa_has_tm `drv_sem` th)) THEN
    MATCH_MP_TAC HOL_BOOT_MEMORY_FRAME THEN
    MAP_EVERY EXISTS_TAC [`word_sub stackpointer (word 248):int64`;`d:int64`;
                          `ctl:int64`;`nctl:num`;`m0:int64->byte`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC cinit_boot_memory_basis THEN ASM_REWRITE_TAC[]]));;

let control_init_boot_memory_theorems =
  control_init_preserve_theorems @ driver_region_frame_theorems @ boot_memory_frame_theorems @
  ["CINIT_BOOT_MEMORY_X86",CINIT_BOOT_MEMORY_X86];;
leaf_audit control_init_boot_memory_theorems control_init_boot_memory_theorems;;
