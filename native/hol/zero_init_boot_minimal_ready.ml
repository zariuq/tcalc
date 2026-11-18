(* Minimal initialization keeps the boot constants on every outcome. *)
needs "native/hol/zero_init_boot_minimal_join.ml";;
needs "native/hol/zero_init_readonly.ml";;

let zinit_boot_minimal_ready_basis = SPEC_ALL ZINIT_BOOT_MINIMAL_X86;;
let zinit_boot_minimal_ready_goal =
  let ant,ens = dest_imp(concl zinit_boot_minimal_ready_basis) in
  let h,args = strip_comb ens in
  let state = `s:x86state` in
  let extra =
   `hol_boot_bytes_at parent m0 /\
    zinit_readonly (zinit_boot_view parent) zinit_boot_slots ctl
      (word_sub stackpointer (word 248)) d (parent 62) 9` in
  let post = mk_abs(state,mk_conj(mk_comb(el 2 args,state),
    `hol_boot_bytes_at parent (read memory (s:x86state))`)) in
  mk_imp(mk_conj(ant,extra),list_mk_comb(h,[el 0 args;el 1 args;post;el 3 args]));;

let ZINIT_BOOT_MINIMAL_READY_X86 = GEN_ALL(prove(zinit_boot_minimal_ready_goal,
  STRIP_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (el 2 (snd(strip_comb(rand(concl zinit_boot_minimal_ready_basis))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> tisa_has_tm `drv_sem` th)) THEN
    SUBGOAL_THEN
     `!i. i < 9 ==> read memory (s:x86state) (word_add (parent 62) (word i)) =
                     (m0:int64->byte)(word_add (parent 62) (word i))`
     ASSUME_TAC THENL
     [MATCH_MP_TAC (ISPECL [`zinit_boot_view (parent:num->int64)`;`zinit_boot_slots`;`ctl:int64`;
                           `word_sub stackpointer (word 248):int64`;`d:int64`;`(parent:num->int64) 62`;
                           `9`;`m0:int64->byte`;`read memory (s:x86state)`] ZINIT_READONLY_FRAME) THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[hol_boot_bytes_at] o
        check (fun th -> zinit_app "hol_boot_bytes_at" (concl th))) THEN
      ASM_SIMP_TAC[hol_boot_bytes_at]];
    MATCH_MP_TAC zinit_boot_minimal_ready_basis THEN ASM_REWRITE_TAC[]]));;

let zero_init_boot_minimal_ready_theorems =
 zero_init_boot_minimal_theorems @ zero_init_readonly_theorems @ zero_init_preserve_theorems @
 ["ZINIT_BOOT_MINIMAL_READY_X86",ZINIT_BOOT_MINIMAL_READY_X86];;
leaf_audit zero_init_boot_minimal_ready_theorems
 ["ZINIT_BOOT_MINIMAL_X86",ZINIT_BOOT_MINIMAL_X86;"ZINIT_BOOT_MINIMAL_READY_X86",ZINIT_BOOT_MINIMAL_READY_X86];;
