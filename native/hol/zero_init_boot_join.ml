(* The native clearing plan establishes the bootstrap's zero-word premise. *)
needs "native/hol/zero_init_boot.ml";;
needs "native/hol/zero_init_preserve.ml";;

let zinit_boot_basis = INST
 [`zinit_word_view (parent:num->int64)`,`bw:num->int64`;
  `zinit_boot_slots`,`slots:num list`] (SPEC_ALL ZINIT_X86_PRESERVES);;

let zinit_boot_x86_goal =
  let ant,ens = dest_imp(concl zinit_boot_basis) in
  let h,args = strip_comb ens in
  let state = `s:x86state` in
  let post = mk_abs(state,mk_conj(mk_comb(el 2 args,state),
    `(read RAX (s:x86state) = word 1 <=>
       ALL (\slot. val(parent(slot + 1)) DIV 8 <= 4294967295) zinit_boot_slots) /\
     (read RAX s = word 1 ==> hol_boot_zero parent (read memory s))`)) in
  mk_imp(mk_conj(ant,`hol_boot_lengths (parent:num->int64)`),
    list_mk_comb(h,[el 0 args;el 1 args;post;el 3 args]));;

let ZINIT_BOOT_X86 = GEN_ALL(prove(zinit_boot_x86_goal,
  STRIP_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (el 2 (snd(strip_comb(rand(concl zinit_boot_basis))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> tisa_has_tm `zinit_abi_post` th)) THEN
    MP_TAC(SPECL [`zinit_word_view (parent:num->int64)`;`zinit_boot_slots`;`d:int64`;
                  `plan:int64`;`used0:int64`;`read RAX (s:x86state)`;`read memory (s:x86state)`]
                  ZINIT_ABI_EXACT) THEN
    ASM_REWRITE_TAC[ZINIT_BOOT_SUPPORTED] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC ZINIT_BOOT_ZERO_VIEW THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o
        (fun th -> MP th (ASSUME `FST(res:int64#num#(int64->byte)#int64) = word 1`)) o
        check (fun th -> is_imp(concl th) && tisa_has_tm `zinit_zero` th))];
    MATCH_MP_TAC zinit_boot_basis THEN ASM_REWRITE_TAC[]]));;

let zero_init_boot_theorems =
 ["ZINIT_BOOT_SLOTS_EVEN",ZINIT_BOOT_SLOTS_EVEN;
  "ZINIT_BOOT_SUPPORTED",ZINIT_BOOT_SUPPORTED;
  "ZINIT_ZERO_NUMBER",ZINIT_ZERO_NUMBER;"ZINIT_BOOT_ZERO",ZINIT_BOOT_ZERO;
  "ZINIT_BOOT_ZERO_VIEW",ZINIT_BOOT_ZERO_VIEW;"ZINIT_BOOT_X86",ZINIT_BOOT_X86];;

leaf_audit zero_init_boot_theorems
 ["ZINIT_BOOT_ZERO_VIEW",ZINIT_BOOT_ZERO_VIEW;"ZINIT_BOOT_X86",ZINIT_BOOT_X86];;
