(* Native bootstrap clearing with fixed-size count and header views. *)
needs "native/hol/zero_init_boot_views.ml";;
needs "native/hol/zero_init_preserve.ml";;
needs "native/hol/zero_init_prefix.ml";;

let ZINIT_BOOT_MINIMAL_EMPTY_THEOREMS = prove
 (`!bw d plan used status m.
     zinit_abi_post (zinit_boot_view bw) zinit_boot_slots d plan used status m
     ==> pl_mw m (bw 20) 0 = 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `zinit_zero (zinit_boot_view bw) [4;10;14;20;26;32;50] m` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[zinit_boot_slots]) THEN
    MP_TAC(SPECL [`zinit_boot_view (bw:num->int64)`;`[4;10;14;20;26;32;50]`;
                  `zinit_boot_marks`;`d:int64`;`plan:int64`;`used:int64`;`status:int64`;`m:int64->byte`]
                 ZINIT_ABI_ZERO_PREFIX) THEN
    ASM_REWRITE_TAC[zinit_boot_marks;APPEND;ZINIT_BOOT_VIEW_COUNTS_SUPPORTED];
    MP_TAC(SPECL [`zinit_boot_view (bw:num->int64)`;`[4;10;14;20;26;32;50]`;
                  `m:int64->byte`;`20`;`0`] ZINIT_ZERO_NUMBER) THEN
    ASM_REWRITE_TAC[MEM;zinit_boot_view] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV]);;

let zinit_boot_minimal_basis = INST
 [`zinit_boot_view (parent:num->int64)`,`bw:num->int64`;
  `zinit_boot_slots`,`slots:num list`] (SPEC_ALL ZINIT_X86_PRESERVES);;

let zinit_boot_minimal_goal =
  let ant,ens = dest_imp(concl zinit_boot_minimal_basis) in
  let h,args = strip_comb ens in
  let state = `s:x86state` in
  let post = mk_abs(state,mk_conj(mk_comb(el 2 args,state),
    `(read RAX (s:x86state) = word 1 <=>
       ALL (\slot. val(parent(slot + 1)) DIV 8 <= 4294967295) zinit_boot_marks) /\
     (read RAX s = word 1 ==> hol_boot_zero parent (read memory s)) /\
     pl_mw (read memory s) (parent 20) 0 = 0`)) in
  mk_imp(ant,list_mk_comb(h,[el 0 args;el 1 args;post;el 3 args]));;

let ZINIT_BOOT_MINIMAL_X86 = GEN_ALL(prove(zinit_boot_minimal_goal,
  STRIP_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (el 2 (snd(strip_comb(rand(concl zinit_boot_minimal_basis))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> tisa_has_tm `zinit_abi_post` th)) THEN
    SUBGOAL_THEN `pl_mw (read memory (s:x86state)) ((parent:num->int64) 20) 0 = 0`
     ASSUME_TAC THENL
     [MATCH_MP_TAC ZINIT_BOOT_MINIMAL_EMPTY_THEOREMS THEN
      MAP_EVERY EXISTS_TAC [`d:int64`;`plan:int64`;`used0:int64`;`read RAX (s:x86state)`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]] THEN
    MP_TAC(SPECL [`zinit_boot_view (parent:num->int64)`;`zinit_boot_slots`;`d:int64`;
                  `plan:int64`;`used0:int64`;`read RAX (s:x86state)`;`read memory (s:x86state)`]
                  ZINIT_ABI_EXACT) THEN
    ASM_REWRITE_TAC[ZINIT_BOOT_VIEW_SUPPORTED] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC ZINIT_BOOT_VIEW_ZERO THEN
      FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o
        (fun th -> MP th (ASSUME `FST(res:int64#num#(int64->byte)#int64) = word 1`)) o
        check (fun th -> is_imp(concl th) && tisa_has_tm `zinit_zero` th))];
    MATCH_MP_TAC zinit_boot_minimal_basis THEN ASM_REWRITE_TAC[]]));;

let zero_init_boot_minimal_theorems = zero_init_boot_view_theorems @
 zero_init_prefix_theorems @
 ["ZINIT_BOOT_MINIMAL_EMPTY_THEOREMS",ZINIT_BOOT_MINIMAL_EMPTY_THEOREMS;
  "ZINIT_BOOT_MINIMAL_X86",ZINIT_BOOT_MINIMAL_X86];;
leaf_audit zero_init_boot_minimal_theorems
 ["ZINIT_BOOT_MINIMAL_X86",ZINIT_BOOT_MINIMAL_X86];;
