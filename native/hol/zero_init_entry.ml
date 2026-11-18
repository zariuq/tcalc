(* Native clearing also prepares the hash arrays and declaration flags. *)
needs "native/hol/zero_init_boot_minimal_join.ml";;
needs "native/hol/zero_init_readonly.ml";;

let zinit_entry_extra = new_definition
 `zinit_entry_extra = [2;8;48;36]`;;

let zinit_entry_slots = new_definition
 `zinit_entry_slots = APPEND zinit_boot_slots zinit_entry_extra`;;

let zinit_entry_arrays = new_definition
 `zinit_entry_arrays = APPEND zinit_boot_marks zinit_entry_extra`;;

let zinit_entry_view = new_definition
 `zinit_entry_view (bw:num->int64) k =
    if MEM k [3;9;49;37] then zinit_round(bw k) else zinit_boot_view bw k`;;

let ZINIT_ENTRY_VIEW_BOOT = prove
 (`!bw slot. MEM slot zinit_boot_slots
     ==> zinit_entry_view bw slot = zinit_boot_view bw slot /\
         zinit_entry_view bw (slot + 1) = zinit_boot_view bw (slot + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zinit_boot_slots;MEM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[zinit_entry_view;MEM] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ZINIT_ENTRY_VIEW_EXTRA = prove
 (`!bw slot. MEM slot zinit_entry_extra
     ==> zinit_entry_view bw slot = bw slot /\
         zinit_entry_view bw (slot + 1) = zinit_round(bw(slot + 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zinit_entry_extra;MEM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[zinit_entry_view;zinit_boot_view;MEM] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ZINIT_ENTRY_VIEW_SUBRANGE = prove
 (`!bw slot. hol_boot_lengths bw /\ MEM slot zinit_entry_slots
     ==> zinit_entry_view bw slot = bw slot /\
         val(zinit_entry_view bw (slot + 1)) <= val(bw(slot + 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zinit_entry_slots;MEM_APPEND] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN ASSUME_TAC)) THENL
   [MP_TAC(SPECL [`bw:num->int64`;`slot:num`] ZINIT_BOOT_VIEW_SUBRANGE) THEN
    ASM_SIMP_TAC[ZINIT_ENTRY_VIEW_BOOT];
    MP_TAC(ISPEC `(bw:num->int64)(slot + 1)` ZINIT_ROUND_VALUE) THEN
    ASM_SIMP_TAC[ZINIT_ENTRY_VIEW_EXTRA] THEN ARITH_TAC]);;

let ZINIT_ENTRY_VIEW_SUPPORTED = prove
 (`!bw. ALL (zinit_supported (zinit_entry_view bw)) zinit_entry_slots <=>
        ALL (\slot. val(bw(slot + 1)) DIV 8 <= 4294967295) zinit_entry_arrays`,
  GEN_TAC THEN
  REWRITE_TAC[zinit_entry_slots;zinit_entry_arrays;zinit_boot_slots;
    zinit_boot_marks;zinit_entry_extra;APPEND;ALL;zinit_supported;
    zinit_entry_view;zinit_boot_view;MEM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[ZINIT_ROUND_DIV;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let ZINIT_ENTRY_COUNTS_SUPPORTED = prove
 (`!bw. ALL (zinit_supported (zinit_entry_view bw)) [4;10;14;20;26;32;50]`,
  GEN_TAC THEN REWRITE_TAC[ALL;zinit_supported;zinit_entry_view;zinit_boot_view;MEM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let ZINIT_ENTRY_ZERO = prove
 (`!bw m. zinit_zero (zinit_entry_view bw) zinit_entry_slots m
     ==> hol_boot_zero bw m /\ zinit_zero bw zinit_entry_extra m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC ZINIT_BOOT_VIEW_ZERO THEN
    REWRITE_TAC[zinit_zero] THEN MAP_EVERY X_GEN_TAC [`slot:num`;`i:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`slot:num`;`i:num`] o REWRITE_RULE[zinit_zero] o
      check (fun th -> zinit_app "zinit_zero" (concl th))) THEN
    ASM_SIMP_TAC[zinit_entry_slots;MEM_APPEND;ZINIT_ENTRY_VIEW_BOOT];
    REWRITE_TAC[zinit_zero] THEN MAP_EVERY X_GEN_TAC [`slot:num`;`i:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`slot:num`;`i:num`] o REWRITE_RULE[zinit_zero] o
      check (fun th -> zinit_app "zinit_zero" (concl th))) THEN
    ASM_SIMP_TAC[zinit_entry_slots;MEM_APPEND;ZINIT_ENTRY_VIEW_EXTRA;ZINIT_ROUND_WORDS]]);;

let ZINIT_ENTRY_EMPTY_THEOREMS = prove
 (`!bw d plan used status m.
     zinit_abi_post (zinit_entry_view bw) zinit_entry_slots d plan used status m
     ==> pl_mw m (bw 20) 0 = 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `zinit_zero (zinit_entry_view bw) [4;10;14;20;26;32;50] m`
   ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[zinit_entry_slots;zinit_boot_slots;zinit_boot_marks;APPEND]) THEN
    MP_TAC(SPECL [`zinit_entry_view (bw:num->int64)`;`[4;10;14;20;26;32;50]`;
                  `APPEND zinit_boot_marks zinit_entry_extra`;`d:int64`;`plan:int64`;
                  `used:int64`;`status:int64`;`m:int64->byte`] ZINIT_ABI_ZERO_PREFIX) THEN
    ASM_REWRITE_TAC[ZINIT_ENTRY_COUNTS_SUPPORTED;zinit_entry_slots;
      zinit_boot_slots;zinit_boot_marks;APPEND];
    MP_TAC(SPECL [`zinit_entry_view (bw:num->int64)`;`[4;10;14;20;26;32;50]`;
                  `m:int64->byte`;`20`;`0`] ZINIT_ZERO_NUMBER) THEN
    ASM_REWRITE_TAC[MEM;zinit_entry_view;zinit_boot_view] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV]);;

let ZINIT_ENTRY_HASH_LIMIT_CONTROL = prove
 (`ALL (zinit_supported (zinit_boot_view
      (\k. if k = 3 then word 34359738368 else word 16))) zinit_boot_slots /\
   ~ALL (zinit_supported (zinit_entry_view
      (\k. if k = 3 then word 34359738368 else word 16))) zinit_entry_slots`,
  REWRITE_TAC[ZINIT_BOOT_VIEW_SUPPORTED;ZINIT_ENTRY_VIEW_SUPPORTED;
    zinit_entry_arrays;zinit_boot_marks;zinit_entry_extra;ALL;APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let zinit_entry_basis = INST
 [`zinit_entry_view (parent:num->int64)`,`bw:num->int64`;
  `zinit_entry_slots`,`slots:num list`] (SPEC_ALL ZINIT_X86_PRESERVES);;

let zinit_entry_goal =
  let ant,ens = dest_imp(concl zinit_entry_basis) in
  let h,args = strip_comb ens in
  let state = `s:x86state` in
  let post = mk_abs(state,mk_conj(mk_comb(el 2 args,state),
    `(read RAX (s:x86state) = word 1 <=>
       ALL (\slot. val(parent(slot + 1)) DIV 8 <= 4294967295) zinit_entry_arrays) /\
     (read RAX s = word 1 ==>
       hol_boot_zero parent (read memory s) /\
       zinit_zero parent zinit_entry_extra (read memory s)) /\
     pl_mw (read memory s) (parent 20) 0 = 0`)) in
  mk_imp(ant,list_mk_comb(h,[el 0 args;el 1 args;post;el 3 args]));;

let ZINIT_ENTRY_X86 = GEN_ALL(prove(zinit_entry_goal,
  STRIP_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (el 2 (snd(strip_comb(rand(concl zinit_entry_basis))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> tisa_has_tm `zinit_abi_post` th)) THEN
    SUBGOAL_THEN `pl_mw (read memory (s:x86state)) ((parent:num->int64) 20) 0 = 0`
     ASSUME_TAC THENL
     [MATCH_MP_TAC ZINIT_ENTRY_EMPTY_THEOREMS THEN
      MAP_EVERY EXISTS_TAC [`d:int64`;`plan:int64`;`used0:int64`;`read RAX (s:x86state)`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]] THEN
    MP_TAC(SPECL [`zinit_entry_view (parent:num->int64)`;`zinit_entry_slots`;`d:int64`;
                  `plan:int64`;`used0:int64`;`read RAX (s:x86state)`;`read memory (s:x86state)`]
                  ZINIT_ABI_EXACT) THEN
    ASM_REWRITE_TAC[ZINIT_ENTRY_VIEW_SUPPORTED] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC ZINIT_ENTRY_ZERO THEN
      FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o
        (fun th -> MP th (ASSUME `FST(res:int64#num#(int64->byte)#int64) = word 1`)) o
        check (fun th -> is_imp(concl th) && tisa_has_tm `zinit_zero` th))];
    MATCH_MP_TAC zinit_entry_basis THEN ASM_REWRITE_TAC[]]));;

let zinit_entry_ready_basis = SPEC_ALL ZINIT_ENTRY_X86;;
let zinit_entry_ready_goal =
  let ant,ens = dest_imp(concl zinit_entry_ready_basis) in
  let h,args = strip_comb ens in
  let state = `s:x86state` in
  let extra =
   `hol_boot_bytes_at parent m0 /\
    zinit_readonly (zinit_entry_view parent) zinit_entry_slots ctl
      (word_sub stackpointer (word 248)) d (parent 62) 9` in
  let post = mk_abs(state,mk_conj(mk_comb(el 2 args,state),
    `hol_boot_bytes_at parent (read memory (s:x86state))`)) in
  mk_imp(mk_conj(ant,extra),list_mk_comb(h,[el 0 args;el 1 args;post;el 3 args]));;

let ZINIT_ENTRY_READY_X86 = GEN_ALL(prove(zinit_entry_ready_goal,
  STRIP_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (el 2 (snd(strip_comb(rand(concl zinit_entry_ready_basis))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> tisa_has_tm `drv_sem` th)) THEN
    SUBGOAL_THEN
     `!i. i < 9 ==> read memory (s:x86state) (word_add (parent 62) (word i)) =
                     (m0:int64->byte)(word_add (parent 62) (word i))`
     ASSUME_TAC THENL
     [MATCH_MP_TAC (ISPECL [`zinit_entry_view (parent:num->int64)`;`zinit_entry_slots`;`ctl:int64`;
                           `word_sub stackpointer (word 248):int64`;`d:int64`;`(parent:num->int64) 62`;
                           `9`;`m0:int64->byte`;`read memory (s:x86state)`] ZINIT_READONLY_FRAME) THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[hol_boot_bytes_at] o
        check (fun th -> zinit_app "hol_boot_bytes_at" (concl th))) THEN
      ASM_SIMP_TAC[hol_boot_bytes_at]];
    MATCH_MP_TAC zinit_entry_ready_basis THEN ASM_REWRITE_TAC[]]));;

let zero_init_entry_theorems =
 ["ZINIT_ENTRY_VIEW_BOOT",ZINIT_ENTRY_VIEW_BOOT;
  "ZINIT_ENTRY_VIEW_EXTRA",ZINIT_ENTRY_VIEW_EXTRA;
  "ZINIT_ENTRY_VIEW_SUBRANGE",ZINIT_ENTRY_VIEW_SUBRANGE;
  "ZINIT_ENTRY_VIEW_SUPPORTED",ZINIT_ENTRY_VIEW_SUPPORTED;
  "ZINIT_ENTRY_COUNTS_SUPPORTED",ZINIT_ENTRY_COUNTS_SUPPORTED;
  "ZINIT_ENTRY_ZERO",ZINIT_ENTRY_ZERO;
  "ZINIT_ENTRY_EMPTY_THEOREMS",ZINIT_ENTRY_EMPTY_THEOREMS;
  "ZINIT_ENTRY_HASH_LIMIT_CONTROL",ZINIT_ENTRY_HASH_LIMIT_CONTROL;
  "ZINIT_ENTRY_X86",ZINIT_ENTRY_X86;
  "ZINIT_ENTRY_READY_X86",ZINIT_ENTRY_READY_X86];;
leaf_audit zero_init_entry_theorems zero_init_entry_theorems;;
