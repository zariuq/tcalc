(* Bytes outside initialization's writes survive in the actual ABI memory. *)
needs "native/hol/zero_init_join.ml";;

let ZINIT_ACTUAL_FRAME = prove
 (`!bw ctl budget cfr slots i m0 used res d plan m.
     drv_sem (\j. zero_words) bw ctl budget cfr (zinit_plan slots) i m0 used res /\
     val ctl + 8 <= 2 EXP 64 /\ val(d:int64) + 64 <= 2 EXP 64 /\
     (!slot. MEM slot slots ==> slot < 2 EXP 64) /\
     (!a. ~drv_stack cfr a ==> m a = drv_final d plan res a)
     ==> !a. ~drv_stack cfr a /\ ~drv_in a d 64 /\ ~drv_in a ctl 8 /\
             (!slot. MEM slot slots ==> ~drv_in a (bw slot) (val(bw(slot + 1))))
             ==> m a = m0 a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`slots:num list`;
                `i:num`;`m0:int64->byte`;`used:int64`;`res:int64#num#(int64->byte)#int64`]
               ZINIT_SEM_FRAME) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ZINIT_FINAL_BYTE]);;

let zinit_preserve_basis = SPEC_ALL ZINIT_X86;;
let zinit_preserve_goal =
  let ant,ens = dest_imp(concl zinit_preserve_basis) in
  let h,args = strip_comb ens in
  let state = `s:x86state` in
  let post = mk_abs(state,mk_conj(mk_comb(el 2 args,state),
   `!a. ~drv_stack (word_sub stackpointer (word 248)) a /\
         ~drv_in a d 64 /\ ~drv_in a ctl 8 /\
         (!slot. MEM slot slots ==> ~drv_in a (bw slot) (val(bw(slot + 1))))
         ==> read memory (s:x86state) a = m0 a`)) in
  mk_imp(ant,list_mk_comb(h,[el 0 args;el 1 args;post;el 3 args]));;

let ZINIT_X86_PRESERVES = GEN_ALL(prove(zinit_preserve_goal,
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[drv_layout;MULT_CLAUSES] o
    check (fun th -> zinit_app "drv_layout" (concl th))) THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (el 2 (snd(strip_comb(rand(concl zinit_preserve_basis))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> tisa_has_tm `drv_sem` th)) THEN
    MATCH_MP_TAC ZINIT_ACTUAL_FRAME THEN
    MAP_EVERY EXISTS_TAC [`budget:int64`;`0`;`used0:int64`;
                          `res:int64#num#(int64->byte)#int64`;`plan:int64`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `slot:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[zinit_range_ok] o CONJUNCT1 o
      (fun th -> MP (SPEC `slot:num` th) (ASSUME `MEM (slot:num) (slots:num list)`)) o
      check (fun th -> is_forall(concl th) && tisa_has_tm `zinit_range_ok` th));
    MATCH_MP_TAC zinit_preserve_basis THEN ASM_REWRITE_TAC[]]));;

let zero_init_preserve_theorems =
 ["ZINIT_ACTUAL_FRAME",ZINIT_ACTUAL_FRAME;"ZINIT_X86_PRESERVES",ZINIT_X86_PRESERVES];;
leaf_audit zero_init_preserve_theorems zero_init_preserve_theorems;;
