(* The header's total publication step over any represented tables. *)
needs "native/hol/kernel_table_handler_basis_load.ml";;
needs "native/hol/header_commit.ml";;

let HDR_COMMIT_TAB = prove
 (`!tb L progs bw ctl nctl budget cfr i m used r cw (s:S) stk inp c.
     progs 3 = eqw /\ 25 < nctl /\
     drv_sem progs bw ctl budget cfr pl_hdr_commit i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\ FST r = word 1 /\
         tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r))) (pl_set cw 7 (cw 25),s,stk) /\
         rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_const_app "drv_sem" o concl)) THEN
  REWRITE_TAC[pl_hdr_commit;drv_sem] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:tisa_state` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL
   [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
        (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
    `L:tabdesc list`;`inp:num list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;
    hd(dest_list(rhs(concl pl_hdr_commit)));`m:int64->byte`;`used:int64`;`t:tisa_state`;`k:num`;
    `u:tisa_state`;`cw:num->num`;`s:S`;`stk:num list`;`c:num`] TAB_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  TRY(ANTS_TAC THENL [STEP_RANGE_TAC;ALL_TAC]) THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(PURE_REWRITE_RULE[ASSUME `val(tisa_fword (u:tisa_state) 19) = (cw:num->num) 25`]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[drv_sem] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST;SND] THEN ASM_REWRITE_TAC[]);;

let header_commit_tab_theorems = ["HDR_COMMIT_TAB",HDR_COMMIT_TAB];;
leaf_audit header_commit_tab_theorems header_commit_tab_theorems;;
