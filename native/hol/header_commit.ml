(* Publish the validated header candidate after the remaining checks. *)
needs "native/hol/kernel_header_basis_load.ml";;

let pl_hdr_commit = new_definition(mk_eq(`pl_hdr_commit:(int64 list)list`,
  mk_list([pl_step_tm 3 [] 25 25 [] 7],`:int64 list`)));;

let HDR_COMMIT_REL = prove
 (`!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     progs 3 = eqw /\ 25 < nctl /\
     drv_sem progs bw ctl budget cfr pl_hdr_commit i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\ FST r = word 1 /\
         plan_rel bw ctl nctl cfr (FST(SND(SND r)))
                  (pl_set cw 7 (cw 25),(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
         rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_const_app "drv_sem" o concl)) THEN
  REWRITE_TAC[pl_hdr_commit;drv_sem] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:tisa_state` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL ([`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;
                 hd(dest_list(rhs(concl pl_hdr_commit)));`m:int64->byte`;`used:int64`;`t:tisa_state`;
                 `k:num`;`u:tisa_state`;`cw:num->num`] @ RD_NS_VARS @ [`inp:num list`;`c:num`])
                RD_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  TRY(ANTS_TAC THENL [STEP_RANGE_TAC;ALL_TAC]) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[drv_sem] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST;SND] THEN ASM_REWRITE_TAC[]);;

let header_commit_theorems = ["HDR_COMMIT_REL",HDR_COMMIT_REL];;
leaf_audit header_commit_theorems header_commit_theorems;;
