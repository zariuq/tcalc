(* ========================================================================= *)
(* Plans in sequence. A run of a plan ends FIRED only at the plan's end      *)
(* (DRV_SEM_FIRED_INDEX), and a run of P1 ++ P2 is a run of P1 followed,    *)
(* when it FIRED, by a run of P2 from P1's final memory and receipt, its    *)
(* step indices shifted by P1's length (DRV_SEM_APPEND). A record's handler *)
(* is its operand prefix, then its kind's plan, then the count's increment. *)
(*                                                                           *)
(* Loaded after driver.ml.                                                   *)
(* ========================================================================= *)

let DRV_SEM_FIRED_INDEX = prove
 (`!progs bw ctl budget cfr P i m used r.
     drv_sem progs bw ctl budget cfr P i m used r /\ FST r = word 1
     ==> FST(SND r) = i + LENGTH P`,
  REPLICATE_TAC 5 GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[drv_sem; LENGTH] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC)) THEN REWRITE_TAC[FST; SND; ADD_CLAUSES];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_sem; LENGTH] THEN
  ASM_CASES_TAC `val(budget:int64) < val(used:int64)` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN REWRITE_TAC[CONJUNCT1 th; FST]) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `tc:tisa_state` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u:tisa_state` STRIP_ASSUME_TAC)))
    ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  ASM_CASES_TAC `tisa_fword u 18 = word 1` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`; `drv_after ctl h u`; `tisa_fword u 21`;
                                  `r:int64#num#(int64->byte)#int64`] o
                  check (fun th -> is_forall(concl th) && can (find_term ((=) `drv_sem`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN ASM_MESON_TAC[]]);;

let DRV_SEM_APPEND = prove
 (`!progs bw ctl budget cfr P1 P2 i m used res.
     drv_sem progs bw ctl budget cfr (APPEND P1 P2) i m used res <=>
     ?r. drv_sem progs bw ctl budget cfr P1 i m used r /\
         (if FST r = word 1
          then drv_sem progs bw ctl budget cfr P2 (i + LENGTH P1) (FST(SND(SND r)))
                       (SND(SND(SND r))) res
          else res = r)`,
  REPLICATE_TAC 5 GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; drv_sem; LENGTH; ADD_CLAUSES] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[UNWIND_THM2; FST; SND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[APPEND; drv_sem; LENGTH] THEN
  ASM_CASES_TAC `val(budget:int64) < val(used:int64)` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[UNWIND_THM2; FST] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `tc:tisa_state` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u:tisa_state`
      STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
    ASM_CASES_TAC `tisa_fword u 18 = word 1` THEN ASM_REWRITE_TAC[] THENL
     [DISCH_THEN(X_CHOOSE_THEN `r:int64#num#(int64->byte)#int64` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `r:int64#num#(int64->byte)#int64` THEN CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`tc:tisa_state`; `k:num`; `u:tisa_state`] THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[ARITH_RULE `i + SUC n = (i + 1) + n`] THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC THEN
      EXISTS_TAC `(tisa_fword u 18,i:num,drv_after ctl h u,tisa_fword u 21)` THEN
      ASM_REWRITE_TAC[FST] THEN
      MAP_EVERY EXISTS_TAC [`tc:tisa_state`; `k:num`; `u:tisa_state`] THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `r:int64#num#(int64->byte)#int64`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `tc:tisa_state` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u:tisa_state`
         STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`tc:tisa_state`; `k:num`; `u:tisa_state`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th) &&
      can (find_term ((=) `tisa_fword u 18`)) (concl th))) THEN
    ASM_CASES_TAC `tisa_fword u 18 = word 1` THEN ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN EXISTS_TAC `r:int64#num#(int64->byte)#int64` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `i + SUC n = (i + 1) + n`]) THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
      ASM_REWRITE_TAC[FST]]]);;
