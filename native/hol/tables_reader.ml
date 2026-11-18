(* ========================================================================= *)
(* The tables' relation beside the reader: tab_rel moves to a memory that   *)
(* agrees with the old one on every described slot's region and on the     *)
(* control words but one, which then holds the step's payload               *)
(* (TAB_REL_AGREE). A reader step changes only the reader's state and its  *)
(* payload word, so it keeps tab_rel whenever the reader's regions lie apart *)
(* from the layout's.                                                       *)
(*                                                                           *)
(* Loaded after tables_frame.ml and reader_rel.ml.                          *)
(* ========================================================================= *)

let TAB_REL_AGREE = prove
 (`!tb L inp bw ctl nctl cfr m m' cw (s:S) stk p v.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ p < nctl /\ 6 < p /\
     (!j a. MEM j (tab_slots L) /\ drv_in a (bw j) (val(bw(j + 1))) ==> m' a = m a) /\
     (!a. drv_in a ctl (8 * nctl) /\ ~drv_in a (word_add ctl (word(8 * p))) 8 ==> m' a = m a) /\
     drv_word m' (word_add ctl (word(8 * p))) = v
     ==> tab_rel tb L inp bw ctl nctl cfr m' (pl_set cw p (val v),s,stk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_rel] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_set] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC PL_CWORDS_SET THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `ALL (tab_mem tb inp bw (m:int64->byte) (s:S)) L` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN X_GEN_TAC `d:tabdesc` THEN DISCH_TAC THEN
    MATCH_MP_TAC TAB_MEM_AGREE THEN EXISTS_TAC `m:int64->byte` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `MEM (j:num) (tab_slots L)` ASSUME_TAC THENL [ASM_MESON_TAC[TAB_SLOTS_DESC]; ALL_TAC] THEN
    BETA_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LT_IMP_LE THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `tab_slots`)) (concl th) && can (find_term ((=) `drv_in`)) (concl th))) THEN
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC PL_STK_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `L:tabdesc list` TAB_SLOTS_STK) THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LT_IMP_LE THEN
      SUBGOAL_THEN `val(bw 40:int64) + val(bw(40 + 1):int64) < 2 EXP 64` MP_TAC THENL
       [ASM_SIMP_TAC[]; CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[]];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `tab_slots`)) (concl th) && can (find_term ((=) `drv_in`)) (concl th))) THEN
      EXISTS_TAC `40` THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The reader's regions beside the layout's. The reader's state region lies *)
(* apart from every described slot's region but the input's, and so does   *)
(* the input region (rd_tab_apart). A step that writes only the reader's   *)
(* state keeps tab_rel (TAB_RD_STEP_KEEP); a plan whose steps write only   *)
(* described slots other than the input keeps rd_rel (TAB_PLAN_KEEPS_RD).   *)
(* ------------------------------------------------------------------------- *)

let rd_tab_apart = new_definition
 `rd_tab_apart L (bw:num->int64) <=>
    !j. MEM j (tab_slots L) /\ ~(j = 54)
        ==> drv_apart (bw 58) (val(bw 59)) (bw j) (val(bw(j + 1))) /\
            drv_apart (bw 54) (val(bw 55)) (bw j) (val(bw(j + 1)))`;;

let TAB_RD_STEP_KEEP = prove
 (`!tb L inp bw ctl nctl budget cfr prog st m used t k u cw (s:S) stk.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ rd_layout bw ctl nctl cfr /\ rd_tab_apart L bw /\
     drv_child bw ctl budget cfr st m used t /\ tisa_leaf_wf prog /\ tisa_entry_ok prog t /\
     tisa_run prog t = TStop k u /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st) /\
     (!r. tisa_rw (tisa_decls prog) r ==> val(EL (1 + r) st) = 58)
     ==> tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),s,stk)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TAB_REL_AGREE THEN EXISTS_TAC `m:int64->byte` THEN
  ASM_REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME] THEN REWRITE_TAC[GSYM drv_after] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_rel]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`j:num`; `a:int64`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`;
                  `val(EL 17 (st:int64 list))`; `a:int64`] TAB_SLOT_ADDR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC DRV_STEP_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`prog:tisa_prog`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                          `used:int64`; `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[drv_base; drv_len] THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `tisa_rw`)) (concl th)
                            then REWRITE_TAC[MATCH_MP th (ASSUME `tisa_rw (tisa_decls prog) r`)] else failwith "") THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_CASES_TAC `j = 54` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC DRV_APART_IN THEN
      MAP_EVERY EXISTS_TAC [`bw 54:int64`; `val(bw 55:int64)`] THEN
      RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC DRV_APART_IN THEN MAP_EVERY EXISTS_TAC [`bw(j:num):int64`; `val(bw(j + 1):int64)`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[rd_tab_apart]];
    X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
    MATCH_MP_TAC DRV_STEP_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`prog:tisa_prog`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                          `used:int64`; `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[drv_base; drv_len] THEN CONJ_TAC THENL
     [MATCH_MP_TAC TAB_CTL_ADDR THEN
      MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `tisa_rw`)) (concl th)
                              then REWRITE_TAC[MATCH_MP th (ASSUME `tisa_rw (tisa_decls prog) r`)] else failwith "") THEN
      CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC DRV_APART_IN THEN
      MAP_EVERY EXISTS_TAC [`ctl:int64`; `8 * nctl`] THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `58` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `54`)) (concl th) && can (find_term ((=) `ctl:int64`)) (concl th))) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN SIMP_TAC[]]]);;

let tab_rd_plan_ok = new_definition
 `tab_rd_plan_ok L (progs:num->tisa_prog) nctl (P:(int64 list)list) <=>
    !st. MEM st P ==> tisa_leaf_wf (progs (val(EL 0 st))) /\ val(EL 17 st) < nctl /\
                      (!r. tisa_rw (tisa_decls (progs (val(EL 0 st)))) r
                           ==> MEM (val(EL (1 + r) st)) (tab_slots L) /\ ~(val(EL (1 + r) st) = 54))`;;

let TAB_PLAN_KEEPS_RD = prove
 (`!L progs bw ctl nctl budget cfr P i m used res inp c.
     drv_sem progs bw ctl budget cfr P i m used res /\ rd_rel bw ctl nctl cfr m inp c /\
     tab_layout L bw ctl nctl cfr /\ rd_tab_apart L bw /\ tab_rd_plan_ok L progs nctl P
     ==> rd_rel bw ctl nctl cfr (FST(SND(SND res))) inp c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_rd_plan_ok] THEN STRIP_TAC THEN
  MATCH_MP_TAC RD_REL_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     ASSUME_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `P:(int64 list)list`; `i:num`; `m:int64->byte`; `used:int64`;
                `res:int64#num#(int64->byte)#int64`] DRV_SEM_KEEPS) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(fun keeps -> X_GEN_TAC `a:int64` THEN DISCH_TAC THEN MATCH_MP_TAC keeps) THEN
  SUBGOAL_THEN `?jr. (jr = 54 \/ jr = 58) /\ drv_in (a:int64) (bw jr) (val(bw(jr + 1)))`
    (X_CHOOSE_THEN `jr:num` (CONJUNCTS_THEN ASSUME_TAC)) THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [EXISTS_TAC `54` THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `58` THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `jr:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `54`)) (concl th) && can (find_term ((=) `ctl:int64`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DRV_IN_NOT_STACK THEN
    MAP_EVERY EXISTS_TAC [`bw(jr:num):int64`; `val(bw(jr + 1):int64)`] THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[drv_base; drv_len] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `st:int64 list` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_leaf_wf`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `r:num` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC DRV_APART_IN THEN MAP_EVERY EXISTS_TAC [`bw(jr:num):int64`; `val(bw(jr + 1):int64)`] THEN
    ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `jr = 54 \/ jr = 58`)) THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_MESON_TAC[rd_tab_apart];
    X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL [`a:int64`; `bw(jr:num):int64`; `val(bw(jr + 1):int64)`; `ctl:int64`; `8 * nctl`] DRV_APART_IN) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DRV_CTL_WORD_IN THEN EXISTS_TAC `val(EL 17 (st:int64 list))` THEN ASM_MESON_TAC[]]);;

(* Every theorem this file states, for the audits. *)
let tables_reader_theorems =
 ["TAB_REL_AGREE", TAB_REL_AGREE; "TAB_RD_STEP_KEEP", TAB_RD_STEP_KEEP; "TAB_PLAN_KEEPS_RD", TAB_PLAN_KEEPS_RD];;
