(* ========================================================================= *)
(* The driver's outcome is a function of the plan's memory outside its stack *)
(* and outside any set X of bytes no step reads (drv_unread): X lies outside *)
(* the driver's stack, the control words and every step's readable regions. *)
(* Two runs from memories that agree outside the stack and X end alike, with *)
(* memories that agree outside the stack and X (DRV_SEM_FUN_X). The record   *)
(* loop's stack beyond the driver's (records.ml, rec_stack) is such an X.    *)
(*                                                                           *)
(* Loaded after driver_det.ml.                                               *)
(* ========================================================================= *)

needs "native/driver/driver_det.ml";;

let drv_unread = new_definition
 `drv_unread (progs:num->tisa_prog) (bw:num->int64) (ctl:int64) nctl (cfr:int64) (sts:(int64 list)list)
             (X:int64->bool) <=>
    !a. X a ==> ~drv_stack cfr a /\ ~drv_in a ctl (8 * nctl) /\
                (!st r. MEM st sts /\ tisa_readable (tisa_decls (progs (val(EL 0 st)))) r
                        ==> ~drv_in a (drv_base bw st r) (val(drv_len bw st r)))`;;

let DRV_UNREAD_TL = prove
 (`!progs bw ctl nctl cfr h t X.
     drv_unread progs bw ctl nctl cfr (CONS h t) X ==> drv_unread progs bw ctl nctl cfr t X`,
  REWRITE_TAC[drv_unread; MEM] THEN MESON_TAC[]);;

let DRV_CW_SAME_X = prove
 (`!cfr ctl nctl (X:int64->bool) m1 m2 (k:int64).
     48 <= val cfr /\ drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl) /\
     val ctl + 8 * nctl <= 2 EXP 64 /\ val k < nctl /\
     (!a. X a ==> ~drv_in a ctl (8 * nctl)) /\
     (!a. ~drv_stack cfr a /\ ~X a ==> m2 a = m1 a)
     ==> drv_cw ctl m2 k = drv_cw ctl m1 k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[drv_cw] THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  MP_TAC(SPECL [`word_add ctl (word(8 * val(k:int64))):int64`; `ctl:int64`; `8 * nctl`;
                `8 * val(k:int64)`] DRV_BYTES_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `drv_stack`)) (concl th))) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [`ctl:int64`; `8 * nctl`] THEN ASM_SIMP_TAC[];
    ASM_MESON_TAC[]]);;

let DRV_INPUTS_SAME_X = prove
 (`!pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc progs bw budget used st X m1 m2.
     drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     drv_step_ok progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw st /\
     (!a. X a ==> ~drv_in a ctl (8 * nctl)) /\
     (!a. ~drv_stack cfr a /\ ~X a ==> m2 a = m1 a)
     ==> drv_regs cfr ctl st m2 = drv_regs cfr ctl st m1 /\
         (!j. j < 24 ==> drv_fw bw ctl budget used st m2 j = drv_fw bw ctl budget used st m1 j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_layout; drv_step_ok] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!f. 10 <= f /\ f < 18 ==> drv_cw ctl m2 (EL f st) = drv_cw ctl m1 (EL f st)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_CW_SAME_X THEN
    MAP_EVERY EXISTS_TAC [`cfr:int64`; `nctl:num`; `X:int64->bool`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; drv_regs] THEN X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `j <= 5` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `drv_cw`)) (concl th))) THEN
    ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[drv_fw] THEN
    ASM_CASES_TAC `j < 18` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `j < 20` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `j = 20` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `j = 21` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `drv_cw`)) (concl th))) THEN
    ASM_ARITH_TAC]);;

let DRV_CHILD_PATCH_X = prove
 (`!bw ctl budget cfr (X:int64->bool) st m1 m2 used t1 t2.
     val cfr + 192 <= 2 EXP 64 /\ (!a. X a ==> ~drv_stack cfr a) /\
     drv_child bw ctl budget cfr st m1 used t1 /\ drv_child bw ctl budget cfr st m2 used t2 /\
     drv_regs cfr ctl st m2 = drv_regs cfr ctl st m1 /\
     (!j. j < 24 ==> drv_fw bw ctl budget used st m2 j = drv_fw bw ctl budget used st m1 j) /\
     (!a. ~drv_stack cfr a /\ ~X a ==> m2 a = m1 a)
     ==> t2 = tisa_patch (\a. drv_free cfr a \/ X a) (tmem t2) t1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_child] THEN STRIP_TAC THEN
  SUBGOAL_THEN `tregs t2 = tregs t1` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `tregs t1 0 = cfr` ASSUME_TAC THENL [ASM_REWRITE_TAC[drv_regs]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < 24 ==> tisa_fword t2 i = tisa_fword t1 i` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM TISA_STATE_ETA] THEN
  REWRITE_TAC[tisa_patch; injectivity "tisa_state"] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:int64` THEN REWRITE_TAC[drv_free] THEN
  ASM_CASES_TAC `drv_stack cfr a` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(X:int64->bool) a` (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC TISA_FRAME_BYTES_SAME THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[drv_regs];
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[]]);;

let DRV_FREE_APART_X = prove
 (`!pc cfr d plan ns nctl bind nbw leaves nl lpc lmc progs bw ctl budget used st m t (X:int64->bool).
     48 <= val cfr /\
     drv_step_ok progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw st /\
     tisa_leaf_wf (progs (val(EL 0 st))) /\
     drv_child bw ctl budget cfr st m used t /\
     (!a. X a ==> ~drv_stack cfr a /\
                  (!r. tisa_readable (tisa_decls (progs (val(EL 0 st)))) r
                       ==> ~drv_in a (drv_base bw st r) (val(drv_len bw st r))))
     ==> tisa_apart (tisa_decls (progs (val(EL 0 st)))) (\a. drv_free cfr a \/ X a) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `nctl:num`; `bind:int64`;
                `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`;
                `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `used:int64`;
                `st:int64 list`; `m:int64->byte`; `t:tisa_state`] DRV_FREE_APART) THEN
  ASM_REWRITE_TAC[tisa_apart] THEN DISCH_TAC THEN X_GEN_TAC `a:int64` THEN BETA_TAC THEN
  STRIP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:int64` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `X:int64->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  REWRITE_TAC[tisa_touch] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `r < 9` ASSUME_TAC THENL
     [UNDISCH_TAC `tisa_readable (tisa_decls (progs (val(EL 0 (st:int64 list))))) r` THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[tisa_leaf_wf] o check (fun th ->
        can (find_term ((=) `tisa_leaf_wf`)) (concl th))) THEN
      REWRITE_TAC[tisa_readable] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
       can (find_term ((=) `tisa_base`)) (concl th) && can (find_term ((=) `drv_base`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
       can (find_term ((=) `tisa_readable`)) (concl th) && can (find_term ((=) `drv_in`)) (concl th))) THEN
    ASM_REWRITE_TAC[drv_in];
    FIRST_X_ASSUM(fun th -> if concl th = `tregs t 0 = cfr` then SUBST_ALL_TAC th else failwith "") THEN
    UNDISCH_TAC `~drv_stack cfr (a:int64)` THEN REWRITE_TAC[drv_stack] THEN ASM_ARITH_TAC]);;

let DRV_SEM_FUN_X_GOAL =
 `!progs pc d plan ns nctl bind nbw leaves nl lpc lmc bw ctl budget cfr X sts i m1 m2 used res1 res2.
     drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     (!j. j < nl ==> tisa_leaf_wf (progs j)) /\
     ALL (drv_step_ok progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw) sts /\
     drv_unread progs bw ctl nctl cfr sts X /\
     (!a. ~drv_stack cfr a /\ ~X a ==> m2 a = m1 a) /\
     drv_sem progs bw ctl budget cfr sts i m1 used res1 /\
     drv_sem progs bw ctl budget cfr sts i m2 used res2
     ==> FST res2 = FST res1 /\ FST(SND res2) = FST(SND res1) /\
         SND(SND(SND res2)) = SND(SND(SND res1)) /\
         (!a. ~drv_stack cfr a /\ ~X a ==> FST(SND(SND res2)) a = FST(SND(SND res1)) a)`;;

let DRV_SEM_FUN_X_IS_APP name th = try fst(dest_const(fst(strip_comb(concl th)))) = name with Failure _ -> false;;
let DRV_SEM_FUN_X_PFREE = `\a:int64. drv_free cfr a \/ (X:int64->bool) a`;;

let DRV_SEM_FUN_X_TAC1 =
  let is_app = DRV_SEM_FUN_X_IS_APP in
  REPLICATE_TAC 17 GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[drv_sem] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_sem; ALL] THEN
  ASM_CASES_TAC `val(budget:int64) < val(used:int64)` THEN ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[FST; SND]; ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `tisa_leaf_wf (progs (val(EL 0 (h:int64 list))))` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                                                can (find_term ((=) `tisa_leaf_wf`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o check (is_app "drv_step_ok")) THEN REWRITE_TAC[drv_step_ok] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!a. (X:int64->bool) a ==> ~drv_stack cfr a) /\
                (!a. X a ==> ~drv_in a ctl (8 * nctl)) /\
                (!a. X a ==> !r. tisa_readable (tisa_decls (progs (val(EL 0 (h:int64 list))))) r
                                 ==> ~drv_in a (drv_base bw h r) (val(drv_len bw h r)))`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[drv_unread; MEM] o check (is_app "drv_unread")) THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DRV_UNREAD_TL o check (is_app "drv_unread")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[drv_layout] o check (is_app "drv_layout"));;

let DRV_SEM_FUN_X = prove(DRV_SEM_FUN_X_GOAL,
  let pt = list_mk_icomb "tisa_patch" [DRV_SEM_FUN_X_PFREE; `tmem t2`; `u1:tisa_state`] in
  DRV_SEM_FUN_X_TAC1 THEN
  MP_TAC(SPECL [`pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`; `nctl:num`;
                `bind:int64`; `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`;
                `progs:num->tisa_prog`; `bw:num->int64`; `budget:int64`; `used:int64`; `h:int64 list`;
                `X:int64->bool`; `m1:int64->byte`; `m2:int64->byte`] DRV_INPUTS_SAME_X) THEN
  ASM_REWRITE_TAC[IMP_CONJ] THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `nctl:num`; `bind:int64`;
                `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`;
                `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `used:int64`;
                `h:int64 list`; `m1:int64->byte`; `t1:tisa_state`; `X:int64->bool`] DRV_FREE_APART_X) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  (* the second child is the first with its free and X bytes changed; so is its run *)
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `X:int64->bool`; `h:int64 list`;
                `m1:int64->byte`; `m2:int64->byte`; `used:int64`; `t1:tisa_state`; `t2:tisa_state`]
               DRV_CHILD_PATCH_X) THEN
  ASM_REWRITE_TAC[IMP_CONJ] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun ceq ->
    MP_TAC(ISPECL [`progs (val(EL 0 (h:int64 list))):tisa_prog`; DRV_SEM_FUN_X_PFREE; `tmem t2`; `t1:tisa_state`]
                  TISA_RUN_PATCH) THEN
    REWRITE_TAC[GSYM ceq]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[tisa_rpatch; injectivity "tisa_result"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) THEN
  (* the patched set lies apart from the result's frame *)
  SUBGOAL_THEN (mk_icomb(mk_icomb(`tisa_fapart`, DRV_SEM_FUN_X_PFREE), `u1:tisa_state`)) ASSUME_TAC THENL
   [SUBGOAL_THEN `tregs u1 0 = tregs t1 0` ASSUME_TAC THENL
     [MP_TAC(SPECL [`progs (val(EL 0 (h:int64 list))):tisa_prog`; `t1:tisa_state`; `k1:num`;
                    `u1:tisa_state`] TISA_RUN_KEEPS) THEN
      ASM_SIMP_TAC[tisa_keeps];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS o
                check (fun th -> DRV_SEM_FUN_X_IS_APP "drv_child" th &&
                                 can (find_term ((=) `t1:tisa_state`)) (concl th))) THEN
    ASM_REWRITE_TAC[tisa_fapart] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `a:int64` THEN BETA_TAC THEN REWRITE_TAC[drv_free] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[CONJUNCT2 th]) ASSUME_TAC) THEN
    SUBGOAL_THEN `~drv_stack cfr (a:int64)` MP_TAC THENL [ASM_SIMP_TAC[]; REWRITE_TAC[drv_stack] THEN ARITH_TAC];
    ALL_TAC] THEN
  (* the result's frame words, and its memory outside the stack and X *)
  SUBGOAL_THEN (mk_forall(`j:num`, mk_imp(`j < 24`,
                 mk_eq(list_mk_icomb "tisa_fword" [pt; `j:num`], `tisa_fword u1 j`))))
  ASSUME_TAC THENL [ASM_SIMP_TAC[TISA_FWORD_PATCH]; ALL_TAC] THEN
  SUBGOAL_THEN (mk_conj(mk_eq(list_mk_icomb "tisa_fword" [pt; `18`], `tisa_fword u1 18`),
                        mk_eq(list_mk_icomb "tisa_fword" [pt; `21`], `tisa_fword u1 21`)))
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_forall(`a:int64`, mk_imp(`~drv_stack cfr a /\ ~(X:int64->bool) a`,
                 mk_eq(list_mk_icomb "drv_after" [`ctl:int64`; `h:int64 list`; pt; `a:int64`],
                       `drv_after ctl h u1 a`))))
  ASSUME_TAC THENL
   [REWRITE_TAC[drv_after] THEN
    SUBGOAL_THEN (mk_eq(list_mk_icomb "tisa_fword" [pt; `19`], `tisa_fword u1 19`)) SUBST1_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC DRV_WRITE_CONG THEN REWRITE_TAC[TISA_PATCH_MEM; drv_free] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM IMP_CONJ] THEN
  ASM_CASES_TAC `tisa_fword u1 18 = word 1` THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN ASM_REWRITE_TAC[] THENL
   [REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
       can (find_term ((=) `drv_sem`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`i + 1`; `drv_after ctl h u1`;
                          list_mk_icomb "drv_after" [`ctl:int64`; `h:int64 list`; pt];
                          `tisa_fword u1 21`] THEN
    ASM_REWRITE_TAC[];
    REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[FST; SND]]);;

let driver_det_x_theorems =
 ["DRV_UNREAD_TL", DRV_UNREAD_TL; "DRV_CW_SAME_X", DRV_CW_SAME_X; "DRV_INPUTS_SAME_X", DRV_INPUTS_SAME_X;
  "DRV_CHILD_PATCH_X", DRV_CHILD_PATCH_X; "DRV_FREE_APART_X", DRV_FREE_APART_X; "DRV_SEM_FUN_X", DRV_SEM_FUN_X];;
