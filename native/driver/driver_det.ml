(* ========================================================================= *)
(* The driver's outcome is a function of the plan's memory outside its      *)
(* stack. drv_child fixes the child's registers, its 24 frame words and the *)
(* memory outside the driver's stack, and leaves the other stack bytes      *)
(* (drv_free) to the child's choice; a leaf's run neither reads nor writes  *)
(* them (TISA_EXEC_PATCH). So two runs of a plan from memories that agree   *)
(* outside the stack end with the same outcome, step index and receipt, and *)
(* with memories that agree outside the stack (DRV_SEM_FUN).                 *)
(*                                                                           *)
(* Loaded after driver.ml.                                                   *)
(* ========================================================================= *)

needs "tisa/hol/tisa_p1_noninterference.ml";;

(* The driver's stack outside the child frame. *)
let drv_free = new_definition
 `drv_free (cfr:int64) (a:int64) <=>
    drv_stack cfr a /\ ~(val cfr <= val a /\ val a < val cfr + 192)`;;

let TISA_STATE_ETA = prove
 (`!t. TState (tregs t) (tmem t) = t`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `t:tisa_state` (cases "tisa_state")) THEN
  REWRITE_TAC[tregs; tmem]);;

(* ------------------------------------------------------------------------- *)
(* Entry validation reads only the registers and the frame words.           *)
(* ------------------------------------------------------------------------- *)

let TISA_PAIRS_OK_SAME = prove
 (`!ds mode b l q s1 s2.
     q + LENGTH ds <= 12 /\ (!i. i < 24 ==> tisa_fword s2 i = tisa_fword s1 i)
     ==> (tisa_pairs_ok s2 mode b l q ds <=> tisa_pairs_ok s1 mode b l q ds)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[tisa_pairs_ok; LENGTH] THEN REPEAT STRIP_TAC THEN
  BINOP_TAC THENL
   [REWRITE_TAC[tisa_base; tisa_len] THEN
    SUBGOAL_THEN `2 * q < 24 /\ 2 * q + 1 < 24` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let TISA_DECLS_OK_SAME = prove
 (`!ds r s1 s2.
     r + LENGTH ds <= 12 /\ tregs s2 0 = tregs s1 0 /\
     (!i. i < 24 ==> tisa_fword s2 i = tisa_fword s1 i)
     ==> (tisa_decls_ok s2 r ds <=> tisa_decls_ok s1 r ds)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[tisa_decls_ok; LENGTH] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `tisa_base s2 r = tisa_base s1 r /\ tisa_len s2 r = tisa_len s1 r /\
                tisa_frame s2 = tisa_frame s1` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[tisa_base; tisa_len; tisa_frame] THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(tisa_pairs_ok s2 (FST(h:num#num#num)) (val(tisa_base s1 r)) (val(tisa_len s1 r)) (r + 1) t <=>
                 tisa_pairs_ok s1 (FST h) (val(tisa_base s1 r)) (val(tisa_len s1 r)) (r + 1) t) /\
                (tisa_decls_ok s2 (r + 1) t <=> tisa_decls_ok s1 (r + 1) t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC TISA_PAIRS_OK_SAME THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ASM_REWRITE_TAC[]]);;

let TISA_ENTRY_OK_SAME = prove
 (`!prog s1 s2.
     tisa_leaf_wf prog /\ tregs s2 0 = tregs s1 0 /\
     (!i. i < 24 ==> tisa_fword s2 i = tisa_fword s1 i)
     ==> (tisa_entry_ok prog s2 <=> tisa_entry_ok prog s1)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[TISA_PROG_CASES] THEN
  REWRITE_TAC[tisa_leaf_wf; tisa_decls; tisa_inits; tisa_root; tisa_entry_ok] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[TISA_INIT_U64] THEN
  SUBGOAL_THEN `tisa_fword s2 20 = tisa_fword s1 20 /\ tisa_fword s2 21 = tisa_fword s1 21`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `tisa_decls_ok s2 0 (tisa_decls prog) <=> tisa_decls_ok s1 0 (tisa_decls prog)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_DECLS_OK_SAME THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[tisa_frame]);;

(* ------------------------------------------------------------------------- *)
(* A run commutes with a change of memory apart from what it touches.       *)
(* ------------------------------------------------------------------------- *)

let TISA_RUN_PATCH = prove
 (`!prog P g t.
     tisa_leaf_wf prog /\ tisa_entry_ok prog t /\ tisa_apart (tisa_decls prog) P t
     ==> tisa_run prog (tisa_patch P g t) = tisa_rpatch P g (tisa_run prog t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `tisa_frame_sep (tisa_decls prog) t` ASSUME_TAC THENL
   [UNDISCH_TAC `tisa_entry_ok prog t` THEN UNDISCH_TAC `tisa_leaf_wf prog` THEN
    ONCE_REWRITE_TAC[TISA_PROG_CASES] THEN
    REWRITE_TAC[tisa_leaf_wf; tisa_decls; tisa_inits; tisa_root] THEN
    MESON_TAC[TISA_ENTRY_FRAME_SEP];
    ALL_TAC] THEN
  SUBGOAL_THEN `tisa_fapart (P:int64->bool) t` ASSUME_TAC THENL
   [ASM_MESON_TAC[TISA_APART_FAPART]; ALL_TAC] THEN
  SUBGOAL_THEN `tisa_entry_ok prog (tisa_patch P g t)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`prog:tisa_prog`; `t:tisa_state`; `tisa_patch P g t`] TISA_ENTRY_OK_SAME) THEN
    ASM_SIMP_TAC[TISA_PATCH_REGS; TISA_FWORD_PATCH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[tisa_run] THEN
  MP_TAC(SPECL [`tisa_root prog`; `tisa_decls prog`; `P:int64->bool`; `g:int64->byte`; `t:tisa_state`]
               TISA_EXEC_PATCH) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[tisa_leaf_wf]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC TISA_THEN_PATCH THEN X_GEN_TAC `u:tisa_state` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC TISA_FAIL_PATCH THEN MATCH_MP_TAC TISA_APART_FAPART THEN
  EXISTS_TAC `tisa_decls prog` THEN MATCH_MP_TAC TISA_KEEPS_SEP_APART THEN
  EXISTS_TAC `t:tisa_state` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`tisa_root prog`; `tisa_decls prog`; `t:tisa_state`] TISA_KEEPS_EXEC) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[tisa_leaf_wf]; ASM_REWRITE_TAC[tisa_state_of]]);;

(* ------------------------------------------------------------------------- *)
(* The frame's bytes are fixed by its 24 words.                              *)
(* ------------------------------------------------------------------------- *)

let READ_BYTES8_BOUND = prove
 (`!(a:int64) (m:int64->byte). read (bytes(a,8)) m < 2 EXP 64`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL [`a:int64`; `8`; `m:int64->byte`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let TISA_FRAME_BYTES_SAME = prove
 (`!s1 s2 a.
     tregs s2 0 = tregs s1 0 /\ val(tregs s1 0) + 192 <= 2 EXP 64 /\
     (!i. i < 24 ==> tisa_fword s2 i = tisa_fword s1 i) /\
     val(tregs s1 0) <= val a /\ val a < val(tregs s1 0) + 192
     ==> tmem s2 a = tmem s1 a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `n = val(a:int64) - val(tregs s1 0)` THEN
  SUBGOAL_THEN `n DIV 8 < 24 /\ n MOD 8 < 8 /\ 8 * n DIV 8 + n MOD 8 = n` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`n:num`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add (tregs s1 0) (word(8 * n DIV 8)):int64) = val(tregs s1 0) + 8 * n DIV 8`
  ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a = word_add (word_add (tregs s1 0) (word(8 * n DIV 8))) (word(n MOD 8)):int64`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ] THEN
    SUBGOAL_THEN `val(word_add (word_add (tregs s1 0) (word(8 * n DIV 8))) (word(n MOD 8)):int64) =
                  val(word_add (tregs s1 0) (word(8 * n DIV 8)):int64) + n MOD 8` SUBST1_TAC THENL
     [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n DIV 8` o check (fun th -> is_forall(concl th))) THEN
  ASM_REWRITE_TAC[tisa_fword; tisa_read; tisa_frame] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN SIMP_TAC[MOD_LT; READ_BYTES8_BOUND] THEN
  REWRITE_TAC[READ_BYTES_EQ] THEN DISCH_THEN(MP_TAC o SPEC `n MOD 8`) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The child: its inputs are read outside the stack, so two children of     *)
(* memories that agree outside the stack differ only in the free bytes.     *)
(* ------------------------------------------------------------------------- *)

let DRV_CW_SAME = prove
 (`!cfr ctl nctl m1 m2 (k:int64).
     48 <= val cfr /\ drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl) /\
     val ctl + 8 * nctl <= 2 EXP 64 /\ val k < nctl /\
     (!a. ~drv_stack cfr a ==> m2 a = m1 a)
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
  MATCH_MP_TAC DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [`ctl:int64`; `8 * nctl`] THEN
  ASM_SIMP_TAC[]);;

let DRV_INPUTS_SAME = prove
 (`!pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc progs bw budget used st m1 m2.
     drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     drv_step_ok progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw st /\
     (!a. ~drv_stack cfr a ==> m2 a = m1 a)
     ==> drv_regs cfr ctl st m2 = drv_regs cfr ctl st m1 /\
         (!j. j < 24 ==> drv_fw bw ctl budget used st m2 j = drv_fw bw ctl budget used st m1 j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_layout; drv_step_ok] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!f. 10 <= f /\ f < 18 ==> drv_cw ctl m2 (EL f st) = drv_cw ctl m1 (EL f st)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_CW_SAME THEN
    MAP_EVERY EXISTS_TAC [`cfr:int64`; `nctl:num`] THEN ASM_SIMP_TAC[];
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

let DRV_CHILD_PATCH = prove
 (`!bw ctl budget cfr st m1 m2 used t1 t2.
     val cfr + 192 <= 2 EXP 64 /\
     drv_child bw ctl budget cfr st m1 used t1 /\ drv_child bw ctl budget cfr st m2 used t2 /\
     drv_regs cfr ctl st m2 = drv_regs cfr ctl st m1 /\
     (!j. j < 24 ==> drv_fw bw ctl budget used st m2 j = drv_fw bw ctl budget used st m1 j) /\
     (!a. ~drv_stack cfr a ==> m2 a = m1 a)
     ==> t2 = tisa_patch (drv_free cfr) (tmem t2) t1`,
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
   [COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC TISA_FRAME_BYTES_SAME THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[drv_regs];
    ASM_SIMP_TAC[]]);;

(* The free bytes lie apart from what the step's leaf may touch. *)
let DRV_FREE_APART = prove
 (`!pc cfr d plan ns nctl bind nbw leaves nl lpc lmc progs bw ctl budget used st m t.
     48 <= val cfr /\
     drv_step_ok progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw st /\
     tisa_leaf_wf (progs (val(EL 0 st))) /\
     drv_child bw ctl budget cfr st m used t
     ==> tisa_apart (tisa_decls (progs (val(EL 0 st)))) (drv_free cfr) t`,
  REWRITE_TAC[drv_step_ok; tisa_leaf_wf] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  MP_TAC(SPECL [`cfr:int64`; `48`] TISA_VAL_SP_SUB) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[tisa_apart; tisa_touch; drv_free; drv_stack] THEN
  X_GEN_TAC `a:int64` THEN STRIP_TAC THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `r < 9` ASSUME_TAC THENL
   [UNDISCH_TAC `tisa_readable (tisa_decls (progs (val(EL 0 (st:int64 list))))) r` THEN
    REWRITE_TAC[tisa_readable] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
     can (find_term ((=) `tisa_base`)) (concl th) && can (find_term ((=) `drv_base`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
     can (find_term ((=) `tisa_readable`)) (concl th) && can (find_term ((=) `drv_apart`)) (concl th))) THEN
  ASM_REWRITE_TAC[drv_apart] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The driver's semantics, functional up to the stack.                       *)
(* ------------------------------------------------------------------------- *)

let DRV_SEM_FUN = prove
 (`!progs pc d plan ns nctl bind nbw leaves nl lpc lmc bw ctl budget cfr sts i m1 m2 used res1 res2.
     drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     (!j. j < nl ==> tisa_leaf_wf (progs j)) /\
     ALL (drv_step_ok progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw) sts /\
     (!a. ~drv_stack cfr a ==> m2 a = m1 a) /\
     drv_sem progs bw ctl budget cfr sts i m1 used res1 /\
     drv_sem progs bw ctl budget cfr sts i m2 used res2
     ==> FST res2 = FST res1 /\ FST(SND res2) = FST(SND res1) /\
         SND(SND(SND res2)) = SND(SND(SND res1)) /\
         (!a. ~drv_stack cfr a ==> FST(SND(SND res2)) a = FST(SND(SND res1)) a)`,
  let is_app name th = try fst(dest_const(fst(strip_comb(concl th)))) = name with Failure _ -> false in
  let pfree = `drv_free cfr` in
  REPLICATE_TAC 16 GEN_TAC THEN LIST_INDUCT_TAC THENL
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
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[drv_layout] o check (is_app "drv_layout")) THEN
  MP_TAC(SPECL [`pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`; `nctl:num`;
                `bind:int64`; `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`;
                `progs:num->tisa_prog`; `bw:num->int64`; `budget:int64`; `used:int64`; `h:int64 list`;
                `m1:int64->byte`; `m2:int64->byte`] DRV_INPUTS_SAME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `nctl:num`; `bind:int64`;
                `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`;
                `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `used:int64`;
                `h:int64 list`; `m1:int64->byte`; `t1:tisa_state`] DRV_FREE_APART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the second child is the first with its free bytes changed; so is its run *)
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `h:int64 list`;
                `m1:int64->byte`; `m2:int64->byte`; `used:int64`; `t1:tisa_state`; `t2:tisa_state`]
               DRV_CHILD_PATCH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun ceq ->
    MP_TAC(ISPECL [`progs (val(EL 0 (h:int64 list))):tisa_prog`; pfree; `tmem t2`; `t1:tisa_state`]
                  TISA_RUN_PATCH) THEN
    REWRITE_TAC[GSYM ceq]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[tisa_rpatch; injectivity "tisa_result"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) THEN
  (* the result's frame words, and its memory outside the stack *)
  SUBGOAL_THEN `tisa_fapart (drv_free cfr) u1` ASSUME_TAC THENL
   [SUBGOAL_THEN `tregs u1 0 = tregs t1 0` ASSUME_TAC THENL
     [MP_TAC(SPECL [`progs (val(EL 0 (h:int64 list))):tisa_prog`; `t1:tisa_state`; `k1:num`;
                    `u1:tisa_state`] TISA_RUN_KEEPS) THEN
      ASM_SIMP_TAC[tisa_keeps];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS o
                check (fun th -> is_app "drv_child" th && can (find_term ((=) `t1:tisa_state`)) (concl th))) THEN
    ASM_REWRITE_TAC[tisa_fapart; drv_free] THEN CONJ_TAC THENL [ASM_ARITH_TAC; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. j < 24 ==> tisa_fword (tisa_patch (drv_free cfr) (tmem t2) u1) j = tisa_fword u1 j`
  ASSUME_TAC THENL [ASM_SIMP_TAC[TISA_FWORD_PATCH]; ALL_TAC] THEN
  SUBGOAL_THEN `tisa_fword (tisa_patch (drv_free cfr) (tmem t2) u1) 18 = tisa_fword u1 18 /\
                tisa_fword (tisa_patch (drv_free cfr) (tmem t2) u1) 21 = tisa_fword u1 21`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!a. ~drv_stack cfr a
                    ==> drv_after ctl h (tisa_patch (drv_free cfr) (tmem t2) u1) a = drv_after ctl h u1 a`
  ASSUME_TAC THENL
   [REWRITE_TAC[drv_after] THEN
    SUBGOAL_THEN `tisa_fword (tisa_patch (drv_free cfr) (tmem t2) u1) 19 = tisa_fword u1 19` SUBST1_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC DRV_WRITE_CONG THEN REWRITE_TAC[TISA_PATCH_MEM; drv_free] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `tisa_fword u1 18 = word 1` THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN ASM_REWRITE_TAC[] THENL
   [REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
       can (find_term ((=) `drv_sem`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`i + 1`; `drv_after ctl h u1`;
                          `drv_after ctl h (tisa_patch (drv_free cfr) (tmem t2) u1)`; `tisa_fword u1 21`] THEN
    ASM_REWRITE_TAC[];
    REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[FST; SND]]);;
