(* ========================================================================= *)
(* A record's plan run is the driver's canonical run. The record loop runs   *)
(* a plan (rec_plan) from its own memory, with the allowance and the receipt *)
(* written into the plan's descriptor. If that memory agrees with mC outside *)
(* the record loop's stack, the run ends as the driver's run from mC with   *)
(* the same two writes: the same outcome and receipt, and a final memory    *)
(* that agrees outside the stack (REC_PLAN_FUN). The bytes of the record    *)
(* loop's stack beyond the driver's must be unread by the plan (drv_unread). *)
(*                                                                           *)
(* Loaded after records.ml.                                                  *)
(* ========================================================================= *)

needs "native/driver/driver_det_x.ml";;

(* Two writes over memories that agree outside the record loop's stack. *)
let REC_W2_CONG_TAC m mC x1 v1 x2 v2 =
  MP_TAC(BETA_RULE(ISPECL [`\a:int64. ~rec_stack E a`; m; mC; x2; v2] DRV_WRITE_CONG)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`\a:int64. ~rec_stack E a`;
                           list_mk_icomb "write" [mk_comb(`bytes64`, x2); v2; m];
                           list_mk_icomb "write" [mk_comb(`bytes64`, x2); v2; mC]; x1; v1] DRV_WRITE_CONG)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];;

let REC_PLAN_FUN = prove
 (`!progs pc plan ns nctl bind nbw leaves nl lpc lmc bw ctl budget E pl d m mC used r resC.
     drv_layout pc (word_sub E (word 312)) d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     (!j. j < nl ==> tisa_leaf_wf (progs j)) /\
     ALL (drv_step_ok progs pc (word_sub E (word 312)) d plan ns nctl bind nbw leaves nl lpc lmc bw) (pl d) /\
     drv_unread progs bw ctl nctl (word_sub E (word 312)) (pl d)
                (\a. rec_stack E a /\ ~drv_stack (word_sub E (word 312)) a) /\
     (!a. drv_stack (word_sub E (word 312)) a ==> rec_stack E a) /\
     (!a. drv_in a d 64 ==> ~rec_stack E a) /\ val d + 64 <= 2 EXP 64 /\
     (!a. ~rec_stack E a ==> m a = mC a) /\
     drv_sem progs bw ctl budget (word_sub E (word 312)) (pl d) 0
             (write (bytes64 (word_add d (word 48))) used (write (bytes64 (word_add d (word 40))) budget mC))
             used resC /\
     rec_plan progs bw ctl budget E pl d m used r
     ==> FST r = FST resC /\ SND(SND r) = SND(SND(SND resC)) /\
         (!a. ~rec_stack E a ==> FST(SND r) a = drv_final d (drv_word mC d) resC a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rec_plan] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m':int64->byte` (X_CHOOSE_THEN `res:int64#num#(int64->byte)#int64`
    STRIP_ASSUME_TAC) o check (is_exists o concl)) THEN
  ABBREV_TAC `cfr:int64 = word_sub E (word 312)` THEN
  (* m' agrees with the canonical start outside the record loop's stack *)
  SUBGOAL_THEN `!a. ~drv_stack cfr a /\ ~(\a. rec_stack E a /\ ~drv_stack cfr a) a
                    ==> m' a = write (bytes64 (word_add d (word 48))) used
                                 (write (bytes64 (word_add d (word 40))) budget mC) a`
    ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN BETA_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `~rec_stack E (a:int64)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    REC_W2_CONG_TAC `m:int64->byte` `mC:int64->byte` `word_add d (word 48):int64` `used:int64`
                   `word_add d (word 40):int64` `budget:int64`;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`progs:num->tisa_prog`; `pc:num`; `d:int64`; `plan:int64`; `ns:num`; `nctl:num`; `bind:int64`;
                 `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`; `bw:num->int64`;
                 `ctl:int64`; `budget:int64`; `cfr:int64`; `\a. rec_stack E a /\ ~drv_stack cfr a`;
                 `(pl:int64->(int64 list)list) d`; `0`;
                 `write (bytes64 (word_add d (word 48))) used (write (bytes64 (word_add d (word 40))) budget mC)`;
                 `m':int64->byte`; `used:int64`; `resC:int64#num#(int64->byte)#int64`;
                 `res:int64#num#(int64->byte)#int64`] DRV_SEM_FUN_X) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[FST; SND] THEN
  (* the final memory *)
  SUBGOAL_THEN `drv_word m d = drv_word mC (d:int64)` SUBST1_TAC THENL
   [MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `mC:int64->byte`)) (concl th) &&
      not(can (find_term (fun t -> try fst(dest_const t) = "write" with _ -> false)) (concl th)))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[drv_in] THEN
    MP_TAC(SPECL [`d:int64`; `i:num`] TISA_VAL_OFFSET) THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. ~rec_stack E a ==> FST(SND(SND(res:int64#num#(int64->byte)#int64))) a =
                                       FST(SND(SND(resC:int64#num#(int64->byte)#int64))) a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[drv_final] THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  REC_W2_CONG_TAC `FST(SND(SND(res:int64#num#(int64->byte)#int64)))` `FST(SND(SND(resC:int64#num#(int64->byte)#int64)))`
    `word_add d (word 56):int64` `word_add (drv_word mC d) (word(144 * FST(SND(resC:int64#num#(int64->byte)#int64))))`
    `word_add d (word 48):int64` `SND(SND(SND(resC:int64#num#(int64->byte)#int64)))`);;

let records_fun_theorems = ["REC_PLAN_FUN", REC_PLAN_FUN];;
