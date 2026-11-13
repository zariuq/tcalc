(* ========================================================================= *)
(* The driver with intern16 as its leaf: a plan of two steps that interns    *)
(* two keys in one interner.                                                 *)
(*                                                                           *)
(* The leaf premises of DRV_CORRECT are discharged from intern16's image     *)
(* theorem (INTERN16_LEAF_SPEC) and by computation (INTERN16_LEAF_WF). The   *)
(* interning guarantee is INTERN16_TISA_RUN_COMPLETE, applied to each step:  *)
(* after a plan whose two steps both FIRED, both keys are rows of a          *)
(* well-formed interner, and the two ids are equal exactly when the keys     *)
(* are (DRV_INTERN16_TWO; DRV_INTERN16_X86 for the native run).              *)
(*                                                                           *)
(* Loaded after the intern16 image record (intern16b.hol), intern16_join.ml, *)
(* intern16_complete.ml, driver_leaf.ml and driver.ml.                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The leaf premises for intern16.                                           *)
(* ------------------------------------------------------------------------- *)

let INTERN16_MC_LENGTH =
  COMPUTE_LENGTH_RULE
    (find (fun th -> try fst(dest_const(lhs(concl th))) = "intern16_mc" with Failure _ -> false)
          (definitions()));;

let INTERN16_DECLS = prove
 (`tisa_decls intern16 = [(2,16,8); (2,8,8); (2,8,8)]`,
  REWRITE_TAC[intern16; tisa_decls]);;

let INTERN16_REGION_KINDS = prove
 (`!r. (tisa_rw (tisa_decls intern16) r <=> r < 3) /\
       (tisa_readable (tisa_decls intern16) r <=> r < 3)`,
  GEN_TAC THEN REWRITE_TAC[INTERN16_DECLS; tisa_rw; tisa_readable; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_CASES_TAC `r < 3` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o
    REWRITE_RULE[ARITH_RULE `r < 3 <=> r = 0 \/ r = 1 \/ r = 2`]) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[FST] THEN CONV_TAC NUM_REDUCE_CONV);;

let INTERN16_LEAF_WF = prove
 (`tisa_leaf_wf intern16`,
  REWRITE_TAC[tisa_leaf_wf; INTERN16_DECLS; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[intern16; intern16_prologue; intern16_body; tisa_root; tisa_inits; ALL;
              tisa_stmt_ok; tisa_instr_ok; REWRITE_RULE[INTERN16_DECLS] INTERN16_REGION_KINDS] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* intern16's image theorem, over the program's name. *)
let INTERN16_ENTRY_X86 = REWRITE_RULE[GSYM INTERN16_TERM] (assoc "intern16" !tisa_entry_thms);;

let INTERN16_LEAF_SPEC = prove
 (`!pc. tisa_leaf_spec intern16 intern16_mc pc`,
  GEN_TAC THEN REWRITE_TAC[tisa_leaf_spec; tisa_leaf_place; INTERN16_MC_LENGTH; INTERN16_REGION_KINDS] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC INTERN16_ENTRY_X86 THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV EXPAND_CASES_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tisa_base; tisa_len; ARITH_RULE
    `2 * 0 = 0 /\ 2 * 0 + 1 = 1 /\ 2 * 1 = 2 /\ 2 * 1 + 1 = 3 /\ 2 * 2 = 4 /\ 2 * 2 + 1 = 5`]) THEN
  ASM_REWRITE_TAC[]);;

(* A step of intern16 that FIRED returned with code 1. *)
let INTERN16_FIRED = prove
 (`!t k u. tisa_run intern16 t = TStop k u /\ tisa_fword u 18 = word 1 ==> k = 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP TISA_RUN_STATUS) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[intern16; intern16_prologue; intern16_body; tisa_root; tisa_returns] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `word k:int64`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

(* An intern16 run keeps the frame words below the status word: the regions
   lie apart from the frame and the run writes only them and words 18..21. *)
let INTERN16_RUN_FRAME = prove
 (`!t k u j. tisa_entry_ok intern16 t /\ tisa_run intern16 t = TStop k u /\ j < 18
             ==> tisa_fword u j = tisa_fword t j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`intern16`; `t:tisa_state`; `k:num`; `u:tisa_state`] TISA_RUN_KEEPS) THEN
  ASM_REWRITE_TAC[INTERN16_LEAF_WF; tisa_keeps] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INTERN16_ENTRY) THEN
  REWRITE_TAC[tisa_fword; tisa_read; tisa_frame] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[tisa_writable; INTERN16_REGION_KINDS; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  SUBGOAL_THEN `val(word_add (word_add (tregs t 0) (word(8 * j))) (word i):int64) =
                val(tregs t 0) + 8 * j + i` SUBST1_TAC THENL
   [SUBGOAL_THEN `val(word_add (tregs t 0) (word(8 * j)):int64) = val(tregs t 0) + 8 * j` ASSUME_TAC THENL
     [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`word_add (tregs t 0) (word(8 * j)):int64`; `i:num`] TISA_VAL_OFFSET) THEN
    ASM_REWRITE_TAC[ADD_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:num` THEN ASM_CASES_TAC `r < 3` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `192`)) (concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* An 8-byte read agrees when its bytes do. *)
let TISA_READ8_AGREE = prove
 (`!s t (a:int64). (!k. k < 8 ==> tmem t (word_add a (word k)) = tmem s (word_add a (word k)))
                   ==> tisa_read t a 8 = tisa_read s a 8`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_read] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[READ_BYTES_EQ]);;

(* A state with intern16's regions where s has them, and s's bytes in them,
   holds s's interner: well-formed when s's is, with s's count and rows. *)
let INTERN16_SAME_REGIONS = prove
 (`!s t. (!r. r < 3 ==> tisa_base t r = tisa_base s r /\ tisa_len t r = tisa_len s r) /\
         (!r. r < 3 ==> val(tisa_base s r) + val(tisa_len s r) < 2 EXP 64) /\
         8 <= val(tisa_len s 2) /\
         (!r a. r < 3 /\ val(tisa_base s r) <= val a /\ val a < val(tisa_base s r) + val(tisa_len s r)
                ==> tmem t a = tmem s a) /\
         intern_ok s
         ==> intern_ok t /\ intern_count t = intern_count s /\
             (!i. i < 2 * val(intern_count s) ==> intern_word t i = intern_word s i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* bytes at offset off + k of region r, off + 8 <= len r, agree *)
  SUBGOAL_THEN `!r off. r < 3 /\ off + 8 <= val(tisa_len s r)
                      ==> tisa_read t (word_add (tisa_base s r) (word off)) 8 =
                          tisa_read s (word_add (tisa_base s r) (word off)) 8`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_READ8_AGREE THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `2 EXP 64`)) (concl th))) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base s r) (word off):int64) = val(tisa_base s r) + off` ASSUME_TAC THENL
     [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`word_add (tisa_base s r) (word off):int64`; `k:num`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `intern_count t = intern_count s` ASSUME_TAC THENL
   [REWRITE_TAC[intern_count] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`2`; `0`]) THEN ASM_REWRITE_TAC[ARITH; WORD_ADD_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `2` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_base t r`)) (concl th))) THEN
    REWRITE_TAC[ARITH] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < 2 * val(intern_count s) ==> intern_word t i = intern_word s i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[intern_word] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_base t r`)) (concl th))) THEN
    REWRITE_TAC[ARITH] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ARITH] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [intern_ok] o
      check (fun th -> can (find_term ((=) `intern_ok`)) (concl th))) THEN
    UNDISCH_TAC `i < 2 * val(intern_count s)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTERN_OK_TRANSFER THEN EXISTS_TAC `s:tisa_state` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_base t r`)) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `1` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_base t r`)) (concl th))) THEN
  REWRITE_TAC[ARITH] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[intern_slots] THEN
  REWRITE_TAC[intern_slot] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ARITH] THEN
  UNDISCH_TAC `val(p:int64) < val(intern_slots s)` THEN REWRITE_TAC[INTERN_SLOTS_VAL] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Two steps that both FIRED, unfolded.                                      *)
(* ------------------------------------------------------------------------- *)

let DRV_SEM_TWO_FIRED = prove
 (`!progs bw ctl budget cfr st1 st2 m used res.
     drv_sem progs bw ctl budget cfr [st1; st2] 0 m used res /\ FST res = word 1
     ==> ?t1 k1 u1 t2 k2 u2.
           drv_child bw ctl budget cfr st1 m used t1 /\
           tisa_entry_ok (progs (val(EL 0 st1))) t1 /\
           tisa_run (progs (val(EL 0 st1))) t1 = TStop k1 u1 /\ tisa_fword u1 18 = word 1 /\
           drv_child bw ctl budget cfr st2 (drv_after ctl st1 u1) (tisa_fword u1 21) t2 /\
           tisa_entry_ok (progs (val(EL 0 st2))) t2 /\
           tisa_run (progs (val(EL 0 st2))) t2 = TStop k2 u2 /\ tisa_fword u2 18 = word 1 /\
           res = (word 1, 2, drv_after ctl st2 u2, tisa_fword u2 21)`,
  let NOT_FIRED_TAC =
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `res:int64#num#(int64->byte)#int64`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `FST:int64#num#(int64->byte)#int64->int64`))
                                                 (concl th))) THEN
    ASM_REWRITE_TAC[FST] THEN CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[] in
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_sem] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `val(budget:int64) < val(used:int64)` THEN ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN NOT_FIRED_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
       STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  ASM_CASES_TAC `tisa_fword u1 18 = word 1` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; DISCH_TAC THEN NOT_FIRED_TAC] THEN
  ASM_CASES_TAC `val(budget:int64) < val(tisa_fword u1 21)` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN NOT_FIRED_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
       STRIP_ASSUME_TAC))) THEN
  ASM_CASES_TAC `tisa_fword u2 18 = word 1` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THENL [ALL_TAC; NOT_FIRED_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t1:tisa_state`; `k1:num`; `u1:tisa_state`;
                        `t2:tisa_state`; `k2:num`; `u2:tisa_state`] THEN
  ASM_REWRITE_TAC[]);;

let DRV_APART_SYM = prove
 (`!(a:int64) m (b:int64) n. drv_apart a m b n <=> drv_apart b n a m`,
  REWRITE_TAC[drv_apart] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* DRV_INTERN16_TWO: a plan of two intern16 steps on one interner. When both *)
(* FIRED, the interner left by the second is well-formed, both keys are rows *)
(* of it at the ids the steps returned, and the ids are equal exactly when   *)
(* the keys are. The second step sees the first's interner: the regions lie  *)
(* apart from the driver's stack and the control words.                      *)
(* ------------------------------------------------------------------------- *)

let DRV_INTERN16_TWO = prove
 (`!bw ctl nctl budget cfr st1 st2 m used res.
     drv_sem (\j. intern16) bw ctl budget cfr [st1; st2] 0 m used res /\
     FST res = word 1 /\
     EL 1 st2 = EL 1 st1 /\ EL 2 st2 = EL 2 st1 /\ EL 3 st2 = EL 3 st1 /\
     48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\ val(EL 17 st1) < nctl /\
     (!r. r < 3
          ==> drv_apart (drv_base bw st1 r) (val(drv_len bw st1 r)) (word_sub cfr (word 48)) 304 /\
              drv_apart (drv_base bw st1 r) (val(drv_len bw st1 r)) ctl (8 * nctl)) /\
     (!t. drv_child bw ctl budget cfr st1 m used t ==> intern_ok t)
     ==> ?t1 u1 t2 u2.
           drv_child bw ctl budget cfr st1 m used t1 /\ tisa_run intern16 t1 = TStop 1 u1 /\
           drv_child bw ctl budget cfr st2 (drv_after ctl st1 u1) (tisa_fword u1 21) t2 /\
           tisa_run intern16 t2 = TStop 1 u2 /\
           res = (word 1, 2, drv_after ctl st2 u2, tisa_fword u2 21) /\
           intern_ok u2 /\
           intern_has u2 (val(tisa_fword u1 19)) (tisa_fword t1 22) (tisa_fword t1 23) /\
           intern_has u2 (val(tisa_fword u2 19)) (tisa_fword t2 22) (tisa_fword t2 23) /\
           (tisa_fword u1 19 = tisa_fword u2 19 <=>
            tisa_fword t1 22 = tisa_fword t2 22 /\ tisa_fword t1 23 = tisa_fword t2 23)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\j:num. intern16`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`;
                 `st1:int64 list`; `st2:int64 list`; `m:int64->byte`; `used:int64`;
                 `res:int64#num#(int64->byte)#int64`] DRV_SEM_TWO_FIRED) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    (X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
      STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `k1 = 1 /\ k2 = 1` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTERN16_FIRED THENL
     [MAP_EVERY EXISTS_TAC [`t1:tisa_state`; `u1:tisa_state`];
      MAP_EVERY EXISTS_TAC [`t2:tisa_state`; `u2:tisa_state`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t1:tisa_state`; `u1:tisa_state`; `t2:tisa_state`; `u2:tisa_state`] THEN
  ASM_REWRITE_TAC[] THEN
  (* Step 1: the interner it leaves. *)
  MP_TAC(SPECL [`t1:tisa_state`; `1`; `u1:tisa_state`] INTERN16_TISA_RUN_COMPLETE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; REWRITE_TAC[] THEN STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INTERN16_ENTRY o
    check (fun th -> concl th = `tisa_entry_ok intern16 t1`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS o
    check (fun th -> concl th = `drv_child bw ctl budget cfr st1 m used t1`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS o
    check (fun th -> concl th = `drv_child bw ctl budget cfr st2 (drv_after ctl st1 u1)
                                   (tisa_fword u1 21) t2`)) THEN
  (* Step 2 sees step 1's interner. *)
  SUBGOAL_THEN `!r. r < 3 ==> tisa_base u1 r = drv_base bw st1 r /\ tisa_len u1 r = drv_len bw st1 r /\
                              tisa_base t2 r = drv_base bw st1 r /\ tisa_len t2 r = drv_len bw st1 r`
  ASSUME_TAC THENL
   [MAP_EVERY (fun c -> FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
                          check (fun th -> concl th = c)))
      [`drv_child bw ctl budget cfr st1 m used t1`;
       `drv_child bw ctl budget cfr st2 (drv_after ctl st1 u1) (tisa_fword u1 21) t2`] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
    REWRITE_TAC[tisa_base; tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    TRY(W(fun (asl,w) -> let j = rand(lhs w) in
       MP_TAC(SPECL [`t1:tisa_state`; `1`; `u1:tisa_state`; j] INTERN16_RUN_FRAME) THEN
       ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC)) THEN
    ASM_SIMP_TAC[ARITH] THEN REWRITE_TAC[drv_fw; drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(SPECL [`u1:tisa_state`; `t2:tisa_state`] INTERN16_SAME_REGIONS) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `2 EXP 64`)) (concl th) && can (find_term ((=) `t1:tisa_state`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      ASM_SIMP_TAC[ARITH_RULE `r < 3 ==> r < 9`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `2` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `drv_len bw st1 r`)) (concl th) && can (find_term ((=) `u1:tisa_state`)) (concl th))) THEN
      REWRITE_TAC[ARITH] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `2` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `r < 9`)) (concl th) && can (find_term ((=) `t1:tisa_state`)) (concl th))) THEN
      REWRITE_TAC[ARITH] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `8 <= val(tisa_len t1 2)`)) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`r:num`; `a:int64`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `drv_len bw st1 r`)) (concl th) && can (find_term ((=) `u1:tisa_state`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `drv_apart`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `tisa_base u1 r = drv_base bw st1 r`;
                                  ASSUME `tisa_len u1 r = drv_len bw st1 r`]) THEN
      SUBGOAL_THEN `~drv_stack cfr a` ASSUME_TAC THENL
       [MATCH_MP_TAC DRV_IN_NOT_STACK THEN
        MAP_EVERY EXISTS_TAC [`drv_base bw st1 r`; `val(drv_len bw st1 r)`] THEN
        ONCE_REWRITE_TAC[DRV_APART_SYM] THEN ASM_REWRITE_TAC[drv_in];
        ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> if concl th = `drv_child bw ctl budget cfr st2 (drv_after ctl st1 u1)
                                               (tisa_fword u1 21) t2`
                              then MP_TAC(CONJUNCT2(CONJUNCT2(GEN_REWRITE_RULE I [drv_child] th)))
                              else failwith "") THEN
      DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~drv_stack cfr a`)]) THEN
      REWRITE_TAC[drv_after] THEN MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN
      SUBGOAL_THEN `val(word_add ctl (word(8 * val(EL 17 (st1:int64 list)))):int64) =
                    val ctl + 8 * val(EL 17 st1)` SUBST1_TAC THENL
       [MATCH_MP_TAC TISA_VAL_OFFSET THEN
        UNDISCH_TAC `val(ctl:int64) + 8 * nctl <= 2 EXP 64` THEN
        UNDISCH_TAC `val(EL 17 (st1:int64 list)) < nctl` THEN ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `drv_apart (drv_base bw st1 r) (val(drv_len bw st1 r)) ctl (8 * nctl)` THEN
      REWRITE_TAC[drv_apart] THEN
      UNDISCH_TAC `val(ctl:int64) + 8 * nctl <= 2 EXP 64` THEN
      UNDISCH_TAC `val(EL 17 (st1:int64 list)) < nctl` THEN
      UNDISCH_TAC `val(drv_base bw st1 r) <= val(a:int64)` THEN
      UNDISCH_TAC `val(a:int64) < val(drv_base bw st1 r) + val(drv_len bw st1 r)` THEN
      ARITH_TAC];
    STRIP_TAC] THEN
  (* Step 2: the interner it leaves. *)
  MP_TAC(SPECL [`t2:tisa_state`; `1`; `u2:tisa_state`] INTERN16_TISA_RUN_COMPLETE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[] THEN STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [intern16_post] o
    check (fun th -> concl th = `intern16_post t2 u2`)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [intern16_post] o
    check (fun th -> concl th = `intern16_post t1 u1`)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `!i. i < 2 * val(intern_count u1) ==> intern_word u2 i = intern_word u1 i`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS `intern_word t2 i` THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `intern_has u2 (val(tisa_fword u1 19)) (tisa_fword t1 22) (tisa_fword t1 23)`
  ASSUME_TAC THENL
   [REWRITE_TAC[intern_has] THEN
    SUBGOAL_THEN `2 * val(tisa_fword u1 19) < 2 * val(intern_count u1) /\
                  2 * val(tisa_fword u1 19) + 1 < 2 * val(intern_count u1)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `val(tisa_fword u1 19) < val(intern_count u1)` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[intern_has] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[intern_has]) THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `intern_word u2 (2 * val(tisa_fword u2 19)) = tisa_fword t1 22 /\
                  intern_word u2 (2 * val(tisa_fword u2 19) + 1) = tisa_fword t1 23` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `tisa_fword u1 19 = tisa_fword u2 19`)) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`val(tisa_fword u1 19)`; `val(tisa_fword u2 19)`] o
      REWRITE_RULE[intern_distinct] o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [intern_ok] o
      check (fun th -> concl th = `intern_ok u2`)) THEN
    REWRITE_TAC[VAL_EQ; intern_has] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `val(tisa_fword u1 19) < val(intern_count u1)` THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `intern_count u2`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* DRV_INTERN16_X86: the native run of a two-step intern16 plan, the leaf    *)
(* linked at ipc. When the driver returns FIRED, both keys are rows of a     *)
(* well-formed interner in the memory it returns with, at the ids the steps  *)
(* returned, and the ids are equal exactly when the keys are.                *)
(* ------------------------------------------------------------------------- *)

let DRV_INTERN16_X86 = prove
 (`!pc ipc stackpointer d plan ctl nctl bind nbw leaves bw st1 st2 budget used0 m0
    ret rbxv rbpv r12v r13v r14v r15v.
     drv_layout pc (word_sub stackpointer (word 248)) d plan 2 ctl nctl bind nbw leaves 1
                (\j. ipc) (\j. intern16_mc) /\
     ALL (drv_step_ok (\j. intern16) pc (word_sub stackpointer (word 248)) d plan 2 nctl bind nbw
                      leaves 1 (\j. ipc) (\j. intern16_mc) bw) [st1; st2] /\
     drv_holds m0 d plan 2 ctl bind leaves budget used0 [st1; st2] bw nbw (\j. ipc) 1 /\
     drv_code m0 pc drv_mc /\ drv_code m0 ipc intern16_mc /\
     EL 1 st2 = EL 1 st1 /\ EL 2 st2 = EL 2 st1 /\ EL 3 st2 = EL 3 st1 /\
     (!r. r < 3 ==> drv_apart (drv_base bw st1 r) (val(drv_len bw st1 r)) ctl (8 * nctl)) /\
     (!t. drv_child bw ctl budget (word_sub stackpointer (word 248)) st1 m0 used0 t ==> intern_ok t)
     ==> ensures x86
          (\s. read RIP s = word pc /\ read RSP s = stackpointer /\ read RDI s = d /\
               read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
               read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
               read memory s = m0 /\ read (memory :> bytes64 stackpointer) s = ret)
          (\s. read RIP s = ret /\ read RSP s = word_add stackpointer (word 8) /\
               read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
               read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
               ?res. drv_sem (\j. intern16) bw ctl budget (word_sub stackpointer (word 248))
                             [st1; st2] 0 m0 used0 res /\
                     read RAX s = FST res /\
                     (!a. ~drv_stack (word_sub stackpointer (word 248)) a
                          ==> read memory s a = drv_final d plan res a) /\
                     (read RAX s = word 1
                      ==> ?t1 u1 t2 u2.
                            drv_child bw ctl budget (word_sub stackpointer (word 248)) st1 m0 used0 t1 /\
                            tisa_run intern16 t1 = TStop 1 u1 /\
                            drv_child bw ctl budget (word_sub stackpointer (word 248)) st2
                                      (drv_after ctl st1 u1) (tisa_fword u1 21) t2 /\
                            tisa_run intern16 t2 = TStop 1 u2 /\
                            FST(SND(SND res)) = drv_after ctl st2 u2 /\
                            intern_ok u2 /\
                            intern_has u2 (val(tisa_fword u1 19)) (tisa_fword t1 22) (tisa_fword t1 23) /\
                            intern_has u2 (val(tisa_fword u2 19)) (tisa_fword t2 22) (tisa_fword t2 23) /\
                            (tisa_fword u1 19 = tisa_fword u2 19 <=>
                             tisa_fword t1 22 = tisa_fword t2 22 /\
                             tisa_fword t1 23 = tisa_fword t2 23)))
          (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                      R12; R13; R14; R15; RBP] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`\j:num. intern16`; `\j:num. (ipc:num)`; `\j:num. intern16_mc`; `1`; `pc:num`;
                `stackpointer:int64`; `d:int64`; `plan:int64`; `2`; `ctl:int64`; `nctl:num`;
                `bind:int64`; `nbw:num`; `leaves:int64`; `bw:num->int64`;
                `[st1; st2]:(int64 list)list`; `budget:int64`; `used0:int64`; `m0:int64->byte`;
                `ret:int64`; `rbxv:int64`; `rbpv:int64`; `r12v:int64`; `r13v:int64`; `r14v:int64`;
                `r15v:int64`] DRV_CORRECT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTERN16_LEAF_WF; INTERN16_LEAF_SPEC];
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP DRV_ENSURES_WEAKEN)] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ALL] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "ALL")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[drv_step_ok; INTERN16_REGION_KINDS] o BETA_RULE o
    check (fun th -> concl th = `drv_step_ok (\j. intern16) pc (word_sub stackpointer (word 248)) d plan 2
                                   nctl bind nbw leaves 1 (\j. ipc) (\j. intern16_mc) bw st1`)) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                  `word_sub stackpointer (word 248):int64`; `st1:int64 list`; `st2:int64 list`;
                  `m0:int64->byte`; `used0:int64`; `res:int64#num#(int64->byte)#int64`]
                 DRV_INTERN16_TWO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `17` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `nctl:num`)) (concl th) && can (find_term ((=) `10`)) (concl th) &&
          can (find_term ((=) `st1:int64 list`)) (concl th))) THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
        X_GEN_TAC `r:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[]];
      STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`t1:tisa_state`; `u1:tisa_state`; `t2:tisa_state`;
                                          `u2:tisa_state`] THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC]);;
