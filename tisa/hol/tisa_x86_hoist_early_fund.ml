(* ========================================================================= *)
(* The fast copy of a hoisted early-exit loop that pays FUND: as in          *)
(* tisa_x86_hoist_early.ml, with the body taking Pj j to Qj j and the latch  *)
(* Qj j to Pj (j + 1), the allowance left dropping as the body pays (as      *)
(* tisa_x86_hoist_fund.ml does for counted loops).                           *)
(* ========================================================================= *)

needs "tisa/hol/tisa_x86_hoist_early.ml";;
(* The facts at a state, read from the hypothesis about the predicate that
   holds there (both Pj's and Qj's hypotheses give the same conclusion). *)
let TISA_FACTS_FROM_TAC p j t =
  FIRST_ASSUM(fun th ->
    let th' = SPECL [j; t] th in
    let ante = lhand(concl th') in
    if fst(strip_comb ante) = p then ACCEPT_TAC(MP th' (ASSUME ante))
    else failwith "TISA_FACTS_FROM_TAC: another predicate");;

let TISA_EARLY_FAST_ITER_RUNSF2 = prove
 (`!mc pc ob ol oend epi x n k (Inv:tisa_state->bool) (Pj:num->tisa_state->bool) (Qj:num->tisa_state->bool) body C nv.
    C ,, C = C /\ ~(k = x) /\
    (!j t. Pj j t ==> tregs t x = word j /\ val(tregs t n) = nv /\ tisa_bool (tregs t k) /\ Inv t) /\
    (!j t. Qj j t ==> tregs t x = word j /\ val(tregs t n) = nv /\ tisa_bool (tregs t k) /\ Inv t) /\
    (!j t. j < nv /\ Qj j t
           ==> Pj (j + 1) (tisa_setreg x (word_add (tregs t x) (word 1)) t)) /\
    tisa_x86_early_fast_latch mc pc ol x n k ob oend C /\
    (!j. j < nv ==> tisa_x86_runs mc pc ob ol epi (Pj j) (Qj j) body C)
    ==> !m j. j + SUC m = nv ==>
         tisa_x86_runsf mc pc ob oend epi (\t. Pj j t /\ ~(tregs t k = word 0)) Inv
           (\t. tisa_early_iter (SUC m) (\st. tisa_exec body st) x k j t) C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[tisa_x86_runsf] THEN ONCE_REWRITE_TAC[tisa_early_iter] THEN
  X_GEN_TAC `t:tisa_state` THEN BETA_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `tregs t x = word j /\ val(tregs t n) = nv /\ tisa_bool (tregs t k) /\ (Inv:tisa_state->bool) t`
   STRIP_ASSUME_TAC THENL [TISA_FACTS_FROM_TAC `Pj:num->tisa_state->bool` `j:num` `t:tisa_state`; ALL_TAC]) THEN
  (SUBGOAL_THEN `j < nv` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_SIMP_TAC[TISA_SETREG_SAME] THEN ASM_REWRITE_TAC[tisa_early_check] THEN
  (* the body *)
  FIRST_ASSUM(MP_TAC o SPEC `t:tisa_state` o REWRITE_RULE[tisa_x86_runs] o
              C MATCH_MP (ASSUME `j < nv`) o SPEC `j:num` o
              check (fun th -> can (find_term ((=) `tisa_x86_runs`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `tisa_exec body t` tisa_result_CASES) THEN
  REWRITE_TAC[tisa_then] THEN DISCH_TAC THEN
  TRY(MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                      tisa_x86_postf (pc + ol) (pc + epi) (Qj (j:num)) (TStop a0 a1) s` THEN
      ASM_REWRITE_TAC[tisa_x86_postf] THEN NO_TAC) THEN
  (ASM_CASES_TAC `(Qj:num->tisa_state->bool) j a` THENL
    [ALL_TAC;
     MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
     EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                     tisa_x86_postf (pc + ol) (pc + epi) (Qj (j:num)) (TCont a) s` THEN
     ASM_REWRITE_TAC[tisa_x86_postf]]) THEN
  (SUBGOAL_THEN `tregs a x = word j /\ val(tregs a n) = nv /\ tisa_bool (tregs a k) /\ (Inv:tisa_state->bool) a`
   STRIP_ASSUME_TAC THENL [TISA_FACTS_FROM_TAC `Qj:num->tisa_state->bool` `j:num` `a:tisa_state`; ALL_TAC]) THEN
  (* x + 1 as a word and as a value, before the latch is rewritten with them *)
  (SUBGOAL_THEN `val(word_add (tregs a x) (word 1):int64) = j + 1` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[GSYM WORD_ADD] THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
     MP_TAC(ISPEC `tregs a n` VAL_BOUND_64) THEN ASM_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `word_add (tregs a x) (word 1):int64 = word(j + 1)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[WORD_ADD]; ALL_TAC]) THEN
  MATCH_MP_TAC(MATCH_MP TISA_TRANS (ASSUME `C ,, C = (C:x86state->x86state->bool)`)) THEN
  EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ol) /\ tisa_x86_rel a s` THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
     EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                     tisa_x86_postf (pc + ol) (pc + epi) (Qj (j:num)) (TCont a) s` THEN
     ASM_REWRITE_TAC[tisa_x86_postf] THEN TISA_IMP_CLOSE_TAC;
     ALL_TAC]) THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `tisa_bool (tregs a k)`) o SPEC `a:tisa_state` o
              REWRITE_RULE[tisa_x86_early_fast_latch] o
              check (fun th -> can (find_term ((=) `tisa_x86_early_fast_latch`)) (concl th))) THEN
  ASM_REWRITE_TAC[tisa_early_check] THEN
  (ASM_CASES_TAC `tregs a k = word 0` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
    [(* k became 0: the latch leaves *)
     MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
     EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + oend) /\ tisa_x86_rel a s` THEN
     ASM_REWRITE_TAC[tisa_x86_postf] THEN TISA_IMP_CLOSE_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `(Pj:num->tisa_state->bool) (j + 1) (tisa_setreg x (word_add (tregs a x) (word 1)) a)` ASSUME_TAC THENL
    [TISA_NEXT_TAC `j:num` `a:tisa_state`; ALL_TAC]) THEN
  (SUBGOAL_THEN `tregs (tisa_setreg x (word_add (tregs a x) (word 1)) a) x = word (j + 1) /\
                 val(tregs (tisa_setreg x (word_add (tregs a x) (word 1)) a) n) = nv /\
                 tisa_bool (tregs (tisa_setreg x (word_add (tregs a x) (word 1)) a) k) /\
                 (Inv:tisa_state->bool) (tisa_setreg x (word_add (tregs a x) (word 1)) a)` STRIP_ASSUME_TAC THENL
    [TISA_FACTS_FROM_TAC `Pj:num->tisa_state->bool` `j + 1` `tisa_setreg x (word_add (tregs a x) (word 1)) a`; ALL_TAC]) THEN
  (SUBGOAL_THEN `~(tregs (tisa_setreg x (word(j + 1)) a) k = word 0)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[tisa_setreg; tregs]; ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_add (tregs a x) (word 1):int64 = word(j + 1)`]) THEN
  ASM_REWRITE_TAC[] THENL
   [(* the last iteration: the latch leaves for the end *)
    SUBGOAL_THEN `~(j + 1 < nv)` (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                    tisa_x86_rel (tisa_setreg x (word(j + 1)) a) s /\
                    read RIP s = word(pc + oend)` THEN
    ASM_REWRITE_TAC[tisa_early_iter; tisa_x86_postf] THEN TISA_IMP_CLOSE_TAC;
    (* more iterations: back to the body, then the rest by induction *)
    SUBGOAL_THEN `j + 1 < nv` (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(MATCH_MP TISA_TRANS (ASSUME `C ,, C = (C:x86state->x86state->bool)`)) THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ob) /\
                    tisa_x86_rel (tisa_setreg x (word(j + 1)) a) s` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                      tisa_x86_rel (tisa_setreg x (word(j + 1)) a) s /\
                      read RIP s = word(pc + ob)` THEN
      ASM_REWRITE_TAC[] THEN TISA_IMP_CLOSE_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j + 1` o
                  check (fun th -> can (find_term ((=) `tisa_early_iter`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[tisa_x86_runsf] THEN
    DISCH_THEN(MP_TAC o SPEC `tisa_setreg x (word(j + 1)) a`) THEN
    ASM_REWRITE_TAC[TISA_EARLY_ITER_SETREG]]);;

let TISA_EARLY_FAST_LOOP_RUNSF2 = prove
 (`!mc pc ob ol oend epi x n k (Inv:tisa_state->bool) (Pj:num->tisa_state->bool) (Qj:num->tisa_state->bool) body C nv.
    C ,, C = C /\ ~(k = x) /\
    (!j t. Pj j t ==> tregs t x = word j /\ val(tregs t n) = nv /\ tisa_bool (tregs t k) /\ Inv t) /\
    (!j t. Qj j t ==> tregs t x = word j /\ val(tregs t n) = nv /\ tisa_bool (tregs t k) /\ Inv t) /\
    (!j t. j < nv /\ Qj j t
           ==> Pj (j + 1) (tisa_setreg x (word_add (tregs t x) (word 1)) t)) /\
    tisa_x86_early_fast_latch mc pc ol x n k ob oend C /\
    (!j. j < nv ==> tisa_x86_runs mc pc ob ol epi (Pj j) (Qj j) body C) /\
    (!t. Pj 0 t ==> 1 <= nv)
    ==> tisa_x86_runsf mc pc ob oend epi (\t. Pj 0 t /\ ~(tregs t k = word 0)) Inv
          (\t. tisa_early_iter nv (\st. tisa_exec body st) x k 0 t) C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `nv = 0` THENL
   [REWRITE_TAC[tisa_x86_runsf] THEN ASM_MESON_TAC[ARITH_RULE `~(1 <= 0)`];
    ALL_TAC] THEN
  MP_TAC(SPEC `nv:num` num_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  MP_TAC(SPECL [`mc:byte list`; `pc:num`; `ob:num`; `ol:num`; `oend:num`; `epi:num`; `x:num`; `n:num`; `k:num`;
                `Inv:tisa_state->bool`; `Pj:num->tisa_state->bool`; `Qj:num->tisa_state->bool`; `body:tisa_stmt`;
                `C:x86state->x86state->bool`; `SUC m`]
               TISA_EARLY_FAST_ITER_RUNSF2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`m:num`; `0`]) THEN
  REWRITE_TAC[ADD_CLAUSES]);;

(* With k 0 at x = 0 the loop does nothing, whatever its bound. *)
