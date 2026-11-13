(* ========================================================================= *)
(* Hoisted EARLY_EXIT_LOOP x n k cap body: the entry test also leaves for    *)
(* the end when k is 0, and the fast copy's latch tests k before x := x + 1: *)
(*   latch': test k,k; je end; add x,1; cmp x,n; jb fast; jmp end            *)
(* ========================================================================= *)

needs "tisa/hol/tisa_x86_hoist.ml";;

let tisa_x86_early_fast_latch = new_definition
 `tisa_x86_early_fast_latch (mc:byte list) pc ol x n k ob oend C <=>
    !t. tisa_bool (tregs t k) ==>
        ensures x86
         (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ol) /\ tisa_x86_rel t s)
         (\s. bytes_loaded s (word pc) mc /\
              (if tregs t k = word 0
               then read RIP s = word(pc + oend) /\ tisa_x86_rel t s
               else tisa_x86_rel (tisa_setreg x (word_add (tregs t x) (word 1)) t) s /\
                    read RIP s = word(pc + (if val(word_add (tregs t x) (word 1)) < val(tregs t n)
                                            then ob else oend))))
         C`;;

(* The fast copy's iterations, entered with x = j < n and k not 0. *)
(* An implication between conjunctions of the same facts, closed without
   search (MESON's search runs out of depth on these goals). *)
let TISA_IMP_CLOSE_TAC = REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];;

let TISA_EARLY_FAST_ITER_RUNSF = prove
 (`!mc pc ob ol oend epi x n k (Inv:tisa_state->bool) (Pj:num->tisa_state->bool) body C nv.
    C ,, C = C /\ ~(k = x) /\
    (!j t. Pj j t ==> tregs t x = word j /\ val(tregs t n) = nv /\ tisa_bool (tregs t k) /\ Inv t) /\
    (!j t. j < nv /\ Pj j t
           ==> Pj (j + 1) (tisa_setreg x (word_add (tregs t x) (word 1)) t)) /\
    tisa_x86_early_fast_latch mc pc ol x n k ob oend C /\
    (!j. j < nv ==> tisa_x86_runs mc pc ob ol epi (Pj j) (Pj j) body C)
    ==> !m j. j + SUC m = nv ==>
         tisa_x86_runsf mc pc ob oend epi (\t. Pj j t /\ ~(tregs t k = word 0)) Inv
           (\t. tisa_early_iter (SUC m) (\st. tisa_exec body st) x k j t) C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[tisa_x86_runsf] THEN ONCE_REWRITE_TAC[tisa_early_iter] THEN
  X_GEN_TAC `t:tisa_state` THEN BETA_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `tregs t x = word j /\ val(tregs t n) = nv /\ tisa_bool (tregs t k) /\ (Inv:tisa_state->bool) t`
   STRIP_ASSUME_TAC THENL [TISA_FACTS_AT_TAC `j:num` `t:tisa_state`; ALL_TAC]) THEN
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
                      tisa_x86_postf (pc + ol) (pc + epi) (Pj (j:num)) (TStop a0 a1) s` THEN
      ASM_REWRITE_TAC[tisa_x86_postf] THEN NO_TAC) THEN
  (ASM_CASES_TAC `(Pj:num->tisa_state->bool) j a` THENL
    [ALL_TAC;
     MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
     EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                     tisa_x86_postf (pc + ol) (pc + epi) (Pj (j:num)) (TCont a) s` THEN
     ASM_REWRITE_TAC[tisa_x86_postf]]) THEN
  (SUBGOAL_THEN `tregs a x = word j /\ val(tregs a n) = nv /\ tisa_bool (tregs a k) /\ (Inv:tisa_state->bool) a`
   STRIP_ASSUME_TAC THENL [TISA_FACTS_AT_TAC `j:num` `a:tisa_state`; ALL_TAC]) THEN
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
                     tisa_x86_postf (pc + ol) (pc + epi) (Pj (j:num)) (TCont a) s` THEN
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
    [TISA_FACTS_AT_TAC `j + 1` `tisa_setreg x (word_add (tregs a x) (word 1)) a`; ALL_TAC]) THEN
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

(* The fast copy from x = 0, entered with k not 0 and at least one iteration. *)
let TISA_EARLY_FAST_LOOP_RUNSF = prove
 (`!mc pc ob ol oend epi x n k (Inv:tisa_state->bool) (Pj:num->tisa_state->bool) body C nv.
    C ,, C = C /\ ~(k = x) /\
    (!j t. Pj j t ==> tregs t x = word j /\ val(tregs t n) = nv /\ tisa_bool (tregs t k) /\ Inv t) /\
    (!j t. j < nv /\ Pj j t
           ==> Pj (j + 1) (tisa_setreg x (word_add (tregs t x) (word 1)) t)) /\
    tisa_x86_early_fast_latch mc pc ol x n k ob oend C /\
    (!j. j < nv ==> tisa_x86_runs mc pc ob ol epi (Pj j) (Pj j) body C) /\
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
                `Inv:tisa_state->bool`; `Pj:num->tisa_state->bool`; `body:tisa_stmt`;
                `C:x86state->x86state->bool`; `SUC m`]
               TISA_EARLY_FAST_ITER_RUNSF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`m:num`; `0`]) THEN
  REWRITE_TAC[ADD_CLAUSES]);;

let TISA_EARLY_ITER_K0 = prove
 (`!m f x k t. tregs t x = word 0 /\ tisa_bool (tregs t k) /\ tregs t k = word 0
               ==> tisa_early_iter m f x k 0 t = TCont t`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[tisa_early_iter; TISA_SETREG_SAME; tisa_early_check; tisa_bool; VAL_WORD_0; LE_0]);;

(* The entry test of a hoisted early-exit loop: to the template head, to the
   end when k is 0, or to the fast copy with H and k not 0. *)
let tisa_x86_hoist_test_early = new_definition
 `tisa_x86_hoist_test_early (mc:byte list) pc ot oh oend of k (P:tisa_state->bool) (H:tisa_state->bool) C <=>
    !t. P t ==> ensures x86
         (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ot) /\ tisa_x86_rel t s)
         (\s. bytes_loaded s (word pc) mc /\ tisa_x86_rel t s /\
              (read RIP s = word(pc + oh) \/
               read RIP s = word(pc + oend) /\ tregs t k = word 0 \/
               read RIP s = word(pc + of) /\ H t /\ ~(tregs t k = word 0)))
         C`;;

let TISA_HOIST_JOIN_EARLY = prove
 (`!mc pc ot oh oend of epi (P:tisa_state->bool) Q H k f C.
        C ,, C = C /\ (=) subsumed C /\
        tisa_x86_hoist_test_early mc pc ot oh oend of k P H C /\
        tisa_x86_runsf mc pc oh oend epi P Q f C /\
        (!t. P t /\ tregs t k = word 0 ==> f t = TCont t /\ Q t) /\
        tisa_x86_runsf mc pc of oend epi (\t. P t /\ H t /\ ~(tregs t k = word 0)) Q f C
        ==> tisa_x86_runsf mc pc ot oend epi P Q f C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_x86_runsf; tisa_x86_hoist_test_early] THEN STRIP_TAC THEN
  X_GEN_TAC `t:tisa_state` THEN DISCH_TAC THEN
  MATCH_MP_TAC(MATCH_MP TISA_TRANS (ASSUME `C ,, C = (C:x86state->x86state->bool)`)) THEN
  EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ tisa_x86_rel t s /\
                  (read RIP s = word(pc + oh) \/
                   read RIP s = word(pc + oend) /\ tregs t k = word 0 \/
                   read RIP s = word(pc + of) /\ (H:tisa_state->bool) t /\ ~(tregs t k = word 0))` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `tregs t k = word 0` THEN ASM_REWRITE_TAC[] THENL
   [(* k is 0: the head or the end *)
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC `\s. (bytes_loaded s (word pc) mc /\ read RIP s = word(pc + oh) /\ tisa_x86_rel t s) \/
                    (bytes_loaded s (word pc) mc /\ read RIP s = word(pc + oend) /\ tisa_x86_rel t s)` THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC TISA_ENSURES_DISJ THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      (* not ASM_MESON_TAC: it reads every assumption, and (=) subsumed C
         (equality as an unapplied constant) breaks its preprocessing *)
      SUBGOAL_THEN `(f:tisa_state->tisa_result) t = TCont t /\ (Q:tisa_state->bool) t` STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[tisa_x86_postf] THEN
      MATCH_MP_TAC ENSURES_ALREADY THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    (* k not 0: the head, or the fast copy with H *)
    ASM_CASES_TAC `(H:tisa_state->bool) t` THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC `\s. (bytes_loaded s (word pc) mc /\ read RIP s = word(pc + oh) /\ tisa_x86_rel t s) \/
                      (bytes_loaded s (word pc) mc /\ read RIP s = word(pc + of) /\ tisa_x86_rel t s)` THEN
      CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC TISA_ENSURES_DISJ THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + oh) /\ tisa_x86_rel t s` THEN
      CONJ_TAC THENL [MESON_TAC[]; ASM_SIMP_TAC[]]]]);;
