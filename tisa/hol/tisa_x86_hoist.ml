(* ========================================================================= *)
(* Loops with hoisted bounds checks (emitter option hoist_bounds).           *)
(*                                                                           *)
(* COUNT_LOOP x n cap body, hoisted, is emitted as                           *)
(*   entry:  mov r14d,cap; cmp n,r14; ja UNSUPPORTED; xor x,x                *)
(*   test:   the entry test; to head when it fails, else on to fast          *)
(*   fast:   body without the hoisted checks                                 *)
(*   latch': add x,1; cmp x,n; jb fast; jmp end                              *)
(*   head:   cmp x,n; jae end        (the template loop, unchanged)          *)
(*   body                                                                    *)
(*   latch:  add x,1; jmp head                                               *)
(* Both copies realize tisa_count_iter from x = 0: the template copy by      *)
(* TISA_COUNT_ITER_RUNSF, the fast copy by TISA_FAST_ITER_RUNSF below, whose *)
(* body is proved under what the entry test established.                     *)
(* ========================================================================= *)

needs "tisa/hol/tisa_x86_loops.ml";;

let TISA_ENSURES_DISJ = prove
 (`!(step:A->A->bool) P R Q C.
        ensures step P Q C /\ ensures step R Q C ==> ensures step (\s. P s \/ R s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

(* The entry test: from ot, with P of the state and the state unchanged (in
   the relation), it goes to the template head oh, or to the fast copy of
   with H of the state. *)
let tisa_x86_hoist_test = new_definition
 `tisa_x86_hoist_test (mc:byte list) pc ot oh of (P:tisa_state->bool) (H:tisa_state->bool) C <=>
    !t. P t ==> ensures x86
         (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ot) /\ tisa_x86_rel t s)
         (\s. bytes_loaded s (word pc) mc /\ tisa_x86_rel t s /\
              (read RIP s = word(pc + oh) \/ read RIP s = word(pc + of) /\ H t))
         C`;;

(* After the test, either copy realizes the same function of the state. *)
let TISA_HOIST_JOIN = prove
 (`!mc pc ot oh of oend epi (P:tisa_state->bool) Q H f C.
        C ,, C = C /\
        tisa_x86_hoist_test mc pc ot oh of P H C /\
        tisa_x86_runsf mc pc oh oend epi P Q f C /\
        tisa_x86_runsf mc pc of oend epi (\t. P t /\ H t) Q f C
        ==> tisa_x86_runsf mc pc ot oend epi P Q f C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_x86_runsf; tisa_x86_hoist_test] THEN STRIP_TAC THEN
  X_GEN_TAC `t:tisa_state` THEN DISCH_TAC THEN
  MATCH_MP_TAC(MATCH_MP TISA_TRANS (ASSUME `C ,, C = (C:x86state->x86state->bool)`)) THEN
  EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ tisa_x86_rel t s /\
                  (read RIP s = word(pc + oh) \/ read RIP s = word(pc + of) /\ (H:tisa_state->bool) t)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(H:tisa_state->bool) t` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC `\s. (bytes_loaded s (word pc) mc /\ read RIP s = word(pc + oh) /\ tisa_x86_rel t s) \/
                    (bytes_loaded s (word pc) mc /\ read RIP s = word(pc + of) /\ tisa_x86_rel t s)` THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC TISA_ENSURES_DISJ THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + oh) /\ tisa_x86_rel t s` THEN
    CONJ_TAC THENL [MESON_TAC[]; ASM_SIMP_TAC[]]]);;

(* The fast copy's latch: x := x + 1, then back to the body while x < n,
   else to the end. *)
let tisa_x86_fast_latch = new_definition
 `tisa_x86_fast_latch (mc:byte list) pc ol x n ob oend C <=>
    !t. ensures x86
         (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ol) /\ tisa_x86_rel t s)
         (\s. bytes_loaded s (word pc) mc /\
              tisa_x86_rel (tisa_setreg x (word_add (tregs t x) (word 1)) t) s /\
              read RIP s = word(pc + (if val(word_add (tregs t x) (word 1)) < val(tregs t n)
                                      then ob else oend)))
         C`;;

(* The fast copy's iterations, entered with x = j < n: by induction on those
   left after the first. *)
let TISA_FAST_ITER_RUNSF = prove
 (`!mc pc ob ol oend epi x n (Pj:num->tisa_state->bool) body C nv.
    C ,, C = C /\
    (!j t. Pj j t ==> tregs t x = word j /\ val(tregs t n) = nv) /\
    (!j t. j < nv /\ Pj j t
           ==> Pj (j + 1) (tisa_setreg x (word_add (tregs t x) (word 1)) t)) /\
    tisa_x86_fast_latch mc pc ol x n ob oend C /\
    (!j. j < nv ==> tisa_x86_runs mc pc ob ol epi (Pj j) (Pj j) body C)
    ==> !m j. j + SUC m = nv ==>
         tisa_x86_runsf mc pc ob oend epi (Pj j) (Pj nv)
           (\t. tisa_count_iter (SUC m) (\st. tisa_exec body st) x j t) C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[tisa_x86_runsf] THEN ONCE_REWRITE_TAC[tisa_count_iter] THEN
  X_GEN_TAC `t:tisa_state` THEN DISCH_TAC THEN
  (SUBGOAL_THEN `tregs t x = word j /\ val(tregs t n) = nv` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `j < nv` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_SIMP_TAC[TISA_SETREG_SAME] THEN BETA_TAC THEN
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
  (* continued with a *)
  (ASM_CASES_TAC `(Pj:num->tisa_state->bool) j a` THENL
    [ALL_TAC;
     MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
     EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                     tisa_x86_postf (pc + ol) (pc + epi) (Pj (j:num)) (TCont a) s` THEN
     ASM_REWRITE_TAC[tisa_x86_postf]]) THEN
  (SUBGOAL_THEN `tregs a x = word j /\ val(tregs a n) = nv` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `val(word_add (tregs a x) (word 1):int64) = j + 1` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[GSYM WORD_ADD] THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
     MP_TAC(ISPEC `tregs a n` VAL_BOUND_64) THEN ASM_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `word_add (tregs a x) (word 1):int64 = word(j + 1)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[WORD_ADD]; ALL_TAC]) THEN
  (SUBGOAL_THEN `(Pj:num->tisa_state->bool) (j + 1) (tisa_setreg x (word(j + 1)) a)` ASSUME_TAC THENL
    [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `word_add (tregs a x) (word 1):int64 = word(j + 1)`)) THEN
     ASM_MESON_TAC[];
     ALL_TAC]) THEN
  (* the body's end, then the latch *)
  MATCH_MP_TAC(MATCH_MP TISA_TRANS (ASSUME `C ,, C = (C:x86state->x86state->bool)`)) THEN
  EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ol) /\
                  tisa_x86_rel a s` THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
     EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                     tisa_x86_postf (pc + ol) (pc + epi) (Pj (j:num)) (TCont a) s` THEN
     ASM_REWRITE_TAC[tisa_x86_postf] THEN MESON_TAC[];
     ALL_TAC]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:tisa_state` o REWRITE_RULE[tisa_x86_fast_latch] o
              check (fun th -> can (find_term ((=) `tisa_x86_fast_latch`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THENL
   [(* the last iteration: the latch leaves for the end *)
    SUBGOAL_THEN `~(j + 1 < nv)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `nv = j + 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                    tisa_x86_rel (tisa_setreg x (word(j + 1)) a) s /\
                    read RIP s = word(pc + oend)` THEN
    ASM_REWRITE_TAC[tisa_count_iter; tisa_x86_postf] THEN MESON_TAC[];
    (* more iterations: back to the body, then the rest by induction *)
    SUBGOAL_THEN `j + 1 < nv` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(MATCH_MP TISA_TRANS (ASSUME `C ,, C = (C:x86state->x86state->bool)`)) THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ob) /\
                    tisa_x86_rel (tisa_setreg x (word(j + 1)) a) s` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                      tisa_x86_rel (tisa_setreg x (word(j + 1)) a) s /\
                      read RIP s = word(pc + ob)` THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j + 1` o
                  check (fun th -> can (find_term ((=) `tisa_count_iter`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[tisa_x86_runsf] THEN
    DISCH_THEN(MP_TAC o SPEC `tisa_setreg x (word(j + 1)) a`) THEN
    ASM_REWRITE_TAC[TISA_COUNT_ITER_SETREG]]);;

(* Weakening the facts after a piece. *)
let TISA_RUNSF_WEAKEN_POST = prove
 (`!mc pc oa oe epi (P:tisa_state->bool) Q R f C.
        (!t. Q t ==> R t) /\ tisa_x86_runsf mc pc oa oe epi P Q f C
        ==> tisa_x86_runsf mc pc oa oe epi P R f C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_x86_runsf] THEN STRIP_TAC THEN
  X_GEN_TAC `t:tisa_state` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(P:tisa_state->bool) t`) o SPEC `t:tisa_state`) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_POSTCONDITION_THM) THEN
  X_GEN_TAC `s:x86state` THEN BETA_TAC THEN
  STRUCT_CASES_TAC(ISPEC `(f:tisa_state->tisa_result) t` tisa_result_CASES) THEN
  REWRITE_TAC[tisa_x86_postf] THEN ASM_MESON_TAC[]);;

(* The fast copy from x = 0, which the test enters only when the facts give
   at least one iteration. *)
let TISA_FAST_LOOP_RUNSF = prove
 (`!mc pc ob ol oend epi x n (Pj:num->tisa_state->bool) body C nv.
    C ,, C = C /\
    (!j t. Pj j t ==> tregs t x = word j /\ val(tregs t n) = nv) /\
    (!j t. j < nv /\ Pj j t
           ==> Pj (j + 1) (tisa_setreg x (word_add (tregs t x) (word 1)) t)) /\
    tisa_x86_fast_latch mc pc ol x n ob oend C /\
    (!j. j < nv ==> tisa_x86_runs mc pc ob ol epi (Pj j) (Pj j) body C) /\
    (!t. Pj 0 t ==> 1 <= nv)
    ==> tisa_x86_runsf mc pc ob oend epi (Pj 0) (Pj nv)
          (\t. tisa_count_iter nv (\st. tisa_exec body st) x 0 t) C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `nv = 0` THENL
   [REWRITE_TAC[tisa_x86_runsf] THEN ASM_MESON_TAC[ARITH_RULE `~(1 <= 0)`];
    ALL_TAC] THEN
  MP_TAC(SPEC `nv:num` num_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  MP_TAC(SPECL [`mc:byte list`; `pc:num`; `ob:num`; `ol:num`; `oend:num`; `epi:num`; `x:num`; `n:num`;
                `Pj:num->tisa_state->bool`; `body:tisa_stmt`; `C:x86state->x86state->bool`; `SUC m`]
               TISA_FAST_ITER_RUNSF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`m:num`; `0`]) THEN
  REWRITE_TAC[ADD_CLAUSES]);;
