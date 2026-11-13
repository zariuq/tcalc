(* ========================================================================= *)
(* Joining the code of loops.                                                *)
(*                                                                           *)
(* COUNT_LOOP x n cap body is emitted as                                     *)
(*   entry:  mov r14d,cap; cmp n,r14; ja UNSUPPORTED; xor x,x                *)
(*   head:   cmp x,n; jae end                                                *)
(*   body                                                                    *)
(*   latch:  add x,1; jmp head                                               *)
(* and runs the body with x = j for j = 0 .. n - 1, as tisa_count_iter does. *)
(* The proof is by induction on the iterations left, with the facts Pj j     *)
(* (the loop invariant, x = word j and val n = nv) at the head.              *)
(* ========================================================================= *)

needs "tisa/hol/tisa_x86_image.ml";;

(* A piece of code given by a function on states. *)
let tisa_x86_runsf = new_definition
 `tisa_x86_runsf (mc:byte list) pc off e epi (P:tisa_state->bool) Q
                 (fn:tisa_state->tisa_result) C <=>
    !t. P t ==>
        ensures x86
         (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + off) /\ tisa_x86_rel t s)
         (\s. bytes_loaded s (word pc) mc /\ tisa_x86_postf (pc + e) (pc + epi) Q (fn t) s)
         C`;;

let TISA_RUNS_RUNSF = prove
 (`!mc pc off e epi P Q S C.
        tisa_x86_runs mc pc off e epi P Q S C <=>
        tisa_x86_runsf mc pc off e epi P Q (\t. tisa_exec S t) C`,
  REWRITE_TAC[tisa_x86_runs; tisa_x86_runsf]);;

(* Sequencing pieces given by functions. *)
let TISA_THEN_RUNSF = prove
 (`!mc pc oa ob oe epi P Q R f1 f2 C.
        C ,, C = C /\
        tisa_x86_runsf mc pc oa ob epi P Q f1 C /\
        tisa_x86_runsf mc pc ob oe epi Q R f2 C
        ==> tisa_x86_runsf mc pc oa oe epi P R (\t. tisa_then (f1 t) f2) C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_x86_runsf] THEN STRIP_TAC THEN
  X_GEN_TAC `t:tisa_state` THEN DISCH_TAC THEN BETA_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(P:tisa_state->bool) t`) o SPEC `t:tisa_state`) THEN
  STRUCT_CASES_TAC(ISPEC `(f1:tisa_state->tisa_result) t` tisa_result_CASES) THEN
  REWRITE_TAC[tisa_then] THEN DISCH_TAC THENL
   [ASM_CASES_TAC `(Q:tisa_state->bool) a` THENL
     [MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
      EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ob) /\
                      tisa_x86_rel a s` THEN
      ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                      tisa_x86_postf (pc + ob) (pc + epi) Q (TCont a) s` THEN
      ASM_REWRITE_TAC[tisa_x86_postf] THEN MESON_TAC[];
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                      tisa_x86_postf (pc + ob) (pc + epi) Q (TCont a) s` THEN
      ASM_REWRITE_TAC[tisa_x86_postf]];
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                    tisa_x86_postf (pc + ob) (pc + epi) Q (TStop a0 a1) s` THEN
    ASM_REWRITE_TAC[tisa_x86_postf]]);;

(* The loop head: x below n goes to the body, else to the end. *)
let tisa_x86_head = new_definition
 `tisa_x86_head (mc:byte list) pc oh x n ob oend C <=>
    !t. ensures x86
         (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + oh) /\ tisa_x86_rel t s)
         (\s. bytes_loaded s (word pc) mc /\ tisa_x86_rel t s /\
              read RIP s = word(pc + (if val(tregs t x) < val(tregs t n) then ob else oend)))
         C`;;

(* The latch: x := x + 1, back to the head. *)
let tisa_x86_latch = new_definition
 `tisa_x86_latch (mc:byte list) pc ol x oh C <=>
    !t. ensures x86
         (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ol) /\ tisa_x86_rel t s)
         (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + oh) /\
              tisa_x86_rel (tisa_setreg x (word_add (tregs t x) (word 1)) t) s)
         C`;;

let TISA_SETREG_SAME = prove
 (`!x v t. tregs t x = v ==> tisa_setreg x v t = t`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t:tisa_state` (prove_cases_thm tisa_state_INDUCT)) THEN
  REWRITE_TAC[tisa_setreg; tregs; tmem; injectivity "tisa_state"; FUN_EQ_THM] THEN
  MESON_TAC[]);;

let TISA_SETREG_SETREG = prove
 (`!x a b t. tisa_setreg x a (tisa_setreg x b t) = tisa_setreg x a t`,
  REWRITE_TAC[tisa_setreg; tregs; tmem; injectivity "tisa_state"; FUN_EQ_THM] THEN
  MESON_TAC[]);;

let TISA_COUNT_ITER_SETREG = prove
 (`!m f x j v t. tisa_count_iter m f x j (tisa_setreg x v t) = tisa_count_iter m f x j t`,
  INDUCT_TAC THEN REWRITE_TAC[tisa_count_iter; TISA_SETREG_SETREG]);;

(* What a loop's entry code does: refuse a bound above the cap, else x := 0. *)
let tisa_loop_entry = new_definition
 `tisa_loop_entry x n cap t =
    if cap < val(tregs t n) then tisa_fail 2 t else TCont (tisa_setreg x (word 0) t)`;;

(* The count loop as its entry followed by the iterations from x = 0. *)
let TISA_COUNT_LOOP_SPLIT = prove
 (`!x n cap body t.
        tisa_exec (TCountLoop x n cap body) t =
        tisa_then (tisa_loop_entry x n cap t)
                  (\u. tisa_count_iter (val(tregs t n)) (\st. tisa_exec body st) x 0 u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_exec; tisa_loop_entry] THEN
  COND_CASES_TAC THEN REWRITE_TAC[tisa_then; tisa_fail; TISA_COUNT_ITER_SETREG]);;

(* Transitivity of ensures for a frame that composes with itself. *)
let TISA_TRANS = prove
 (`!(C:x86state->x86state->bool) P Q R.
        C ,, C = C ==> ensures x86 P Q C /\ ensures x86 Q R C ==> ensures x86 P R C`,
  MESON_TAC[ENSURES_TRANS_SIMPLE]);;

(* The iterations, by induction on those left. *)
let TISA_COUNT_ITER_RUNSF = prove
 (`!mc pc oh ob ol oend epi x n (Pj:num->tisa_state->bool) body C nv.
    C ,, C = C /\
    (!j t. Pj j t ==> tregs t x = word j /\ val(tregs t n) = nv) /\
    (!j t. j < nv /\ Pj j t
           ==> Pj (j + 1) (tisa_setreg x (word_add (tregs t x) (word 1)) t)) /\
    tisa_x86_head mc pc oh x n ob oend C /\
    tisa_x86_latch mc pc ol x oh C /\
    (!j. j < nv ==> tisa_x86_runs mc pc ob ol epi (Pj j) (Pj j) body C)
    ==> !m j. j + m = nv ==>
         tisa_x86_runsf mc pc oh oend epi (Pj j) (Pj nv)
           (\t. tisa_count_iter m (\st. tisa_exec body st) x j t) C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[tisa_x86_runsf; tisa_count_iter] THEN X_GEN_TAC `t:tisa_state` THEN DISCH_TAC THEN
  (SUBGOAL_THEN `tregs t x = word j /\ val(tregs t n) = nv` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `val(tregs t x) = j` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
     MP_TAC(ISPEC `tregs t n` VAL_BOUND_64) THEN ASM_ARITH_TAC;
     ALL_TAC]) THEN
  ASM_SIMP_TAC[TISA_SETREG_SAME] THEN BETA_TAC THENL
   [(* no iteration left: j = nv, and the head exits *)
    SUBGOAL_THEN `j:num = nv` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:tisa_state` o REWRITE_RULE[tisa_x86_head] o
                check (fun th -> can (find_term ((=) `tisa_x86_head`)) (concl th))) THEN
    ASM_REWRITE_TAC[LT_REFL] THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ tisa_x86_rel t s /\
                    read RIP s = word(pc + oend)` THEN
    ASM_REWRITE_TAC[tisa_x86_postf] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* an iteration: the head enters the body *)
  SUBGOAL_THEN `j < nv` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(MATCH_MP TISA_TRANS (ASSUME `C ,, C = (C:x86state->x86state->bool)`)) THEN
  EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ob) /\
                  tisa_x86_rel t s` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `t:tisa_state` o REWRITE_RULE[tisa_x86_head] o
                check (fun th -> can (find_term ((=) `tisa_x86_head`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ tisa_x86_rel t s /\
                    read RIP s = word(pc + ob)` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the body *)
  FIRST_ASSUM(MP_TAC o SPEC `t:tisa_state` o REWRITE_RULE[tisa_x86_runs] o
              C MATCH_MP (ASSUME `j < nv`) o SPEC `j:num` o
              check (fun th -> can (find_term ((=) `tisa_x86_runs`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `tisa_exec body t` tisa_result_CASES) THEN
  REWRITE_TAC[tisa_then] THEN DISCH_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                    tisa_x86_postf (pc + ol) (pc + epi) (Pj (j:num)) (TStop a0 a1) s` THEN
    ASM_REWRITE_TAC[tisa_x86_postf]] THEN
  (* continued with a: the latch, then the remaining iterations *)
  ASM_CASES_TAC `(Pj:num->tisa_state->bool) j a` THENL
   [ALL_TAC;
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                    tisa_x86_postf (pc + ol) (pc + epi) (Pj (j:num)) (TCont a) s` THEN
    ASM_REWRITE_TAC[tisa_x86_postf]] THEN
  SUBGOAL_THEN `tregs a x = word j` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(MATCH_MP TISA_TRANS (ASSUME `C ,, C = (C:x86state->x86state->bool)`)) THEN
  EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ol) /\
                  tisa_x86_rel a s` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                    tisa_x86_postf (pc + ol) (pc + epi) (Pj (j:num)) (TCont a) s` THEN
    ASM_REWRITE_TAC[tisa_x86_postf] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(MATCH_MP TISA_TRANS (ASSUME `C ,, C = (C:x86state->x86state->bool)`)) THEN
  EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + oh) /\
                  tisa_x86_rel (tisa_setreg x (word_add (tregs a x) (word 1)) a) s` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `a:tisa_state` o REWRITE_RULE[tisa_x86_latch] o
                check (fun th -> can (find_term ((=) `tisa_x86_latch`)) (concl th))) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j + 1` o
                check (fun th -> can (find_term ((=) `tisa_count_iter`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[tisa_x86_runsf] THEN
  DISCH_THEN(MP_TAC o SPEC `tisa_setreg x (word_add (tregs a x) (word 1)) a`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[TISA_COUNT_ITER_SETREG]);;

(* ------------------------------------------------------------------------- *)
(* EARLY_EXIT_LOOP x n k cap body: the head also leaves when k is 0, and so  *)
(* does the latch, before x := x + 1.                                        *)
(*   head:   cmp x,n; jae end; test k,k; je end                              *)
(*   latch:  test k,k; je end; add x,1; jmp head                             *)
(* ------------------------------------------------------------------------- *)

let tisa_x86_early_head = new_definition
 `tisa_x86_early_head (mc:byte list) pc oh x n k ob oend C <=>
    !t. tisa_bool (tregs t k) ==>
        ensures x86
         (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + oh) /\ tisa_x86_rel t s)
         (\s. bytes_loaded s (word pc) mc /\ tisa_x86_rel t s /\
              read RIP s = word(pc + (if val(tregs t x) < val(tregs t n) /\ ~(tregs t k = word 0)
                                      then ob else oend)))
         C`;;

let tisa_x86_early_latch = new_definition
 `tisa_x86_early_latch (mc:byte list) pc ol x k oh oend C <=>
    !t. tisa_bool (tregs t k) ==>
        ensures x86
         (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ol) /\ tisa_x86_rel t s)
         (\s. bytes_loaded s (word pc) mc /\
              (if tregs t k = word 0
               then read RIP s = word(pc + oend) /\ tisa_x86_rel t s
               else read RIP s = word(pc + oh) /\
                    tisa_x86_rel (tisa_setreg x (word_add (tregs t x) (word 1)) t) s))
         C`;;

(* Instances of the loop hypotheses: the facts at a state, and the next
   iteration's facts after the latch. *)
let TISA_FACTS_AT_TAC j t =
  FIRST_ASSUM(fun th ->
    let th' = SPECL [j; t] th in
    ACCEPT_TAC(MP th' (ASSUME (lhand(concl th')))));;

let TISA_NEXT_TAC j t =
  FIRST_ASSUM(fun th ->
    let th' = SPECL [j; t] th in
    let a,b = dest_conj(lhand(concl th')) in
    ACCEPT_TAC(MP th' (CONJ (ASSUME a) (ASSUME b))));;

let TISA_EARLY_ITER_SETREG = prove
 (`!m f x k j v t. tisa_early_iter m f x k j (tisa_setreg x v t) = tisa_early_iter m f x k j t`,
  INDUCT_TAC THEN REWRITE_TAC[tisa_early_iter; TISA_SETREG_SETREG]);;

let TISA_EARLY_LOOP_SPLIT = prove
 (`!x n k cap body t.
        tisa_exec (TEarlyLoop x n k cap body) t =
        tisa_then (tisa_loop_entry x n cap t)
                  (\u. tisa_early_iter (val(tregs t n)) (\st. tisa_exec body st) x k 0 u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_exec; tisa_loop_entry] THEN
  COND_CASES_TAC THEN REWRITE_TAC[tisa_then; tisa_fail; TISA_EARLY_ITER_SETREG]);;

let TISA_EARLY_ITER_RUNSF = prove
 (`!mc pc oh ob ol oend epi x n k (Inv:tisa_state->bool) (Pj:num->tisa_state->bool) body C nv.
    C ,, C = C /\
    (!j t. Pj j t ==> tregs t x = word j /\ val(tregs t n) = nv /\ tisa_bool (tregs t k) /\ Inv t) /\
    (!j t. j < nv /\ Pj j t
           ==> Pj (j + 1) (tisa_setreg x (word_add (tregs t x) (word 1)) t)) /\
    tisa_x86_early_head mc pc oh x n k ob oend C /\
    tisa_x86_early_latch mc pc ol x k oh oend C /\
    (!j. j < nv ==> tisa_x86_runs mc pc ob ol epi (Pj j) (Pj j) body C)
    ==> !m j. j + m = nv ==>
         tisa_x86_runsf mc pc oh oend epi (Pj j) Inv
           (\t. tisa_early_iter m (\st. tisa_exec body st) x k j t) C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[tisa_x86_runsf; tisa_early_iter] THEN X_GEN_TAC `t:tisa_state` THEN DISCH_TAC THEN
  (SUBGOAL_THEN `tregs t x = word j /\ val(tregs t n) = nv /\ tisa_bool (tregs t k) /\ (Inv:tisa_state->bool) t`
   STRIP_ASSUME_TAC THENL [TISA_FACTS_AT_TAC `j:num` `t:tisa_state`; ALL_TAC]) THEN
  (SUBGOAL_THEN `val(tregs t x) = j` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
     MP_TAC(ISPEC `tregs t n` VAL_BOUND_64) THEN ASM_ARITH_TAC;
     ALL_TAC]) THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `tisa_bool (tregs t k)`) o SPEC `t:tisa_state` o
              REWRITE_RULE[tisa_x86_early_head] o
              check (fun th -> can (find_term ((=) `tisa_x86_early_head`)) (concl th))) THEN
  ASM_SIMP_TAC[TISA_SETREG_SAME] THEN BETA_TAC THENL
   [(* no iteration left: j = nv, the head exits *)
    SUBGOAL_THEN `j:num = nv` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LT_REFL] THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ tisa_x86_rel t s /\ read RIP s = word(pc + oend)` THEN
    ASM_REWRITE_TAC[tisa_x86_postf] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `j < nv` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[tisa_early_check] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `tregs t k = word 0` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [(* k is 0: the head leaves *)
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ tisa_x86_rel t s /\ read RIP s = word(pc + oend)` THEN
    ASM_REWRITE_TAC[tisa_x86_postf] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the head enters the body *)
  MATCH_MP_TAC(MATCH_MP TISA_TRANS (ASSUME `C ,, C = (C:x86state->x86state->bool)`)) THEN
  EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ob) /\ tisa_x86_rel t s` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ tisa_x86_rel t s /\ read RIP s = word(pc + ob)` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:tisa_state` o REWRITE_RULE[tisa_x86_runs] o
              C MATCH_MP (ASSUME `j < nv`) o SPEC `j:num` o
              check (fun th -> can (find_term ((=) `tisa_x86_runs`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `tisa_exec body t` tisa_result_CASES) THEN
  REWRITE_TAC[tisa_then] THEN DISCH_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                    tisa_x86_postf (pc + ol) (pc + epi) (Pj (j:num)) (TStop a0 a1) s` THEN
    ASM_REWRITE_TAC[tisa_x86_postf]] THEN
  ASM_CASES_TAC `(Pj:num->tisa_state->bool) j a` THENL
   [ALL_TAC;
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                    tisa_x86_postf (pc + ol) (pc + epi) (Pj (j:num)) (TCont a) s` THEN
    ASM_REWRITE_TAC[tisa_x86_postf]] THEN
  SUBGOAL_THEN `tregs a x = word j /\ val(tregs a n) = nv /\ tisa_bool (tregs a k) /\ (Inv:tisa_state->bool) a`
  STRIP_ASSUME_TAC THENL [TISA_FACTS_AT_TAC `j:num` `a:tisa_state`; ALL_TAC] THEN
  MATCH_MP_TAC(MATCH_MP TISA_TRANS (ASSUME `C ,, C = (C:x86state->x86state->bool)`)) THEN
  EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ol) /\ tisa_x86_rel a s` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                    tisa_x86_postf (pc + ol) (pc + epi) (Pj (j:num)) (TCont a) s` THEN
    ASM_REWRITE_TAC[tisa_x86_postf] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `tisa_bool (tregs a k)`) o SPEC `a:tisa_state` o
              REWRITE_RULE[tisa_x86_early_latch] o
              check (fun th -> can (find_term ((=) `tisa_x86_early_latch`)) (concl th))) THEN
  ASM_REWRITE_TAC[tisa_early_check] THEN
  ASM_CASES_TAC `tregs a k = word 0` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [(* k became 0: the latch leaves *)
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + oend) /\ tisa_x86_rel a s` THEN
    ASM_REWRITE_TAC[tisa_x86_postf] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(MATCH_MP TISA_TRANS (ASSUME `C ,, C = (C:x86state->x86state->bool)`)) THEN
  EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + oh) /\
                  tisa_x86_rel (tisa_setreg x (word_add (tregs a x) (word 1)) a) s` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j + 1` o
                check (fun th -> can (find_term ((=) `tisa_early_iter`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[tisa_x86_runsf] THEN
  DISCH_THEN(MP_TAC o SPEC `tisa_setreg x (word_add (tregs a x) (word 1)) a`) THEN
  ANTS_TAC THENL [TISA_NEXT_TAC `j:num` `a:tisa_state`; ALL_TAC] THEN
  ASM_REWRITE_TAC[TISA_EARLY_ITER_SETREG]);;

let TISA_EARLY_LOOP_RUNS_OF = prove
 (`!mc pc oa oe epi P Q x n k cap body C nv.
        (!t. P t ==> val(tregs t n) = nv) /\
        tisa_x86_runsf mc pc oa oe epi P Q
          (\t. tisa_then (tisa_loop_entry x n cap t)
                         (\u. tisa_early_iter nv (\st. tisa_exec body st) x k 0 u)) C
        ==> tisa_x86_runs mc pc oa oe epi P Q (TEarlyLoop x n k cap body) C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_x86_runs; tisa_x86_runsf; TISA_EARLY_LOOP_SPLIT] THEN
  STRIP_TAC THEN X_GEN_TAC `t:tisa_state` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:tisa_state`) THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* From the pieces to the loop statement.                                    *)
(* ------------------------------------------------------------------------- *)

let TISA_COUNT_LOOP_RUNS_OF = prove
 (`!mc pc oa oe epi P Q x n cap body C nv.
        (!t. P t ==> val(tregs t n) = nv) /\
        tisa_x86_runsf mc pc oa oe epi P Q
          (\t. tisa_then (tisa_loop_entry x n cap t)
                         (\u. tisa_count_iter nv (\st. tisa_exec body st) x 0 u)) C
        ==> tisa_x86_runs mc pc oa oe epi P Q (TCountLoop x n cap body) C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_x86_runs; tisa_x86_runsf; TISA_COUNT_LOOP_SPLIT] THEN
  STRIP_TAC THEN X_GEN_TAC `t:tisa_state` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:tisa_state`) THEN ASM_SIMP_TAC[]);;

(* A parameter fixed by the facts, then forgotten. *)
let TISA_RUNS_PARAM = prove
 (`!mc pc oa oe epi P (Pn:num->tisa_state->bool) Q R S C.
        (!nv. tisa_x86_runs mc pc oa oe epi (Pn nv) (Q nv) S C) /\
        (!t. P t ==> ?nv. Pn nv t) /\
        (!nv t. Q nv t ==> R t)
        ==> tisa_x86_runs mc pc oa oe epi P R S C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_x86_runs] THEN STRIP_TAC THEN
  X_GEN_TAC `t:tisa_state` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(P:tisa_state->bool) t`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `nv:num`) THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(Pn:num->tisa_state->bool) nv t`) o SPECL [`nv:num`; `t:tisa_state`]) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_POSTCONDITION_THM) THEN
  X_GEN_TAC `s:x86state` THEN BETA_TAC THEN
  STRUCT_CASES_TAC(ISPEC `tisa_exec S t` tisa_result_CASES) THEN
  REWRITE_TAC[tisa_x86_postf] THEN ASM_MESON_TAC[]);;

let TISA_SETREG_FWORD = prove
 (`!x v t i. ~(x = 0) ==> tisa_fword (tisa_setreg x v t) i = tisa_fword t i`,
  SIMP_TAC[tisa_fword; tisa_read; tisa_frame; tisa_setreg; tregs; tmem]);;

(* The head and latch of a count loop, per instance. *)
let TISA_HEAD_TAC execth stops =
  REWRITE_TAC[tisa_x86_head; tisa_x86_rel] THEN X_GEN_TAC `t:tisa_state` THEN
  TISA_NAME_STATE_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN TISA_RUN_TAC execth `pc:num` stops 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN TISA_TARGET_ARITH_TAC;;

let TISA_LATCH_TAC execth stops =
  REWRITE_TAC[tisa_x86_latch; tisa_x86_rel; tisa_setreg; tregs; tmem] THEN
  X_GEN_TAC `t:tisa_state` THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  TISA_NAME_STATE_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN TISA_RUN_TAC execth `pc:num` stops 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let tisa_head_goal mc oh x n ob oend =
  parse_term (Printf.sprintf "tisa_x86_head %s pc %d %d %d %d %d (%s)" mc oh x n ob oend tisa_frame_str);;

let tisa_latch_goal mc ol x oh =
  parse_term (Printf.sprintf "tisa_x86_latch %s pc %d %d %d (%s)" mc ol x oh tisa_frame_str);;

(* ------------------------------------------------------------------------- *)
(* Facts through statements without proofs: a loop's invariant is the       *)
(* greatest set of its entry facts that its body preserves.                  *)
(* ------------------------------------------------------------------------- *)

let rec tisa_post_facts node f =
  match tisa_cname node with
  | "TSkip" | "TFund" -> f
  | "TSeq" -> let _,[a;b] = strip_comb node in tisa_post_facts b (tisa_post_facts a f)
  | "TIf" -> let _,[_;a;b] = strip_comb node in tisa_meet (tisa_post_facts a f) (tisa_post_facts b f)
  | "TInstr" -> tisa_transfer (rand node) f
  | "TReturn" -> None
  | "TCountLoop" | "TEarlyLoop" -> tisa_loop_invariant node f
  | k -> failwith ("tisa_post_facts: " ^ k)
and tisa_loop_invariant node f =
  let _,args = strip_comb node in
  let x = tisa_num (hd args) and body = last args in
  let rec fix i =
    let i' = tisa_meet i (tisa_kill x (tisa_post_facts body i)) in
    if i' = i then i else fix i' in
  match f with None -> None | Some _ -> fix (tisa_kill x f);;

(* "word j0" in a facts text, as a function of j0 *)
let tisa_facts_fun jname text =
  mk_abs(mk_var(jname, `:num`), parse_term text);;

(* ------------------------------------------------------------------------- *)
(* The generator's loop case.                                                *)
(* ------------------------------------------------------------------------- *)

let tisa_frame_tm () = parse_term tisa_frame_str;;

let TISA_PRESERVE_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC[TISA_SETREG_FWORD; ARITH_EQ] THEN
  REWRITE_TAC[tisa_setreg; tregs] THEN CONV_TAC NUM_REDUCE_CONV THEN
  TISA_FACTS_CLOSE_TAC;;

let tisa_prove_count_loop_unguarded ctx node path f cursor =
  let mc = ctx.mc and epi = ctx.epi in
  let _,[x;n;cap;body] = strip_comb node in
  let xi = tisa_num x and ni = tisa_num n in
  let spans = tisa_span ctx path in
  let (oe0,_,_) = el 0 spans and (oh,lh,_) = el 1 spans and (ol,ll,_) = el 2 spans in
  let ob = oh + lh and oend = ol + ll in
  if oe0 <> cursor then failwith ("loop entry not at the cursor at " ^ path);
  let depth = length !tisa_extra_facts in
  let jn = "j" ^ string_of_int depth and nvn = "nv" ^ string_of_int depth in
  let jv = mk_var(jn, `:num`) and nvv = mk_var(nvn, `:num`) in
  let inv = tisa_loop_invariant node f in
  let saved = !tisa_extra_facts in
  let nfact = Printf.sprintf "val(tregs t %d) = %s" ni nvn in
  let xfact j = Printf.sprintf "tregs t %d = word %s" xi j in
  tisa_extra_facts := saved @ [nfact];
  let p_nv = tisa_facts_text ctx.nregions f in
  tisa_extra_facts := saved @ [xfact "0"; nfact];
  let p_0 = tisa_facts_text ctx.nregions inv in
  tisa_extra_facts := saved @ [xfact jn; nfact];
  let pj = tisa_facts_text ctx.nregions inv in
  let thb,sb,eb,fb = tisa_prove_stmt ctx body (tisa_child path 0) inv ob in
  let qb = tisa_facts_text ctx.nregions fb in
  tisa_extra_facts := saved;
  let p_entry = tisa_facts_text ctx.nregions f and r_exit = tisa_facts_text ctx.nregions inv in
  if sb <> ob || eb <> ol then failwith ("loop body not between head and latch at " ^ path);
  let thb = if qb = pj then thb else MATCH_MP TISA_RUNS_WEAKEN (CONJ (tisa_imp_facts qb pj) thb) in
  (* the iterations *)
  let pcv = `pc:num` and frame = tisa_frame_tm () in
  let hth = time_prove (path ^ " head") (tisa_head_goal mc oh xi ni ob oend) (TISA_HEAD_TAC ctx.execth [ob; oend]) in
  let lth = time_prove (path ^ " latch") (tisa_latch_goal mc ol xi oh) (TISA_LATCH_TAC ctx.execth [oh]) in
  let lem = BETA_RULE (ISPECL [parse_term mc; pcv; mk_small_numeral oh; mk_small_numeral ob; mk_small_numeral ol;
                               mk_small_numeral oend; mk_small_numeral epi; x; n; tisa_facts_fun jn pj; body;
                               frame; nvv] TISA_COUNT_ITER_RUNSF) in
  let ants = conjuncts(lhand(concl lem)) in
  let idx = tisa_side_prove (path ^ " index") (el 1 ants, REPEAT GEN_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC) in
  let pres = tisa_side_prove (path ^ " preserve") (el 2 ants, TISA_PRESERVE_TAC) in
  let bodyth = GEN jv (DISCH (mk_binary "<" (jv, nvv)) thb) in
  let ith = MP lem (end_itlist CONJ [TISA_FRAME_IDEMPOT; idx; pres; hth; lth;
                                     CONV_RULE (ONCE_DEPTH_CONV (ALPHA_CONV `j:num`)) bodyth]) in
  let ith = MP (SPECL [nvv; `0`] ith) (ARITH_RULE (mk_eq(mk_binary "+" (`0`, nvv), nvv))) in
  let ith = BETA_RULE (INST [`0`, jv] ith) in
  (* the entry *)
  let eg = parse_term (Printf.sprintf "tisa_x86_runsf %s pc %d %d %d %s %s (\\t. tisa_loop_entry %d %d %s t) (%s)"
                         mc oe0 oh epi p_nv p_0 xi ni (string_of_term cap) tisa_frame_str) in
  let eth = time_prove (path ^ " entry") (mk_imp(ctx.global, eg))
              (REWRITE_TAC[tisa_x86_runsf; tisa_loop_entry] THEN TISA_RUNS_TAC ctx.execth [oh; epi]) in
  let eth = tisa_cut_global ctx eth in
  (* entry, then the iterations; the loop statement; the bound forgotten *)
  let cth = BETA_RULE (MATCH_MP TISA_THEN_RUNSF (CONJ TISA_FRAME_IDEMPOT (CONJ eth ith))) in
  let lth2 = MATCH_MP TISA_COUNT_LOOP_RUNS_OF
               (CONJ (tisa_side_prove (path ^ " bound") (parse_term (Printf.sprintf "!t:tisa_state. %s t ==> val(tregs t %d) = %s" p_nv ni nvn),
                            GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC)) cth) in
  let pnfun = mk_abs(nvv, parse_term p_nv) and qfun = mk_abs(nvv, parse_term (
                 (tisa_extra_facts := saved @ [xfact nvn; nfact];
                  let s = tisa_facts_text ctx.nregions inv in tisa_extra_facts := saved; s))) in
  let plem = BETA_RULE (ISPECL [parse_term mc; pcv; mk_small_numeral oe0; mk_small_numeral oend;
                                mk_small_numeral epi; parse_term p_entry; pnfun; qfun; parse_term r_exit;
                                node; frame] TISA_RUNS_PARAM) in
  let pants = conjuncts(lhand(concl plem)) in
  let ex = tisa_side_prove (path ^ " exists") (el 1 pants, GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC (mk_comb(`val:int64->num`, mk_comb(mk_comb(`tregs`, `t:tisa_state`), n))) THEN TISA_FACTS_CLOSE_TAC) in
  let wk = tisa_side_prove (path ^ " weaken") (el 2 pants, REPEAT GEN_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC) in
  let th = MP plem (end_itlist CONJ [GEN nvv lth2; ex; wk]) in
  (th, oe0, oend, inv);;

let TISA_EARLY_HEAD_TAC execth stops =
  REWRITE_TAC[tisa_x86_early_head; tisa_x86_rel; tisa_bool] THEN X_GEN_TAC `t:tisa_state` THEN
  TISA_NAME_STATE_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN TISA_RUN_TAC execth `pc:num` stops 1 THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_REFL; VAL_EQ_0]) THEN ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN TISA_TARGET_ARITH_TAC;;

let TISA_EARLY_LATCH_TAC execth stops =
  REWRITE_TAC[tisa_x86_early_latch; tisa_x86_rel; tisa_setreg; tregs; tmem; tisa_bool] THEN
  X_GEN_TAC `t:tisa_state` THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  TISA_NAME_STATE_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN TISA_RUN_TAC execth `pc:num` stops 1 THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_REFL; VAL_EQ_0]) THEN ASM_REWRITE_TAC[];;

let tisa_early_head_goal mc oh x n k ob oend =
  parse_term (Printf.sprintf "tisa_x86_early_head %s pc %d %d %d %d %d %d (%s)" mc oh x n k ob oend tisa_frame_str);;

let tisa_early_latch_goal mc ol x k oh oend =
  parse_term (Printf.sprintf "tisa_x86_early_latch %s pc %d %d %d %d %d (%s)" mc ol x k oh oend tisa_frame_str);;

let tisa_prove_early_loop_unguarded ctx node path f cursor =
  let mc = ctx.mc and epi = ctx.epi in
  let _,[x;n;k;cap;body] = strip_comb node in
  let xi = tisa_num x and ni = tisa_num n and ki = tisa_num k in
  let spans = tisa_span ctx path in
  let (oe0,_,_) = el 0 spans and (oh,lh,_) = el 1 spans and (ol,ll,_) = el 2 spans in
  let ob = oh + lh and oend = ol + ll in
  if oe0 <> cursor then failwith ("loop entry not at the cursor at " ^ path);
  let depth = length !tisa_extra_facts in
  let jn = "j" ^ string_of_int depth and nvn = "nv" ^ string_of_int depth in
  let jv = mk_var(jn, `:num`) and nvv = mk_var(nvn, `:num`) in
  let inv = tisa_loop_invariant node f in
  (* unreachable code (facts None, the precondition F) needs no Boolean *)
  (match inv with None -> () | Some(_,bs) when mem ki bs -> () | _ -> failwith ("loop continuation not known Boolean at " ^ path));
  let saved = !tisa_extra_facts in
  let nfact = Printf.sprintf "val(tregs t %d) = %s" ni nvn in
  let xfact j = Printf.sprintf "tregs t %d = word %s" xi j in
  tisa_extra_facts := saved @ [nfact];
  let p_nv = tisa_facts_text ctx.nregions f in
  tisa_extra_facts := saved @ [xfact "0"; nfact];
  let p_0 = tisa_facts_text ctx.nregions inv in
  tisa_extra_facts := saved @ [xfact jn; nfact];
  let pj = tisa_facts_text ctx.nregions inv in
  let thb,sb,eb,fb = tisa_prove_stmt ctx body (tisa_child path 0) inv ob in
  let qb = tisa_facts_text ctx.nregions fb in
  tisa_extra_facts := saved;
  let p_entry = tisa_facts_text ctx.nregions f and r_exit = tisa_facts_text ctx.nregions inv in
  if sb <> ob || eb <> ol then failwith ("loop body not between head and latch at " ^ path);
  let thb = if qb = pj then thb else MATCH_MP TISA_RUNS_WEAKEN (CONJ (tisa_imp_facts qb pj) thb) in
  let pcv = `pc:num` and frame = tisa_frame_tm () in
  let hth = time_prove (path ^ " early head") (tisa_early_head_goal mc oh xi ni ki ob oend)
              (TISA_EARLY_HEAD_TAC ctx.execth [ob; oend]) in
  let lth = time_prove (path ^ " early latch") (tisa_early_latch_goal mc ol xi ki oh oend)
              (TISA_EARLY_LATCH_TAC ctx.execth [oh; oend]) in
  let lem = BETA_RULE (ISPECL [parse_term mc; pcv; mk_small_numeral oh; mk_small_numeral ob; mk_small_numeral ol;
                               mk_small_numeral oend; mk_small_numeral epi; x; n; k; parse_term r_exit;
                               tisa_facts_fun jn pj; body; frame; nvv] TISA_EARLY_ITER_RUNSF) in
  let ants = conjuncts(lhand(concl lem)) in
  let idx = tisa_side_prove (path ^ " index") (el 1 ants, REPEAT GEN_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC) in
  let pres = tisa_side_prove (path ^ " preserve") (el 2 ants, TISA_PRESERVE_TAC) in
  let bodyth = GEN jv (DISCH (mk_binary "<" (jv, nvv)) thb) in
  let ith = MP lem (end_itlist CONJ [TISA_FRAME_IDEMPOT; idx; pres; hth; lth;
                                     CONV_RULE (ONCE_DEPTH_CONV (ALPHA_CONV `j:num`)) bodyth]) in
  let ith = MP (SPECL [nvv; `0`] ith) (ARITH_RULE (mk_eq(mk_binary "+" (`0`, nvv), nvv))) in
  let ith = BETA_RULE (INST [`0`, jv] ith) in
  let eg = parse_term (Printf.sprintf "tisa_x86_runsf %s pc %d %d %d %s %s (\\t. tisa_loop_entry %d %d %s t) (%s)"
                         mc oe0 oh epi p_nv p_0 xi ni (string_of_term cap) tisa_frame_str) in
  let eth = time_prove (path ^ " entry") (mk_imp(ctx.global, eg))
              (REWRITE_TAC[tisa_x86_runsf; tisa_loop_entry] THEN TISA_RUNS_TAC ctx.execth [oh; epi]) in
  let eth = tisa_cut_global ctx eth in
  let cth = BETA_RULE (MATCH_MP TISA_THEN_RUNSF (CONJ TISA_FRAME_IDEMPOT (CONJ eth ith))) in
  let lth2 = MATCH_MP TISA_EARLY_LOOP_RUNS_OF
               (CONJ (tisa_side_prove (path ^ " bound") (parse_term (Printf.sprintf "!t:tisa_state. %s t ==> val(tregs t %d) = %s" p_nv ni nvn),
                            GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC)) cth) in
  let pnfun = mk_abs(nvv, parse_term p_nv) and qfun = mk_abs(nvv, parse_term r_exit) in
  let plem = BETA_RULE (ISPECL [parse_term mc; pcv; mk_small_numeral oe0; mk_small_numeral oend;
                                mk_small_numeral epi; parse_term p_entry; pnfun; qfun; parse_term r_exit;
                                node; frame] TISA_RUNS_PARAM) in
  let pants = conjuncts(lhand(concl plem)) in
  let ex = tisa_side_prove (path ^ " exists") (el 1 pants, GEN_TAC THEN STRIP_TAC THEN
                   EXISTS_TAC (mk_comb(`val:int64->num`, mk_comb(mk_comb(`tregs`, `t:tisa_state`), n))) THEN
                   TISA_FACTS_CLOSE_TAC) in
  let wk = tisa_side_prove (path ^ " weaken") (el 2 pants, REPEAT GEN_TAC THEN REWRITE_TAC[]) in
  let th = MP plem (end_itlist CONJ [GEN nvv lth2; ex; wk]) in
  (th, oe0, oend, inv);;

(* A failed loop proof must not leave its index and bound facts behind. *)
let tisa_guard_extras prover ctx node path f cursor =
  let saved = !tisa_extra_facts in
  try prover ctx node path f cursor
  with e -> (tisa_extra_facts := saved; raise e);;

let tisa_prove_count_loop = tisa_guard_extras tisa_prove_count_loop_unguarded;;
let tisa_prove_early_loop = tisa_guard_extras tisa_prove_early_loop_unguarded;;

let () = tisa_loop_hook := (fun ctx node path f cursor ->
  match tisa_cname node with
  | "TCountLoop" -> tisa_prove_count_loop ctx node path f cursor
  | "TEarlyLoop" -> tisa_prove_early_loop ctx node path f cursor
  | k -> failwith ("loops: " ^ k));;
