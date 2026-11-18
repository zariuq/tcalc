(* Weakest preconditions for early-exit loops. *)

needs "native/hol/tisa_wp.ml";;

let TISA_RWP_MONO_Q = prove
 (`!r Q Q' R. (!s. Q s ==> Q' s) ==> tisa_rwp r Q R ==> tisa_rwp r Q' R`,
  REWRITE_TAC[tisa_rwp] THEN MESON_TAC[]);;

let TISA_WP_EARLY_LOOP = prove
 (`!(Inv:num->num->tisa_state->bool) x n k cap body Q R st.
     (cap < val(tregs st n) ==> R 2 (tisa_failst 2 st)) /\
     (~(cap < val(tregs st n)) ==> Inv (val(tregs st n)) 0 st) /\
     (!N j s0. j < N /\ Inv N j s0
               ==> (~tisa_bool (tregs (tisa_setreg x (word j) s0) k)
                    ==> R 3 (tisa_failst 3 (tisa_setreg x (word j) s0))) /\
                   (tisa_bool (tregs (tisa_setreg x (word j) s0) k) /\
                    tregs (tisa_setreg x (word j) s0) k = word 0
                    ==> Q (tisa_setreg x (word j) s0)) /\
                   (tisa_bool (tregs (tisa_setreg x (word j) s0) k) /\
                    ~(tregs (tisa_setreg x (word j) s0) k = word 0)
                    ==> tisa_wp body
                          (\s2. (~tisa_bool (tregs s2 k) ==> R 3 (tisa_failst 3 s2)) /\
                                (tisa_bool (tregs s2 k) /\ tregs s2 k = word 0 ==> Q s2) /\
                                (tisa_bool (tregs s2 k) /\ ~(tregs s2 k = word 0)
                                 ==> Inv N (j + 1) s2))
                          R (tisa_setreg x (word j) s0))) /\
     (!N s. Inv N N s ==> Q (tisa_setreg x (word N) s))
     ==> tisa_wp (TEarlyLoop x n k cap body) Q R st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tisa_wp; tisa_exec] THEN
  COND_CASES_TAC THENL [ASM_SIMP_TAC[TISA_FAIL_STOP; TISA_RWP_STOP]; ALL_TAC] THEN
  SUBGOAL_THEN `(Inv:num->num->tisa_state->bool) (val(tregs st n)) 0 st` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `N = val(tregs st n)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!m j s0. j + m = N /\ (Inv:num->num->tisa_state->bool) N j s0
             ==> tisa_rwp (tisa_early_iter m (\st'. tisa_exec body st') x k j s0) Q R`
   (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[ADD_CLAUSES]) THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tisa_early_iter] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `j:num = N`)) THEN
    REWRITE_TAC[TISA_RWP_CONT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `j:num`; `s0:tisa_state`] o
    check (fun th -> can (find_term ((=) `tisa_wp`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `s1 = tisa_setreg x (word j) s0` THEN STRIP_TAC THEN
  REWRITE_TAC[tisa_early_check] THEN
  ASM_CASES_TAC `tisa_bool (tregs s1 k)` THEN
  ASM_REWRITE_TAC[TISA_FAIL_STOP; TISA_RWP_STOP] THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  ASM_CASES_TAC `tregs s1 k = word 0` THEN ASM_REWRITE_TAC[TISA_RWP_CONT] THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[TISA_RWP_THEN] THEN BETA_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `tisa_wp`)) (concl th))) THEN
  ASM_REWRITE_TAC[tisa_wp] THEN MATCH_MP_TAC TISA_RWP_MONO_Q THEN
  X_GEN_TAC `s2:tisa_state` THEN BETA_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `tisa_bool (tregs s2 k)` THEN
  ASM_REWRITE_TAC[TISA_FAIL_STOP; TISA_RWP_STOP] THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  ASM_CASES_TAC `tregs s2 k = word 0` THEN ASM_REWRITE_TAC[TISA_RWP_CONT] THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term ((=) `tisa_early_iter`)) (concl th) && is_forall (concl th))) THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]]);;
