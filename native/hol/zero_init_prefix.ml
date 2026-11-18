(* A supported initial segment is cleared on every initialization outcome. *)
needs "native/hol/zero_init_join.ml";;

let ZINIT_PREFIX_MEM = prove
 (`!(P:num->bool) front back done rest.
     ALL P front /\ APPEND front back = APPEND done rest /\
     (rest = [] \/ ~P(HD rest))
     ==> !slot. MEM slot front ==> MEM slot done`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MEM]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`back:num list`;`done:num list`;`rest:num list`] THEN
  REWRITE_TAC[ALL] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPEC `done:num list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `ds:num list` SUBST_ALL_TAC))) THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o REWRITE_RULE[APPEND] o
      check (fun th -> is_eq(concl th) && can (find_term (zinit_app "APPEND")) (concl th))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_CONS_NIL;HD]) THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[APPEND;CONS_11] o
      check (fun th -> is_eq(concl th) && can (find_term (zinit_app "APPEND")) (concl th))) THEN
    DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT2 th) THEN SUBST_ALL_TAC(CONJUNCT1 th)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`back:num list`;`ds:num list`;`rest:num list`] o
      check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]]);;

let ZINIT_ABI_ZERO_PREFIX = prove
 (`!bw front back d plan used status m.
     zinit_abi_post bw (APPEND front back) d plan used status m /\
     ALL (zinit_supported bw) front
     ==> zinit_zero bw front m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zinit_abi_post] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `done:num list` (X_CHOOSE_THEN `rest:num list` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  SUBGOAL_THEN `!slot:num. MEM slot (front:num list) ==> MEM slot (done:num list)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SPECL [`zinit_supported (bw:num->int64)`;`front:num list`;`back:num list`;
                        `done:num list`;`rest:num list`] ZINIT_PREFIX_MEM) THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `rest:num list = []` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REWRITE_TAC[zinit_zero] THEN MAP_EVERY X_GEN_TAC [`slot:num`;`i:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `MEM (slot:num) (done:num list)` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`slot:num`;`i:num`] o REWRITE_RULE[zinit_zero] o
      check (fun th -> zinit_app "zinit_zero" (concl th))) THEN ASM_REWRITE_TAC[]]);;

let zero_init_prefix_theorems =
 ["ZINIT_PREFIX_MEM",ZINIT_PREFIX_MEM;"ZINIT_ABI_ZERO_PREFIX",ZINIT_ABI_ZERO_PREFIX];;
leaf_audit zero_init_prefix_theorems zero_init_prefix_theorems;;
