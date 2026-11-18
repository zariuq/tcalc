(* A checked-entry source adapter preserves the existing component profile. *)
needs "native/driver/native_component_typed.ml";;

let component_guarded = new_definition
 `component_guarded c = NativeComponent (component_decls c) []
    (\t. if tisa_init_ok t (component_inits c) then component_run c t else tisa_fail 3 t)`;;

let COMPONENT_GUARDED_FIELDS = prove
 (`!c. component_decls(component_guarded c) = component_decls c /\
       component_inits(component_guarded c) = [] /\
       (!t. component_run (component_guarded c) t =
        if tisa_init_ok t (component_inits c) then component_run c t else tisa_fail 3 t)`,
  REWRITE_TAC[component_guarded;component_decls;component_inits;component_run]);;

let COMPONENT_GUARDED_ENTRY = prove
 (`!c t. component_entry (component_guarded c) t <=>
    val(tisa_frame t) + 192 <= 2 EXP 64 /\
    val(tisa_fword t 21) <= val(tisa_fword t 20) /\ tisa_decls_ok t 0 (component_decls c)`,
  REWRITE_TAC[component_entry;COMPONENT_GUARDED_FIELDS;tisa_init_ok]);;

let COMPONENT_GUARDED_TYPED_ENTRY = prove
 (`!c t. component_entry (component_guarded c) t /\ tisa_init_ok t (component_inits c)
    <=> component_entry c t`,
  REWRITE_TAC[COMPONENT_GUARDED_ENTRY;component_entry] THEN MESON_TAC[]);;

let COMPONENT_GUARDED_FRAME_SEP = prove
 (`!c t. LENGTH(component_decls c) <= 9 /\ component_entry (component_guarded c) t
    ==> tisa_frame_sep (component_decls c) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`component_decls c`;`[]:(num#tisa_ty#num)list`;`TSkip`;`t:tisa_state`]
    TISA_ENTRY_FRAME_SEP) THEN
  ASM_REWRITE_TAC[tisa_entry_ok;COMPONENT_GUARDED_ENTRY;tisa_init_ok] THEN
  ASM_MESON_TAC[COMPONENT_GUARDED_ENTRY]);;

let COMPONENT_GUARDED_ON_TYPED_ENTRY = prove
 (`!c t. component_entry c t
    ==> component_run (component_guarded c) t = component_run c t`,
  SIMP_TAC[COMPONENT_GUARDED_FIELDS;component_entry]);;

let COMPONENT_GUARDED_INVALID = prove
 (`!c t. ~tisa_init_ok t (component_inits c)
    ==> component_run (component_guarded c) t = tisa_fail 3 t`,
  SIMP_TAC[COMPONENT_GUARDED_FIELDS]);;

let COMPONENT_GUARDED_TOTAL = prove
 (`!c t. component_typed_ok c ==> ?k u. component_run (component_guarded c) t = TStop k u`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[COMPONENT_GUARDED_FIELDS] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC COMPONENT_TYPED_STOP THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[tisa_fail] THEN MAP_EVERY EXISTS_TAC
     [`3`;`tisa_setfword 19 (word 3) (tisa_setfword 18 (word 3) t)`] THEN REFL_TAC]);;

let COMPONENT_GUARDED_LAWS = prove
 (`!c t k u. component_typed_ok c /\ component_entry (component_guarded c) t /\
     component_run (component_guarded c) t = TStop k u
     ==> tisa_fuel_le (component_decls c) t u /\ tisa_fword u 18 = word k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `tisa_init_ok t (component_inits c)` THENL
   [SUBGOAL_THEN `component_entry c t` ASSUME_TAC THENL
     [MP_TAC(SPECL [`c:native_component`;`t:tisa_state`] COMPONENT_GUARDED_TYPED_ENTRY) THEN
      ASM_REWRITE_TAC[];ALL_TAC] THEN
    SUBGOAL_THEN `component_run c t = TStop k u` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `component_run (component_guarded c) t`)) THEN
      ASM_REWRITE_TAC[COMPONENT_GUARDED_FIELDS];ALL_TAC] THEN
    MATCH_MP_TAC COMPONENT_TYPED_RUN_LAWS THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `tisa_frame_sep (component_decls c) t` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPONENT_GUARDED_FRAME_SEP THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[component_typed_ok] o
      check (fun th -> fst(strip_comb(concl th)) = `component_typed_ok`));ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `component_run (component_guarded c) t`)) THEN
  ASM_REWRITE_TAC[COMPONENT_GUARDED_FIELDS;tisa_fail;injectivity "tisa_result"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`component_decls c`;`t:tisa_state`;`3`] TISA_FUEL_LE_FAIL) THEN
    ASM_REWRITE_TAC[tisa_fail;tisa_state_of];
    REWRITE_TAC[TISA_FWORD18_SET]]);;

let COMPONENT_GUARDED_OK = prove
 (`!c. component_typed_ok c ==> component_ok (component_guarded c)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[component_ok] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COMPONENT_GUARDED_FIELDS] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[component_typed_ok]);
    REWRITE_TAC[COMPONENT_GUARDED_FIELDS;ALL];
    GEN_TAC THEN MATCH_MP_TAC COMPONENT_GUARDED_TOTAL THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[COMPONENT_GUARDED_FIELDS] THEN
    MATCH_MP_TAC COMPONENT_GUARDED_LAWS THEN ASM_REWRITE_TAC[]]);;

let native_component_guard_theorems =
 ["COMPONENT_GUARDED_FIELDS",COMPONENT_GUARDED_FIELDS;
  "COMPONENT_GUARDED_ENTRY",COMPONENT_GUARDED_ENTRY;
  "COMPONENT_GUARDED_TYPED_ENTRY",COMPONENT_GUARDED_TYPED_ENTRY;
  "COMPONENT_GUARDED_FRAME_SEP",COMPONENT_GUARDED_FRAME_SEP;
  "COMPONENT_GUARDED_ON_TYPED_ENTRY",COMPONENT_GUARDED_ON_TYPED_ENTRY;
  "COMPONENT_GUARDED_INVALID",COMPONENT_GUARDED_INVALID;
  "COMPONENT_GUARDED_TOTAL",COMPONENT_GUARDED_TOTAL;
  "COMPONENT_GUARDED_LAWS",COMPONENT_GUARDED_LAWS;
  "COMPONENT_GUARDED_OK",COMPONENT_GUARDED_OK];;
