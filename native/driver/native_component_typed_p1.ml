(* p1 component laws depend on entry typing, not a U64-only hot-input list. *)
needs "native/driver/native_component_typed.ml";;
needs "native/driver/native_component_p1.ml";;

let component_p1_wf = new_definition
 `component_p1_wf p <=>
    LENGTH(tisa_decls p) <= 9 /\ tisa_stmt_ok (tisa_decls p) (tisa_root p)`;;

let COMPONENT_P1_U64_PROFILE = prove
 (`!p. tisa_leaf_wf p <=> component_p1_wf p /\
    ALL (\v:num#tisa_ty#num. FST(SND v) = TyU64) (tisa_inits p)`,
  REWRITE_TAC[tisa_leaf_wf;component_p1_wf] THEN MESON_TAC[]);;

let TISA_TYPED_RUN_FUEL_FRAME = prove
 (`!p t k u. component_p1_wf p /\ tisa_entry_ok p t /\ tisa_run p t = TStop k u
     ==> tisa_fuel_le (tisa_decls p) t u`,
  GEN_TAC THEN ONCE_REWRITE_TAC[TISA_PROG_CASES] THEN
  REWRITE_TAC[component_p1_wf;tisa_decls;tisa_inits;tisa_root] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `tisa_frame_sep (tisa_decls p) t` ASSUME_TAC THENL
   [ASM_MESON_TAC[TISA_ENTRY_FRAME_SEP];ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `tisa_run`)) (concl th))) THEN
  ASM_REWRITE_TAC[tisa_run;tisa_root] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `tisa_fuel_le (tisa_decls p) t
      (tisa_state_of (tisa_then (tisa_exec (tisa_root p) t) (\s. tisa_fail 2 s)))`
    MP_TAC THENL
   [MATCH_MP_TAC TISA_FUEL_LE_THEN THEN ASM_SIMP_TAC[TISA_FUEL_LE_EXEC] THEN
    X_GEN_TAC `w:tisa_state` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC TISA_FUEL_LE_FAIL THEN
    MP_TAC(SPECL [`tisa_root p`;`tisa_decls p`;`t:tisa_state`] TISA_FUEL_LE_EXEC) THEN
    ASM_REWRITE_TAC[tisa_state_of] THEN ASM_MESON_TAC[TISA_FUEL_LE_SEP];
    ASM_REWRITE_TAC[tisa_state_of]]);;

let COMPONENT_P1_TYPED_OK = prove
 (`!p. component_p1_wf p ==> component_typed_ok (component_of_p1 p)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[component_typed_ok;COMPONENT_P1_FIELDS;COMPONENT_P1_ENTRY] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[component_p1_wf]) THEN
  ASM_REWRITE_TAC[TISA_RUN_STOP] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC TISA_TYPED_RUN_FUEL_FRAME THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[TISA_RUN_STATUS]]);;

let native_component_typed_p1_theorems = native_component_typed_theorems @
 ["COMPONENT_P1_U64_PROFILE",COMPONENT_P1_U64_PROFILE;
  "TISA_TYPED_RUN_FUEL_FRAME",TISA_TYPED_RUN_FUEL_FRAME;
  "COMPONENT_P1_TYPED_OK",COMPONENT_P1_TYPED_OK];;
