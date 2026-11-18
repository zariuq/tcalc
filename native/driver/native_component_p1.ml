(* Every admitted p1 leaf implements the common native-component interface. *)
needs "native/driver/native_component.ml";;

let component_of_p1 = new_definition
 `component_of_p1 p = NativeComponent (tisa_decls p) (tisa_inits p) (tisa_run p)`;;

let COMPONENT_P1_FIELDS = prove
 (`!p. component_decls(component_of_p1 p) = tisa_decls p /\
       component_inits(component_of_p1 p) = tisa_inits p /\
       component_run(component_of_p1 p) = tisa_run p`,
  REWRITE_TAC[component_of_p1;component_decls;component_inits;component_run]);;

let COMPONENT_P1_ENTRY = prove
 (`!p t. component_entry (component_of_p1 p) t <=> tisa_entry_ok p t`,
  GEN_TAC THEN ONCE_REWRITE_TAC[TISA_PROG_CASES] THEN
  REWRITE_TAC[component_entry;COMPONENT_P1_FIELDS;tisa_entry_ok;tisa_decls;tisa_inits]);;

let COMPONENT_P1_PLACE = prove
 (`!p mc pc t stackpointer.
     component_place (component_of_p1 p) mc pc t stackpointer <=>
     tisa_leaf_place p mc pc t stackpointer`,
  REWRITE_TAC[component_place;COMPONENT_P1_FIELDS;tisa_leaf_place]);;

let COMPONENT_P1_IMAGE = prove
 (`!p mc pc. component_image (component_of_p1 p) mc pc <=> tisa_leaf_spec p mc pc`,
  REWRITE_TAC[component_image;tisa_leaf_spec;COMPONENT_P1_ENTRY;COMPONENT_P1_PLACE;COMPONENT_P1_FIELDS]);;

let TISA_RUN_FUEL_FRAME = prove
 (`!p t k u.
     tisa_leaf_wf p /\ tisa_entry_ok p t /\ tisa_run p t = TStop k u
     ==> tisa_fuel_le (tisa_decls p) t u`,
  GEN_TAC THEN ONCE_REWRITE_TAC[TISA_PROG_CASES] THEN
  REWRITE_TAC[tisa_leaf_wf;tisa_decls;tisa_inits;tisa_root] THEN
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

let COMPONENT_P1_OK = prove
 (`!p. tisa_leaf_wf p ==> component_ok (component_of_p1 p)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[component_ok;COMPONENT_P1_FIELDS;COMPONENT_P1_ENTRY] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[tisa_leaf_wf]) THEN
  ASM_REWRITE_TAC[TISA_RUN_STOP] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC TISA_RUN_FUEL_FRAME THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[TISA_RUN_STATUS]]);;

let native_component_p1_theorems =
 ["COMPONENT_P1_FIELDS",COMPONENT_P1_FIELDS;"COMPONENT_P1_ENTRY",COMPONENT_P1_ENTRY;
  "COMPONENT_P1_PLACE",COMPONENT_P1_PLACE;"COMPONENT_P1_IMAGE",COMPONENT_P1_IMAGE;
  "TISA_RUN_FUEL_FRAME",TISA_RUN_FUEL_FRAME;"COMPONENT_P1_OK",COMPONENT_P1_OK];;
