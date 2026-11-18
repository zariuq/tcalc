(* Lower source operation ordinals and calls to the shared runtime table. *)
needs "native/procedures/procedure_catalog_controller.ml";;
needs "native/procedures/procedure_call_syntax.ml";;

let procedure_primitive_bindings_ok = new_definition
 `procedure_primitive_bindings_ok original (st:int64 list) <=>
    ALL (\r. val(EL (1 + r) st) + 1 < original) [0;1;2;3;4;5;6;7;8]`;;

let procedure_compile_lowered = define
 `(procedure_compile_lowered catalog original procedures (st:int64 list) NONE = NONE) /\
  (procedure_compile_lowered catalog original procedures st (SOME lowered) =
    if val(EL 0 st) = procedure_catalog_call_tag catalog then
      if procedure_binding_count original procedures <= 2 EXP 64 /\
         val(EL 1 st) < procedures
      then SOME(procedure_linked_call_step (val(EL 0 lowered)) original st)
      else NONE
    else if procedure_primitive_bindings_ok original st then SOME lowered else NONE)`;;

let procedure_compile_step = new_definition
 `procedure_compile_step catalog table original procedures (st:int64 list) =
    procedure_compile_lowered catalog original procedures st
      (procedure_catalog_lower catalog table st)`;;

let PROCEDURE_PRIMITIVE_BINDINGS_EQ = prove
 (`!original st. procedure_primitive_bindings_ok original st <=>
    !r. r < 9 ==> val(EL (1 + r) st) + 1 < original`,
  REWRITE_TAC[procedure_primitive_bindings_ok;ALL] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let PROCEDURE_COMPILE_NONE = prove
 (`!catalog table original procedures st.
    procedure_catalog_lower catalog table st = NONE ==>
    procedure_compile_step catalog table original procedures st = NONE`,
  SIMP_TAC[procedure_compile_step;procedure_compile_lowered]);;

let PROCEDURE_COMPILE_PRIMITIVE = prove
 (`!catalog table original procedures st lowered.
    val(EL 0 (st:int64 list)) < LENGTH catalog /\
    procedure_catalog_lower catalog table st = SOME lowered /\
    procedure_primitive_bindings_ok original st ==>
    procedure_compile_step catalog table original procedures st = SOME lowered`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(EL 0 (st:int64 list)) = procedure_catalog_call_tag catalog)`
  ASSUME_TAC THENL [REWRITE_TAC[procedure_catalog_call_tag] THEN ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_REWRITE_TAC[procedure_compile_step;procedure_compile_lowered]);;

let PROCEDURE_COMPILE_CALL = prove
 (`!catalog table original procedures st lowered.
    val(EL 0 (st:int64 list)) = procedure_catalog_call_tag catalog /\
    procedure_catalog_lower catalog table st = SOME lowered /\
    procedure_binding_count original procedures <= 2 EXP 64 /\
    val(EL 1 st) < procedures ==>
    procedure_compile_step catalog table original procedures st =
      SOME(procedure_linked_call_step (val(EL 0 lowered)) original st)`,
  SIMP_TAC[procedure_compile_step;procedure_compile_lowered]);;

let PROCEDURE_COMPILE_ADMITTED = prove
 (`!catalog table original procedures st out.
    procedure_compile_step catalog table original procedures st = SOME out ==>
    ?lowered. procedure_catalog_lower catalog table st = SOME lowered /\
      ((val(EL 0 st) = procedure_catalog_call_tag catalog /\
        procedure_binding_count original procedures <= 2 EXP 64 /\
        val(EL 1 st) < procedures /\
        out = procedure_linked_call_step (val(EL 0 lowered)) original st) \/
       (~(val(EL 0 st) = procedure_catalog_call_tag catalog) /\
        procedure_primitive_bindings_ok original st /\ out = lowered))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[procedure_compile_step] THEN
  MP_TAC(ISPEC `procedure_catalog_lower catalog table (st:int64 list)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `lowered:int64 list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[procedure_compile_lowered;option_DISTINCT] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT;option_INJ] THEN
  DISCH_TAC THEN EXISTS_TAC `lowered:int64 list` THEN ASM_MESON_TAC[]);;

let PROCEDURE_COMPILE_FIELDS = prove
 (`!catalog table original procedures st out.
    procedure_compile_step catalog table original procedures st = SOME out ==>
    LENGTH out = 18 /\ (!j. 10 <= j /\ j < 18 ==> EL j out = EL j st)`,
  REPEAT GEN_TAC THEN DISCH_THEN
    (X_CHOOSE_THEN `lowered:int64 list` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) o
      MATCH_MP PROCEDURE_COMPILE_ADMITTED) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`val(EL 0 (lowered:int64 list))`;`original:num`;`st:int64 list`]
      PROCEDURE_LINKED_CALL_FIELDS) THEN
    REWRITE_TAC[NATIVE_ABI_StepWords] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PROCEDURE_LINKED_CALL_ARGUMENT_FIELD];
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROCEDURE_CATALOG_LOWER_FIELDS o
      check (fun th -> fst(strip_comb(lhs(concl th))) = `procedure_catalog_lower`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ARITH_RULE `10 <= (j:num) ==> 0 < j`]]);;

let PROCEDURE_COMPILE_OPCODE = prove
 (`!catalog table original procedures st out.
    procedure_compile_step catalog table original procedures st = SOME out ==>
    ?lowered. procedure_catalog_lower catalog table st = SOME lowered /\
              val(EL 0 out) = val(EL 0 lowered)`,
  REPEAT GEN_TAC THEN DISCH_THEN
    (X_CHOOSE_THEN `lowered:int64 list` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) o
      MATCH_MP PROCEDURE_COMPILE_ADMITTED) THEN
  EXISTS_TAC `lowered:int64 list` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
  ASM_REWRITE_TAC[procedure_linked_call_step;procedure_marker_step;EL;HD;WORD_VAL]);;

let PROCEDURE_COMPILE_RUNTIME_CALL_EXACT = prove
 (`!catalog table original procedures st out.
    procedure_compile_step catalog table original procedures st = SOME out /\
    MEM ProcedureCallMarker table ==>
    (val(EL 0 out) = native_operation_offset table ProcedureCallMarker <=>
     val(EL 0 st) = procedure_catalog_call_tag catalog)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `lowered:int64 list` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) o
    MATCH_MP PROCEDURE_COMPILE_OPCODE o
    check (fun th -> fst(strip_comb(lhs(concl th))) = `procedure_compile_step`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROCEDURE_CATALOG_LOWER_ADMITTED o
    check (fun th -> fst(strip_comb(lhs(concl th))) = `procedure_catalog_lower`)) THEN
  MP_TAC(SPECL [`catalog:native_operation list`;`table:native_operation list`;
    `st:int64 list`;`lowered:int64 list`] PROCEDURE_CATALOG_RUNTIME_CALL_EXACT) THEN
  ASM_REWRITE_TAC[]);;

let PROCEDURE_COMPILE_PRIMITIVE_RUN = prove
 (`!catalog table original procedures st out operations b cw (s:A) used.
    procedure_compile_step catalog table original procedures st = SOME out /\
    val(EL 0 st) < LENGTH catalog ==>
    procedure_catalog_primitive catalog operations b st cw s used =
      procedure_table_primitive table operations b out cw s used`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `lowered:int64 list` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) o
    MATCH_MP PROCEDURE_COMPILE_ADMITTED o
    check (fun th -> fst(strip_comb(lhs(concl th))) = `procedure_compile_step`)) THEN
  SUBGOAL_THEN `(out:int64 list) = lowered` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `val(EL 0 (st:int64 list)) = procedure_catalog_call_tag catalog` THEN
    REWRITE_TAC[procedure_catalog_call_tag] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PROCEDURE_CATALOG_PRIMITIVE_LOWER THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PROCEDURE_CATALOG_LOWER_ADMITTED]);;

let PROCEDURE_COMPILE_CALL_SHAPE = prove
 (`!catalog table original procedures st out.
    procedure_compile_step catalog table original procedures st = SOME out /\
    val(EL 0 (st:int64 list)) = procedure_catalog_call_tag catalog ==>
    procedure_binding_count original procedures <= 2 EXP 64 /\
    val(EL 1 st) < procedures /\
    ?index. out = procedure_linked_call_step index original st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `lowered:int64 list`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) o MATCH_MP PROCEDURE_COMPILE_ADMITTED o
    check (fun th -> fst(strip_comb(lhs(concl th))) = `procedure_compile_step`)) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
  ASM_MESON_TAC[]);;

let procedure_step_compile_theorems =
 ["PROCEDURE_PRIMITIVE_BINDINGS_EQ",PROCEDURE_PRIMITIVE_BINDINGS_EQ;
  "PROCEDURE_COMPILE_NONE",PROCEDURE_COMPILE_NONE;
  "PROCEDURE_COMPILE_PRIMITIVE",PROCEDURE_COMPILE_PRIMITIVE;
  "PROCEDURE_COMPILE_CALL",PROCEDURE_COMPILE_CALL;
  "PROCEDURE_COMPILE_ADMITTED",PROCEDURE_COMPILE_ADMITTED;
  "PROCEDURE_COMPILE_FIELDS",PROCEDURE_COMPILE_FIELDS;
  "PROCEDURE_COMPILE_OPCODE",PROCEDURE_COMPILE_OPCODE;
  "PROCEDURE_COMPILE_RUNTIME_CALL_EXACT",PROCEDURE_COMPILE_RUNTIME_CALL_EXACT;
  "PROCEDURE_COMPILE_PRIMITIVE_RUN",PROCEDURE_COMPILE_PRIMITIVE_RUN;
  "PROCEDURE_COMPILE_CALL_SHAPE",PROCEDURE_COMPILE_CALL_SHAPE];;
