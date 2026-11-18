(* Typed primitive interpretations and catalog-bound procedure execution. *)
needs "native/procedures/procedure_controller_math_load.ml";;
needs "native/procedures/procedure_catalog.ml";;

(* Operations see the operand fields, not a source or runtime opcode. *)
let procedure_catalog_primitive = new_definition
 `procedure_catalog_primitive catalog operations (b:num) (st:int64 list)
    (cw:num->num) (s:A) (used:num) =
    if procedure_catalog_ok catalog /\ val(EL 0 st) < LENGTH catalog
    then operations (EL (val(EL 0 st)) catalog) b (TL st) cw s used
    else (3,3,s,used)`;;

let procedure_table_primitive = new_definition
 `procedure_table_primitive table operations (b:num) (st:int64 list)
    (cw:num->num) (s:A) (used:num) =
    if native_operation_unique table /\ val(EL 0 st) < LENGTH table /\
       ~(EL (val(EL 0 st)) table = ProcedureCallMarker)
    then operations (EL (val(EL 0 st)) table) b (TL st) cw s used
    else (3,3,s,used)`;;

let procedure_catalog_run = new_definition
 `procedure_catalog_run cap catalog operations P b pid args (s:A) used =
    if procedure_catalog_ok catalog then
      procedure_eval_call cap (procedure_catalog_call_tag catalog)
        (procedure_catalog_primitive catalog operations) P b pid args s used
    else (3,3,s,used)`;;

let PROCEDURE_CATALOG_PRIMITIVE_RUN = prove
 (`!catalog operations b st cw (s:A) used.
    procedure_catalog_ok catalog /\ val(EL 0 st) < LENGTH catalog ==>
    procedure_catalog_primitive catalog operations b st cw s used =
      operations (EL (val(EL 0 st)) catalog) b (TL st) cw s used`,
  SIMP_TAC[procedure_catalog_primitive]);;

let PROCEDURE_TABLE_PRIMITIVE_LOWER = prove
 (`!table op st out operations b cw (s:A) used.
    native_operation_lower table op st = SOME out /\ ~(op = ProcedureCallMarker) ==>
    procedure_table_primitive table operations b out cw s used =
      operations op b (TL st) cw s used`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NATIVE_OPERATION_LOWER_ADMITTED o
    check (fun th -> fst(strip_comb(lhs(concl th))) = `native_operation_lower`)) THEN
  SUBGOAL_THEN `native_operation_offset table op < LENGTH(table:native_operation list)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[NATIVE_OPERATION_OFFSET_BOUND];ALL_TAC] THEN
  SUBGOAL_THEN `native_operation_offset table op < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[procedure_table_primitive;TL;EL;HD;VAL_WORD;DIMINDEX_64;MOD_LT;
    NATIVE_OPERATION_OFFSET_READ]);;

let PROCEDURE_CATALOG_PRIMITIVE_LOWER = prove
 (`!catalog table st out operations b cw (s:A) used.
    procedure_catalog_ok catalog /\ val(EL 0 st) < LENGTH catalog /\
    procedure_catalog_lower catalog table st = SOME out ==>
    procedure_catalog_primitive catalog operations b st cw s used =
    procedure_table_primitive table operations b out cw s used`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROCEDURE_CATALOG_LOWER_ADMITTED o
    check (fun th -> fst(strip_comb(lhs(concl th))) = `procedure_catalog_lower`)) THEN
  MP_TAC(SPECL [`catalog:native_operation list`;`val(EL 0 (st:int64 list))`]
    PROCEDURE_CATALOG_PRIMITIVE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(op:native_operation) = EL (val(EL 0 (st:int64 list))) catalog` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[option_INJ];ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(operations:native_operation->num->int64 list->(num->num)->A->num->num#num#A#num)
    (EL (val(EL 0 st)) catalog) b (TL st) cw s used` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[PROCEDURE_CATALOG_PRIMITIVE_RUN];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC PROCEDURE_TABLE_PRIMITIVE_LOWER THEN
    ASM_REWRITE_TAC[]]);;

let PROCEDURE_CATALOG_RUN_EXACT = prove
 (`!catalog operations P b cap pid args (s:A) used k pay s1 used1.
    procedure_catalog_ok catalog ==>
    (procedure_catalog_run cap catalog operations P b pid args s used = (k,pay,s1,used1) <=>
     procedure_controller_path (procedure_catalog_call_tag catalog)
       (procedure_catalog_primitive catalog operations) P b cap
       (ProcedureEnter pid args,[],s,used) (ProcedureReturn k pay,[],s1,used1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[procedure_catalog_run;PROCEDURE_CONTROLLER_EXACT]);;

let PROCEDURE_CATALOG_BAD_RUN = prove
 (`!catalog operations P b cap pid args (s:A) used.
    ~procedure_catalog_ok catalog ==>
    procedure_catalog_run cap catalog operations P b pid args s used = (3,3,s,used)`,
  SIMP_TAC[procedure_catalog_run]);;

let procedure_catalog_controller_theorems =
 ["PROCEDURE_CATALOG_PRIMITIVE_RUN",PROCEDURE_CATALOG_PRIMITIVE_RUN;
  "PROCEDURE_TABLE_PRIMITIVE_LOWER",PROCEDURE_TABLE_PRIMITIVE_LOWER;
  "PROCEDURE_CATALOG_PRIMITIVE_LOWER",PROCEDURE_CATALOG_PRIMITIVE_LOWER;
  "PROCEDURE_CATALOG_RUN_EXACT",PROCEDURE_CATALOG_RUN_EXACT;
  "PROCEDURE_CATALOG_BAD_RUN",PROCEDURE_CATALOG_BAD_RUN];;
