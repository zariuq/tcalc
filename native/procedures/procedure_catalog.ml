(* Procedure-local operation codes are independent of runtime table positions. *)
needs "native/procedures/procedure_operation_names.ml";;

let procedure_catalog_ok = new_definition
 `procedure_catalog_ok catalog <=> native_operation_unique catalog /\
    ~MEM ProcedureCallMarker catalog /\ LENGTH catalog < 2 EXP 64`;;

let procedure_catalog_call_tag = new_definition
 `procedure_catalog_call_tag (catalog:native_operation list) = LENGTH catalog`;;

let procedure_catalog_operation = new_definition
 `procedure_catalog_operation catalog code =
    if code < LENGTH catalog then SOME(EL code catalog)
    else if code = LENGTH catalog then SOME ProcedureCallMarker else NONE`;;

let procedure_catalog_apply = define
 `(procedure_catalog_apply table NONE (st:int64 list) = NONE) /\
  (procedure_catalog_apply table (SOME op) st = native_operation_lower table op st)`;;

let procedure_catalog_lower = new_definition
 `procedure_catalog_lower catalog table (st:int64 list) =
    if procedure_catalog_ok catalog /\ LENGTH st = 18
    then procedure_catalog_apply table (procedure_catalog_operation catalog (val(EL 0 st))) st
    else NONE`;;

let PROCEDURE_CATALOG_CALL = prove
 (`!catalog. procedure_catalog_operation catalog (procedure_catalog_call_tag catalog) = SOME ProcedureCallMarker`,
  REWRITE_TAC[procedure_catalog_operation;procedure_catalog_call_tag;LT_REFL]);;

let PROCEDURE_CATALOG_PRIMITIVE = prove
 (`!catalog code. procedure_catalog_ok catalog /\ code < LENGTH catalog ==>
    procedure_catalog_operation catalog code = SOME(EL code catalog) /\
    ~(EL code catalog = ProcedureCallMarker)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[procedure_catalog_ok] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[procedure_catalog_operation] THEN ASM_MESON_TAC[MEM_EL]);;

let PROCEDURE_CATALOG_CALL_EXACT = prove
 (`!catalog code. procedure_catalog_ok catalog ==>
    (procedure_catalog_operation catalog code = SOME ProcedureCallMarker <=>
     code = procedure_catalog_call_tag catalog)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `(code:num) < LENGTH(catalog:native_operation list)` THENL
   [MP_TAC(SPECL [`catalog:native_operation list`;`code:num`] PROCEDURE_CATALOG_PRIMITIVE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[procedure_catalog_call_tag;option_INJ] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[procedure_catalog_operation;procedure_catalog_call_tag] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]]);;

let PROCEDURE_CATALOG_INVALID = prove
 (`!catalog code. procedure_catalog_call_tag catalog < code ==>
    procedure_catalog_operation catalog code = NONE`,
  REWRITE_TAC[procedure_catalog_call_tag;procedure_catalog_operation] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let PROCEDURE_CATALOG_UNIQUE_APPEND = prove
 (`!catalog. native_operation_unique catalog /\ ~MEM ProcedureCallMarker catalog ==>
    native_operation_unique(APPEND catalog [ProcedureCallMarker])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND;native_operation_unique;MEM;MEM_APPEND] THEN
  ASM_MESON_TAC[]);;

let PROCEDURE_CATALOG_CALL_OFFSET = prove
 (`!catalog. ~MEM ProcedureCallMarker catalog ==>
    native_operation_offset (APPEND catalog [ProcedureCallMarker]) ProcedureCallMarker =
    procedure_catalog_call_tag catalog`,
  REWRITE_TAC[procedure_catalog_call_tag] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM;APPEND;native_operation_offset;procedure_catalog_call_tag;LENGTH;DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

let PROCEDURE_CATALOG_LOWER_ADMITTED = prove
 (`!catalog table st out. procedure_catalog_lower catalog table st = SOME out ==>
    procedure_catalog_ok catalog /\ LENGTH st = 18 /\
    ?op. procedure_catalog_operation catalog (val(EL 0 st)) = SOME op /\
         native_operation_lower table op st = SOME out`,
  REPEAT GEN_TAC THEN REWRITE_TAC[procedure_catalog_lower] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC(ISPEC `procedure_catalog_operation catalog (val(EL 0 (st:int64 list)))` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `op:native_operation` SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[procedure_catalog_apply;option_DISTINCT] THEN
  ASM_MESON_TAC[]);;

let PROCEDURE_CATALOG_LOWER_FIELDS = prove
 (`!catalog table st out. procedure_catalog_lower catalog table st = SOME out ==>
    LENGTH out = 18 /\ (!j. 0 < j /\ j < 18 ==> EL j out = EL j st)`,
  MESON_TAC[PROCEDURE_CATALOG_LOWER_ADMITTED;NATIVE_OPERATION_LOWER_FIELDS]);;

let PROCEDURE_CATALOG_RUNTIME_CALL_EXACT = prove
 (`!catalog table st out. procedure_catalog_ok catalog /\ MEM ProcedureCallMarker table /\
    procedure_catalog_lower catalog table st = SOME out ==>
    (val(EL 0 out) = native_operation_offset table ProcedureCallMarker <=>
     val(EL 0 st) = procedure_catalog_call_tag catalog)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROCEDURE_CATALOG_LOWER_ADMITTED o
    check (fun th -> fst(strip_comb(lhs(concl th))) = `procedure_catalog_lower`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NATIVE_OPERATION_LOWER_FIELDS o
    check (fun th -> fst(strip_comb(lhs(concl th))) = `native_operation_lower`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NATIVE_OPERATION_LOWER_ADMITTED o
    check (fun th -> fst(strip_comb(lhs(concl th))) = `native_operation_lower`)) THEN
  SUBGOAL_THEN
   `(op:native_operation) = ProcedureCallMarker <=>
     val(EL 0 (st:int64 list)) = procedure_catalog_call_tag catalog` ASSUME_TAC THENL
   [MP_TAC(SPECL [`catalog:native_operation list`;`val(EL 0 (st:int64 list))`]
      PROCEDURE_CATALOG_CALL_EXACT) THEN ASM_REWRITE_TAC[option_INJ];ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NATIVE_OPERATION_OFFSET_INJECTIVE]);;

let PROCEDURE_CATALOG_MARKER_REFUSED = prove
 (`!catalog table st. MEM ProcedureCallMarker catalog ==>
    procedure_catalog_lower catalog table st = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[procedure_catalog_lower;procedure_catalog_ok] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let PROCEDURE_CATALOG_REORDER_CONTROL = prove
 (`procedure_catalog_ok [ReaderOperation 32;KernelOperation 32] /\
    procedure_catalog_call_tag [ReaderOperation 32;KernelOperation 32] = 2 /\
    procedure_catalog_operation [ReaderOperation 32;KernelOperation 32] 0 = SOME(ReaderOperation 32) /\
    procedure_catalog_operation [ReaderOperation 32;KernelOperation 32] 2 = SOME ProcedureCallMarker /\
    native_operation_offset [ProcedureCallMarker;KernelOperation 32;ReaderOperation 32] ProcedureCallMarker = 0 /\
    native_operation_offset [ProcedureCallMarker;KernelOperation 32;ReaderOperation 32] (ReaderOperation 32) = 2`,
  REWRITE_TAC[procedure_catalog_ok;native_operation_unique;MEM;LENGTH;
    procedure_catalog_call_tag;procedure_catalog_operation;native_operation_offset;
    NATIVE_OPERATION_DISTINCT;NATIVE_OPERATION_INJECTIVE;EL;HD;TL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let procedure_catalog_forty = new_definition
 (mk_eq(`procedure_catalog_forty:native_operation list`,
   mk_list(map (fun i -> mk_comb(`KernelOperation`,mk_small_numeral i)) (0--39),`:native_operation`)));;

let PROCEDURE_CATALOG_FORTY_INHABITED = prove
 (`procedure_catalog_ok procedure_catalog_forty /\
   procedure_catalog_call_tag procedure_catalog_forty = 40 /\
   procedure_catalog_operation procedure_catalog_forty 32 = SOME(KernelOperation 32) /\
   procedure_catalog_operation procedure_catalog_forty 40 = SOME ProcedureCallMarker`,
  REWRITE_TAC[procedure_catalog_forty;procedure_catalog_ok;procedure_catalog_call_tag;
    procedure_catalog_operation;native_operation_unique;MEM;LENGTH;
    NATIVE_OPERATION_DISTINCT;NATIVE_OPERATION_INJECTIVE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

let PROCEDURE_CATALOG_DUPLICATE_REFUSED = prove
 (`!table st. procedure_catalog_lower [ReaderOperation 32;ReaderOperation 32] table st = NONE`,
  REWRITE_TAC[procedure_catalog_lower;procedure_catalog_ok;native_operation_unique;MEM]);;

let procedure_catalog_theorems =
 ["PROCEDURE_CATALOG_CALL",PROCEDURE_CATALOG_CALL;
  "PROCEDURE_CATALOG_PRIMITIVE",PROCEDURE_CATALOG_PRIMITIVE;
  "PROCEDURE_CATALOG_CALL_EXACT",PROCEDURE_CATALOG_CALL_EXACT;
  "PROCEDURE_CATALOG_INVALID",PROCEDURE_CATALOG_INVALID;
  "PROCEDURE_CATALOG_UNIQUE_APPEND",PROCEDURE_CATALOG_UNIQUE_APPEND;
  "PROCEDURE_CATALOG_CALL_OFFSET",PROCEDURE_CATALOG_CALL_OFFSET;
  "PROCEDURE_CATALOG_LOWER_ADMITTED",PROCEDURE_CATALOG_LOWER_ADMITTED;
  "PROCEDURE_CATALOG_LOWER_FIELDS",PROCEDURE_CATALOG_LOWER_FIELDS;
  "PROCEDURE_CATALOG_REORDER_CONTROL",PROCEDURE_CATALOG_REORDER_CONTROL;
  "PROCEDURE_CATALOG_RUNTIME_CALL_EXACT",PROCEDURE_CATALOG_RUNTIME_CALL_EXACT;
  "PROCEDURE_CATALOG_MARKER_REFUSED",PROCEDURE_CATALOG_MARKER_REFUSED;
  "PROCEDURE_CATALOG_FORTY_INHABITED",PROCEDURE_CATALOG_FORTY_INHABITED;
  "PROCEDURE_CATALOG_DUPLICATE_REFUSED",PROCEDURE_CATALOG_DUPLICATE_REFUSED];;
