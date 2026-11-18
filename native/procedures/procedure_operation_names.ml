(* Logical operation names are distinct from positions in a native table. *)
needs "Library/words.ml";;

let native_operation_INDUCT,native_operation_RECURSION = define_type
 "native_operation = KernelOperation num | ReaderOperation num | ProcedureCallMarker";;
let NATIVE_OPERATION_DISTINCT = prove_constructors_distinct native_operation_RECURSION;;
let NATIVE_OPERATION_INJECTIVE = prove_constructors_injective native_operation_RECURSION;;

let native_operation_offset = define
 `(native_operation_offset ([]:native_operation list) op = 0) /\
  (native_operation_offset (CONS h t) op =
     if h = op then 0 else SUC(native_operation_offset t op))`;;

let native_operation_unique = define
 `(native_operation_unique ([]:native_operation list) <=> T) /\
  (native_operation_unique (CONS h t) <=> ~MEM h t /\ native_operation_unique t)`;;

let NATIVE_OPERATION_OFFSET_BOUND = prove
 (`!table op. MEM op table ==> native_operation_offset table op < LENGTH table`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM;native_operation_offset;LENGTH] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LT_0;LT_SUC] THEN ASM_MESON_TAC[]);;

let NATIVE_OPERATION_OFFSET_READ = prove
 (`!table op. MEM op table ==> EL (native_operation_offset table op) table = op`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM;native_operation_offset] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[EL;HD;TL] THEN ASM_MESON_TAC[]);;

let NATIVE_OPERATION_OFFSET_INJECTIVE = prove
 (`!table a b. MEM a table /\ MEM b table /\
    native_operation_offset table a = native_operation_offset table b ==> a = b`,
  MESON_TAC[NATIVE_OPERATION_OFFSET_READ]);;

let NATIVE_OPERATION_NAMESPACES = prove
 (`!table k r. MEM (KernelOperation k) table /\ MEM (ReaderOperation r) table
    ==> ~(native_operation_offset table (KernelOperation k) =
          native_operation_offset table (ReaderOperation r))`,
  MESON_TAC[NATIVE_OPERATION_OFFSET_INJECTIVE;NATIVE_OPERATION_DISTINCT]);;

let NATIVE_OPERATION_CALL_NAMESPACE = prove
 (`!table r. MEM (ReaderOperation r) table /\ MEM ProcedureCallMarker table
    ==> ~(native_operation_offset table (ReaderOperation r) =
          native_operation_offset table ProcedureCallMarker)`,
  MESON_TAC[NATIVE_OPERATION_OFFSET_INJECTIVE;NATIVE_OPERATION_DISTINCT]);;

let native_operation_lower = new_definition
 `native_operation_lower table op (st:int64 list) =
    if native_operation_unique table /\ MEM op table /\ LENGTH st = 18 /\ LENGTH table < 2 EXP 64
    then SOME(CONS (word(native_operation_offset table op)) (TL st))
    else NONE`;;

let NATIVE_OPERATION_LOWER_ADMITTED = prove
 (`!table op st out. native_operation_lower table op st = SOME out
    ==> native_operation_unique table /\ MEM op table /\ LENGTH st = 18 /\
        LENGTH table < 2 EXP 64 /\
        out = CONS (word(native_operation_offset table op)) (TL st)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[native_operation_lower] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT;option_INJ] THEN SIMP_TAC[]);;

let NATIVE_OPERATION_LOWER_FIELDS = prove
 (`!table op st out. native_operation_lower table op st = SOME out
    ==> LENGTH out = 18 /\ val(EL 0 out) = native_operation_offset table op /\
        (!j. 0 < j /\ j < 18 ==> EL j out = EL j st)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP NATIVE_OPERATION_LOWER_ADMITTED) THEN
  SUBGOAL_THEN `native_operation_offset table op < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `LENGTH(table:native_operation list)` THEN
    ASM_SIMP_TAC[NATIVE_OPERATION_OFFSET_BOUND];ALL_TAC] THEN
  MP_TAC(ISPEC `st:int64 list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `head:int64` (X_CHOOSE_THEN `tail:int64 list` SUBST_ALL_TAC))) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH;ARITH_EQ]) THEN FIRST_ASSUM CONTR_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
    ASM_SIMP_TAC[LENGTH;TL;EL;HD;VAL_WORD;DIMINDEX_64;MOD_LT] THEN
    INDUCT_TAC THEN REWRITE_TAC[EL;TL;CONJUNCT1 LT;LT_0]]);;

let NATIVE_OPERATION_COLLISION_CONTROL = prove
 (`native_operation_unique [KernelOperation 25;ReaderOperation 25;ReaderOperation 32;ProcedureCallMarker] /\
   native_operation_offset [KernelOperation 25;ReaderOperation 25;ReaderOperation 32;ProcedureCallMarker]
     (KernelOperation 25) = 0 /\
   native_operation_offset [KernelOperation 25;ReaderOperation 25;ReaderOperation 32;ProcedureCallMarker]
     (ReaderOperation 25) = 1 /\
   native_operation_offset [KernelOperation 25;ReaderOperation 25;ReaderOperation 32;ProcedureCallMarker]
     (ReaderOperation 32) = 2 /\
   native_operation_offset [KernelOperation 25;ReaderOperation 25;ReaderOperation 32;ProcedureCallMarker]
     ProcedureCallMarker = 3`,
  REWRITE_TAC[native_operation_unique;native_operation_offset;MEM;
    NATIVE_OPERATION_DISTINCT;NATIVE_OPERATION_INJECTIVE] THEN CONV_TAC NUM_REDUCE_CONV);;

let NATIVE_OPERATION_DUPLICATE_REFUSED = prove
 (`!st. native_operation_lower [ReaderOperation 25;ReaderOperation 25]
         (ReaderOperation 25) st = NONE`,
  REWRITE_TAC[native_operation_lower;native_operation_unique;MEM]);;

let NATIVE_OPERATION_MISSING_REFUSED = prove
 (`!st. native_operation_lower [ProcedureCallMarker] (ReaderOperation 32) st = NONE`,
  REWRITE_TAC[native_operation_lower;MEM;NATIVE_OPERATION_DISTINCT]);;

let NATIVE_OPERATION_LOWER_INHABITED = prove
 (`native_operation_lower
     [KernelOperation 25;ReaderOperation 25;ReaderOperation 32;ProcedureCallMarker]
     (ReaderOperation 25)
     (MAP (word:num->int64) [25;0;2;4;6;8;10;12;14;16;8;9;10;11;12;13;14;7]) =
   SOME(MAP (word:num->int64) [1;0;2;4;6;8;10;12;14;16;8;9;10;11;12;13;14;7])`,
  REWRITE_TAC[native_operation_lower;native_operation_unique;native_operation_offset;
              MEM;MAP;LENGTH;TL;NATIVE_OPERATION_DISTINCT;NATIVE_OPERATION_INJECTIVE] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let procedure_operation_name_theorems =
 ["NATIVE_OPERATION_OFFSET_BOUND",NATIVE_OPERATION_OFFSET_BOUND;
  "NATIVE_OPERATION_OFFSET_READ",NATIVE_OPERATION_OFFSET_READ;
  "NATIVE_OPERATION_OFFSET_INJECTIVE",NATIVE_OPERATION_OFFSET_INJECTIVE;
  "NATIVE_OPERATION_NAMESPACES",NATIVE_OPERATION_NAMESPACES;
  "NATIVE_OPERATION_CALL_NAMESPACE",NATIVE_OPERATION_CALL_NAMESPACE;
  "NATIVE_OPERATION_LOWER_ADMITTED",NATIVE_OPERATION_LOWER_ADMITTED;
  "NATIVE_OPERATION_LOWER_FIELDS",NATIVE_OPERATION_LOWER_FIELDS;
  "NATIVE_OPERATION_COLLISION_CONTROL",NATIVE_OPERATION_COLLISION_CONTROL;
  "NATIVE_OPERATION_DUPLICATE_REFUSED",NATIVE_OPERATION_DUPLICATE_REFUSED;
  "NATIVE_OPERATION_MISSING_REFUSED",NATIVE_OPERATION_MISSING_REFUSED;
  "NATIVE_OPERATION_LOWER_INHABITED",NATIVE_OPERATION_LOWER_INHABITED];;
