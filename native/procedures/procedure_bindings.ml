(* Static binding words for procedure requests and target metadata. *)
needs "Library/words.ml";;

let procedure_binding_count = new_definition
 `procedure_binding_count (original:num) procedures = original + 4 + 2 * procedures`;;

let procedure_request_binding = new_definition
 `procedure_request_binding (original:num) = original`;;

let procedure_empty_binding = new_definition
 `procedure_empty_binding (original:num) = original + 2`;;

let procedure_target_binding = new_definition
 `procedure_target_binding (original:num) target = original + 4 + 2 * target`;;

let procedure_linked_bindings = new_definition
 `procedure_linked_bindings (bw:num->int64) original procedures request extent n =
    if n < original then bw n
    else if n = original then request
    else if n = original + 1 then extent
    else if n < original + 4 then word 0
    else if n < procedure_binding_count original procedures then
      if (n - (original + 4)) MOD 2 = 0 then word 0
      else word((n - (original + 4)) DIV 2)
    else word 0`;;

let PROCEDURE_BINDINGS_PREFIX = prove
 (`!bw original procedures request extent n. n < original ==>
    procedure_linked_bindings bw original procedures request extent n = bw n`,
  SIMP_TAC[procedure_linked_bindings]);;

let PROCEDURE_BINDINGS_REQUEST = prove
 (`!bw original procedures request extent.
    procedure_linked_bindings bw original procedures request extent
      (procedure_request_binding original) = request /\
    procedure_linked_bindings bw original procedures request extent
      (procedure_request_binding original + 1) = extent`,
  REWRITE_TAC[procedure_linked_bindings;procedure_request_binding] THEN
  SIMP_TAC[LT_REFL;ARITH_RULE `~(n + 1 < n) /\ ~(n + 1 = n)`]);;

let PROCEDURE_BINDINGS_EMPTY = prove
 (`!bw original procedures request extent.
    procedure_linked_bindings bw original procedures request extent
      (procedure_empty_binding original) = word 0 /\
    procedure_linked_bindings bw original procedures request extent
      (procedure_empty_binding original + 1) = word 0`,
  REWRITE_TAC[procedure_linked_bindings;procedure_empty_binding;GSYM ADD_ASSOC] THEN
  SIMP_TAC[ARITH_RULE
    `!(n:num). ~(n + 2 < n) /\ ~(n + 2 = n) /\ ~(n + 2 = n + 1) /\ n + 2 < n + 4 /\
     ~(n + 2 + 1 < n) /\ ~(n + 2 + 1 = n) /\ ~(n + 2 + 1 = n + 1) /\
     n + 2 + 1 < n + 4`]);;

let PROCEDURE_BINDINGS_TARGET = prove
 (`!bw original procedures request extent target. target < procedures ==>
    procedure_linked_bindings bw original procedures request extent
      (procedure_target_binding original target) = word 0 /\
    procedure_linked_bindings bw original procedures request extent
      (procedure_target_binding original target + 1) = word target`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[procedure_linked_bindings;procedure_target_binding;procedure_binding_count;
    GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN
    `~(original + 4 + 2 * (target:num) < original) /\
     ~(original + 4 + 2 * target = original) /\
     ~(original + 4 + 2 * target = original + 1) /\
     ~(original + 4 + 2 * target < original + 4) /\
     original + 4 + 2 * target < original + 4 + 2 * procedures /\
     ~(original + 4 + 2 * target + 1 < original) /\
     ~(original + 4 + 2 * target + 1 = original) /\
     ~(original + 4 + 2 * target + 1 = original + 1) /\
     ~(original + 4 + 2 * target + 1 < original + 4) /\
     original + 4 + 2 * target + 1 < original + 4 + 2 * procedures /\
     (original + 4 + 2 * target) - (original + 4) = 2 * target /\
     (original + 4 + 2 * target + 1) - (original + 4) = 2 * target + 1`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_REWRITE_TAC[MOD_MULT] THEN
  SIMP_TAC[MOD_MULT_ADD;DIV_MULT_ADD;ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES]);;

let PROCEDURE_BINDINGS_TARGET_DISTINCT = prove
 (`!original a b.
    procedure_target_binding original a = procedure_target_binding original b <=> a = b`,
  REWRITE_TAC[procedure_target_binding] THEN ARITH_TAC);;

let PROCEDURE_BINDINGS_PRIVATE_PAIRS = prove
 (`!original target.
    procedure_request_binding original + 2 <= procedure_empty_binding original /\
    procedure_empty_binding original + 2 <= procedure_target_binding original target`,
  REWRITE_TAC[procedure_request_binding;procedure_empty_binding;procedure_target_binding] THEN
  ARITH_TAC);;

let PROCEDURE_BINDINGS_INDEX_BOUNDS = prove
 (`!original procedures target. target < procedures ==>
    procedure_request_binding original + 1 < procedure_binding_count original procedures /\
    procedure_empty_binding original + 1 < procedure_binding_count original procedures /\
    procedure_target_binding original target + 1 < procedure_binding_count original procedures`,
  REWRITE_TAC[procedure_request_binding;procedure_empty_binding;procedure_target_binding;
    procedure_binding_count] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let PROCEDURE_BINDINGS_TARGET_WORD_BOUNDS = prove
 (`!original procedures target.
    procedure_binding_count original procedures <= 2 EXP 64 /\ target < procedures ==>
    procedure_request_binding original < 2 EXP 64 /\
    procedure_empty_binding original < 2 EXP 64 /\
    procedure_target_binding original target < 2 EXP 64 /\ target < 2 EXP 64`,
  REWRITE_TAC[procedure_request_binding;procedure_empty_binding;procedure_target_binding;
    procedure_binding_count] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let PROCEDURE_BINDINGS_OUTSIDE = prove
 (`!bw original procedures request extent n.
    procedure_binding_count original procedures <= n ==>
    procedure_linked_bindings bw original procedures request extent n = word 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[procedure_binding_count] THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `~((n:num) < original) /\ ~(n = original) /\ ~(n = original + 1) /\
     ~(n < original + 4) /\ ~(n < original + 4 + 2 * procedures)`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_REWRITE_TAC[procedure_linked_bindings;procedure_binding_count]);;

let PROCEDURE_BINDINGS_LAYOUT_CONTROL = prove
 (`procedure_request_binding 10 = 10 /\ procedure_empty_binding 10 = 12 /\
    procedure_target_binding 10 7 = 28 /\ procedure_binding_count 10 8 = 30 /\
    procedure_linked_bindings (\n. word(n + 100)) 10 8 (word 4096) (word 64) 9 = word 109 /\
    procedure_linked_bindings (\n. word(n + 100)) 10 8 (word 4096) (word 64) 10 = word 4096 /\
    procedure_linked_bindings (\n. word(n + 100)) 10 8 (word 4096) (word 64) 11 = word 64 /\
    procedure_linked_bindings (\n. word(n + 100)) 10 8 (word 4096) (word 64) 28 = word 0 /\
    procedure_linked_bindings (\n. word(n + 100)) 10 8 (word 4096) (word 64) 29 = word 7`,
  REWRITE_TAC[procedure_request_binding;procedure_empty_binding;procedure_target_binding;
    procedure_binding_count;procedure_linked_bindings] THEN CONV_TAC NUM_REDUCE_CONV);;

let PROCEDURE_BINDINGS_TARGET_ALIAS_CONTROL = prove
 (`~(procedure_target_binding 10 0 = procedure_target_binding 10 7) /\
    ~(procedure_linked_bindings (\n. word(n + 100)) 10 8 (word 4096) (word 64) 29 = word 0)`,
  REWRITE_TAC[procedure_target_binding;procedure_linked_bindings;procedure_binding_count] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

let procedure_bindings_theorems =
 ["PROCEDURE_BINDINGS_PREFIX",PROCEDURE_BINDINGS_PREFIX;
  "PROCEDURE_BINDINGS_REQUEST",PROCEDURE_BINDINGS_REQUEST;
  "PROCEDURE_BINDINGS_EMPTY",PROCEDURE_BINDINGS_EMPTY;
  "PROCEDURE_BINDINGS_TARGET",PROCEDURE_BINDINGS_TARGET;
  "PROCEDURE_BINDINGS_TARGET_DISTINCT",PROCEDURE_BINDINGS_TARGET_DISTINCT;
  "PROCEDURE_BINDINGS_PRIVATE_PAIRS",PROCEDURE_BINDINGS_PRIVATE_PAIRS;
  "PROCEDURE_BINDINGS_INDEX_BOUNDS",PROCEDURE_BINDINGS_INDEX_BOUNDS;
  "PROCEDURE_BINDINGS_TARGET_WORD_BOUNDS",PROCEDURE_BINDINGS_TARGET_WORD_BOUNDS;
  "PROCEDURE_BINDINGS_OUTSIDE",PROCEDURE_BINDINGS_OUTSIDE;
  "PROCEDURE_BINDINGS_LAYOUT_CONTROL",PROCEDURE_BINDINGS_LAYOUT_CONTROL;
  "PROCEDURE_BINDINGS_TARGET_ALIAS_CONTROL",PROCEDURE_BINDINGS_TARGET_ALIAS_CONTROL];;
