(* Work-region frames: checked capacity, disjoint activations and word frames. *)
needs "native/driver/driver.ml";;

let procedure_capacity = new_definition
 `procedure_capacity extent stride = extent DIV stride`;;
let procedure_frame_base = new_definition
 `procedure_frame_base (base:int64) stride depth = word_add base (word(depth * stride))`;;
let procedure_frame_word = new_definition
 `procedure_frame_word (base:int64) stride header depth slot =
    word_add (procedure_frame_base base stride depth) (word(header + 8 * slot))`;;

let PROCEDURE_CAPACITY_EXACT = prove
 (`!extent stride depth. 0 < stride
     ==> (depth < procedure_capacity extent stride <=> (depth + 1) * stride <= extent)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(stride = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[procedure_capacity;ARITH_RULE `d < c <=> d + 1 <= c`] THEN
  ASM_SIMP_TAC[LE_RDIV_EQ;MULT_SYM]);;

let PROCEDURE_FRAME_BOUNDS = prove
 (`!base extent stride cap depth.
     0 < stride /\ cap * stride <= extent /\ val(base:int64) + extent < 2 EXP 64 /\ depth < cap
     ==> val(procedure_frame_base base stride depth) = val base + depth * stride /\
         val(procedure_frame_base base stride depth) + stride <= val base + extent`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(depth + 1) * stride <= extent` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `cap * stride` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `val(base:int64) + depth * stride < 2 EXP 64` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_ADD_DISTRIB;MULT_CLAUSES]) THEN ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[procedure_frame_base;TISA_VAL_OFFSET] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_ADD_DISTRIB;MULT_CLAUSES]) THEN ASM_ARITH_TAC);;

let PROCEDURE_FRAMES_APART = prove
 (`!base extent stride cap i j.
     0 < stride /\ cap * stride <= extent /\ val(base:int64) + extent < 2 EXP 64 /\ i < j /\ j < cap
     ==> drv_apart (procedure_frame_base base stride i) stride
                   (procedure_frame_base base stride j) stride`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `i < cap` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  MP_TAC(SPECL [`base:int64`;`extent:num`;`stride:num`;`cap:num`;`i:num`] PROCEDURE_FRAME_BOUNDS) THEN
  MP_TAC(SPECL [`base:int64`;`extent:num`;`stride:num`;`cap:num`;`j:num`] PROCEDURE_FRAME_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(i + 1) * stride <= j * stride` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[drv_apart] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_ADD_DISTRIB;MULT_CLAUSES]) THEN ASM_ARITH_TAC);;

let PROCEDURE_FRAME_WORD_BOUNDS = prove
 (`!base extent stride cap header nctl depth slot.
     0 < stride /\ cap * stride <= extent /\ val(base:int64) + extent < 2 EXP 64 /\
     depth < cap /\ header + 8 * nctl <= stride /\ slot < nctl
     ==> val(procedure_frame_word base stride header depth slot) =
           val base + depth * stride + header + 8 * slot /\
         val(procedure_frame_word base stride header depth slot) + 8 <= val base + extent`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`base:int64`;`extent:num`;`stride:num`;`cap:num`;`depth:num`] PROCEDURE_FRAME_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(procedure_frame_base base stride depth) + (header + 8 * slot) < 2 EXP 64`
    ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[procedure_frame_word;TISA_VAL_OFFSET] THEN ASM_ARITH_TAC);;

let PROCEDURE_WRITE_WORD_APART = prove
 (`!src dst (value:int64) m.
     val(src:int64) + 8 <= 2 EXP 64 /\ val(dst:int64) + 8 <= 2 EXP 64 /\ drv_apart src 8 dst 8
     ==> drv_word (write (bytes64 dst) value m) src = drv_word m src`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word_add src (word i):int64) = val src + i` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[drv_apart]) THEN ASM_ARITH_TAC);;

let PROCEDURE_RESULT_POLICY_APART = prove
 (`!work extent stride cap header nctl depth parent nparent.
     0 < stride /\ cap * stride <= extent /\ val(work:int64) + extent < 2 EXP 64 /\
     depth < cap /\ header + 8 * nctl <= stride /\ 7 < nctl /\ 7 < nparent /\
     val(parent:int64) + 8 * nparent < 2 EXP 64 /\ drv_apart work extent parent (8 * nparent)
     ==> drv_apart (procedure_frame_word work stride header depth 7) 8
                   (word_add parent (word 56)) 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`work:int64`;`extent:num`;`stride:num`;`cap:num`;`header:num`;
                `nctl:num`;`depth:num`;`7`] PROCEDURE_FRAME_WORD_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add parent (word 56):int64) = val parent + 56` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[drv_apart] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[drv_apart]) THEN ASM_ARITH_TAC);;

let PROCEDURE_RESULT_POLICY_KEPT = prove
 (`!work extent stride cap header nctl depth parent nparent value m.
     0 < stride /\ cap * stride <= extent /\ val(work:int64) + extent < 2 EXP 64 /\
     depth < cap /\ header + 8 * nctl <= stride /\ 7 < nctl /\ 7 < nparent /\
     val(parent:int64) + 8 * nparent < 2 EXP 64 /\ drv_apart work extent parent (8 * nparent)
     ==> drv_word (write (bytes64 (procedure_frame_word work stride header depth 7)) value m)
                    (word_add parent (word 56)) = drv_word m (word_add parent (word 56))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC PROCEDURE_WRITE_WORD_APART THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `val(word_add parent (word 56):int64) = val parent + 56` SUBST1_TAC THENL
     [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ASM_ARITH_TAC];ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`work:int64`;`extent:num`;`stride:num`;`cap:num`;`header:num`;
                  `nctl:num`;`depth:num`;`7`] PROCEDURE_FRAME_WORD_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ONCE_REWRITE_TAC[DRV_APART_SYM] THEN MATCH_MP_TAC PROCEDURE_RESULT_POLICY_APART THEN
    MAP_EVERY EXISTS_TAC [`extent:num`;`cap:num`;`nctl:num`;`nparent:num`] THEN
    ASM_REWRITE_TAC[]]);;

let procedure_stack_theorems =
 ["PROCEDURE_CAPACITY_EXACT",PROCEDURE_CAPACITY_EXACT;
  "PROCEDURE_FRAME_BOUNDS",PROCEDURE_FRAME_BOUNDS;
  "PROCEDURE_FRAMES_APART",PROCEDURE_FRAMES_APART;
  "PROCEDURE_FRAME_WORD_BOUNDS",PROCEDURE_FRAME_WORD_BOUNDS;
  "PROCEDURE_WRITE_WORD_APART",PROCEDURE_WRITE_WORD_APART;
  "PROCEDURE_RESULT_POLICY_APART",PROCEDURE_RESULT_POLICY_APART;
  "PROCEDURE_RESULT_POLICY_KEPT",PROCEDURE_RESULT_POLICY_KEPT];;
