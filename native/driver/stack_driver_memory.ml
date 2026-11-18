(* The driver's physical memory window for an explicit callee stack bound. *)
needs "native/driver/native_component_stack.ml";;

let stack_drv_stack = new_definition
 `stack_drv_stack reserve (cfr:int64) (a:int64) <=>
    val cfr <= val a + (reserve + 8) /\ val a < val cfr + 248`;;

(* Include the caller's return address in the separation window, while
   excluding it from the writable stack mask above. *)
let stack_drv_apart = new_definition
 `stack_drv_apart reserve (cfr:int64) b n <=>
    drv_apart (word_sub cfr (word(reserve + 8))) (reserve + 264) b n`;;

let stack_drv_child = new_definition
 `stack_drv_child reserve bw ctl budget cfr st m used t <=>
    tregs t = drv_regs cfr ctl st m /\
    (!j. j < 24 ==> tisa_fword t j = drv_fw bw ctl budget used st m j) /\
    (!a. ~stack_drv_stack reserve cfr a ==> tmem t a = m a)`;;

let stack_drv_layout = new_definition
 `stack_drv_layout reserve pc cfr d plan ns ctl nctl bind nbw leaves nl
       (lpc:num->num) (lmc:num->byte list) <=>
    40 <= reserve /\ reserve + 8 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\
    pc + 522 <= 2 EXP 64 /\ val d + 64 <= 2 EXP 64 /\ val plan + 144 * ns < 2 EXP 64 /\
    val ctl + 8 * nctl <= 2 EXP 64 /\ val bind + 8 * nbw <= 2 EXP 64 /\
    val leaves + 8 * nl <= 2 EXP 64 /\
    (!j. j < nl ==> lpc j + LENGTH(lmc j) <= 2 EXP 64) /\
    stack_drv_apart reserve cfr (word pc) 522 /\
    (!j. j < nl ==> stack_drv_apart reserve cfr (word(lpc j)) (LENGTH(lmc j))) /\
    stack_drv_apart reserve cfr d 64 /\
    stack_drv_apart reserve cfr plan (144 * ns) /\
    stack_drv_apart reserve cfr ctl (8 * nctl) /\
    stack_drv_apart reserve cfr bind (8 * nbw) /\
    stack_drv_apart reserve cfr leaves (8 * nl) /\
    drv_apart ctl (8 * nctl) (word pc) 522 /\
    (!j. j < nl ==> drv_apart ctl (8 * nctl) (word(lpc j)) (LENGTH(lmc j))) /\
    drv_apart ctl (8 * nctl) d 64 /\ drv_apart ctl (8 * nctl) plan (144 * ns) /\
    drv_apart ctl (8 * nctl) bind (8 * nbw) /\ drv_apart ctl (8 * nctl) leaves (8 * nl) /\
    drv_apart d 64 (word pc) 522 /\
    (!j. j < nl ==> drv_apart d 64 (word(lpc j)) (LENGTH(lmc j)))`;;

let STACK_DRV_STACK_BASE = prove
 (`!cfr a. stack_drv_stack 40 cfr a <=> drv_stack cfr a`,
  REWRITE_TAC[stack_drv_stack;drv_stack] THEN CONV_TAC NUM_REDUCE_CONV);;

let STACK_DRV_APART_BASE = prove
 (`!cfr b n. stack_drv_apart 40 cfr b n <=>
     drv_apart (word_sub cfr (word 48)) 304 b n`,
  REWRITE_TAC[stack_drv_apart] THEN CONV_TAC NUM_REDUCE_CONV);;

let STACK_DRV_CHILD_BASE = prove
 (`!bw ctl budget cfr st m used t.
    stack_drv_child 40 bw ctl budget cfr st m used t <=>
    drv_child bw ctl budget cfr st m used t`,
  REWRITE_TAC[stack_drv_child;drv_child;STACK_DRV_STACK_BASE]);;

let STACK_DRV_LAYOUT_BASE = prove
 (`!pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc.
    stack_drv_layout 40 pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc <=>
    drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc`,
  REWRITE_TAC[stack_drv_layout;drv_layout;STACK_DRV_APART_BASE] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let STACK_DRV_LOWER_VAL = prove
 (`!reserve cfr. reserve + 8 <= val(cfr:int64) ==>
    val(word_sub cfr (word(reserve + 8)):int64) = val cfr - (reserve + 8)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_VAL_SP_SUB THEN ASM_REWRITE_TAC[]);;

let STACK_DRV_WINDOW_END = prove
 (`!reserve cfr. reserve + 8 <= val(cfr:int64) ==>
    val(word_sub cfr (word(reserve + 8)):int64) + (reserve + 264) = val cfr + 256`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[STACK_DRV_LOWER_VAL] THEN ASM_ARITH_TAC);;

let STACK_DRV_STACK_MONO = prove
 (`!n m cfr a. n <= m /\ stack_drv_stack n cfr a ==>
    stack_drv_stack m cfr a`,
  REWRITE_TAC[stack_drv_stack] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let STACK_DRV_STACK_LEGACY = prove
 (`!reserve cfr a. 40 <= reserve /\ drv_stack cfr a ==>
    stack_drv_stack reserve cfr a`,
  REWRITE_TAC[stack_drv_stack;drv_stack] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let STACK_DRV_APART_SHRINK = prove
 (`!n m cfr b extent.
    n <= m /\ m + 8 <= val(cfr:int64) /\ stack_drv_apart m cfr b extent ==>
    stack_drv_apart n cfr b extent`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n + 8 <= val(cfr:int64)` ASSUME_TAC THENL
   [ASM_ARITH_TAC;ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_drv_apart;drv_apart]) THEN
  REWRITE_TAC[stack_drv_apart;drv_apart] THEN
  ASM_SIMP_TAC[STACK_DRV_LOWER_VAL] THEN
  MP_TAC(SPECL [`m:num`;`cfr:int64`] STACK_DRV_LOWER_VAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_ARITH_TAC);;

let STACK_DRV_LAYOUT_LEGACY = prove
 (`!reserve pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc.
    stack_drv_layout reserve pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc ==>
    drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_drv_layout;drv_layout] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM STACK_DRV_APART_BASE] THEN REPEAT CONJ_TAC THEN
  ASM_MESON_TAC[STACK_DRV_APART_SHRINK;ARITH_RULE
    `40 <= reserve /\ reserve + 8 <= cfr ==> 48 <= cfr`]);;

let STACK_DRV_IN_NOT_STACK = prove
 (`!reserve cfr a b n.
    reserve + 8 <= val(cfr:int64) /\ stack_drv_apart reserve cfr b n /\ drv_in a b n ==>
    ~stack_drv_stack reserve cfr a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`reserve:num`;`cfr:int64`] STACK_DRV_LOWER_VAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_drv_apart;drv_apart;drv_in]) THEN
  REWRITE_TAC[stack_drv_stack] THEN ASM_ARITH_TAC);;

let STACK_DRV_STACK_NOT_IN = prove
 (`!reserve cfr b n a.
    reserve + 8 <= val(cfr:int64) /\ stack_drv_apart reserve cfr b n /\
    val cfr <= val a + (reserve + 8) /\ val a < val cfr + 256 ==>
    ~drv_in a b n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`reserve:num`;`cfr:int64`] STACK_DRV_LOWER_VAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_drv_apart;drv_apart]) THEN
  REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC);;

let STACK_DRV_NOT_SAVED = prove
 (`!reserve cfr a.
    reserve + 8 <= val(cfr:int64) /\ ~stack_drv_stack reserve cfr a ==>
    ~component_stack_saved reserve (word_sub cfr (word 8)) a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[component_stack_saved] THEN
  SUBGOAL_THEN `val(word_sub cfr (word 8):int64) = val cfr - 8` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_SP_SUB THEN ASM_ARITH_TAC;ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_drv_stack]) THEN ASM_ARITH_TAC);;

let STACK_DRV_AREA_BYTES = prove
 (`!reserve cfr (b:int64) n x k (P:int64->bool).
    reserve + 8 <= val cfr /\ val b + n <= 2 EXP 64 /\ stack_drv_apart reserve cfr b n /\
    (!a. drv_in a b n ==> P a) /\ val x = val b + k /\ k + 8 <= n ==>
    !i. i < 8 ==> P (word_add x (word i)) /\
                  ~stack_drv_stack reserve cfr (word_add x (word i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:int64`;`b:int64`;`n:num`;`k:num`] DRV_BYTES_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC STACK_DRV_IN_NOT_STACK THEN
  MAP_EVERY EXISTS_TAC [`b:int64`;`n:num`] THEN ASM_REWRITE_TAC[]);;

let STACK_DRV_READ_OUT = prove
 (`!reserve s M cfr (x:int64).
    (!a. ~stack_drv_stack reserve cfr a ==> read memory s a = M a) /\
    (!i. i < 8 ==> ~stack_drv_stack reserve cfr (word_add x (word i))) ==>
    read (memory :> bytes64 x) s = drv_word M x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DRV_READ64] THEN
  MATCH_MP_TAC DRV_WORD_AGREE THEN ASM_SIMP_TAC[]);;

let STACK_DRV_READ_STATIC = prove
 (`!reserve s M m0 cfr (P:int64->bool) (x:int64).
    (!a. ~stack_drv_stack reserve cfr a ==> read memory s a = M a) /\
    (!a. P a ==> M a = m0 a) /\
    (!i. i < 8 ==> P (word_add x (word i)) /\
                  ~stack_drv_stack reserve cfr (word_add x (word i))) ==>
    read (memory :> bytes64 x) s = drv_word m0 x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DRV_READ64] THEN
  MATCH_MP_TAC DRV_WORD_AGREE THEN ASM_SIMP_TAC[]);;

let STACK_DRV_WIDE_LAYOUT_CONTROL = prove
 (`stack_drv_layout 512 256 (word 4096) (word 8192) (word 12288) 1
      (word 16384) 48 (word 20480) 20 (word 24576) 0
      (\j. 0) (\j. [])`,
  REWRITE_TAC[stack_drv_layout;stack_drv_apart;drv_apart;LENGTH] THEN
  SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let STACK_DRV_STACK_ALIAS_CONTROL = prove
 (`drv_layout 256 (word 4096) (word 8192) (word 12288) 1
      (word 3800) 4 (word 20480) 20 (word 24576) 0 (\j. 0) (\j. []) /\
   ~stack_drv_layout 512 256 (word 4096) (word 8192) (word 12288) 1
      (word 3800) 4 (word 20480) 20 (word 24576) 0 (\j. 0) (\j. [])`,
  REWRITE_TAC[drv_layout;stack_drv_layout;stack_drv_apart;drv_apart;LENGTH] THEN
  SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let stack_driver_memory_theorems =
 ["STACK_DRV_STACK_BASE",STACK_DRV_STACK_BASE;
  "STACK_DRV_APART_BASE",STACK_DRV_APART_BASE;
  "STACK_DRV_CHILD_BASE",STACK_DRV_CHILD_BASE;
  "STACK_DRV_LAYOUT_BASE",STACK_DRV_LAYOUT_BASE;
  "STACK_DRV_LOWER_VAL",STACK_DRV_LOWER_VAL;
  "STACK_DRV_WINDOW_END",STACK_DRV_WINDOW_END;
  "STACK_DRV_STACK_MONO",STACK_DRV_STACK_MONO;
  "STACK_DRV_STACK_LEGACY",STACK_DRV_STACK_LEGACY;
  "STACK_DRV_APART_SHRINK",STACK_DRV_APART_SHRINK;
  "STACK_DRV_LAYOUT_LEGACY",STACK_DRV_LAYOUT_LEGACY;
  "STACK_DRV_IN_NOT_STACK",STACK_DRV_IN_NOT_STACK;
  "STACK_DRV_STACK_NOT_IN",STACK_DRV_STACK_NOT_IN;
  "STACK_DRV_NOT_SAVED",STACK_DRV_NOT_SAVED;
  "STACK_DRV_AREA_BYTES",STACK_DRV_AREA_BYTES;
  "STACK_DRV_READ_OUT",STACK_DRV_READ_OUT;
  "STACK_DRV_READ_STATIC",STACK_DRV_READ_STATIC;
  "STACK_DRV_WIDE_LAYOUT_CONTROL",STACK_DRV_WIDE_LAYOUT_CONTROL;
  "STACK_DRV_STACK_ALIAS_CONTROL",STACK_DRV_STACK_ALIAS_CONTROL];;
