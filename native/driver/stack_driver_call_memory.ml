(* Word transport and protected memory across a bounded native callee. *)
needs "native/driver/stack_driver_memory.ml";;

let STACK_DRV_CHILD_REGIONS = prove
 (`!reserve bw ctl budget cfr st m used t.
    stack_drv_child reserve bw ctl budget cfr st m used t ==>
    tregs t 0 = cfr /\
    !r. r < 9 ==> tisa_base t r = drv_base bw st r /\ tisa_len t r = drv_len bw st r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_drv_child] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[drv_regs];
    REWRITE_TAC[tisa_base;tisa_len] THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[ARITH] THEN
    REWRITE_TAC[drv_fw;drv_base;drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ADD_CLAUSES]]);;

let STACK_DRV_RET_SLOT = prove
 (`!reserve pc cfr d plan ns bind nbw leaves nl lpc lmc i.
    val cfr + 256 <= 2 EXP 64 /\ i < 8 ==>
    drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc
      (word_add (word_add cfr (word 248)) (word i)) /\
    ~stack_drv_stack reserve cfr (word_add (word_add cfr (word 248)) (word i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `val(word_add (word_add cfr (word 248)) (word i):int64) = val cfr + 248 + i`
  ASSUME_TAC THENL
   [REWRITE_TAC[DRV_ADDR_ASSOC] THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`pc:num`;`cfr:int64`;`d:int64`;`plan:int64`;`ns:num`;`bind:int64`;
    `nbw:num`;`leaves:int64`;`nl:num`;`lpc:num->num`;`lmc:num->byte list`;`i:num`]
    DRV_RET_SLOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[stack_drv_stack] THEN
  ASM_ARITH_TAC);;

let STACK_DRV_CODE_NONOVERLAP = prove
 (`!reserve cfr p len (x:int64) k extent.
    reserve + 8 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\ p + len <= 2 EXP 64 /\
    stack_drv_apart reserve cfr (word p) len /\
    val x + (reserve + 8) = val cfr + k /\ k + extent <= reserve + 264 ==>
    nonoverlapping (word p:int64,len) (x,extent)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `len = 0` THENL
   [ASM_REWRITE_TAC[nonoverlapping] THEN
    MATCH_MP_TAC NONOVERLAPPING_MODULO_TRIVIAL THEN REWRITE_TAC[];ALL_TAC] THEN
  ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN MATCH_MP_TAC DRV_SUB_NONOVERLAP THEN
  MAP_EVERY EXISTS_TAC [`word_sub cfr (word(reserve + 8)):int64`;
    `reserve + 264`;`k:num`] THEN
  ASM_REWRITE_TAC[GSYM stack_drv_apart] THEN
  MP_TAC(SPECL [`reserve:num`;`cfr:int64`] STACK_DRV_LOWER_VAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `val(word p:int64) = p` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let STACK_DRV_RET_WORD = prove
 (`!reserve s stackpointer u (x:int64).
    (!a. ~component_stack_saved reserve stackpointer a ==>
         read memory s a = tmem u a) /\
    (!i. i < 8 ==> ~component_stack_saved reserve stackpointer (word_add x (word i))) ==>
    read (memory :> bytes64 x) s = drv_word (tmem u) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DRV_READ64] THEN
  MATCH_MP_TAC DRV_WORD_AGREE THEN ASM_SIMP_TAC[]);;

let STACK_DRV_OUT_NONOVERLAP248 = prove
 (`!reserve cfr (x:int64).
    40 <= reserve /\ reserve + 8 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\
    (!i. i < 8 ==> ~stack_drv_stack reserve cfr (word_add x (word i))) ==>
    nonoverlapping (x,8) (cfr,248)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC DRV_OUT_NONOVERLAP248 THEN
  REPEAT CONJ_TAC THEN ASM_MESON_TAC[STACK_DRV_STACK_LEGACY;ARITH_RULE
    `40 <= reserve /\ reserve + 8 <= cfr ==> 48 <= cfr`]);;

let STACK_DRV_AREA_READ = prove
 (`!reserve s (M:int64->byte) cfr (b:int64) len k.
    40 <= reserve /\ reserve + 8 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\
    val b + len <= 2 EXP 64 /\ stack_drv_apart reserve cfr b len /\
    (!a. ~stack_drv_stack reserve cfr a ==> read memory s a = M a) /\ k + 8 <= len ==>
    read (memory :> bytes64 (word_add b (word k))) s = drv_word M (word_add b (word k)) /\
    nonoverlapping (word_add b (word k),8) (cfr,192)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`reserve:num`;`cfr:int64`;`b:int64`;`len:num`;
    `word_add b (word k):int64`;`k:num`;`\a:int64. T`] STACK_DRV_AREA_BYTES) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;DISCH_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC STACK_DRV_READ_OUT THEN
    MAP_EVERY EXISTS_TAC [`reserve:num`;`cfr:int64`] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC DRV_OUT_NONOVERLAP THEN REPEAT CONJ_TAC THEN
    ASM_MESON_TAC[STACK_DRV_STACK_LEGACY;ARITH_RULE
      `40 <= reserve /\ reserve + 8 <= cfr ==> 48 <= cfr`]]);;

let STACK_DRV_AREA_READ_STATIC = prove
 (`!reserve s (M:int64->byte) m0 (P:int64->bool) cfr (b:int64) len k.
    40 <= reserve /\ reserve + 8 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\
    val b + len <= 2 EXP 64 /\ stack_drv_apart reserve cfr b len /\
    (!a. drv_in a b len ==> P a) /\ (!a. P a ==> M a = m0 a) /\
    (!a. ~stack_drv_stack reserve cfr a ==> read memory s a = M a) /\ k + 8 <= len ==>
    read (memory :> bytes64 (word_add b (word k))) s = drv_word m0 (word_add b (word k)) /\
    nonoverlapping (word_add b (word k),8) (cfr,192)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`reserve:num`;`cfr:int64`;`b:int64`;`len:num`;
    `word_add b (word k):int64`;`k:num`;`P:int64->bool`] STACK_DRV_AREA_BYTES) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;DISCH_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC STACK_DRV_READ_STATIC THEN
    MAP_EVERY EXISTS_TAC [`reserve:num`;`M:int64->byte`;`cfr:int64`;`P:int64->bool`] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC DRV_OUT_NONOVERLAP THEN REPEAT CONJ_TAC THEN
    ASM_MESON_TAC[STACK_DRV_STACK_LEGACY;ARITH_RULE
      `40 <= reserve /\ reserve + 8 <= cfr ==> 48 <= cfr`]]);;

let STACK_DRV_AFTER_STATIC = prove
 (`!reserve s7 t u decls cfr bw h (M:int64->byte) m0 (P:int64->bool) x.
    (!a. ~component_stack_saved reserve (word_sub cfr (word 8)) a ==>
         read memory s7 a = tmem u a) /\
    tisa_keeps decls t u /\ tregs t 0 = cfr /\ LENGTH decls <= 9 /\
    (!r. r < 9 ==> tisa_base t r = drv_base bw h r /\ tisa_len t r = drv_len bw h r) /\
    (!r a. tisa_rw decls r /\ P a ==> ~drv_in a (drv_base bw h r) (val(drv_len bw h r))) /\
    (!a. ~stack_drv_stack reserve cfr a ==> tmem t a = M a) /\
    (!a. P a ==> M a = m0 a) /\ reserve + 8 <= val cfr /\
    (!i. i < 8 ==> P (word_add x (word i)) /\
                  ~stack_drv_stack reserve cfr (word_add x (word i))) ==>
    read (memory :> bytes64 x) s7 = drv_word m0 x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i < 8 ==> ~tisa_writable decls t (word_add x (word i))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC DRV_NOT_WRITABLE THEN
    MAP_EVERY EXISTS_TAC [`cfr:int64`;`bw:num->int64`;`h:int64 list`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[stack_drv_stack] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[];ASM_ARITH_TAC];ALL_TAC] THEN
  MP_TAC(ISPECL [`reserve:num`;`s7:x86state`;`word_sub cfr (word 8):int64`;
    `u:tisa_state`;`x:int64`] STACK_DRV_RET_WORD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC STACK_DRV_NOT_SAVED THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`decls:(num#num#num)list`;`t:tisa_state`;`u:tisa_state`;`x:int64`]
    DRV_KEPT_WORD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC DRV_WORD_AGREE THEN ASM_MESON_TAC[]);;

let STACK_DRV_AFTER_FRAME = prove
 (`!reserve s7 u cfr j.
    (!a. ~component_stack_saved reserve (word_sub cfr (word 8)) a ==>
         read memory s7 a = tmem u a) /\
    tregs u 0 = cfr /\ reserve + 8 <= val cfr /\
    val cfr + 256 <= 2 EXP 64 /\ j < 24 ==>
    read (memory :> bytes64 (word_add cfr (word(8 * j)))) s7 = tisa_fword u j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[DRV_FWORD] THEN
  MATCH_MP_TAC STACK_DRV_RET_WORD THEN
  MAP_EVERY EXISTS_TAC [`reserve:num`;`word_sub cfr (word 8):int64`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[component_stack_saved] THEN
  SUBGOAL_THEN `val(word_sub cfr (word 8):int64) = val cfr - 8` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_SP_SUB THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN
    `val(word_add (word_add cfr (word(8 * j))) (word i):int64) = val cfr + 8 * j + i`
  SUBST1_TAC THENL
   [REWRITE_TAC[DRV_ADDR_ASSOC] THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let STACK_DRV_AFTER_BYTE = prove
 (`!reserve s7 tc u decls cfr bw h (M:int64->byte) m0 (P:int64->bool) a.
    (!a. ~component_stack_saved reserve (word_sub cfr (word 8)) a ==>
         read memory s7 a = tmem u a) /\
    tisa_keeps decls tc u /\ tregs tc 0 = cfr /\ LENGTH decls <= 9 /\
    (!r. r < 9 ==> tisa_base tc r = drv_base bw h r /\ tisa_len tc r = drv_len bw h r) /\
    (!r a. tisa_rw decls r /\ P a ==> ~drv_in a (drv_base bw h r) (val(drv_len bw h r))) /\
    (!a. ~stack_drv_stack reserve cfr a ==> tmem tc a = M a) /\
    (!a. P a ==> M a = m0 a) /\ reserve + 8 <= val cfr /\ P a /\
    ~stack_drv_stack reserve cfr a ==>
    read memory s7 a = m0 a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~tisa_writable decls tc a` ASSUME_TAC THENL
   [MATCH_MP_TAC DRV_NOT_WRITABLE THEN
    MAP_EVERY EXISTS_TAC [`cfr:int64`;`bw:num->int64`;`h:int64 list`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];RULE_ASSUM_TAC(REWRITE_RULE[stack_drv_stack]) THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tisa_keeps]) THEN ASM_MESON_TAC[STACK_DRV_NOT_SAVED]);;

let STACK_DRV_AFTER_PUSHED = prove
 (`!reserve s7 tc u decls cfr bw h (x:int64) v.
    (!a. ~component_stack_saved reserve (word_sub cfr (word 8)) a ==>
         read memory s7 a = tmem u a) /\
    tisa_keeps decls tc u /\ tregs tc 0 = cfr /\ LENGTH decls <= 9 /\
    (!r. r < 9 ==> tisa_base tc r = drv_base bw h r /\ tisa_len tc r = drv_len bw h r) /\
    (!r. tisa_readable decls r ==>
         stack_drv_apart reserve cfr (drv_base bw h r) (val(drv_len bw h r))) /\
    reserve + 8 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\
    val cfr + 176 <= val x /\ val x + 8 <= val cfr + 248 /\
    drv_word (tmem tc) x = v ==>
    read (memory :> bytes64 x) s7 = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i < 8 ==> val(word_add x (word i):int64) = val x + i`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ALL_TAC] THEN
  MP_TAC(ISPECL [`reserve:num`;`s7:x86state`;`word_sub cfr (word 8):int64`;
    `u:tisa_state`;`x:int64`] STACK_DRV_RET_WORD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[component_stack_saved] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(word_sub cfr (word 8):int64) = val cfr - 8` SUBST1_TAC THENL
     [MATCH_MP_TAC TISA_VAL_SP_SUB THEN ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && is_var(rhs(concl th)) && rhs(concl th) = `v:int64`)) THEN
  MATCH_MP_TAC DRV_KEPT_WORD THEN EXISTS_TAC `decls:(num#num#num)list` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC DRV_NOT_WRITABLE THEN
  MAP_EVERY EXISTS_TAC [`cfr:int64`;`bw:num->int64`;`h:int64 list`] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ALL_TAC;ASM_ARITH_TAC] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN MATCH_MP_TAC STACK_DRV_STACK_NOT_IN THEN
  MAP_EVERY EXISTS_TAC [`reserve:num`;`cfr:int64`] THEN
  ASM_SIMP_TAC[TISA_RW_READABLE] THEN ASM_ARITH_TAC);;

let STACK_DRV_STATIC_NOT_STACK = prove
 (`!reserve pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc a.
    stack_drv_layout reserve pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
    drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a ==>
    ~stack_drv_stack reserve cfr a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [stack_drv_layout]) THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [drv_static] o
    check (fun th -> can (find_term ((=) `drv_static`)) (concl th))) THEN
  TRY(FIRST (map (fun (b,n) ->
    MATCH_MP_TAC STACK_DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [b;n] THEN
    ASM_SIMP_TAC[] THEN NO_TAC)
    [`word pc:int64`,`522`;`d:int64`,`64`;`plan:int64`,`144 * ns`;
     `bind:int64`,`8 * nbw`;`leaves:int64`,`8 * nl`;
     `word((lpc:num->num) j):int64`,`LENGTH((lmc:num->byte list) j)`])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[drv_in]) THEN REWRITE_TAC[stack_drv_stack] THEN
  SUBGOAL_THEN `val(word_add cfr (word 248):int64) = val cfr + 248`
  ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_ARITH_TAC);;

let stack_driver_call_memory_theorems =
 ["STACK_DRV_CHILD_REGIONS",STACK_DRV_CHILD_REGIONS;
  "STACK_DRV_RET_SLOT",STACK_DRV_RET_SLOT;
  "STACK_DRV_CODE_NONOVERLAP",STACK_DRV_CODE_NONOVERLAP;
  "STACK_DRV_RET_WORD",STACK_DRV_RET_WORD;
  "STACK_DRV_OUT_NONOVERLAP248",STACK_DRV_OUT_NONOVERLAP248;
  "STACK_DRV_AREA_READ",STACK_DRV_AREA_READ;
  "STACK_DRV_AREA_READ_STATIC",STACK_DRV_AREA_READ_STATIC;
  "STACK_DRV_AFTER_STATIC",STACK_DRV_AFTER_STATIC;
  "STACK_DRV_AFTER_FRAME",STACK_DRV_AFTER_FRAME;
  "STACK_DRV_AFTER_BYTE",STACK_DRV_AFTER_BYTE;
  "STACK_DRV_AFTER_PUSHED",STACK_DRV_AFTER_PUSHED;
  "STACK_DRV_STATIC_NOT_STACK",STACK_DRV_STATIC_NOT_STACK];;
