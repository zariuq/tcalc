(* Word observations of the initializer's exact byte-memory patch. *)
needs "native/leaves/control_init/control_init.ml";;
needs "native/hol/memory_words.ml";;

let CONTROL_WORD_WRITE = prove
 (`!base length i j (v:int64) m.
     val(base:int64) + length < 2 EXP 64 /\
     8 * i + 8 <= length /\ 8 * j + 8 <= length
     ==> drv_word (write (bytes(word_add base (word(8 * i)),8)) (val v) m)
                  (word_add base (word(8 * j))) =
         if i = j then v else drv_word m (word_add base (word(8 * j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:num = j` THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM TISA_WRITE_BYTES64;DRV_WORD_WRITE_SAME];ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word_add base (word(8 * i)):int64) = val base + 8 * i` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add base (word(8 * j)):int64) = val base + 8 * j` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[drv_word] THEN AP_TERM_TAC THEN MATCH_MP_TAC TISA_READ_WRITE_APART THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let CONTROL_WORD_PATCH = prove
 (`!indices base (values:num->int64) m length j.
     val(base:int64) + length < 2 EXP 64 /\ 8 * j + 8 <= length /\
     ALL (\i. 8 * i + 8 <= length) indices
     ==> drv_word
          (ITLIST (\i mem. write (bytes(word_add base (word(8 * i)),8))
                                (val(values i)) mem) indices m)
          (word_add base (word(8 * j))) =
         if MEM j indices then values j
         else drv_word m (word_add base (word(8 * j)))`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[ITLIST;MEM];ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ITLIST;MEM;ALL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`base:int64`;`length:num`;`h:num`;`j:num`;`(values:num->int64) h`;
    `ITLIST (\i mem. write (bytes(word_add base (word(8 * i)),8))
                           (val((values:num->int64) i)) mem) t m:(int64->byte)`] CONTROL_WORD_WRITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `h:num = j` THENL
   [ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(j:num = h)` ASSUME_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `length:num` THEN ASM_REWRITE_TAC[]]);;

let CONTROL_MEM_REVERSE = prove
 (`!l:num list. !j. MEM j (REVERSE l) <=> MEM j l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE;MEM_APPEND;MEM] THEN MESON_TAC[]);;

let CONTROL_INDEX_MEMBER = prove
 (`!j n. MEM j (REVERSE(list_of_seq (\i:num. i) n)) <=> j < n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONTROL_MEM_REVERSE;MEM_EXISTS_EL;LENGTH_LIST_OF_SEQ] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN EXISTS_TAC `j:num` THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ]]);;

let CONTROL_INIT_PATCH_WORD = prove
 (`!base (policy:int64) m length j.
     val(base:int64) + length < 2 EXP 64 /\ 192 <= length /\ 8 * j + 8 <= length
     ==> drv_word (control_init_patch base policy m) (word_add base (word(8 * j))) =
         if j < 24 then control_init_value policy j
         else drv_word m (word_add base (word(8 * j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[control_init_patch] THEN
  MP_TAC(ISPECL [`REVERSE(list_of_seq (\i:num. i) 24)`;`base:int64`;`control_init_value policy`;
                `m:int64->byte`;`length:num`;`j:num`] CONTROL_WORD_PATCH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM ALL_MEM;CONTROL_INDEX_MEMBER] THEN
    REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[CONTROL_INDEX_MEMBER]]);;

let CONTROL_INIT_FINISH_WORD = prove
 (`!t s out (v:int64) j.
     tisa_entry_ok control_init t /\ tregs s 0 = tregs t 0 /\
     8 * j + 8 <= val(tisa_len t 0)
     ==> drv_word (tmem(tisa_finst out v s))
                  (word_add (tisa_base t 0) (word(8 * j))) =
         drv_word (tmem s) (word_add (tisa_base t 0) (word(8 * j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o MATCH_MP CONTROL_INIT_ENTRY) THEN
  SUBGOAL_THEN
   `val(word_add (tisa_base t 0) (word(8 * j)):int64) = val(tisa_base t 0) + 8 * j`
   ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ALL_TAC] THEN
  MP_TAC(SPECL [`s:tisa_state`;`out:num`;`v:int64`;
                `word_add (tisa_base t 0) (word(8 * j)):int64`] TISA_READ_FINST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[tisa_read;drv_word]);;

let CONTROL_INIT_RUN_WORD = prove
 (`!t k u j.
     tisa_entry_ok control_init t /\ tisa_run control_init t = TStop k u /\
     8 * j + 8 <= val(tisa_len t 0)
     ==> drv_word (tmem u) (word_add (tisa_base t 0) (word(8 * j))) =
         if val(tisa_fword t 22) <= 2 /\ j < 24
         then control_init_value (tisa_fword t 22) j
         else drv_word (tmem t) (word_add (tisa_base t 0) (word(8 * j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o MATCH_MP CONTROL_INIT_ENTRY) THEN
  ASM_CASES_TAC `val(tisa_fword t 22) <= 2` THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] CONTROL_INIT_RUN) THEN
  ASM_REWRITE_TAC[control_init_post] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  ASM_SIMP_TAC[CONTROL_INIT_FINISH_WORD;tregs;tmem] THEN
  FIRST [REFL_TAC;
         MATCH_MP_TAC CONTROL_INIT_PATCH_WORD THEN EXISTS_TAC `val(tisa_len t 0)` THEN ASM_REWRITE_TAC[]]);;

let CONTROL_INIT_RUN_NUMBER = prove
 (`!t k u j.
     tisa_entry_ok control_init t /\ tisa_run control_init t = TStop k u /\
     8 * j + 8 <= val(tisa_len t 0)
     ==> pl_mw (tmem u) (tisa_base t 0) j =
         if val(tisa_fword t 22) <= 2 /\ j < 24
         then val(control_init_value (tisa_fword t 22) j)
         else pl_mw (tmem t) (tisa_base t 0) j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`;`j:num`] CONTROL_INIT_RUN_WORD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  REWRITE_TAC[pl_mw] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let control_init_word_theorems =
 ["CONTROL_WORD_WRITE",CONTROL_WORD_WRITE;"CONTROL_WORD_PATCH",CONTROL_WORD_PATCH;
  "CONTROL_MEM_REVERSE",CONTROL_MEM_REVERSE;"CONTROL_INDEX_MEMBER",CONTROL_INDEX_MEMBER;
  "CONTROL_INIT_PATCH_WORD",CONTROL_INIT_PATCH_WORD;
  "CONTROL_INIT_FINISH_WORD",CONTROL_INIT_FINISH_WORD;
  "CONTROL_INIT_RUN_WORD",CONTROL_INIT_RUN_WORD;
  "CONTROL_INIT_RUN_NUMBER",CONTROL_INIT_RUN_NUMBER];;
