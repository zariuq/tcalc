(* A whole-word zero initializer over one writable region. *)
needs "native/leaves/common/leaf_lib.ml";;

let zero_words_checks = new_definition
 `zero_words_checks = (TSeq (TInstr (TLoadFrame TyU64 1 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 2 1 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 3 2 3)) (TSeq (TInstr (TCmp CondEq TyU64 4 3 (OpReg 1))) (TSeq (TIf 4 TSkip (TReturn 2 2)) (TSeq (TInstr (TLoadFrame TyPtr 6 0)) (TInstr (TImm TyU64 7 (word 0)))))))))`;;

let zero_words_body = new_definition
 `zero_words_body = (TSeq (TInstr (TAddr 0 8 6 (SOME 5) 3 (&0:int))) (TInstr (TStore 8 0 8 (&0:int) 7)))`;;

let zero_words = new_definition
 `zero_words = TProg [(2,0,8)] []
   (TSeq zero_words_checks (TSeq (TCountLoop 5 2 4294967295 zero_words_body) (TReturn 1 2)))`;;

let ZERO_WORDS_TERM = prove
 (`zero_words = (TProg [(2,0,8)] [] (TSeq (TSeq (TInstr (TLoadFrame TyU64 1 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 2 1 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 3 2 3)) (TSeq (TInstr (TCmp CondEq TyU64 4 3 (OpReg 1))) (TSeq (TIf 4 TSkip (TReturn 2 2)) (TSeq (TInstr (TLoadFrame TyPtr 6 0)) (TInstr (TImm TyU64 7 (word 0))))))))) (TSeq (TCountLoop 5 2 4294967295 (TSeq (TInstr (TAddr 0 8 6 (SOME 5) 3 (&0:int))) (TInstr (TStore 8 0 8 (&0:int) 7)))) (TReturn 1 2))))`,
  REWRITE_TAC[zero_words;zero_words_checks;zero_words_body]);;

let ZERO_WORDS_DECLS = prove
 (`tisa_decls zero_words = [(2,0,8)]`,REWRITE_TAC[zero_words;tisa_decls]);;
let ZERO_WORDS_LEAF_WF = prove
 (`tisa_leaf_wf zero_words`,LEAF_WF_TAC ZERO_WORDS_DECLS ZERO_WORDS_TERM);;

let zero_words_count = new_definition
 `zero_words_count t = val(tisa_len t 0) DIV 8`;;
let zero_words_supported = new_definition
 `zero_words_supported t <=>
    8 * zero_words_count t = val(tisa_len t 0) /\ zero_words_count t <= 4294967295`;;
let zero_words_post = new_definition
 `zero_words_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 20 = tisa_fword t 20 /\
    tisa_fword u 21 = tisa_fword t 21 /\
    (if zero_words_supported t
     then k = 1 /\ tisa_fword u 19 = word(zero_words_count t) /\
          (!i. i < zero_words_count t
               ==> tisa_read u (word_add (tisa_base u 0) (word(8 * i))) 8 = word 0)
     else k = 2 /\ tmem u = tmem(tisa_finst 2 (tisa_fword u 19) t))`;;

let ZERO_WORDS_ENTRY = prove
 (`!t. tisa_entry_ok zero_words t
       ==> val(tregs t 0) + 192 <= 2 EXP 64 /\
           val(tisa_base t 0) + val(tisa_len t 0) < 2 EXP 64 /\
           (val(tisa_len t 0) = 0 \/
            val(tisa_base t 0) + val(tisa_len t 0) <= val(tregs t 0) \/
            val(tregs t 0) + 192 <= val(tisa_base t 0))`,
  GEN_TAC THEN REWRITE_TAC[zero_words;tisa_entry_ok;tisa_decls_ok;tisa_pairs_ok;
    tisa_init_ok;tisa_region_ok;tisa_frame;tisa_base;tisa_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[]);;

let ZERO_WORDS_LENGTH = prove
 (`!length:int64. word_shl (word_ushr length 3) 3 = length <=>
                  8 * (val length DIV 8) = val length`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ;VAL_WORD_SHL;VAL_WORD_USHR;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `8 * (val(length:int64) DIV 8) < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ISPEC `length:int64` VAL_BOUND_64) THEN
    MP_TAC(SPECL [`val(length:int64)`;`8`] DIVISION) THEN ARITH_TAC;
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_SIMP_TAC[MOD_LT]]);;

let zero_words_inv = new_definition
 `zero_words_inv t N j s <=>
    tregs s 0 = tregs t 0 /\
    (!k. k < 24 ==> tisa_fword s k = tisa_fword t k) /\
    N = zero_words_count t /\ 8 * N = val(tisa_len t 0) /\ j <= N /\
    tregs s 2 = word N /\ tregs s 6 = tisa_base t 0 /\ tregs s 7 = word 0 /\
    (!i. i < j ==> tisa_read s (word_add (tisa_base t 0) (word(8 * i))) 8 = word 0)`;;

let ZERO_WORDS_VIEW = prove
 (`!t N j s. zero_words_inv t N j s
     ==> (!r. r < 12 ==> tisa_base s r = tisa_base t r) /\
         (!r. r < 12 ==> tisa_len s r = tisa_len t r)`,
  REWRITE_TAC[zero_words_inv;tisa_base;tisa_len] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let ZERO_WORDS_INDEX = prove
 (`!t N j. tisa_entry_ok zero_words t /\ N = zero_words_count t /\
           8 * N = val(tisa_len t 0) /\ j < N
       ==> j < 2 EXP 64 /\
           val(word_add (tisa_base t 0) (word(8 * j)):int64) = val(tisa_base t 0) + 8 * j /\
           val(tisa_base t 0) + 8 * j + 8 <= val(tisa_base t 0) + val(tisa_len t 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ZERO_WORDS_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `val(word_add (tisa_base t 0) (word(8 * j)):int64) = val(tisa_base t 0) + 8 * j`
   ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let ZERO_WORDS_SETREG = prove
 (`!t N j s x v. zero_words_inv t N j s /\ ~(x = 0) /\ ~(x = 2) /\ ~(x = 6) /\ ~(x = 7)
       ==> zero_words_inv t N j (tisa_setreg x v s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[zero_words_inv] o
    check (fun th -> tisa_has_tm `zero_words_inv` th)) THEN
  ASM_SIMP_TAC[zero_words_inv;TISA_TREGS_SETREG;TISA_FWORD_SETREG;TISA_READ_SETREG;EQ_SYM_EQ]);;

let ZERO_WORDS_STORE_INV = prove
 (`!t N j s. tisa_entry_ok zero_words t /\ zero_words_inv t N j s /\ j < N
       ==> zero_words_inv t N (j + 1)
             (tisa_store (word_add (tisa_base t 0) (word(8 * j))) 8 (word 0) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[zero_words_inv] o
    check (fun th -> tisa_has_tm `zero_words_inv` th)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ZERO_WORDS_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`t:tisa_state`;`N:num`;`j:num`] ZERO_WORDS_INDEX) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`word_add (tisa_base t 0) (word(8 * j)):int64`;`8`;`word 0:int64`;`s:tisa_state`]
    TISA_STORE_KEEPS_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[zero_words_inv;TISA_TREGS_STORE] THEN ASM_SIMP_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i:num = j` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TISA_READ_STORE_SAME THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `i < j` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word_add (tisa_base t 0) (word(8 * i)):int64) = val(tisa_base t 0) + 8 * i`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS `tisa_read s (word_add (tisa_base t 0) (word(8 * i))) 8` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[]]]);;

let ZERO_WORDS_BODY_WP = prove
 (`!t N j s0. tisa_entry_ok zero_words t /\ j < N /\ zero_words_inv t N j s0
       ==> tisa_wp zero_words_body (zero_words_inv t N (j + 1)) (zero_words_post t)
             (tisa_setreg 5 (word j) s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ZERO_WORDS_VIEW) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ZERO_WORDS_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[zero_words_inv] o
    check (fun th -> tisa_has_tm `zero_words_inv` th)) THEN
  MP_TAC(SPECL [`t:tisa_state`;`N:num`;`j:num`] ZERO_WORDS_INDEX) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = zero_words_count t`)) THEN
  REWRITE_TAC[zero_words_body] THEN TISA_VCG_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `val(word j:int64) = j` then
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC) THEN
  FIRST [MATCH_MP_TAC ZERO_WORDS_STORE_INV THEN ASM_REWRITE_TAC[] THEN
           MATCH_MP_TAC ZERO_WORDS_SETREG THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
           MATCH_MP_TAC ZERO_WORDS_SETREG THEN ASM_REWRITE_TAC[ARITH_EQ];
         FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && tisa_has_tm `tisa_inside` th)) THEN
         REWRITE_TAC[tisa_inside] THEN CONV_TAC INT_REDUCE_CONV THEN
         ASM_SIMP_TAC[ARITH_RULE `0 < 12`] THEN
         REWRITE_TAC[INT_OF_NUM_MUL;INT_OF_NUM_ADD;INT_OF_NUM_LE] THEN
         ASM_ARITH_TAC]);;

let ZERO_WORDS_COUNT_BOUND = prove
 (`!t. zero_words_count t < 2 EXP 61 /\
       val(word(zero_words_count t):int64) = zero_words_count t`,
  GEN_TAC THEN SUBGOAL_THEN `zero_words_count t < 2 EXP 61` ASSUME_TAC THENL
   [REWRITE_TAC[zero_words_count] THEN SIMP_TAC[RDIV_LT_EQ;ARITH_EQ] THEN
    MP_TAC(ISPEC `tisa_len t 0` VAL_BOUND_64) THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN ASM_ARITH_TAC]);;

let ZERO_WORDS_SHR = prove
 (`!length:int64. word_ushr length 3 = word(val length DIV 8)`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN
  REWRITE_TAC[VAL_WORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV);;

let ZERO_WORDS_MEM_TAC =
  REWRITE_TAC[tisa_finst;tisa_setfword;tisa_store;tmem;tregs;tisa_frame;
              TISA_TREGS_SETREG;TISA_TMEM_SETREG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

let ZERO_WORDS_FAILST = prove
 (`!k s. tisa_failst k s = tisa_finst k (word k) s`,
  REWRITE_TAC[tisa_failst;tisa_finst]);;

let ZERO_WORDS_PROLOGUE_WP = prove
 (`!t. tisa_entry_ok zero_words t
       ==> tisa_wp zero_words_checks
             (\s. tmem s = tmem t /\ zero_words_inv t (zero_words_count t) 0 s)
             (zero_words_post t) t`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ZERO_WORDS_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[zero_words_checks] THEN TISA_VCG_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ZERO_WORDS_LENGTH;GSYM zero_words_count]) THEN
  REWRITE_TAC[zero_words_post;zero_words_supported;ZERO_WORDS_SHR;GSYM zero_words_count;
              zero_words_inv;TISA_TREGS_SETREG;TISA_TMEM_SETREG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THENL
   [SIMP_TAC[TISA_FWORD_SETREG;ARITH_EQ;LE_0;LT];
    TISA_STATE_NORM_TAC THEN ZERO_WORDS_MEM_TAC]);;

let ZERO_WORDS_FINISH = prove
 (`!t N s. tisa_entry_ok zero_words t /\ zero_words_inv t N N s /\ N <= 4294967295
       ==> zero_words_post t 1
             (tisa_finst 1 (word N) (tisa_setreg 5 (word N) s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ZERO_WORDS_VIEW) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ZERO_WORDS_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[zero_words_inv] o
    check (fun th -> tisa_has_tm `zero_words_inv` th)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = zero_words_count t`)) THEN
  ASM_REWRITE_TAC[zero_words_post;zero_words_supported] THEN
  TISA_STATE_NORM_TAC THEN ASM_SIMP_TAC[ARITH_EQ;ARITH_RULE `20 < 24 /\ 21 < 24 /\ 0 < 12`] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`zero_words_count t`;`i:num`] ZERO_WORDS_INDEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  TISA_STATE_NORM_TAC THEN ASM_SIMP_TAC[TISA_READ_SETREG]);;

let ZERO_WORDS_ROOT_WP = prove
 (`!t. tisa_entry_ok zero_words t
       ==> tisa_wp (tisa_root zero_words) (\s. F) (zero_words_post t) t`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[zero_words;tisa_root;TISA_WP_SEQ] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  EXISTS_TAC `\s. tmem s = tmem t /\ zero_words_inv t (zero_words_count t) 0 s` THEN
  EXISTS_TAC `zero_words_post t` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC ZERO_WORDS_PROLOGUE_WP THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `s:tisa_state` THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[zero_words_inv] o
    check (fun th -> tisa_has_tm `zero_words_inv` th)) THEN
  MP_TAC(SPEC `t:tisa_state` ZERO_WORDS_COUNT_BOUND) THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ZERO_WORDS_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC TISA_WP_COUNT_LOOP THEN
  EXISTS_TAC `\N j s. zero_words_count t <= 4294967295 /\ zero_words_inv t N j s` THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `~(zero_words_supported t)` ASSUME_TAC THENL
     [REWRITE_TAC[zero_words_supported] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[zero_words_post;ZERO_WORDS_FAILST] THEN
    TISA_STATE_NORM_TAC THEN ASM_SIMP_TAC[ARITH_RULE `20 < 24 /\ 21 < 24`] THEN ZERO_WORDS_MEM_TAC;
    DISCH_TAC THEN ASM_ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC ZERO_WORDS_BODY_WP THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`N:num`;`s1:tisa_state`] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[zero_words_inv] o
      check (fun th -> tisa_has_tm `zero_words_inv` th)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = zero_words_count t`)) THEN
    REWRITE_TAC[TISA_WP_RETURN;TISA_TREGS_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ZERO_WORDS_FINISH THEN ASM_REWRITE_TAC[]]);;

let ZERO_WORDS_RUN = prove
 (`!t k u. tisa_entry_ok zero_words t /\ tisa_run zero_words t = TStop k u
       ==> zero_words_post t k u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`zero_words`;`t:tisa_state`;`zero_words_post t`] LEAF_RUN_BY_WP) THEN
  ASM_SIMP_TAC[ZERO_WORDS_ROOT_WP] THEN
  DISCH_THEN(MP_TAC o SPECL [`k:num`;`u:tisa_state`]) THEN ASM_REWRITE_TAC[]);;

let ZERO_WORDS_FRAME = prove
 (`!t k u. tisa_entry_ok zero_words t /\ tisa_run zero_words t = TStop k u
       ==> tisa_keeps [(2,0,8)] t u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`zero_words`;`t:tisa_state`;`k:num`;`u:tisa_state`] TISA_RUN_KEEPS) THEN
  ASM_REWRITE_TAC[ZERO_WORDS_LEAF_WF;ZERO_WORDS_DECLS]);;

let ZERO_WORDS_RUN_FRAMED = prove
 (`!t k u. tisa_entry_ok zero_words t /\ tisa_run zero_words t = TStop k u
       ==> zero_words_post t k u /\ tisa_keeps [(2,0,8)] t u`,
  MESON_TAC[ZERO_WORDS_RUN;ZERO_WORDS_FRAME]);;

let zero_words_contract = new_definition
 `zero_words_contract t k u <=> zero_words_post t k u /\ tisa_keeps [(2,0,8)] t u`;;

let ZERO_WORDS_CONTRACT_RUN = prove
 (`!t k u. tisa_entry_ok zero_words t /\ tisa_run zero_words t = TStop k u
       ==> zero_words_contract t k u`,
  REWRITE_TAC[zero_words_contract] THEN MATCH_ACCEPT_TAC ZERO_WORDS_RUN_FRAMED);;

let ZERO_WORDS_EXACT = prove
 (`!t k u. tisa_entry_ok zero_words t /\ tisa_run zero_words t = TStop k u
       ==> (k = 1 <=> zero_words_supported t) /\ (k = 1 \/ k = 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] ZERO_WORDS_RUN) THEN
  ASM_REWRITE_TAC[zero_words_post] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ]);;

let ZERO_WORDS_TERMINATES = prove
 (`!t. tisa_entry_ok zero_words t
       ==> ?k u. tisa_run zero_words t = TStop k u /\ zero_words_post t k u /\
                 tisa_keeps [(2,0,8)] t u`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`zero_words`;`t:tisa_state`] TISA_RUN_STOP) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u:tisa_state` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:num`;`u:tisa_state`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ZERO_WORDS_RUN_FRAMED THEN ASM_REWRITE_TAC[]);;

let ZERO_WORDS_REGION_ZERO = prove
 (`!t k u i. tisa_entry_ok zero_words t /\ tisa_run zero_words t = TStop k u /\
             k = 1 /\ 8 * i + 8 <= val(tisa_len t 0)
       ==> tisa_read u (word_add (tisa_base u 0) (word(8 * i))) 8 = word 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] ZERO_WORDS_RUN) THEN
  ASM_REWRITE_TAC[zero_words_post] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[zero_words_supported] o
    check (fun th -> tisa_has_tm `zero_words_supported` th)) THEN ASM_ARITH_TAC);;

let zero_words_theorems =
 ["ZERO_WORDS_TERM",ZERO_WORDS_TERM;"ZERO_WORDS_DECLS",ZERO_WORDS_DECLS;
  "ZERO_WORDS_LEAF_WF",ZERO_WORDS_LEAF_WF;"ZERO_WORDS_ENTRY",ZERO_WORDS_ENTRY;
  "ZERO_WORDS_LENGTH",ZERO_WORDS_LENGTH;"ZERO_WORDS_VIEW",ZERO_WORDS_VIEW;
  "ZERO_WORDS_INDEX",ZERO_WORDS_INDEX;"ZERO_WORDS_SETREG",ZERO_WORDS_SETREG;
  "ZERO_WORDS_STORE_INV",ZERO_WORDS_STORE_INV;"ZERO_WORDS_BODY_WP",ZERO_WORDS_BODY_WP;
  "ZERO_WORDS_COUNT_BOUND",ZERO_WORDS_COUNT_BOUND;"ZERO_WORDS_SHR",ZERO_WORDS_SHR;
  "ZERO_WORDS_FAILST",ZERO_WORDS_FAILST;"ZERO_WORDS_PROLOGUE_WP",ZERO_WORDS_PROLOGUE_WP;
  "ZERO_WORDS_FINISH",ZERO_WORDS_FINISH;"ZERO_WORDS_ROOT_WP",ZERO_WORDS_ROOT_WP;
  "ZERO_WORDS_RUN",ZERO_WORDS_RUN;"ZERO_WORDS_FRAME",ZERO_WORDS_FRAME;
  "ZERO_WORDS_CONTRACT_RUN",ZERO_WORDS_CONTRACT_RUN;
  "ZERO_WORDS_RUN_FRAMED",ZERO_WORDS_RUN_FRAMED;"ZERO_WORDS_EXACT",ZERO_WORDS_EXACT;
  "ZERO_WORDS_TERMINATES",ZERO_WORDS_TERMINATES;"ZERO_WORDS_REGION_ZERO",ZERO_WORDS_REGION_ZERO];;
