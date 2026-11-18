(* The counted ID reader, from scalar decoding through list publication. *)

needs "native/leaves/ids_next/ids_next_program.ml";;
needs "native/hol/reader_leb128.ml";;

let ids_available = new_definition
 `ids_available st = val(tisa_len st 0) - val(tregs st 6)`;;

let ids_byte_at = new_definition
 `ids_byte_at st j = region_byte st 0 (val(tregs st 6) + j)`;;

let ids_input = new_definition
 `ids_input st = list_of_seq (ids_byte_at st) (ids_available st)`;;

let IDS_INPUT_BYTES = prove
 (`!st. ids_input st = region_from st 0 (val(tregs st 6))`,
  GEN_TAC THEN REWRITE_TAC[ids_input; ids_available; region_from] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; ids_byte_at]);;

let ids_scan_view = new_definition
 `ids_scan_view st s <=>
    tmem s = tmem st /\
    tregs s 0 = tregs st 0 /\ tregs s 1 = tregs st 1 /\
    tregs s 2 = tregs st 2 /\ tregs s 3 = tregs st 3 /\ tregs s 4 = tregs st 4`;;

let ids_scan_inv = new_definition
 `ids_scan_inv st j s <=>
    ids_scan_view st s /\
    tregs s 5 = word 1 /\ tregs s 6 = tregs st 6 /\
    tregs s 7 = word(leb_dec(list_of_seq (ids_byte_at st) j)) /\
    tregs s 8 = word(128 EXP j) /\ tregs s 10 = word 9 /\
    j <= ids_available st /\ (!i. i < j ==> 128 <= ids_byte_at st i)`;;

let ids_scan_finished = new_definition
 `ids_scan_finished st s <=>
    ids_scan_view st s /\ tregs s 5 = word 0 /\
    ?v. leb_fires (ids_input st) v /\ tregs s 7 = word v /\
        tregs s 6 = word(val(tregs st 6) + LENGTH(leb_enc v))`;;

let ids_scan_bad = new_definition
 `ids_scan_bad st k s <=>
    k = 0 /\ (!v. ~leb_fires (ids_input st) v) /\
    tmem s = tmem(tisa_finst 0 (word 0) st) /\
    tregs s 0 = tregs st 0 /\ tregs s 1 = tregs st 1 /\
    tregs s 2 = tregs st 2 /\ tregs s 3 = tregs st 3 /\ tregs s 4 = tregs st 4`;;

let IDS_LOW_DIGIT = prove
 (`!v. v < 256 ==> tisa_extract (word v:int64) 0 7 = word(v MOD 128)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word v:int64) = v` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[tisa_extract; ARITH_RULE `7 < 64`; WORD_USHR_ZERO;
              CONJUNCT1 WORD_AND_MASK_WORD] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let IDS_SCAN_STATES_TAC =
  REWRITE_TAC[ids_scan_view; TISA_TREGS_SETREG; TISA_TMEM_SETREG; tisa_finst;
              tisa_setfword; TISA_TMEM_STORE; TISA_TREGS_STORE; tisa_frame] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

let IDS_SCAN_BYTE_LT = prove
 (`!st j. ids_byte_at st j < 256`,
  REWRITE_TAC[ids_byte_at; REGION_BYTE_LT]);;

let IDS_SCAN_BYTE_READ = prove
 (`!st j. tisa_read st (word_add (tisa_base st 0) (word(val(tregs st 6) + j))) 1 =
          word(ids_byte_at st j)`,
  REWRITE_TAC[ids_byte_at; READ_REGION_BYTE]);;

let IDS_SCAN_WORD_BYTE = prove
 (`!st j. val(word(ids_byte_at st j):int64) = ids_byte_at st j`,
  REWRITE_TAC[ids_byte_at; VAL_WORD_REGION_BYTE]);;

let IDS_SCAN_ROOT_WORD = prove
 (`!st j. word_add (word_add (tregs st 6) (word j)) (word 1):int64 =
          word(val(tregs st 6) + SUC j)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [GSYM WORD_VAL] THEN
  REWRITE_TAC[GSYM WORD_ADD; ADD1; ADD_ASSOC]);;

let IDS_SCAN_DEC_TAC =
  FIRST_ASSUM(fun th -> if concl th = `ids_byte_at st j < 128` then
      let eq = MATCH_MP (SPECL [`ids_byte_at st`; `j:num`] LEB_STEP_DEC)
                         (CONJ th (ASSUME `j < 9`)) in
      RULE_ASSUM_TAC(REWRITE_RULE[eq]) THEN REWRITE_TAC[eq]
    else NO_TAC);;

let IDS_SCAN_VERDICT_TAC th extra =
  REWRITE_TAC[ids_input] THEN
  MP_TAC(ISPECL ([`ids_byte_at st`; `ids_available st`] @ extra) th) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IDS_SCAN_BYTE_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC;
    SIMP_TAC[]];;

let IDS_SCAN_ACCEPT_TAC =
  REWRITE_TAC[ids_scan_finished] THEN
  CONJ_TAC THENL [IDS_SCAN_STATES_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [IDS_SCAN_STATES_TAC; ALL_TAC] THEN
  EXISTS_TAC `leb_dec (list_of_seq (ids_byte_at st) (SUC j))` THEN
  MP_TAC(SPECL [`ids_byte_at st`; `ids_available st`; `j:num`] LEB_SEQ_FIRES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IDS_SCAN_BYTE_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC;
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[ids_input] THEN IDS_SCAN_STATES_TAC THEN
  REWRITE_TAC[IDS_SCAN_ROOT_WORD; GSYM WORD_ADD; GSYM WORD_MUL; LEB_DEC_SEQ_SUC] THEN
  ASM_SIMP_TAC[MOD_LT];;

let IDS_SCAN_ZERO_TAC =
  REWRITE_TAC[ids_scan_finished] THEN
  CONJ_TAC THENL [IDS_SCAN_STATES_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [IDS_SCAN_STATES_TAC; ALL_TAC] THEN
  EXISTS_TAC `0` THEN
  SUBGOAL_THEN `leb_enc 0 = [0]` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[leb_enc_def] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ids_input; LEB_FIRES_SEQ; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN IDS_SCAN_STATES_TAC THEN
  ASM_REWRITE_TAC[list_of_seq; leb_dec; TISA_WORD_ADD_VAL; ADD1] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
  TRY(X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `i = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[EL; HD] THEN
      MATCH_ACCEPT_TAC (SUBS [ASSUME `j = 0`] (ASSUME `ids_byte_at st j = 0`)));;

let IDS_SCAN_INCR_TAC =
  REWRITE_TAC[ids_scan_inv] THEN IDS_SCAN_STATES_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[IDS_LOW_DIGIT; IDS_SCAN_BYTE_LT] THEN
  REWRITE_TAC[GSYM ADD1; LEB_SCALE_STEP; GSYM WORD_ADD; GSYM WORD_MUL; LEB_DEC_SEQ_SUC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
  TRY(X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[] THEN
      TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let IDS_SCAN_REFUSE_TAC = REWRITE_TAC[ids_scan_bad] THEN IDS_SCAN_STATES_TAC;;

let IDS_SCAN_SHORT_TAC =
  SUBGOAL_THEN `ids_available st = j` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  IDS_SCAN_REFUSE_TAC THEN REWRITE_TAC[ids_input] THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(SPECL [`ids_byte_at st`; `j:num`] LEB_SEQ_SHORT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IDS_SCAN_BYTE_LT] THEN ASM_ARITH_TAC; SIMP_TAC[]];;

let IDS_SCAN_ADDRESS_TAC =
  SUBGOAL_THEN `F` CONTR_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
     is_neg(concl th) && fst(strip_comb(dest_neg(concl th))) = `tisa_inside`)) THEN
  ASM_SIMP_TAC[tisa_inside; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_MUL;
               GSYM INT_OF_NUM_ADD; INT_OF_NUM_LE; EXP; MULT_CLAUSES; ADD_CLAUSES] THEN
  UNDISCH_TAC `j < ids_available st` THEN REWRITE_TAC[ids_available] THEN ASM_ARITH_TAC;;

let IDS_NEXT_LEB_BYTE_WP = prove
 (`!st j s.
     val(tregs st 6) <= val(tisa_len st 0) /\
     val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64 /\
     j < 9 /\ ids_scan_inv st j s
     ==> tisa_wp ids_next_leb_byte
        (\u. ids_scan_finished st u \/ ids_scan_inv st (j + 1) u)
        (ids_scan_bad st) (tisa_setreg 9 (word j) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ids_scan_inv]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ids_scan_view]) THEN
  MP_TAC(SPECL [`s:tisa_state`; `st:tisa_state`] TISA_SAME_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (tisa_len st 0) (tregs st 6)) = ids_available st` ASSUME_TAC THENL
   [REWRITE_TAC[ids_available] THEN MATCH_MP_TAC TISA_VAL_SUB_EXACT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add (tisa_base st 0) (word (1 * val(tregs st 6))):int64) =
                 val(tisa_base st 0) + val(tregs st 6)` ASSUME_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES] THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `j < ids_available st
    ==> val(word_add (tisa_base st 0) (word(1 * val(tregs st 6) + 1 * val(word j:int64))):int64) =
        val(tisa_base st 0) + val(tregs st 6) + j` ASSUME_TAC THENL
   [REWRITE_TAC[ids_available] THEN STRIP_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; GSYM ADD_ASSOC] THEN
    MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ids_next_leb_byte] THEN TISA_VCG_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word j:int64) = j`;
     ASSUME `val(word_sub (tisa_len st 0) (tregs st 6)) = ids_available st`]) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; IDS_SCAN_BYTE_READ; IDS_SCAN_WORD_BYTE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IDS_SCAN_BYTE_READ; IDS_SCAN_WORD_BYTE; GSYM VAL_EQ_0]) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word j:int64) = j`]) THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `F` CONTR_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `j = 0`; list_of_seq; leb_dec; VAL_WORD_0]) THEN ASM_ARITH_TAC;
    DISJ1_TAC THEN IDS_SCAN_ZERO_TAC;
    IDS_SCAN_REFUSE_TAC THEN IDS_SCAN_VERDICT_TAC LEB_SEQ_NONMINIMAL [`j:num`];
    IDS_SCAN_DEC_TAC THEN IDS_SCAN_REFUSE_TAC THEN IDS_SCAN_VERDICT_TAC LEB_SEQ_TOO_BIG [`j:num`];
    IDS_SCAN_DEC_TAC THEN DISJ1_TAC THEN IDS_SCAN_ACCEPT_TAC;
    DISJ2_TAC THEN IDS_SCAN_INCR_TAC;
    IDS_SCAN_ADDRESS_TAC;
    IDS_SCAN_ADDRESS_TAC;
    IDS_SCAN_SHORT_TAC] THEN
  REWRITE_TAC[ASSUME `val(word j:int64) = j`; TISA_WORD_ADD_VAL; ADD1]);;
needs "native/hol/tisa_wp_early.ml";;

let ids_scan_ended = new_definition
 `ids_scan_ended st s <=>
    ids_scan_finished st s \/
    ids_scan_view st s /\ tregs s 5 = word 1 /\ (!v. ~leb_fires (ids_input st) v)`;;

let IDS_NEXT_LEB_LATCH = prove
 (`!st j u.
      (ids_scan_finished st u \/ ids_scan_inv st (j + 1) u)
      ==> (~tisa_bool(tregs u 5) ==> ids_scan_bad st 3 (tisa_failst 3 u)) /\
          (tisa_bool(tregs u 5) /\ tregs u 5 = word 0 ==> ids_scan_ended st u) /\
          (tisa_bool(tregs u 5) /\ ~(tregs u 5 = word 0)
           ==> ids_scan_inv st (j + 1) u)`,
  REPEAT GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ids_scan_finished]);
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ids_scan_inv])] THEN
  ASM_REWRITE_TAC[tisa_bool; VAL_WORD_0; VAL_WORD_1; ids_scan_ended] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let IDS_NEXT_LEB_LOOP_WP = prove
 (`!st s.
     val(tregs st 6) <= val(tisa_len st 0) /\
     val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64 /\
     ids_scan_inv st 0 s
     ==> tisa_wp (TEarlyLoop 9 10 5 9 ids_next_leb_byte)
          (ids_scan_ended st) (ids_scan_bad st) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `tregs s 10 = word 9:int64` ASSUME_TAC THENL
   [ASM_MESON_TAC[ids_scan_inv]; ALL_TAC] THEN
  MATCH_MP_TAC TISA_WP_EARLY_LOOP THEN
  EXISTS_TAC `\N j s. N = 9 /\ ids_scan_inv st j s` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`N:num`; `j:num`; `before:tisa_state`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = 9`)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ids_scan_inv] o check
      (fun th -> fst(strip_comb(concl th)) = `ids_scan_inv`)) THEN
    REWRITE_TAC[TISA_TREGS_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[tisa_bool] THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC TISA_WP_MONO THEN
    MAP_EVERY EXISTS_TAC
     [`\u. ids_scan_finished st u \/ ids_scan_inv st (j + 1) u`; `ids_scan_bad st`] THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `u:tisa_state` THEN
      MATCH_ACCEPT_TAC (REWRITE_RULE[tisa_bool]
        (SPECL [`st:tisa_state`; `j:num`; `u:tisa_state`] IDS_NEXT_LEB_LATCH));
      MATCH_MP_TAC IDS_NEXT_LEB_BYTE_WP THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`N:num`; `before:tisa_state`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = 9`)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ids_scan_inv] o check
      (fun th -> fst(strip_comb(concl th)) = `ids_scan_inv`)) THEN
    REWRITE_TAC[ids_scan_ended] THEN DISJ2_TAC THEN
    REWRITE_TAC[ids_scan_view; TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ids_scan_view]; IDS_SCAN_VERDICT_TAC LEB_SEQ_NINE []]]);;

let IDS_NEXT_LEB_TAIL_WP = prove
 (`!st s. ids_scan_ended st s
    ==> tisa_wp (TIf 5 (TSeq (TInstr (TImm TyU64 11 (word 0))) (TReturn 0 11)) TSkip)
          (ids_scan_finished st) (ids_scan_bad st) s`,
  SUBGOAL_THEN `tisa_bool(word 0:int64) /\ tisa_bool(word 1:int64) /\ ~(word 1:int64 = word 0)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[tisa_bool] THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ids_scan_ended] THEN DISCH_THEN DISJ_CASES_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ids_scan_finished] o check
      (fun th -> fst(strip_comb(concl th)) = `ids_scan_finished`)) THEN
    ASM_REWRITE_TAC[TISA_WP_IF; TISA_WP_SKIP];
    FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ids_scan_view] o check
      (fun th -> fst(strip_comb(concl th)) = `ids_scan_view`)) THEN
    ASM_REWRITE_TAC[TISA_WP_IF] THEN TISA_VCG_TAC THEN IDS_SCAN_REFUSE_TAC]);;

let IDS_NEXT_LEB_WP = prove
 (`!st.
      val(tregs st 6) <= val(tisa_len st 0) /\
      val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64
      ==> tisa_wp ids_next_leb (ids_scan_finished st) (ids_scan_bad st) st`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ids_next_leb] THEN TISA_VCG_TAC THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  MAP_EVERY EXISTS_TAC [`ids_scan_ended st`; `ids_scan_bad st`] THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [BETA_TAC THEN REWRITE_TAC[IDS_NEXT_LEB_TAIL_WP];
    MATCH_MP_TAC IDS_NEXT_LEB_LOOP_WP THEN ASM_REWRITE_TAC[ids_scan_inv; ids_scan_view] THEN
    TISA_STATE_NORM_TAC THEN
    REWRITE_TAC[list_of_seq; leb_dec; EXP; LE_0; LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[]]);;
(* Relate a consumed byte prefix to the readback of the remaining suffix. *)
let IDS_REGION_FROM_CONSUME = prove
 (`!st r off pre rest.
      region_from st r off = APPEND pre rest
      ==> region_from st r (off + LENGTH pre) = rest`,
  REPEAT GEN_TAC THEN REWRITE_TAC[region_from] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:num list->num`) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_APPEND] THEN DISCH_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN CONJ_TAC THENL
   [ASM_ARITH_TAC; X_GEN_TAC `j:num` THEN DISCH_TAC] THEN
  SUBGOAL_THEN `j < LENGTH(rest:num list) /\ LENGTH(pre:num list) + j < val(tisa_len st r) - off /\
                 j < val(tisa_len st r) - (off + LENGTH pre)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `EL (LENGTH (pre:num list) + j):num list->num` o
    check (fun th -> is_eq(concl th) &&
       fst(strip_comb(lhand(concl th))) = `list_of_seq:(num->num)->num->num list`)) THEN
  ASM_SIMP_TAC[EL_APPEND; EL_LIST_OF_SEQ; ARITH_RULE `~(n + j < n) /\ (n + j) - n = j`; ADD_ASSOC]);;

let IDS_NEXT_LEB_REST = prove
 (`!st s.
      val(tregs st 6) <= val(tisa_len st 0) /\ ids_scan_finished st s
      ==> ?v rest. v < 2 EXP 62 /\
           ids_input st = APPEND (leb_enc v) rest /\
           tregs s 7 = word v /\
           val(tregs s 6) = val(tregs st 6) + LENGTH(leb_enc v) /\
           val(tregs s 6) <= val(tisa_len st 0) /\
           region_from s 0 (val(tregs s 6)) = rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ids_scan_finished; ids_scan_view; leb_fires] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:num`
      (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `rest:num list`))
        STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN
   `val(tregs st 6) + LENGTH(leb_enc v) <= val(tisa_len st 0)`
   ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:num list->num` o check
      (fun th -> is_eq(concl th) && lhs(concl th) = `ids_input st`)) THEN
    REWRITE_TAC[ids_input; ids_available; LENGTH_LIST_OF_SEQ; LENGTH_APPEND] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(tregs s 6) = val(tregs st 6) + LENGTH(leb_enc v)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN
    MP_TAC(ISPEC `tisa_len st 0` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`s:tisa_state`; `st:tisa_state`] TISA_SAME_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!off. region_from s 0 off = region_from st 0 off` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[region_from; region_byte]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`v:num`; `rest:num list`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (SPECL [`st:tisa_state`; `0`; `val(tregs st 6)`;
                       `leb_enc v`; `rest:num list`] IDS_REGION_FROM_CONSUME) THEN
  ASM_REWRITE_TAC[GSYM IDS_INPUT_BYTES]);;
needs "native/hol/reader_ids.ml";;

let ids_saved_count = new_definition
 `ids_saved_count st = tisa_read st (word_add (tisa_base st 1) (word 8)) 8`;;

let ids_finish_post = new_definition
 `ids_finish_post st k s <=>
    tregs s 0 = tregs st 0 /\
    if 8 * val(ids_saved_count st) <= val(tisa_len st 2)
    then k = 1 /\
         tmem s = tmem(tisa_finst 1 (ids_saved_count st)
             (tisa_store (tisa_base st 1) 8 (tregs st 6) st))
    else k = 2 /\ tmem s = tmem(tisa_finst 2 (word 0) st)`;;

let IDS_NEXT_STACK_SIZE = prove
 (`!w:int64. val(word_ushr w 3) = val w DIV 8`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_USHR; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `w:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN
  MP_TAC(SPECL [`val(w:int64)`; `8`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let IDS_NEXT_FINISH_WP = prove
 (`!st.
      16 <= val(tisa_len st 1) /\ val(tisa_base st 1) + val(tisa_len st 1) < 2 EXP 64
      ==> tisa_wp ids_next_finish (\s. F) (ids_finish_post st) st`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ids_next_finish] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[ids_finish_post; ids_saved_count] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IDS_NEXT_STACK_SIZE; RD_ID_STACK_FITS]) THEN
  ASM_REWRITE_TAC[] THEN IDS_SCAN_STATES_TAC);;

(* The body following the scalar decoder in the actual inner loop. *)
let ids_next_store_id =
  let rec last_statement term =
    let op,args = strip_comb term in
    if op = `TSeq` then last_statement (el 1 args) else term in
  let loop_body = el 3 (snd(strip_comb(last_statement (rhs(concl ids_next_chunk))))) in
  let opcode,args = strip_comb loop_body in
  if opcode <> `TSeq` || hd args <> `ids_next_leb` then
    failwith "unexpected body in ids_next chunk";
  new_definition(mk_eq(`ids_next_store_id:tisa_stmt`,el 1 args));;

let ids_store_slot = new_definition
 `ids_store_slot st = 2147483648 * val(tregs st 1) + val(tregs st 3)`;;

let ids_store_post = new_definition
 `ids_store_post st s <=>
    tregs s 0 = tregs st 0 /\
    tregs s 1 = tregs st 1 /\ tregs s 2 = tregs st 2 /\
    tregs s 3 = tregs st 3 /\ tregs s 4 = tregs st 4 /\
    tregs s 6 = tregs st 6 /\ tregs s 7 = tregs st 7 /\
    if 8 * val(ids_saved_count st) <= val(tisa_len st 2)
    then tmem s = tmem(tisa_store (word_add (tisa_base st 2) (word(8 * ids_store_slot st)))
                                 8 (tregs st 7) st)
    else tmem s = tmem st`;;

let IDS_SLOT_INDEX_WORD = prove
 (`!st. word_add (word_shl (tregs st 1) 31) (tregs st 3):int64 = word(ids_store_slot st)`,
  GEN_TAC THEN REWRITE_TAC[ids_store_slot] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [GSYM WORD_VAL] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM WORD_VAL] THEN
  REWRITE_TAC[WORD_SHL_WORD; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_SYM]);;

let IDS_NEXT_SLOT_WP = prove
 (`!st.
      16 <= val(tisa_len st 1) /\ val(tisa_base st 1) + val(tisa_len st 1) < 2 EXP 64 /\
      val(tisa_base st 2) + val(tisa_len st 2) < 2 EXP 64 /\
      ids_store_slot st < val(ids_saved_count st) /\ val(ids_saved_count st) < 2 EXP 62
      ==> tisa_wp ids_next_store_id (ids_store_post st) (\k s. F) st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word(ids_store_slot st):int64) = ids_store_slot st` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add (word_shl (tregs st 1) 31) (tregs st 3):int64) = ids_store_slot st`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[IDS_SLOT_INDEX_WORD]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ids_saved_count]) THEN
  REWRITE_TAC[ids_next_store_id] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[ids_store_post; ids_saved_count] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IDS_NEXT_STACK_SIZE; RD_ID_STACK_FITS; MULT_CLAUSES; ADD_CLAUSES]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TISA_TREGS_SETREG; TISA_TREGS_STORE; TISA_TMEM_SETREG; TISA_TMEM_STORE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let IDS_STACK_WORD_WRITE = prove
 (`!st (base:int64) (v:int64) capacity i j.
      val base + capacity < 2 EXP 64 /\ 8 * i + 8 <= capacity /\ 8 * j + 8 <= capacity
      ==> tisa_read (tisa_store (word_add base (word(8 * i))) 8 v st)
                    (word_add base (word(8 * j))) 8 =
          if j = i then v else tisa_read st (word_add base (word(8 * j))) 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add base (word(8 * i)):int64) = val base + 8 * i` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add base (word(8 * j)):int64) = val base + 8 * j` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `j:num = i` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC TISA_READ_STORE_SAME THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* Decode and save the count. *)

let ids_initial_cursor = new_definition
 `ids_initial_cursor st = tisa_read st (tisa_base st 1) 8`;;

let ids_count_input = new_definition
 `ids_count_input st = region_from st 0 (val(ids_initial_cursor st))`;;

let ids_count_good = new_definition
 `ids_count_good st n tail <=>
    n < 2 EXP 62 /\ ids_count_input st = APPEND (leb_enc n) tail /\ n <= LENGTH tail`;;

let ids_count_ready = new_definition
 `ids_count_ready st s <=>
    tregs s 0 = tregs st 0 /\
    ?n tail. ids_count_good st n tail /\
        tregs s 2 = word(n DIV 2147483648 + 1) /\
        val(tregs s 6) = val(ids_initial_cursor st) + LENGTH(leb_enc n) /\
        tmem s = tmem(tisa_store (word_add (tisa_base st 1) (word 8)) 8 (word n) st)`;;

let ids_count_refused = new_definition
 `ids_count_refused st k s <=>
    k = 0 /\ tregs s 0 = tregs st 0 /\
    tmem s = tmem(tisa_finst 0 (word 0) st) /\
    ~(?n tail. ids_count_good st n tail)`;;

let IDS_COUNT_LAYOUT = prove
 (`!st. tisa_entry_ok ids_next st
      ==> val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64 /\
          16 <= val(tisa_len st 1) /\
          val(tisa_base st 1) + val(tisa_len st 1) < 2 EXP 64 /\
          val(tisa_base st 2) + val(tisa_len st 2) < 2 EXP 64`,
  REWRITE_TAC[ids_next; tisa_entry_ok; tisa_decls_ok; tisa_region_ok] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN MESON_TAC[]);;

let IDS_COUNT_WORD = prove
 (`!n. n < 2 EXP 62 ==>
      word_add (word_ushr (word n:int64) 31) (word 1) = word(n DIV 2147483648 + 1)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word n:int64) = n` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[word_ushr; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let IDS_COUNT_EXACT_SUFFIX = prove
 (`!st n tail n' tail'.
      n < 2 EXP 62 /\ ids_count_input st = APPEND (leb_enc n) tail /\ ids_count_good st n' tail'
      ==> n' = n /\ tail' = tail`,
  REWRITE_TAC[ids_count_good] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `leb_fires (ids_count_input st) n' /\ leb_fires (ids_count_input st) n` ASSUME_TAC THENL
   [REWRITE_TAC[leb_fires] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `n':num = n` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[LEB_FIRES_UNIQUE]; ASM_MESON_TAC[RD_ID_PAYLOAD_CANCEL]]);;

let IDS_COUNT_INPUT_VIEW = prove
 (`!st before.
      tregs before 0 = tregs st 0 /\ tmem before = tmem st /\
      tregs before 6 = ids_initial_cursor st
      ==> ids_input before = ids_count_input st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`before:tisa_state`; `st:tisa_state`] TISA_SAME_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IDS_INPUT_BYTES; ids_count_input; region_from; region_byte]);;

let IDS_COUNT_PAST_END = prove
 (`!st. val(tisa_len st 0) < val(ids_initial_cursor st)
        ==> ~(?n tail. ids_count_good st n tail)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `ids_count_input st = []` ASSUME_TAC THENL
   [REWRITE_TAC[ids_count_input; region_from] THEN
    SUBGOAL_THEN `val(tisa_len st 0) - val(ids_initial_cursor st) = 0` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[list_of_seq]];
    ASM_REWRITE_TAC[ids_count_good; NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SYM o check (fun th -> is_eq(concl th) &&
                                            lhs(concl th) = `[]:num list`)) THEN
    REWRITE_TAC[APPEND_EQ_NIL; LEB_ENC_NONEMPTY]]);;

(* The code after decoding the count in the exported image. *)
let ids_count_tail =
  let rec after_decoder term =
    let op,args = strip_comb term in
    if op <> `TSeq` then failwith "the count's scalar decoder is missing";
    if hd args = `ids_next_leb` then el 1 args else after_decoder (el 1 args) in
  new_definition(mk_eq(`ids_count_tail:tisa_stmt`,
    after_decoder (rhs(concl ids_next_count))));;

let IDS_COUNT_TAIL_WP = prove
 (`!st s n tail.
     tisa_entry_ok ids_next st /\
     tregs s 0 = tregs st 0 /\ tmem s = tmem st /\
     n < 2 EXP 62 /\ ids_count_input st = APPEND (leb_enc n) tail /\
     tregs s 7 = word n /\
     val(tregs s 6) = val(ids_initial_cursor st) + LENGTH(leb_enc n) /\
     val(tregs s 6) <= val(tisa_len st 0) /\
     LENGTH tail = val(tisa_len st 0) - val(tregs s 6)
     ==> tisa_wp ids_count_tail (ids_count_ready st) (ids_count_refused st) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_COUNT_LAYOUT) THEN
  MP_TAC(SPECL [`s:tisa_state`; `st:tisa_state`] TISA_SAME_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word n:int64) = n` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (tisa_len st 0) (tregs s 6)) = LENGTH(tail:num list)`
   ASSUME_TAC THENL
   [MP_TAC(SPECL [`tisa_len st 0`; `tregs s 6`] TISA_VAL_SUB_EXACT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ids_count_tail] THEN TISA_VCG_TAC THENL
   [REWRITE_TAC[ids_count_refused] THEN IDS_SCAN_STATES_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `n':num` (X_CHOOSE_TAC `tail':num list`)) THEN
    MP_TAC(SPECL [`st:tisa_state`; `n:num`; `tail:num list`; `n':num`; `tail':num list`]
       IDS_COUNT_EXACT_SUFFIX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `n <= LENGTH(tail:num list)` MP_TAC THENL
     [UNDISCH_TAC `ids_count_good st n' tail'` THEN ASM_REWRITE_TAC[ids_count_good];
      ASM_ARITH_TAC];
    REWRITE_TAC[ids_count_ready] THEN CONJ_TAC THENL
     [IDS_SCAN_STATES_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `tail:num list`] THEN
    REWRITE_TAC[ids_count_good] THEN
    IDS_SCAN_STATES_TAC THEN ASM_SIMP_TAC[IDS_COUNT_WORD] THEN ASM_ARITH_TAC]);;


let IDS_COUNT_DECODE_WP = prove
 (`!st before.
    tisa_entry_ok ids_next st /\
    tregs before 0 = tregs st 0 /\ tmem before = tmem st /\
    tregs before 6 = ids_initial_cursor st /\
    val(ids_initial_cursor st) <= val(tisa_len st 0)
    ==> tisa_wp (TSeq ids_next_leb ids_count_tail)
          (ids_count_ready st) (ids_count_refused st) before`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_COUNT_LAYOUT) THEN
  SUBGOAL_THEN `ids_input before = ids_count_input st` ASSUME_TAC THENL
   [MATCH_MP_TAC IDS_COUNT_INPUT_VIEW THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`before:tisa_state`; `st:tisa_state`] TISA_SAME_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[TISA_WP_SEQ] THEN MATCH_MP_TAC TISA_WP_MONO THEN
  MAP_EVERY EXISTS_TAC [`ids_scan_finished before`; `ids_scan_bad before`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:tisa_state` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`before:tisa_state`; `s:tisa_state`] IDS_NEXT_LEB_REST) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `tail:num list` STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ids_scan_finished; ids_scan_view] o
      check (fun th -> concl th = `ids_scan_finished before s`)) THEN
    SUBGOAL_THEN `tisa_len s 0 = tisa_len st 0` ASSUME_TAC THENL
     [MP_TAC(SPECL [`s:tisa_state`; `st:tisa_state`] TISA_SAME_VIEW) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC IDS_COUNT_TAIL_WP THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `tail:num list`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN `region_from s 0 (val(tregs s 6)) = tail`
      (MP_TAC o AP_TERM `LENGTH:num list->num`) THEN
    ASM_REWRITE_TAC[region_from; LENGTH_LIST_OF_SEQ] THEN MESON_TAC[];
    REWRITE_TAC[ids_scan_bad; ids_count_refused] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [IDS_SCAN_STATES_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[leb_fires]) THEN ASM_MESON_TAC[ids_count_good];
    MATCH_MP_TAC IDS_NEXT_LEB_WP THEN ASM_REWRITE_TAC[]]);;

let IDS_NEXT_COUNT_WP = prove
 (`!st. tisa_entry_ok ids_next st
       ==> tisa_wp ids_next_count (ids_count_ready st) (ids_count_refused st) st`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_COUNT_LAYOUT) THEN
  REWRITE_TAC[ids_next_count; GSYM ids_count_tail] THEN TISA_VCG_TAC THENL
   [REWRITE_TAC[ids_count_refused] THEN IDS_SCAN_STATES_TAC THEN
    MATCH_MP_TAC IDS_COUNT_PAST_END THEN ASM_REWRITE_TAC[ids_initial_cursor];
    MATCH_MP_TAC (REWRITE_RULE[TISA_WP_SEQ] IDS_COUNT_DECODE_WP) THEN
    IDS_SCAN_STATES_TAC THEN REWRITE_TAC[ids_initial_cursor] THEN ASM_ARITH_TAC]);;

(* The canonical prefix and its private buffer. *)

(* A known canonical prefix fixes where checking the remaining IDs resumes. *)
let IDS_PAYLOAD_PREFIX_EXISTS = prove
 (`!prefix n bs rest.
    rd_id_payload (LENGTH prefix) bs prefix rest
    ==> ((?ids tail. rd_id_payload (LENGTH prefix + n) bs ids tail) <=>
         (?ids tail. rd_id_payload n rest ids tail))`,
  LIST_INDUCT_TAC THENL
   [SIMP_TAC[LENGTH; ADD_CLAUSES; RD_ID_PAYLOAD_NIL];
    REWRITE_TAC[LENGTH; ADD_CLAUSES; RD_ID_PAYLOAD_CONS] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `next:num list` STRIP_ASSUME_TAC)) THEN
    MP_TAC(SPECL [`LENGTH(t:num list) + n`; `bs:num list`; `h:num`; `next:num list`]
      RD_ID_PAYLOAD_STEP) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[leb_fires]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let ids_frame_same = new_definition
 `ids_frame_same st s <=>
    tregs s 0 = tregs st 0 /\
    !i. i < 24 ==> tisa_fword s i = tisa_fword st i`;;

let IDS_FRAME_SAME_LAYOUT = prove
 (`!st s. ids_frame_same st s
    ==> tisa_frame s = tisa_frame st /\
        !r. r < 12 ==> tisa_base s r = tisa_base st r /\
                       tisa_len s r = tisa_len st r`,
  SIMP_TAC[ids_frame_same; tisa_frame; tisa_base; tisa_len;
           ARITH_RULE `r < 12 ==> 2 * r < 24 /\ 2 * r + 1 < 24`]);;

let IDS_FRAME_SAME_ENTRY = prove
 (`!st s. tisa_entry_ok ids_next st /\ ids_frame_same st s
    ==> tisa_entry_ok ids_next s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_FRAME_SAME_LAYOUT) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ids_frame_same]) THEN
  UNDISCH_TAC `tisa_entry_ok ids_next st` THEN
  REWRITE_TAC[ids_next; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[ARITH_RULE `0 < 12 /\ 1 < 12 /\ 2 < 12 /\
                                                         20 < 24 /\ 21 < 24`]);;

let IDS_FRAME_SAME_TRANS = prove
 (`!st s u. ids_frame_same st s /\ ids_frame_same s u ==> ids_frame_same st u`,
  SIMP_TAC[ids_frame_same] THEN MESON_TAC[]);;

let IDS_ENTRY_WRITABLE_FRAME = prove
 (`!st r. tisa_entry_ok ids_next st /\ (r = 1 \/ r = 2)
      ==> val(tisa_len st r) = 0 \/
          val(tisa_base st r) + val(tisa_len st r) <= val(tregs st 0) \/
          val(tregs st 0) + 192 <= val(tisa_base st r)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  UNDISCH_TAC `tisa_entry_ok ids_next st` THEN
  REWRITE_TAC[ids_next; tisa_entry_ok; tisa_decls_ok] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fun th ->
    if fst(strip_comb(concl th)) = `tisa_region_ok` then
      MATCH_ACCEPT_TAC(last(CONJUNCTS(CONV_RULE NUM_REDUCE_CONV
        (REWRITE_RULE[tisa_region_ok; tisa_frame] th))))
    else NO_TAC));;

let IDS_FRAME_SAME_STORE = prove
 (`!st a v r.
     tisa_entry_ok ids_next st /\ (r = 1 \/ r = 2) /\
     val(tisa_base st r) <= val a /\ val a + 8 <= val(tisa_base st r) + val(tisa_len st r)
     ==> ids_frame_same st (tisa_store a 8 v st)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN REWRITE_TAC[ids_frame_same; TISA_TREGS_STORE] THEN
  MP_TAC(SPECL [`a:int64`; `8`; `v:int64`; `st:tisa_state`] TISA_STORE_KEEPS_FRAME) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LEAF_ENTRY_FRAME) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_COUNT_LAYOUT) THEN
  MP_TAC(SPECL [`st:tisa_state`; `r:num`] IDS_ENTRY_WRITABLE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  DISJ_CASES_THEN SUBST_ALL_TAC (ASSUME `r = 1 \/ r = 2`) THEN ASM_ARITH_TAC);;

let IDS_ENTRY_REGION_PAIR = prove
 (`!st r q.
     tisa_entry_ok ids_next st /\ (r = 1 \/ r = 2) /\ q < 3 /\ ~(q = r) /\
     0 < val(tisa_len st r) /\ 0 < val(tisa_len st q)
     ==> val(tisa_base st r) + val(tisa_len st r) <= val(tisa_base st q) \/
         val(tisa_base st q) + val(tisa_len st q) <= val(tisa_base st r)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  UNDISCH_TAC `tisa_entry_ok ids_next st` THEN
  REWRITE_TAC[ids_next; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_pair_ok] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ASSUME `r = 1 \/ r = 2`) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `q = 0 \/ q = 1 \/ q = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC;
                                                     ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_ARITH_TAC);;

let IDS_REGION_READ_STORE = prove
 (`!st r a v q off w.
     tisa_entry_ok ids_next st /\ (r = 1 \/ r = 2) /\ q < 3 /\ ~(q = r) /\
     val(tisa_base st r) <= val a /\ val a + 8 <= val(tisa_base st r) + val(tisa_len st r) /\
     0 < w /\ off + w <= val(tisa_len st q)
     ==> tisa_read (tisa_store a 8 v st) (word_add (tisa_base st q) (word off)) w =
         tisa_read st (word_add (tisa_base st q) (word off)) w`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_COUNT_LAYOUT) THEN
  SUBGOAL_THEN `val(tisa_base st q) + val(tisa_len st q) < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ARITH_RULE `q < 3 ==> q = 0 \/ q = 1 \/ q = 2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(a:int64) + 8 <= 2 EXP 64` ASSUME_TAC THENL
   [DISJ_CASES_THEN SUBST_ALL_TAC (ASSUME `r = 1 \/ r = 2`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add (tisa_base st q) (word off):int64) = val(tisa_base st q) + off`
    ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`st:tisa_state`; `r:num`; `q:num`] IDS_ENTRY_REGION_PAIR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC TISA_READ_STORE_APART_W THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let IDS_INPUT_STORE = prove
 (`!st a v r off.
     tisa_entry_ok ids_next st /\ (r = 1 \/ r = 2) /\
     val(tisa_base st r) <= val a /\ val a + 8 <= val(tisa_base st r) + val(tisa_len st r)
     ==> region_from (tisa_store a 8 v st) 0 off = region_from st 0 off`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `ids_frame_same st (tisa_store a 8 v st)` ASSUME_TAC THENL
   [MATCH_MP_TAC IDS_FRAME_SAME_STORE THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_FRAME_SAME_LAYOUT) THEN
  REWRITE_TAC[region_from; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 12`; EL_LIST_OF_SEQ] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[region_byte] THEN ASM_SIMP_TAC[ARITH_RULE `0 < 12`] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC IDS_REGION_READ_STORE THEN
  EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;



let ids_slot = new_definition
 `ids_slot s r j = tisa_read s (word_add (tisa_base s r) (word(8 * j))) 8`;;

let ids_list_view = new_definition
 `ids_list_view st n xs s <=>
    ids_frame_same st s /\
    ids_initial_cursor s = ids_initial_cursor st /\
    ids_saved_count s = word n /\
    (!off. region_from s 0 off = region_from st 0 off) /\
    (8 * n <= val(tisa_len st 2)
     ==> !j. j < LENGTH xs ==> ids_slot s 2 j = word(EL j xs))`;;

let IDS_LIST_VIEW_EQ = prove
 (`!st n xs s u. tregs u 0 = tregs s 0 /\ tmem u = tmem s
    ==> (ids_list_view st n xs u <=> ids_list_view st n xs s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:tisa_state`; `s:tisa_state`] TISA_SAME_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ids_list_view; ids_frame_same; ids_initial_cursor; ids_saved_count;
                  region_from; region_byte; ids_slot]);;

let IDS_LIST_VIEW_ADD = prove
 (`!st n xs s v.
     tisa_entry_ok ids_next st /\ ids_list_view st n xs s /\ LENGTH xs < n
     ==> ids_list_view st n (APPEND xs [v])
           (if 8 * n <= val(tisa_len st 2)
            then tisa_store (word_add (tisa_base s 2) (word(8 * LENGTH xs))) 8 (word v) s
            else s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `8 * n <= val(tisa_len st 2)` THENL
   [ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[ids_list_view]) THEN ASM_REWRITE_TAC[ids_list_view]] THEN
  SUBGOAL_THEN `tisa_entry_ok ids_next s` ASSUME_TAC THENL
   [ASM_MESON_TAC[ids_list_view; IDS_FRAME_SAME_ENTRY]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ids_list_view]) THEN
  FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o
    check (fun th -> is_conj(concl th) && fst(strip_comb(lhand(concl th))) = `ids_frame_same`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_FRAME_SAME_LAYOUT) THEN
  SUBGOAL_THEN `val(tisa_len s 2) = val(tisa_len st 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `2 < 12`]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_COUNT_LAYOUT o
    check (fun th -> concl th = `tisa_entry_ok ids_next s`)) THEN
  ABBREV_TAC `a = word_add (tisa_base s 2) (word(8 * LENGTH(xs:num list))) :int64` THEN
  SUBGOAL_THEN `val(a:int64) = val(tisa_base s 2) + 8 * LENGTH(xs:num list)` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(tisa_base s 2) <= val(a:int64) /\
                val a + 8 <= val(tisa_base s 2) + val(tisa_len s 2)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ids_frame_same s (tisa_store a 8 (word v) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC IDS_FRAME_SAME_STORE THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_FRAME_SAME_LAYOUT o
    check (fun th -> lhand(concl th) = `s:tisa_state`)) THEN
  SUBGOAL_THEN `!off. off + 8 <= val(tisa_len s 1)
                     ==> tisa_read (tisa_store a 8 (word v) s)
                           (word_add (tisa_base s 1) (word off)) 8 =
                         tisa_read s (word_add (tisa_base s 1) (word off)) 8`
    ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC IDS_REGION_READ_STORE THEN
    EXISTS_TAC `2` THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `tisa_base (tisa_store a 8 (word v) s) 1 = tisa_base s 1 /\
     tisa_base (tisa_store a 8 (word v) s) 2 = tisa_base s 2`
   (CONJUNCTS_THEN2 (LABEL_TAC "new_base1") (LABEL_TAC "new_base2")) THENL
   [ASM_SIMP_TAC[ARITH_RULE `1 < 12 /\ 2 < 12`]; ALL_TAC] THEN
  REWRITE_TAC[ids_list_view] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IDS_FRAME_SAME_TRANS THEN EXISTS_TAC `s:tisa_state` THEN ASM_REWRITE_TAC[];
    USE_THEN "new_base1" (fun th -> REWRITE_TAC[ids_initial_cursor; th]) THEN
    MP_TAC(SPEC `0` (ASSUME
      `!off. off + 8 <= val(tisa_len s 1)
             ==> tisa_read (tisa_store a 8 (word v) s)
                           (word_add (tisa_base s 1) (word off)) 8 =
                 tisa_read s (word_add (tisa_base s 1) (word off)) 8`)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD_0] THEN DISCH_THEN SUBST1_TAC] THEN
    MATCH_ACCEPT_TAC(REWRITE_RULE[ids_initial_cursor]
      (ASSUME `ids_initial_cursor s = ids_initial_cursor st`));
    USE_THEN "new_base1" (fun th -> REWRITE_TAC[ids_saved_count; th]) THEN
    MP_TAC(SPEC `8` (ASSUME
      `!off. off + 8 <= val(tisa_len s 1)
             ==> tisa_read (tisa_store a 8 (word v) s)
                           (word_add (tisa_base s 1) (word off)) 8 =
                 tisa_read s (word_add (tisa_base s 1) (word off)) 8`)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MATCH_ACCEPT_TAC(REWRITE_RULE[ids_saved_count] (ASSUME `ids_saved_count s = word n`));
    GEN_TAC THEN MP_TAC(SPECL [`s:tisa_state`; `a:int64`; `word v:int64`; `2`; `off:num`]
      IDS_INPUT_STORE) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `j:num` THEN REWRITE_TAC[LENGTH_APPEND; LENGTH; ARITH_RULE `SUC 0 = 1`] THEN DISCH_TAC THEN
    USE_THEN "new_base2" (fun th -> REWRITE_TAC[ids_slot; th]) THEN EXPAND_TAC "a" THEN
    MP_TAC(SPECL [`s:tisa_state`; `tisa_base s 2`; `word v:int64`; `val(tisa_len s 2)`;
                   `LENGTH(xs:num list)`; `j:num`] IDS_STACK_WORD_WRITE) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_CASES_TAC `j < LENGTH(xs:num list)` THENL
     [ASM_SIMP_TAC[EL_APPEND; ARITH_RULE `j < k ==> ~(j = k)`; GSYM ids_slot];
      SUBGOAL_THEN `j = LENGTH(xs:num list)` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD]]]]);;

let ids_list_inv = new_definition
 `ids_list_inv st n tail j s <=>
    ?xs rest. rd_id_payload j tail xs rest /\
              val(tregs s 6) <= val(tisa_len st 0) /\
              val(tregs s 6) = val(ids_initial_cursor st) + LENGTH(leb_enc n) +
                                 LENGTH(ITLIST APPEND (MAP leb_enc xs) []) /\
              region_from s 0 (val(tregs s 6)) = rest /\
              ids_list_view st n xs s`;;

let ids_list_bad = new_definition
 `ids_list_bad st n tail k s <=>
    k = 0 /\ ~(?xs rest. rd_id_payload n tail xs rest) /\
    tisa_fword s 21 = tisa_fword st 21 /\ ids_initial_cursor s = ids_initial_cursor st`;;

(* The final published result and its frame. *)

let IDS_CURSOR_SLOT = prove
 (`!st. ids_initial_cursor st = ids_slot st 1 0`,
  REWRITE_TAC[ids_initial_cursor; ids_slot; MULT_CLAUSES; WORD_ADD_0]);;

let IDS_FINISH_WORDS = prove
 (`!s u k v.
     tisa_entry_ok ids_next s /\
     tregs u 0 = tregs s 0 /\ tmem u = tmem(tisa_finst k v s)
     ==> tisa_fword u 19 = v /\ tisa_fword u 21 = tisa_fword s 21 /\
         !r j. (r = 1 \/ r = 2) /\ 8 * j + 8 <= val(tisa_len s r)
               ==> ids_slot u r j = ids_slot s r j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LEAF_ENTRY_FRAME) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_COUNT_LAYOUT) THEN
  MP_TAC(SPECL [`u:tisa_state`; `tisa_finst k v s`] TISA_SAME_VIEW) THEN
  ASM_REWRITE_TAC[TISA_TREGS_FINST] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `v:int64`; `s:tisa_state`] TISA_FINST_VIEW) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "read_after_finish")))) THEN
  ASM_SIMP_TAC[ARITH_RULE `19 < 24 /\ 21 < 24 /\ ~(21 = 19) /\ ~(21 = 18)`] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `r < 9` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ids_slot] THEN
  USE_THEN "read_after_finish" MATCH_MP_TAC THEN
  MP_TAC(SPECL [`s:tisa_state`; `r:num`] IDS_ENTRY_WRITABLE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(tisa_base s r) + val(tisa_len s r) < 2 EXP 64` ASSUME_TAC THENL
   [DISJ_CASES_THEN SUBST_ALL_TAC (ASSUME `r = 1 \/ r = 2`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add (tisa_base s r) (word(8 * j))) = val(tisa_base s r) + 8 * j`
    SUBST1_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let IDS_PUBLISH_CURSOR = prove
 (`!s.
     tisa_entry_ok ids_next s
     ==> let u = tisa_store (tisa_base s 1) 8 (tregs s 6) s in
         ids_frame_same s u /\ ids_initial_cursor u = tregs s 6 /\
         (!j. 8 * j + 8 <= val(tisa_len s 2) ==> ids_slot u 2 j = ids_slot s 2 j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_COUNT_LAYOUT) THEN
  SUBGOAL_THEN `val(tisa_base s 1) + 8 <= val(tisa_base s 1) + val(tisa_len s 1)`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ids_frame_same s (tisa_store (tisa_base s 1) 8 (tregs s 6) s)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC IDS_FRAME_SAME_STORE THEN EXISTS_TAC `1` THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_FRAME_SAME_LAYOUT) THEN
  ASM_SIMP_TAC[ids_initial_cursor; ids_slot; ARITH_RULE `1 < 12 /\ 2 < 12`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC TISA_READ_STORE_SAME THEN ASM_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC IDS_REGION_READ_STORE THEN EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC[LE_REFL] THEN CONV_TAC NUM_REDUCE_CONV]);;



(* Refusals keep the caller's cursor and the fuel receipt. *)
let IDS_FINISH_KEEP = prove
 (`!s u k v. tisa_entry_ok ids_next s /\
      tregs u 0 = tregs s 0 /\ tmem u = tmem(tisa_finst k v s)
      ==> tisa_fword u 21 = tisa_fword s 21 /\ ids_initial_cursor u = ids_initial_cursor s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_COUNT_LAYOUT) THEN
  MP_TAC(SPECL [`s:tisa_state`; `u:tisa_state`; `k:num`; `v:int64`] IDS_FINISH_WORDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IDS_CURSOR_SLOT] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`1`; `0`]) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    REWRITE_TAC[]]);;

let ids_loads = new_definition
 `ids_loads st xs rest <=>
    ?n tail. ids_count_good st n tail /\ rd_id_payload n tail xs rest`;;

let ids_next_post = new_definition
 `ids_next_post st k u <=>
    tisa_fword u 21 = tisa_fword st 21 /\
    ((k = 0 /\ ~(?xs rest. ids_loads st xs rest) /\ ids_initial_cursor u = ids_initial_cursor st) \/
     (?xs rest. ids_loads st xs rest /\
      if 8 * LENGTH xs <= val(tisa_len st 2)
      then k = 1 /\ tisa_fword u 19 = word(LENGTH xs) /\
           (!j. j < LENGTH xs ==> ids_slot u 2 j = word(EL j xs)) /\
           ids_initial_cursor u =
             word(val(ids_initial_cursor st) + LENGTH(leb_enc(LENGTH xs)) +
                  LENGTH(ITLIST APPEND (MAP leb_enc xs) []))
      else k = 2 /\ ids_initial_cursor u = ids_initial_cursor st))`;;

let IDS_FINAL_LIST_WP = prove
 (`!st n tail s. tisa_entry_ok ids_next st /\ ids_count_good st n tail /\
                  ids_list_inv st n tail n s
     ==> tisa_wp ids_next_finish (\u. F) (ids_next_post st) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ids_list_inv] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `xs:num list` (X_CHOOSE_THEN `rest:num list` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `ids_loads st xs rest /\ LENGTH(xs:num list) = n /\ n < 2 EXP 62`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [REWRITE_TAC[ids_loads] THEN ASM_MESON_TAC[];
     ASM_MESON_TAC[ids_count_good; rd_id_payload]];
    ALL_TAC] THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[ids_list_view] (ASSUME `ids_list_view st n xs s`)) THEN
  STRIP_ASSUME_TAC(MATCH_MP IDS_FRAME_SAME_LAYOUT (ASSUME `ids_frame_same st s`)) THEN
  SUBGOAL_THEN `tisa_entry_ok ids_next s /\ tisa_fword s 21 = tisa_fword st 21`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IDS_FRAME_SAME_ENTRY; ids_frame_same; ARITH_RULE `21 < 24`]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_COUNT_LAYOUT o
    check (fun th -> concl th = `tisa_entry_ok ids_next s`)) THEN
  SUBGOAL_THEN `val(word n:int64) = n` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  MAP_EVERY EXISTS_TAC [`\u:tisa_state. F`; `ids_finish_post s`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `u:tisa_state`] THEN
    REWRITE_TAC[ids_finish_post] THEN ASM_SIMP_TAC[ARITH_RULE `2 < 12`] THEN
    ASM_CASES_TAC `8 * n <= val(tisa_len st 2)` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [ABBREV_TAC `published = tisa_store (tisa_base s 1) 8 (tregs s 6) s` THEN
      MP_TAC(SPEC `s:tisa_state` IDS_PUBLISH_CURSOR) THEN
      ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "published_slots"))) THEN
      SUBGOAL_THEN `tisa_entry_ok ids_next published /\ tisa_fword published 21 = tisa_fword s 21 /\
                    tregs published 0 = tregs s 0` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[IDS_FRAME_SAME_ENTRY; ids_frame_same; ARITH_RULE `21 < 24`]; ALL_TAC] THEN
      STRIP_ASSUME_TAC(MATCH_MP IDS_FRAME_SAME_LAYOUT (ASSUME `ids_frame_same s published`)) THEN
      MP_TAC(SPECL [`published:tisa_state`; `u:tisa_state`; `1`; `word n:int64`] IDS_FINISH_WORDS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "result_slots"))) THEN
      REWRITE_TAC[ids_next_post] THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`xs:num list`; `rest:num list`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `8 * j + 8 <= val(tisa_len s 2)` ASSUME_TAC THENL
         [ASM_SIMP_TAC[ARITH_RULE `2 < 12`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "result_slots" (MP_TAC o SPECL [`2`; `j:num`]) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC[ARITH_RULE `2 < 12`] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        USE_THEN "published_slots" (MP_TAC o SPEC `j:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        MP_TAC(SPEC `j:num` (MP
          (ASSUME `8 * n <= val(tisa_len st 2)
                   ==> !i. i < LENGTH xs ==> ids_slot s 2 i = word(EL i xs)`)
          (ASSUME `8 * n <= val(tisa_len st 2)`))) THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `ids_initial_cursor u = ids_initial_cursor published` SUBST1_TAC THENL
         [MP_TAC(SPECL [`published:tisa_state`; `u:tisa_state`; `1`; `word n:int64`] IDS_FINISH_KEEP) THEN
          ASM_REWRITE_TAC[] THEN SIMP_TAC[];
          ASM_REWRITE_TAC[] THEN
          MP_TAC(AP_TERM `word:num->int64`
            (ASSUME `val(tregs s 6) = val(ids_initial_cursor st) + LENGTH(leb_enc n) +
                                      LENGTH(ITLIST APPEND (MAP leb_enc xs) [])`)) THEN
          REWRITE_TAC[WORD_VAL]]];
      MP_TAC(SPECL [`s:tisa_state`; `u:tisa_state`; `2`; `word 0:int64`] IDS_FINISH_KEEP) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[ids_next_post] THEN
      ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`xs:num list`; `rest:num list`] THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC IDS_NEXT_FINISH_WP THEN ASM_REWRITE_TAC[]]);;

(* Establish the invariant and process one ID. *)

let IDS_LIST_PREPARED = prove
 (`!st n. tisa_entry_ok ids_next st
     ==> ids_list_view st n []
           (tisa_store (word_add (tisa_base st 1) (word 8)) 8 (word n) st)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_COUNT_LAYOUT) THEN
  ABBREV_TAC `a = word_add (tisa_base st 1) (word 8):int64` THEN
  SUBGOAL_THEN `val(a:int64) = val(tisa_base st 1) + 8` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(tisa_base st 1) <= val(a:int64) /\
                val a + 8 <= val(tisa_base st 1) + val(tisa_len st 1)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ids_frame_same st (tisa_store a 8 (word n) st)` ASSUME_TAC THENL
   [MATCH_MP_TAC IDS_FRAME_SAME_STORE THEN EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_FRAME_SAME_LAYOUT) THEN
  REWRITE_TAC[ids_list_view; LENGTH; LT; ids_initial_cursor; ids_saved_count] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 < 12`] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC TISA_READ_STORE_SAME THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    GEN_TAC THEN MATCH_MP_TAC IDS_INPUT_STORE THEN EXISTS_TAC `1` THEN ASM_REWRITE_TAC[]]);;

let IDS_LIST_BEGIN = prove
 (`!st s. tisa_entry_ok ids_next st /\ ids_count_ready st s
     ==> ?n tail. ids_count_good st n tail /\
                   val(tregs s 2) = n DIV 2147483648 + 1 /\
                   ids_list_inv st n tail 0 s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ids_count_ready] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num`
      (X_CHOOSE_THEN `tail:num list` STRIP_ASSUME_TAC)))) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[ids_count_good] (ASSUME `ids_count_good st n tail`)) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `tail:num list`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN
    MP_TAC(SPEC `n:num` RD_ID_CHUNK_COUNT) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `prepared = tisa_store (word_add (tisa_base st 1) (word 8)) 8 (word n) st` THEN
  SUBGOAL_THEN `tregs s 0 = tregs prepared 0 /\ tmem s = tmem prepared` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "prepared" THEN ASM_REWRITE_TAC[TISA_TREGS_STORE]; ALL_TAC] THEN
  SUBGOAL_THEN `ids_list_view st n [] prepared` ASSUME_TAC THENL
   [EXPAND_TAC "prepared" THEN ASM_SIMP_TAC[IDS_LIST_PREPARED]; ALL_TAC] THEN
  SUBGOAL_THEN `ids_list_view st n [] s` ASSUME_TAC THENL
   [(let view = SPECL [`st:tisa_state`; `n:num`; `[]:num list`; `prepared:tisa_state`;
                       `s:tisa_state`] IDS_LIST_VIEW_EQ in
     let same = CONJ (ASSUME `tregs s 0 = tregs prepared 0`) (ASSUME `tmem s = tmem prepared`) in
     ACCEPT_TAC(EQ_MP (SYM(MP view same)) (ASSUME `ids_list_view st n [] prepared`)));
    ALL_TAC] THEN
  SUBGOAL_THEN `val(ids_initial_cursor st) + LENGTH(leb_enc n) <= val(tisa_len st 0)`
    ASSUME_TAC THENL
   [UNDISCH_THEN `ids_count_input st = APPEND (leb_enc n) tail`
      (MP_TAC o AP_TERM `LENGTH:num list->num`) THEN
    REWRITE_TAC[ids_count_input; region_from; LENGTH_LIST_OF_SEQ; LENGTH_APPEND] THEN
    MP_TAC(SPEC `n:num` LEB_ENC_LENGTH_POS) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ids_list_inv] THEN MAP_EVERY EXISTS_TAC [`[]:num list`; `tail:num list`] THEN
  ASM_REWRITE_TAC[RD_ID_PAYLOAD_NIL; MAP; ITLIST; LENGTH; ADD_CLAUSES] THEN
  SUBGOAL_THEN `!off. region_from s 0 off = region_from st 0 off` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[ids_list_view];
    MATCH_MP_TAC IDS_REGION_FROM_CONSUME THEN
    ASM_REWRITE_TAC[GSYM ids_count_input] THEN ASM_ARITH_TAC]);;

let IDS_LIST_SLOT_POST = prove
 (`!st n xs s v u.
    tisa_entry_ok ids_next st /\ ids_list_view st n xs s /\ n < 2 EXP 62 /\ LENGTH xs < n /\
    ids_store_slot s = LENGTH xs /\ tregs s 7 = word v /\ ids_store_post s u
    ==> ids_list_view st n (APPEND xs [v]) u /\ tregs u 6 = tregs s 6`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o REWRITE_RULE[ids_list_view] o
    check (fun th -> fst(strip_comb(concl th)) = `ids_list_view`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_FRAME_SAME_LAYOUT) THEN
  SUBGOAL_THEN `val(word n:int64) = n` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `next = if 8 * n <= val(tisa_len st 2)
                then tisa_store (word_add (tisa_base s 2) (word(8 * LENGTH(xs:num list)))) 8 (word v) s
                else s` THEN
  SUBGOAL_THEN `ids_list_view st n (APPEND xs [v]) next` ASSUME_TAC THENL
   [EXPAND_TAC "next" THEN MATCH_MP_TAC IDS_LIST_VIEW_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `tregs u 0 = tregs next 0 /\ tregs u 6 = tregs s 6 /\ tmem u = tmem next`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
      (fun th -> is_eq(concl th) && rand(concl th) = `next:tisa_state`)) THEN
    UNDISCH_TAC `ids_store_post s u` THEN
    ASM_SIMP_TAC[ids_store_post; ARITH_RULE `2 < 12`] THEN
    ASM_CASES_TAC `8 * n <= val(tisa_len st 2)` THEN
    ASM_REWRITE_TAC[TISA_TREGS_STORE] THEN SIMP_TAC[];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`st:tisa_state`; `n:num`; `APPEND xs [v]:num list`; `next:tisa_state`;
                   `u:tisa_state`] IDS_LIST_VIEW_EQ) THEN ASM_REWRITE_TAC[]]);;

let IDS_NEXT_ID_WP = prove
 (`!st n tail j before.
    tisa_entry_ok ids_next st /\ n < 2 EXP 62 /\ j < n /\
    ids_list_inv st n tail j before /\ ids_store_slot before = j
    ==> tisa_wp (TSeq ids_next_leb ids_next_store_id)
                 (\u. tregs u 1 = tregs before 1 /\ ids_list_inv st n tail (j + 1) u)
                 (ids_list_bad st n tail) before`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ids_list_inv] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `xs:num list` (X_CHOOSE_THEN `rest:num list` STRIP_ASSUME_TAC)) ASSUME_TAC)))) THEN
  SUBGOAL_THEN `LENGTH(xs:num list) = j` ASSUME_TAC THENL
   [ASM_MESON_TAC[rd_id_payload]; ALL_TAC] THEN
  SUBGOAL_THEN `tisa_entry_ok ids_next before` ASSUME_TAC THENL
   [ASM_MESON_TAC[ids_list_view; IDS_FRAME_SAME_ENTRY]; ALL_TAC] THEN
  SUBGOAL_THEN `tisa_len before 0 = tisa_len st 0` ASSUME_TAC THENL
   [ASM_MESON_TAC[ids_list_view; IDS_FRAME_SAME_LAYOUT; ARITH_RULE `0 < 12`]; ALL_TAC] THEN
  SUBGOAL_THEN `ids_input before = rest` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IDS_INPUT_BYTES]; ALL_TAC] THEN
  REWRITE_TAC[TISA_WP_SEQ] THEN MATCH_MP_TAC TISA_WP_MONO THEN
  MAP_EVERY EXISTS_TAC [`ids_scan_finished before`; `ids_scan_bad before`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:tisa_state` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`before:tisa_state`; `s:tisa_state`] IDS_NEXT_LEB_REST) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `v:num` (X_CHOOSE_THEN `next:num list` STRIP_ASSUME_TAC))] THEN
    SUBGOAL_THEN `rest = APPEND (leb_enc v) next` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_THEN `ids_scan_finished before s`
      (STRIP_ASSUME_TAC o REWRITE_RULE[ids_scan_view] o CONJUNCT1 o REWRITE_RULE[ids_scan_finished]) THEN
    SUBGOAL_THEN `ids_list_view st n xs s` ASSUME_TAC THENL
     [MP_TAC(SPECL [`st:tisa_state`; `n:num`; `xs:num list`; `before:tisa_state`; `s:tisa_state`]
       IDS_LIST_VIEW_EQ) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `tisa_entry_ok ids_next s` ASSUME_TAC THENL
     [ASM_MESON_TAC[ids_list_view; IDS_FRAME_SAME_ENTRY]; ALL_TAC] THEN
    SUBGOAL_THEN `ids_store_slot s = j` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[ids_store_slot; GSYM(REWRITE_RULE[ids_store_slot] (ASSUME `ids_store_slot before = j`))];
      ALL_TAC] THEN
    MATCH_MP_TAC TISA_WP_MONO THEN
    MAP_EVERY EXISTS_TAC [`ids_store_post s`; `\(k:num) (u:tisa_state). F`] THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `u:tisa_state` THEN DISCH_TAC THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[ids_store_post]; ALL_TAC] THEN
      MP_TAC(SPECL [`st:tisa_state`; `n:num`; `xs:num list`; `s:tisa_state`;
                     `v:num`; `u:tisa_state`] IDS_LIST_SLOT_POST) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `rd_id_payload (j+1) tail (APPEND xs [v]) next` ASSUME_TAC THENL
       [MATCH_MP_TAC RD_ID_PAYLOAD_PUSH THEN
        REWRITE_TAC[GSYM(ASSUME `rest = APPEND (leb_enc v) next`)] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `region_from u 0 (val(tregs u 6)) = next` ASSUME_TAC THENL
       [SUBGOAL_THEN `!off. region_from u 0 off = region_from s 0 off`
          (fun th -> REWRITE_TAC[th; ASSUME `tregs u 6 = tregs s 6`]) THENL
         [ASM_MESON_TAC[ids_list_view];
          MATCH_ACCEPT_TAC(ASSUME `region_from s 0 (val(tregs s 6)) = next`)];
        ALL_TAC] THEN
      REWRITE_TAC[ids_list_inv] THEN MAP_EVERY EXISTS_TAC [`APPEND xs [v]:num list`; `next:num list`] THEN
      ASSUME_TAC(REWRITE_RULE[ASSUME `tisa_len before 0 = tisa_len st 0`]
        (ASSUME `val(tregs s 6) <= val(tisa_len before 0)`)) THEN
      REWRITE_TAC[ASSUME `region_from u 0 (val(tregs u 6)) = next`] THEN
      ASM_REWRITE_TAC[RD_ID_FLAT_APPEND; LENGTH_APPEND; MAP; ITLIST; APPEND_NIL; ADD_ASSOC] THEN ASM_ARITH_TAC;
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_COUNT_LAYOUT o
        check (fun th -> concl th = `tisa_entry_ok ids_next s`)) THEN
      SUBGOAL_THEN `ids_saved_count s = word n` ASSUME_TAC THENL
       [ASM_MESON_TAC[ids_list_view]; ALL_TAC] THEN
      MATCH_MP_TAC IDS_NEXT_SLOT_WP THEN ASM_SIMP_TAC[TISA_VAL_WORD_EXACT; ARITH_RULE `n < 2 EXP 62 ==> n < 2 EXP 64`]];
    REWRITE_TAC[ids_scan_bad; ids_list_bad] THEN MAP_EVERY X_GEN_TAC [`k:num`; `u:tisa_state`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`xs:num list`; `n-j`; `tail:num list`; `rest:num list`] IDS_PAYLOAD_PREFIX_EXISTS) THEN
      ASM_SIMP_TAC[ARITH_RULE `j < n ==> j + (n-j) = n`] THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `n - j = SUC(n - j - 1)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; MATCH_MP_TAC RD_ID_PAYLOAD_MALFORMED THEN
        ACCEPT_TAC(REWRITE_RULE[ASSUME `ids_input before = rest`]
          (ASSUME `!v. ~leb_fires (ids_input before) v`))];
      MP_TAC(SPECL [`before:tisa_state`; `u:tisa_state`; `0`; `word 0:int64`] IDS_FINISH_KEEP) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[ids_list_view] (ASSUME `ids_list_view st n xs before`)) THEN
      UNDISCH_TAC `ids_frame_same st before` THEN REWRITE_TAC[ids_frame_same] THEN
      ASM_SIMP_TAC[ARITH_RULE `21 < 24`]];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_COUNT_LAYOUT o
      check (fun th -> concl th = `tisa_entry_ok ids_next before`)) THEN
    MATCH_MP_TAC IDS_NEXT_LEB_WP THEN
    REWRITE_TAC[ASSUME `tisa_len before 0 = tisa_len st 0`;
      ASSUME `val(tregs before 6) <= val(tisa_len st 0)`] THEN
    ASM_MESON_TAC[IDS_COUNT_LAYOUT]]);;

(* Traverse the full count in two bounded loops. *)

let IDS_LIST_INV_SAME = prove
 (`!st n tail j s u.
    tregs u 0 = tregs s 0 /\ tregs u 6 = tregs s 6 /\ tmem u = tmem s /\
    ids_list_inv st n tail j s
    ==> ids_list_inv st n tail j u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:tisa_state`; `s:tisa_state`] TISA_SAME_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ids_list_inv st n tail j s` THEN
  REWRITE_TAC[ids_list_inv] THEN ASM_REWRITE_TAC[region_from; region_byte] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:num list` (X_CHOOSE_THEN `rest:num list` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`xs:num list`; `rest:num list`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`st:tisa_state`; `n:num`; `xs:num list`; `s:tisa_state`; `u:tisa_state`]
    IDS_LIST_VIEW_EQ) THEN ASM_REWRITE_TAC[]);;

let IDS_INNER_LOOP_WP = prove
 (`!st n tail q s.
    tisa_entry_ok ids_next st /\ n < 2 EXP 62 /\ 2147483648 * q <= n /\
    tregs s 1 = word q /\
    val(tregs s 4) = MIN 2147483648 (n - 2147483648 * q) /\
    ids_list_inv st n tail (2147483648 * q) s
    ==> tisa_wp (TCountLoop 3 4 2147483648 (TSeq ids_next_leb ids_next_store_id))
          (ids_list_inv st n tail (2147483648 * q + MIN 2147483648 (n - 2147483648 * q)))
          (ids_list_bad st n tail) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(2147483648 < MIN 2147483648 (n - 2147483648 * q))` ASSUME_TAC THENL
   [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC TISA_WP_COUNT_LOOP THEN
  EXISTS_TAC `\N j u.
      N = MIN 2147483648 (n - 2147483648 * q) /\
      tregs u 1 = word q /\ ids_list_inv st n tail (2147483648 * q + j) u` THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`N:num`; `j:num`; `u:tisa_state`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `j < 2147483648 /\ 2147483648 * q + j < n` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `N = MIN 2147483648 (n - 2147483648 * q)` THEN
      REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word q:int64) = q /\ val(word j:int64) = j` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TISA_WP_MONO THEN
    MAP_EVERY EXISTS_TAC
     [`\v. tregs v 1 = tregs (tisa_setreg 3 (word j) u) 1 /\
           ids_list_inv st n tail ((2147483648 * q + j) + 1) v`;
      `ids_list_bad st n tail`] THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[TISA_TREGS_SETREG; ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];
      MATCH_MP_TAC IDS_NEXT_ID_WP THEN ASM_REWRITE_TAC[ids_store_slot; TISA_TREGS_SETREG] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IDS_LIST_INV_SAME THEN EXISTS_TAC `u:tisa_state` THEN
      ASM_REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN CONV_TAC NUM_REDUCE_CONV];
    MAP_EVERY X_GEN_TAC [`N:num`; `u:tisa_state`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IDS_LIST_INV_SAME THEN EXISTS_TAC `u:tisa_state` THEN
    ASM_REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM(ASSUME `N = MIN 2147483648 (n - 2147483648 * q)`)] THEN ASM_REWRITE_TAC[]]);;

let IDS_CHUNK_WORD = prove
 (`!n q. n < 2 EXP 62 /\ 2147483648 * q <= n
     ==> val(word_sub (word n) (word_shl (word q) 31):int64) = n - 2147483648 * q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[WORD_SHL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(word n:int64) = n /\ val(word(2147483648 * q):int64) = 2147483648 * q`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`word n:int64`; `word(2147483648 * q):int64`] TISA_VAL_SUB_EXACT) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let IDS_NEXT_CHUNK_WP = prove
 (`!st n tail q s.
    tisa_entry_ok ids_next st /\ n < 2 EXP 62 /\ q < n DIV 2147483648 + 1 /\
    tregs s 1 = word q /\ ids_list_inv st n tail (MIN n (2147483648 * q)) s
    ==> tisa_wp ids_next_chunk (ids_list_inv st n tail (MIN n (2147483648 * (q + 1))))
                (ids_list_bad st n tail) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `2147483648 * q <= n` ASSUME_TAC THENL
   [ASM_MESON_TAC[RD_ID_CHUNK_START]; ALL_TAC] THEN
  SUBGOAL_THEN `MIN n (2147483648 * q) = 2147483648 * q` ASSUME_TAC THENL
   [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASSUME_TAC(REWRITE_RULE[ASSUME `MIN n (2147483648 * q) = 2147483648 * q`]
    (ASSUME `ids_list_inv st n tail (MIN n (2147483648 * q)) s`)) THEN
  SUBGOAL_THEN `tisa_entry_ok ids_next s /\ ids_saved_count s = word n` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ids_list_inv; ids_list_view; IDS_FRAME_SAME_ENTRY]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IDS_COUNT_LAYOUT o
    check (fun th -> concl th = `tisa_entry_ok ids_next s`)) THEN
  SUBGOAL_THEN `val(word_sub (word n) (word_shl (word q) 31):int64) = n - 2147483648 * q`
    ASSUME_TAC THENL [MATCH_MP_TAC IDS_CHUNK_WORD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `MIN n (2147483648 * (q + 1)) =
                2147483648 * q + MIN 2147483648 (n - 2147483648 * q)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[RD_ID_CHUNK_PREFIX]; ALL_TAC] THEN
  REWRITE_TAC[ids_next_chunk; GSYM ids_next_store_id] THEN
  MP_TAC(REWRITE_RULE[ids_saved_count] (ASSUME `ids_saved_count s = word n`)) THEN
  DISCH_TAC THEN
  TISA_VCG_TAC THEN
  (MATCH_MP_TAC IDS_INNER_LOOP_WP THEN
   ASM_REWRITE_TAC[TISA_TREGS_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
    [LEAF_VAL_NUMERALS_TAC THEN ASM_REWRITE_TAC[MIN] THEN ASM_ARITH_TAC;
     MATCH_MP_TAC IDS_LIST_INV_SAME THEN EXISTS_TAC `s:tisa_state` THEN
     REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]));;

let IDS_LIST_LOOP_WP = prove
 (`!st n tail s.
    tisa_entry_ok ids_next st /\ n < 2 EXP 62 /\
    val(tregs s 2) = n DIV 2147483648 + 1 /\ ids_list_inv st n tail 0 s
    ==> tisa_wp (TCountLoop 1 2 2147483648 ids_next_chunk)
                (ids_list_inv st n tail n) (ids_list_bad st n tail) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n DIV 2147483648 + 1 <= 2147483648` ASSUME_TAC THENL
   [ASM_MESON_TAC[RD_ID_CHUNK_COUNT]; ALL_TAC] THEN
  SUBGOAL_THEN `~(2147483648 < n DIV 2147483648 + 1)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `MIN n 0 = 0` ASSUME_TAC THENL
   [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC TISA_WP_COUNT_LOOP THEN
  EXISTS_TAC `\N j u.
    N = n DIV 2147483648 + 1 /\ ids_list_inv st n tail (MIN n (2147483648 * j)) u` THEN
  ASM_SIMP_TAC[MULT_CLAUSES; ETA_AX] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`N:num`; `j:num`; `u:tisa_state`] THEN STRIP_TAC THEN
    MATCH_MP_TAC IDS_NEXT_CHUNK_WP THEN
    ASM_REWRITE_TAC[TISA_TREGS_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC IDS_LIST_INV_SAME THEN EXISTS_TAC `u:tisa_state` THEN
      ASM_REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN CONV_TAC NUM_REDUCE_CONV];
    MAP_EVERY X_GEN_TAC [`N:num`; `u:tisa_state`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `n <= 2147483648 * N` ASSUME_TAC THENL
     [MP_TAC(SPECL [`n:num`; `2147483648`] DIVISION) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `MIN n (2147483648 * N) = n` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[MIN]; ALL_TAC] THEN
    ASSUME_TAC(REWRITE_RULE[ASSUME `MIN n (2147483648 * N) = n`]
      (ASSUME `ids_list_inv st n tail (MIN n (2147483648 * N)) u`)) THEN
    MATCH_MP_TAC IDS_LIST_INV_SAME THEN EXISTS_TAC `u:tisa_state` THEN
    ASM_REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* Compose the count, both loops, and publication. *)

let IDS_COUNT_BAD_RESULT = prove
 (`!st k u.
     tisa_entry_ok ids_next st /\ ids_count_refused st k u ==> ids_next_post st k u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ids_count_refused] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `u:tisa_state`; `0`; `word 0:int64`] IDS_FINISH_KEEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[ids_next_post] THEN ASM_REWRITE_TAC[] THEN
  DISJ1_TAC THEN ASM_MESON_TAC[ids_loads]);;

let IDS_LIST_BAD_RESULT = prove
 (`!st n tail k u.
     ids_count_good st n tail /\ ids_list_bad st n tail k u ==> ids_next_post st k u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ids_list_bad] THEN STRIP_TAC THEN
  REWRITE_TAC[ids_next_post] THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
  REWRITE_TAC[ids_loads; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`xs:num list`;`rest:num list`;`n':num`;`tail':num list`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`;`n:num`;`tail:num list`;`n':num`;`tail':num list`]
         IDS_COUNT_EXACT_SUFFIX) THEN
  ASM_MESON_TAC[ids_count_good]);;

let IDS_NEXT_ROOT_WP = prove
 (`!st. tisa_entry_ok ids_next st
        ==> tisa_wp (tisa_root ids_next) (\u. F) (ids_next_post st) st`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ids_next; tisa_root; TISA_WP_SEQ] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  MAP_EVERY EXISTS_TAC [`ids_count_ready st`;`ids_count_refused st`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:tisa_state` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`st:tisa_state`;`s:tisa_state`] IDS_LIST_BEGIN) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `tail:num list` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC TISA_WP_MONO THEN
    MAP_EVERY EXISTS_TAC [`ids_list_inv st n tail n`;`ids_list_bad st n tail`] THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `before:tisa_state` THEN DISCH_TAC THEN
      MATCH_MP_TAC(SPECL [`st:tisa_state`;`n:num`;`tail:num list`;`before:tisa_state`]
        IDS_FINAL_LIST_WP) THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`k:num`;`u:tisa_state`] THEN DISCH_TAC THEN
      MATCH_MP_TAC(SPECL [`st:tisa_state`;`n:num`;`tail:num list`;`k:num`;`u:tisa_state`]
        IDS_LIST_BAD_RESULT) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IDS_LIST_LOOP_WP THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ids_count_good]];
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC IDS_COUNT_BAD_RESULT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IDS_NEXT_COUNT_WP THEN ASM_REWRITE_TAC[]]);;

let IDS_NEXT_RUN = prove
 (`!st k u. tisa_entry_ok ids_next st /\ tisa_run ids_next st = TStop k u
            ==> ids_next_post st k u`,
  MESON_TAC[IDS_NEXT_ROOT_WP; LEAF_RUN_BY_WP]);;
