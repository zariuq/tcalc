(* Capture all call operands before the driver's unconditional result write. *)
needs "native/leaves/common/leaf_lib.ml";;
needs "native/leaves/procedure_call/procedure_call_program.ml";;
needs "native/leaves/procedure_call/procedure_call_view.ml";;
needs "native/hol/control_init_words.ml";;

let PROCEDURE_CALL_MARKER_DECLS = prove
 (`tisa_decls procedure_call_marker = [(2,64,8)]`,
  REWRITE_TAC[PROCEDURE_CALL_MARKER_TERM;tisa_decls]);;
let PROCEDURE_CALL_MARKER_LEAF_WF = prove
 (`tisa_leaf_wf procedure_call_marker`,
  LEAF_WF_TAC PROCEDURE_CALL_MARKER_DECLS PROCEDURE_CALL_MARKER_TERM);;

let procedure_request_patch = new_definition
 `procedure_request_patch t =
    ITLIST (\i mem. write (bytes(word_add (tisa_base t 0) (word(8 * i)),8))
                           (val(procedure_request_value t i)) mem)
           (REVERSE(list_of_seq (\i. i) 8)) (tmem t)`;;

let procedure_call_marker_post = new_definition
 `procedure_call_marker_post t k u <=>
    k = 2 /\
    tmem u = tmem(tisa_finst 2 (word 0)
      (TState (tregs t) (procedure_request_patch t)))`;;

let PROCEDURE_CALL_MARKER_ENTRY = prove
 (`!t. tisa_entry_ok procedure_call_marker t
       ==> val(tregs t 0) + 192 <= 2 EXP 64 /\
           val(tisa_base t 0) + val(tisa_len t 0) < 2 EXP 64 /\
           64 <= val(tisa_len t 0) /\
           (val(tisa_base t 0) + val(tisa_len t 0) <= val(tregs t 0) \/
            val(tregs t 0) + 192 <= val(tisa_base t 0))`,
  GEN_TAC THEN REWRITE_TAC[PROCEDURE_CALL_MARKER_TERM;tisa_entry_ok;tisa_decls_ok;
    tisa_pairs_ok;tisa_init_ok;tisa_region_ok;tisa_frame;tisa_base;tisa_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let PROCEDURE_CALL_MARKER_WP = prove
 (`!t. tisa_entry_ok procedure_call_marker t
       ==> tisa_wp (tisa_root procedure_call_marker) (\s. F) (procedure_call_marker_post t) t`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o MATCH_MP PROCEDURE_CALL_MARKER_ENTRY) THEN
  REWRITE_TAC[PROCEDURE_CALL_MARKER_TERM;tisa_root] THEN
  LEAF_FOCUS_TAC TISA_VCG_TAC THEN REWRITE_TAC[procedure_call_marker_post] THEN
  TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[procedure_request_patch] THEN CONV_TAC(DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[REVERSE;APPEND;ITLIST;procedure_request_value] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[tisa_finst;tisa_setfword;tisa_store;tisa_frame;tregs;tmem;TISA_TREGS_SETREG;
              TISA_TMEM_SETREG;TISA_TREGS_STORE;TISA_TMEM_STORE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  LEAF_VAL_NUMERALS_TAC THEN REWRITE_TAC[tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC);;

let PROCEDURE_CALL_MARKER_RUN = prove
 (`!t k u. tisa_entry_ok procedure_call_marker t /\
           tisa_run procedure_call_marker t = TStop k u
       ==> procedure_call_marker_post t k u`,
  MESON_TAC[PROCEDURE_CALL_MARKER_WP;LEAF_RUN_BY_WP]);;

let PROCEDURE_REQUEST_PATCH_WORD = prove
 (`!t j. tisa_entry_ok procedure_call_marker t /\ 8 * j + 8 <= val(tisa_len t 0)
     ==> drv_word (procedure_request_patch t) (word_add (tisa_base t 0) (word(8 * j))) =
         if j < 8 then procedure_request_value t j
         else drv_word (tmem t) (word_add (tisa_base t 0) (word(8 * j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o MATCH_MP PROCEDURE_CALL_MARKER_ENTRY o
    check (fun th -> fst(strip_comb(concl th)) = `tisa_entry_ok`)) THEN
  REWRITE_TAC[procedure_request_patch] THEN
  MATCH_MP_TAC(REWRITE_RULE[CONTROL_INDEX_MEMBER]
    (ISPECL [`REVERSE(list_of_seq (\i:num. i) 8)`;`tisa_base t 0`;
              `procedure_request_value t`;`tmem t`;`val(tisa_len t 0)`;`j:num`]
             CONTROL_WORD_PATCH)) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM ALL_MEM;CONTROL_INDEX_MEMBER] THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let PROCEDURE_CALL_MARKER_WORD = prove
 (`!t k u j. tisa_entry_ok procedure_call_marker t /\
             tisa_run procedure_call_marker t = TStop k u /\ j < 8
     ==> k = 2 /\ drv_word (tmem u) (word_add (tisa_base t 0) (word(8 * j))) =
                   procedure_request_value t j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o MATCH_MP PROCEDURE_CALL_MARKER_ENTRY o
    check (fun th -> fst(strip_comb(concl th)) = `tisa_entry_ok`)) THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] PROCEDURE_CALL_MARKER_RUN) THEN
  ASM_REWRITE_TAC[procedure_call_marker_post] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word_add (tisa_base t 0) (word(8 * j)):int64) = val(tisa_base t 0) + 8 * j`
    ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;ALL_TAC] THEN
  MP_TAC(SPECL [`TState (tregs t) (procedure_request_patch t)`;`2`;`word 0:int64`;
                `word_add (tisa_base t 0) (word(8 * j)):int64`] TISA_READ_FINST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[tregs] THEN ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[tisa_read;drv_word;tmem] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM drv_word] THEN ASM_SIMP_TAC[PROCEDURE_REQUEST_PATCH_WORD;ARITH_RULE `j < 8 /\ 64 <= n ==> 8 * j + 8 <= n`]);;

let PROCEDURE_CALL_MARKER_RECEIPT_WP = prove
 (`!t. tisa_entry_ok procedure_call_marker t
     ==> tisa_wp (tisa_root procedure_call_marker) (\s. F)
          (\k u. tisa_fword u 20 = tisa_fword t 20 /\ tisa_fword u 21 = tisa_fword t 21) t`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o MATCH_MP PROCEDURE_CALL_MARKER_ENTRY) THEN
  REWRITE_TAC[PROCEDURE_CALL_MARKER_TERM;tisa_root] THEN
  LEAF_FOCUS_TAC TISA_VCG_TAC THEN TISA_STATE_NORM_TAC);;

let PROCEDURE_CALL_MARKER_RECEIPT = prove
 (`!t k u. tisa_entry_ok procedure_call_marker t /\ tisa_run procedure_call_marker t = TStop k u
     ==> tisa_fword u 20 = tisa_fword t 20 /\ tisa_fword u 21 = tisa_fword t 21`,
  MESON_TAC[PROCEDURE_CALL_MARKER_RECEIPT_WP;LEAF_RUN_BY_WP]);;

let procedure_call_marker_theorems =
 ["PROCEDURE_CALL_MARKER_DECLS",PROCEDURE_CALL_MARKER_DECLS;
  "PROCEDURE_CALL_MARKER_LEAF_WF",PROCEDURE_CALL_MARKER_LEAF_WF;
  "PROCEDURE_CALL_MARKER_ENTRY",PROCEDURE_CALL_MARKER_ENTRY;
  "PROCEDURE_CALL_MARKER_WP",PROCEDURE_CALL_MARKER_WP;
  "PROCEDURE_CALL_MARKER_RUN",PROCEDURE_CALL_MARKER_RUN;
  "PROCEDURE_REQUEST_PATCH_WORD",PROCEDURE_REQUEST_PATCH_WORD;
  "PROCEDURE_CALL_MARKER_WORD",PROCEDURE_CALL_MARKER_WORD;
  "PROCEDURE_CALL_MARKER_RECEIPT_WP",PROCEDURE_CALL_MARKER_RECEIPT_WP;
  "PROCEDURE_CALL_MARKER_RECEIPT",PROCEDURE_CALL_MARKER_RECEIPT];;
