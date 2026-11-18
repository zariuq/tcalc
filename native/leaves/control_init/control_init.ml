(* The entry control initializer, defined from the same text as its image. *)
needs "native/leaves/common/leaf_lib.ml";;
needs "native/leaves/control_init/control_init_program.ml";;

let CONTROL_INIT_DECLS = prove
 (`tisa_decls control_init = [(2,192,8)]`,REWRITE_TAC[CONTROL_INIT_TERM;tisa_decls]);;
let CONTROL_INIT_LEAF_WF = prove
 (`tisa_leaf_wf control_init`,LEAF_WF_TAC CONTROL_INIT_DECLS CONTROL_INIT_TERM);;

let control_init_value = new_definition
 `control_init_value (policy:int64) i =
    if i <= 6 then word i else if i = 7 then policy else
    if i = 22 then word 14695981039346656037 else word 0`;;

let control_init_patch = new_definition
 `control_init_patch (base:int64) policy (m:int64->byte) =
    ITLIST (\i mem. write (bytes(word_add base (word(8 * i)),8))
                           (val(control_init_value policy i)) mem)
           (REVERSE(list_of_seq (\i. i) 24)) m`;;

let control_init_post = new_definition
 `control_init_post t k u <=>
    if val(tisa_fword t 22) <= 2
    then k = 1 /\
         tmem u = tmem(tisa_finst 1 (tisa_fword t 22)
           (TState (tregs t) (control_init_patch (tisa_base t 0) (tisa_fword t 22) (tmem t))))
    else k = 0 /\ tmem u = tmem(tisa_finst 0 (word 0) t)`;;

let CONTROL_INIT_ENTRY = prove
 (`!t. tisa_entry_ok control_init t
       ==> val(tregs t 0) + 192 <= 2 EXP 64 /\
           val(tisa_base t 0) + val(tisa_len t 0) < 2 EXP 64 /\
           192 <= val(tisa_len t 0) /\
           (val(tisa_base t 0) + val(tisa_len t 0) <= val(tregs t 0) \/
            val(tregs t 0) + 192 <= val(tisa_base t 0))`,
  GEN_TAC THEN REWRITE_TAC[CONTROL_INIT_TERM;tisa_entry_ok;tisa_decls_ok;tisa_pairs_ok;
    tisa_init_ok;tisa_region_ok;tisa_frame;tisa_base;tisa_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let CONTROL_INIT_WP = prove
 (`!t. tisa_entry_ok control_init t
       ==> tisa_wp (tisa_root control_init) (\s. F) (control_init_post t) t`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CONTROL_INIT_ENTRY) THEN
  REWRITE_TAC[CONTROL_INIT_TERM;tisa_root] THEN
  LEAF_FOCUS_TAC TISA_VCG_TAC THEN
  REWRITE_TAC[control_init_post] THEN LEAF_VAL_NUMERALS_TAC THEN
  TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[control_init_patch] THEN CONV_TAC(DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[REVERSE;APPEND;ITLIST;control_init_value] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[tisa_finst;tisa_setfword;tisa_store;tisa_frame;tregs;tmem;TISA_TREGS_SETREG;
              TISA_TMEM_SETREG;TISA_TREGS_STORE;TISA_TMEM_STORE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  LEAF_VAL_NUMERALS_TAC THEN REFL_TAC);;

let CONTROL_INIT_RUN = prove
 (`!t k u. tisa_entry_ok control_init t /\ tisa_run control_init t = TStop k u
       ==> control_init_post t k u`,
  MESON_TAC[CONTROL_INIT_WP;LEAF_RUN_BY_WP]);;

let control_init_theorems =
 ["CONTROL_INIT_DECLS",CONTROL_INIT_DECLS;"CONTROL_INIT_LEAF_WF",CONTROL_INIT_LEAF_WF;
  "CONTROL_INIT_ENTRY",CONTROL_INIT_ENTRY;"CONTROL_INIT_WP",CONTROL_INIT_WP;
  "CONTROL_INIT_RUN",CONTROL_INIT_RUN];;
