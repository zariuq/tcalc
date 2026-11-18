(* Functional leaf facts shared by source-level table and reader proofs. *)
needs "native/leaves/common/leaf_lib.ml";;
needs "native/hol/intern16_complete.ml";;
needs "native/hol/intern_name.ml";;
needs "native/hol/reader_fnv.ml";;
needs "native/hol/reader_leb128.ml";;

let INTERN16_DECLS = prove
 (`tisa_decls intern16 = [(2,16,8); (2,8,8); (2,8,8)]`,
  REWRITE_TAC[intern16; tisa_decls]);;

let INTERN16_REGION_KINDS = prove
 (`!r. (tisa_rw (tisa_decls intern16) r <=> r < 3) /\
       (tisa_readable (tisa_decls intern16) r <=> r < 3)`,
  GEN_TAC THEN REWRITE_TAC[INTERN16_DECLS; tisa_rw; tisa_readable; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_CASES_TAC `r < 3` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o
    REWRITE_RULE[ARITH_RULE `r < 3 <=> r = 0 \/ r = 1 \/ r = 2`]) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[FST] THEN CONV_TAC NUM_REDUCE_CONV);;

let INTERN16_LEAF_WF = prove
 (`tisa_leaf_wf intern16`,
  REWRITE_TAC[tisa_leaf_wf; INTERN16_DECLS; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[intern16; intern16_prologue; intern16_body; tisa_root; tisa_inits; ALL;
              tisa_stmt_ok; tisa_instr_ok; REWRITE_RULE[INTERN16_DECLS] INTERN16_REGION_KINDS] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let TISA_READ8_AGREE = prove
 (`!s t (a:int64). (!k. k < 8 ==> tmem t (word_add a (word k)) = tmem s (word_add a (word k)))
                   ==> tisa_read t a 8 = tisa_read s a 8`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_read] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[READ_BYTES_EQ]);;

let INTERN16_SAME_REGIONS = prove
 (`!s t. (!r. r < 3 ==> tisa_base t r = tisa_base s r /\ tisa_len t r = tisa_len s r) /\
         (!r. r < 3 ==> val(tisa_base s r) + val(tisa_len s r) < 2 EXP 64) /\
         8 <= val(tisa_len s 2) /\
         (!r a. r < 3 /\ val(tisa_base s r) <= val a /\ val a < val(tisa_base s r) + val(tisa_len s r)
                ==> tmem t a = tmem s a) /\
         intern_ok s
         ==> intern_ok t /\ intern_count t = intern_count s /\
             (!i. i < 2 * val(intern_count s) ==> intern_word t i = intern_word s i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* bytes at offset off + k of region r, off + 8 <= len r, agree *)
  SUBGOAL_THEN `!r off. r < 3 /\ off + 8 <= val(tisa_len s r)
                      ==> tisa_read t (word_add (tisa_base s r) (word off)) 8 =
                          tisa_read s (word_add (tisa_base s r) (word off)) 8`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_READ8_AGREE THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `2 EXP 64`)) (concl th))) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base s r) (word off):int64) = val(tisa_base s r) + off` ASSUME_TAC THENL
     [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`word_add (tisa_base s r) (word off):int64`; `k:num`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `intern_count t = intern_count s` ASSUME_TAC THENL
   [REWRITE_TAC[intern_count] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`2`; `0`]) THEN ASM_REWRITE_TAC[ARITH; WORD_ADD_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `2` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_base t r`)) (concl th))) THEN
    REWRITE_TAC[ARITH] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < 2 * val(intern_count s) ==> intern_word t i = intern_word s i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[intern_word] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_base t r`)) (concl th))) THEN
    REWRITE_TAC[ARITH] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ARITH] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [intern_ok] o
      check (fun th -> can (find_term ((=) `intern_ok`)) (concl th))) THEN
    UNDISCH_TAC `i < 2 * val(intern_count s)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTERN_OK_TRANSFER THEN EXISTS_TAC `s:tisa_state` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_base t r`)) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `1` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_base t r`)) (concl th))) THEN
  REWRITE_TAC[ARITH] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[intern_slots] THEN
  REWRITE_TAC[intern_slot] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ARITH] THEN
  UNDISCH_TAC `val(p:int64) < val(intern_slots s)` THEN REWRITE_TAC[INTERN_SLOTS_VAL] THEN
  ARITH_TAC);;

let FNV_DECLS = prove(`tisa_decls fnv = [(1,0,1)]`, REWRITE_TAC[fnv; tisa_decls]);;

let LEB128_DECLS = prove(`tisa_decls leb128 = [(1,0,1); (2,16,8)]`, REWRITE_TAC[leb128; tisa_decls]);;

let NAME_DECLS = prove
 (`tisa_decls intern_name = [(1,0,1); (2,16,8); (2,1,1); (2,8,8); (2,16,8)]`,
  REWRITE_TAC[intern_name; tisa_decls]);;

let FNV_LEAF_WF = prove (`tisa_leaf_wf fnv`, LEAF_WF_TAC FNV_DECLS FNV_TERM);;
let LEB128_LEAF_WF = prove (`tisa_leaf_wf leb128`, LEAF_WF_TAC LEB128_DECLS LEB128_TERM);;
let NAME_LEAF_WF = prove (`tisa_leaf_wf intern_name`, LEAF_WF_TAC NAME_DECLS INTERN_NAME_TERM);;

let FNV_STATUS = prove
 (`!t k u. tisa_run fnv t = TStop k u ==> tisa_fword u 18 = word k /\ k < 5`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP TISA_RUN_STATUS) THEN
  REWRITE_TAC[FNV_TERM; tisa_root; tisa_returns] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let NAME_STATUS = prove
 (`!t k u. tisa_run intern_name t = TStop k u ==> tisa_fword u 18 = word k /\ k < 5`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP TISA_RUN_STATUS) THEN
  REWRITE_TAC[INTERN_NAME_TERM; tisa_root; tisa_returns] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;
