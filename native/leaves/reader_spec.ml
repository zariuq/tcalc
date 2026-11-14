(* ========================================================================= *)
(* The reader's leaves against their specifications (tcalc/native/hol/      *)
(* plans_leaves.ml, "The reader's leaves"): PL_CUR_SPEC, PL_INC_SPEC,       *)
(* PL_LEB_NEXT_SPEC, PL_AT_END_SPEC, PL_SKIP_SPEC and PL_LE8_NEXT_SPEC, from *)
(* each leaf's run theorem. cur and inc take leaves_spec.ml's bridge as it  *)
(* is. leb_next's post-condition gives the memory after the run as the      *)
(* entry memory with its stores and the frame's status and return words;    *)
(* with the frame register kept (TISA_RUN_KEEPS) the status, the receipt    *)
(* and the cursor read off that memory. skip and le8_next state the cursor  *)
(* they write at the entry state's region 1, whose base the run keeps        *)
(* (TISA_RUN_REGIONS); le8_next's word is its 8 input bytes, little-endian   *)
(* (LE8_REGION_RANGE).                                                       *)
(*                                                                           *)
(* Loaded after leaves_spec.ml.                                              *)
(* ========================================================================= *)

needs "native/leaves/leaves_spec.ml";;
needs "native/leaves/cur/cur.ml";;
needs "native/leaves/leb_next/leb_next.ml";;
needs "native/leaves/inc/inc.ml";;
needs "native/leaves/at_end/at_end.ml";;
needs "native/leaves/skip/skip.ml";;
needs "native/leaves/le8_next/le8_next.ml";;
needs "native/hol/tisa_symex.ml";;

let PL_CUR_SPEC = prove
 (`pl_cur_spec cur`,
  LEAF_BRIDGE_TAC pl_cur_spec CUR_RUN cur_post CUR_LEAF_WF CUR_DECLS);;

let PL_INC_SPEC = prove
 (`pl_inc_spec inc`,
  LEAF_BRIDGE_TAC pl_inc_spec INC_RUN inc_post INC_LEAF_WF INC_DECLS);;

(* Two states with the same frame register and memory have the same frame words. *)
let LEB_NEXT_VIEW = prove
 (`!t u s j. tregs u 0 = tregs s 0 /\ tmem u = tmem s ==> tisa_fword u j = tisa_fword s j`,
  REWRITE_TAC[tisa_fword; tisa_read; tisa_frame] THEN SIMP_TAC[]);;

(* The post's three outcomes, each with u's view equal to the described state's. *)
let LEB_NEXT_BRIDGE_PREP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] LEB_NEXT_RUN) THEN
  MP_TAC(SPECL [`leb_next`; `t:tisa_state`; `k:num`; `u:tisa_state`] TISA_RUN_KEEPS) THEN
  ASM_REWRITE_TAC[LEB_NEXT_LEAF_WF; tisa_keeps; leb_next_post] THEN STRIP_TAC THEN STRIP_TAC;;

(* The status and the receipt: frame words 18 and 21 of the described state. *)
let LEB_NEXT_FRAME_CASE_TAC =
  FIRST_ASSUM(MP_TAC o MATCH_MP LEB_NEXT_ENTRY o check (fun th -> can (find_term ((=) `tisa_entry_ok`)) (concl th))) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `tmem u` then
     let s = rand(rhs(concl th)) in
     SUBGOAL_THEN (mk_conj(mk_eq(`tisa_fword u 18`, list_mk_icomb "tisa_fword" [s; `18`]),
                           mk_eq(`tisa_fword u 21`, list_mk_icomb "tisa_fword" [s; `21`])))
       (fun eqs -> REWRITE_TAC[eqs])
     THENL [CONJ_TAC THEN MATCH_MP_TAC LEB_NEXT_VIEW THEN ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[tisa_finst; TISA_SETFWORD_REGS; TISA_TREGS_STORE] THEN ASM_REWRITE_TAC[];
            ALL_TAC]
   else failwith "no tmem") THEN
  TISA_STATE_NORM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

(* FIRED: the value, the cursor past it. *)
let LEB_NEXT_FIRED_SPEC_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[leb_next_bytes; leb_next_state; MULT_CLAUSES; WORD_ADD_0]) THEN
  REWRITE_TAC[pl_cursor; pl_w; MULT_CLAUSES; WORD_ADD_0] THEN
  DISJ1_TAC THEN EXISTS_TAC `v:num` THEN ASM_REWRITE_TAC[];;

(* REFUSED: no value; the cursor kept (only the frame's words are written). *)
let LEB_NEXT_REFUSED_SPEC_TAC =
  FIRST_ASSUM(MP_TAC o MATCH_MP LEB_NEXT_ENTRY o check (fun th -> can (find_term ((=) `tisa_entry_ok`)) (concl th))) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  DISJ2_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[leb_next_bytes]) THEN
  REWRITE_TAC[pl_cursor; pl_w; MULT_CLAUSES; WORD_ADD_0] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[LEB_FIRES_NOT_SHORT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `tmem u` then
     let s = rand(rhs(concl th)) in
     MP_TAC(SPECL [`u:tisa_state`; s] TISA_SAME_VIEW) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[tisa_finst; TISA_SETFWORD_REGS] THEN ASM_REWRITE_TAC[];
        DISCH_THEN(fun vw -> REWRITE_TAC[vw])]
   else failwith "no tmem") THEN
  TISA_STATE_NORM_TAC;;

let PL_LEB_NEXT_SPEC = prove
 (`pl_leb_next_spec leb_next`,
  REWRITE_TAC[pl_leb_next_spec; pl_leaf_ok; LEB_NEXT_LEAF_WF; LEB_NEXT_DECLS] THEN CONJ_TAC THEN
  LEB_NEXT_BRIDGE_PREP_TAC THENL
   [LEB_NEXT_FRAME_CASE_TAC; LEB_NEXT_FRAME_CASE_TAC; LEB_NEXT_FRAME_CASE_TAC;
    LEB_NEXT_FIRED_SPEC_TAC; LEB_NEXT_REFUSED_SPEC_TAC; LEB_NEXT_REFUSED_SPEC_TAC]);;

(* at_end: the cursor against the input's length. *)
let PL_AT_END_SPEC = prove
 (`pl_at_end_spec at_end`,
  REWRITE_TAC[pl_at_end_spec; pl_leaf_ok; AT_END_LEAF_WF; AT_END_DECLS] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] AT_END_RUN) THEN
  ASM_REWRITE_TAC[at_end_post; pl_cursor; pl_w; MULT_CLAUSES; WORD_ADD_0; VAL_EQ] THEN
  SIMP_TAC[] THEN COND_CASES_TAC THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A leaf's run keeps the base and length of every region it may read.     *)
(* ------------------------------------------------------------------------- *)

let TISA_ENTRY_SEP = prove
 (`!prog t. LENGTH(tisa_decls prog) <= 9 /\ tisa_entry_ok prog t ==> tisa_frame_sep (tisa_decls prog) t`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `prog:tisa_prog` (cases "tisa_prog")) THEN
  REWRITE_TAC[tisa_decls] THEN MESON_TAC[TISA_ENTRY_FRAME_SEP]);;

let TISA_RUN_REGIONS = prove
 (`!prog t k u r.
     tisa_leaf_wf prog /\ tisa_entry_ok prog t /\ tisa_run prog t = TStop k u /\
     tisa_readable (tisa_decls prog) r
     ==> tisa_base u r = tisa_base t r /\ tisa_len u r = tisa_len t r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC TISA_KEEPS_REGIONS THEN
  EXISTS_TAC `tisa_decls prog` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC TISA_ENTRY_SEP THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[tisa_leaf_wf]);
    MATCH_MP_TAC TISA_RUN_KEEPS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]]);;

(* A reader leaf's run keeps the base of region 1, the reader's state. *)
let RD_REGION1_TAC prog wf decls =
  MP_TAC(SPECL [prog; `t:tisa_state`; `k:num`; `u:tisa_state`; `1`] TISA_RUN_REGIONS) THEN
  ASM_REWRITE_TAC[wf; decls; tisa_readable; LENGTH] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[FST] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC;;

(* skip: the cursor advanced, read back from the state region. *)
let PL_SKIP_SPEC = prove
 (`pl_skip_spec skip`,
  REWRITE_TAC[pl_skip_spec; pl_leaf_ok; SKIP_LEAF_WF; SKIP_DECLS] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RD_REGION1_TAC `skip` SKIP_LEAF_WF SKIP_DECLS THEN
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] SKIP_RUN) THEN
  ASM_REWRITE_TAC[skip_post; pl_cursor; pl_w; MULT_CLAUSES; WORD_ADD_0] THEN
  SIMP_TAC[] THEN COND_CASES_TAC THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* le8_next: a word read from memory is its 8 bytes, little-endian.          *)
(* ------------------------------------------------------------------------- *)

(* A read of at most 8 bytes is the number they encode. *)
let TISA_READ_VAL = prove
 (`!st a n. n <= 8 ==> val(tisa_read st a n) = read (bytes(a,n)) (tmem st)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_read] THEN MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP (8 * n)` THEN
  REWRITE_TAC[READ_BYTES_BOUND; LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC);;

(* Byte i of an 8-byte little-endian number. *)
let LE8_BYTE = prove
 (`!(a:int64) m i. i < 8
     ==> (read (bytes(a,8)) m DIV 2 EXP (8 * i)) MOD 256 = read (bytes(word_add a (word i),1)) m`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_BYTES_DIV; ARITH_RULE `256 = 2 EXP (8 * 1)`; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN (8 - i) 1 = 1` SUBST1_TAC THENL
   [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN ASM_ARITH_TAC; REFL_TAC]);;

let LE8_TISA_READ = prove
 (`!st a. le8 (tisa_read st a 8) = list_of_seq (\j. val(tisa_read st (word_add a (word j)) 1)) 8`,
  REPEAT GEN_TAC THEN CONV_TAC(RAND_CONV LIST_OF_SEQ_CONV) THEN
  SIMP_TAC[le8; MAP; TISA_READ_VAL; LE_REFL; ARITH_RULE `1 <= 8`] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  SIMP_TAC[LE8_BYTE; ARITH_RULE `0 < 8 /\ 1 < 8 /\ 2 < 8 /\ 3 < 8 /\ 4 < 8 /\ 5 < 8 /\ 6 < 8 /\ 7 < 8`]);;

let LE8_REGION_RANGE = prove
 (`!t r c. le8 (tisa_read t (word_add (tisa_base t r) (word c)) 8) = region_range t r c 8`,
  REWRITE_TAC[LE8_TISA_READ; region_range; region_byte; WORD_ADD; WORD_ADD_ASSOC]);;

let PL_LE8_NEXT_SPEC = prove
 (`pl_le8_next_spec le8_next`,
  REWRITE_TAC[pl_le8_next_spec; pl_leaf_ok; LE8_NEXT_LEAF_WF; LE8_NEXT_DECLS] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RD_REGION1_TAC `le8_next` LE8_NEXT_LEAF_WF LE8_NEXT_DECLS THEN
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] LE8_NEXT_RUN) THEN
  ASM_REWRITE_TAC[le8_next_post; pl_cursor; pl_w; MULT_CLAUSES; WORD_ADD_0] THEN
  SIMP_TAC[] THEN COND_CASES_TAC THEN SIMP_TAC[LE8_REGION_RANGE]);;

(* Every theorem this file states, for the audits. *)
let reader_spec_theorems =
 ["PL_CUR_SPEC", PL_CUR_SPEC;
  "PL_INC_SPEC", PL_INC_SPEC;
  "LEB_NEXT_VIEW", LEB_NEXT_VIEW;
  "PL_LEB_NEXT_SPEC", PL_LEB_NEXT_SPEC;
  "PL_AT_END_SPEC", PL_AT_END_SPEC;
  "TISA_ENTRY_SEP", TISA_ENTRY_SEP;
  "TISA_RUN_REGIONS", TISA_RUN_REGIONS;
  "PL_SKIP_SPEC", PL_SKIP_SPEC;
  "TISA_READ_VAL", TISA_READ_VAL;
  "LE8_BYTE", LE8_BYTE;
  "LE8_TISA_READ", LE8_TISA_READ;
  "LE8_REGION_RANGE", LE8_REGION_RANGE;
  "PL_LE8_NEXT_SPEC", PL_LE8_NEXT_SPEC];;
