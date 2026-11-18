(* ========================================================================= *)
(* The reader's END and header plans over the general relation: their steps *)
(* (at_end, fnv over the input, le8_next; const_next against slot 60,       *)
(* pol_max) on the reader alone and then over any tables and layout apart   *)
(* from the reader's regions, which they keep whatever the outcome; END's   *)
(* and the header's pieces and the composed plans (pl_plan_end,             *)
(* pl_plan_hdr) with tab_rel in place of plan_rel.                          *)
(*                                                                           *)
(* Loaded after reader_tab.ml, reader_end.ml and reader_hdr.ml.             *)
(* ========================================================================= *)

needs "native/hol/header_commit_tab.ml";;

(* ------------------------------------------------------------------------- *)
(* END's reader steps (at_end, fnv over the input, le8_next): their effect  *)
(* on the reader alone, then over the tables, which they keep whatever the   *)
(* outcome.                                                                   *)
(* ------------------------------------------------------------------------- *)

let RD_STEP_AT_END0 = prove
 (`!bw ctl nctl budget cfr st m used t k u inp c.
     rd_rel bw ctl nctl cfr m inp c /\ 48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok at_end t /\ tisa_run at_end t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 17 st) < nctl
     ==> tisa_fword u 21 = used /\
         (if c = LENGTH inp
          then tisa_fword u 18 = word 1 /\ rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DRV_CHILD_RECEIPT) THEN
  SUBGOAL_THEN `val(tisa_len t 0) = LENGTH(inp:num list)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
      STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC PL_AT_END_SPEC THEN REWRITE_TAC[pl_at_end_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `c:num`)) THEN
  MATCH_MP_TAC RD_STEP_RO0 THEN
  MAP_EVERY EXISTS_TAC [`at_end`; `budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[AT_END_LEAF_WF; AT_END_RO]);;

let TAB_STEP_AT_END = prove
 (`!tb L inp bw ctl nctl budget cfr st m used t k u cw (s:S) stk c.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok at_end t /\ tisa_run at_end t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),s,stk) /\
         (if c = LENGTH inp
          then tisa_fword u 18 = word 1 /\ rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_FRAME) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; `inp:num list`; `c:num`]
               RD_STEP_AT_END0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TAB_REL_RO_STEP THEN
  MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `at_end`; `k:num`] THEN
  ASM_REWRITE_TAC[AT_END_LEAF_WF; AT_END_RO]);;

(* fnv over the input: region 0 bound to the input; any range inside it      *)
(* reads the relation's bytes.                                               *)
let RD_CHILD_INP0 = prove
 (`!bw ctl nctl budget cfr st m used t inp c.
     drv_child bw ctl budget cfr st m used t /\ 48 <= val cfr /\
     rd_rel bw ctl nctl cfr m inp c /\ val(EL 1 st) = 54
     ==> tisa_base t 0 = bw 54 /\ tisa_len t 0 = bw 55 /\
         (!off n. off + n <= LENGTH inp
                  ==> region_range t 0 off n = list_of_seq (\j. EL (off + j) inp) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `drv_base`)) (concl th) then
     MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC `0` th)) else failwith "") THEN
  ASM_REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[region_range; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `n':num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[region_byte; tisa_read; READ_BYTES_1] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `drv_in (word_add (bw 54) (word(off + n')):int64) (bw 54) (val(bw 55:int64))` ASSUME_TAC THENL
   [REWRITE_TAC[drv_in] THEN MP_TAC(SPECL [`bw 54:int64`; `off + n':num`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `tmem t (word_add (bw 54) (word(off + n')):int64) = (m:int64->byte) (word_add (bw 54) (word(off + n')))`
    SUBST1_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
      check (fun th -> is_const_app "drv_child" (concl th))) THEN
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `word_add (bw 54) (word(off + n')):int64`]
                 RD_INP_ADDR0) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `val((m:int64->byte) (word_add (bw 54) (word(off + n')))) < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(m:int64->byte) (word_add (bw 54) (word(off + n')))` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let RD_STEP_FNV0 = prove
 (`!bw ctl nctl budget cfr st m used t k u cw inp c.
     rd_rel bw ctl nctl cfr m inp c /\ 48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\
     pl_cwords ctl nctl m cw /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok fnv t /\ tisa_run fnv t = TStop k u /\
     val(EL 1 st) = 54 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         (tisa_fword u 18 = word 1
          ==> cw(val(EL 10 st)) + cw(val(EL 11 st)) <= LENGTH inp /\
              tisa_fword u 19 = fnv1a (word(cw(val(EL 12 st))))
                                  (list_of_seq (\j. EL (cw(val(EL 10 st)) + j) inp) (cw(val(EL 11 st)))) /\
              rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c) /\
         (cw(val(EL 10 st)) + cw(val(EL 11 st)) <= LENGTH inp /\ cw(val(EL 11 st)) <= 4294967295
          ==> tisa_fword u 18 = word 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RD_CHILD_ARGS0_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD_INP0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(tisa_len t 0) = LENGTH(inp:num list)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
      STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* v1 as a word *)
  SUBGOAL_THEN `tregs t 1 = word(cw(val(EL 12 (st:int64 list))))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tregs`)) (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC PL_FNV_SPEC THEN REWRITE_TAC[pl_fnv_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* the three ends: k substituted, so no rewrite touches the payload word *)
  FIRST_X_ASSUM(fun th -> if is_disj(concl th) then
    DISJ_CASES_THEN2 STRIP_ASSUME_TAC (DISJ_CASES_THEN STRIP_ASSUME_TAC) th else failwith "") THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `k:num`)) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[] THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[];
      MATCH_MP_TAC RD_STEP_RO0 THEN
      MAP_EVERY EXISTS_TAC [`fnv`; `budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`] THEN
      ASM_REWRITE_TAC[FNV_LEAF_WF; FNV_RO] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) && can (find_term ((=) `nctl:num`)) (concl th))) THEN
      ARITH_TAC];
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let TAB_STEP_FNV = prove
 (`!tb L inp bw ctl nctl budget cfr st m used t k u cw (s:S) stk c.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok fnv t /\ tisa_run fnv t = TStop k u /\
     val(EL 1 st) = 54 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),s,stk) /\
         (tisa_fword u 18 = word 1
          ==> cw(val(EL 10 st)) + cw(val(EL 11 st)) <= LENGTH inp /\
              tisa_fword u 19 = fnv1a (word(cw(val(EL 12 st))))
                                  (list_of_seq (\j. EL (cw(val(EL 10 st)) + j) inp) (cw(val(EL 11 st)))) /\
              rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c) /\
         (cw(val(EL 10 st)) + cw(val(EL 11 st)) <= LENGTH inp /\ cw(val(EL 11 st)) <= 4294967295
          ==> tisa_fword u 18 = word 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_FRAME) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; `cw:num->num`;
                `inp:num list`; `c:num`] RD_STEP_FNV0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TAB_REL_RO_STEP THEN
  MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `fnv`; `k:num`] THEN
  ASM_REWRITE_TAC[FNV_LEAF_WF; FNV_RO] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

(* le8_next: FIRED with the 8 input bytes at the cursor, little-endian; the  *)
(* cursor advanced by 8.                                                     *)
let RD_STEP_LE8_0 = prove
 (`!bw ctl nctl budget cfr st m used t k u inp c.
     rd_rel bw ctl nctl cfr m inp c /\ 48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok le8_next t /\ tisa_run le8_next t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 17 st) < nctl
     ==> tisa_fword u 21 = used /\
         (if c + 8 <= LENGTH inp
          then tisa_fword u 18 = word 1 /\
               le8 (tisa_fword u 19) = list_of_seq (\j. EL (c + j) inp) 8 /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp (c + 8)
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD_INP0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DRV_CHILD_RECEIPT) THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  SUBGOAL_THEN `val(tisa_len t 0) = LENGTH(inp:num list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC PL_LE8_NEXT_SPEC THEN REWRITE_TAC[pl_le8_next_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* the 8 bytes: the input's, by the relation *)
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* What le8_next keeps: everything outside the state and the payload word. *)
  SUBGOAL_THEN `!a. ~drv_stack cfr a /\ ~drv_in a (bw 58) (val(bw 59)) /\
                    ~drv_in a (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8
                    ==> drv_after ctl st u a = (m:int64->byte) a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RD_LE8_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `used:int64`;
                          `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* rd_rel: the input kept; the cursor advanced by 8. *)
  REWRITE_TAC[rd_rel] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `drv_in (word_add (bw 54) (word i)) (bw 54) (val(bw 55:int64))` ASSUME_TAC THENL
     [REWRITE_TAC[drv_in] THEN MP_TAC(SPECL [`bw 54:int64`; `i:num`] TISA_VAL_OFFSET) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `word_add (bw 54) (word i):int64`]
                 RD_INP_ADDR0) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `drv_after ctl st u (word_add (bw 54) (word i)) = (m:int64->byte) (word_add (bw 54) (word i))`
      SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~drv_in (word_add (bw 54) (word i):int64) ctl (8 * nctl)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC DRV_CTL_WORD_IN THEN EXISTS_TAC `val(EL 17 (st:int64 list))` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    SUBGOAL_THEN `tisa_base u 1 = tisa_base t 1` ASSUME_TAC THENL
     [MP_TAC(SPECL [`le8_next`; `t:tisa_state`; `k:num`; `u:tisa_state`; `1`] TISA_RUN_REGIONS) THEN
      ASM_REWRITE_TAC[LE8_NEXT_LEAF_WF; LE8_NEXT_READABLE] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `drv_word (drv_after ctl st u) (word_add (bw 58) (word 0)) =
                  drv_word (tmem u) (word_add (bw 58) (word 0))` ASSUME_TAC THENL
     [MATCH_MP_TAC DRV_WORD_AREA THEN EXISTS_TAC `val(bw 59:int64)` THEN
      REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `a:int64` THEN DISCH_TAC THEN REWRITE_TAC[drv_after] THEN
      MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN
      MP_TAC(SPECL [`ctl:int64`; `8 * val(EL 17 (st:int64 list))`] TISA_VAL_OFFSET) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] RD_ST_ADDR0) THEN
      ASM_REWRITE_TAC[drv_in] THEN STRIP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[pl_mw; MULT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `drv_word (tmem u) (word_add (bw 58) (word 0)) = pl_w u 1 0` SUBST1_TAC THENL
     [REWRITE_TAC[pl_w; tisa_read; drv_word; MULT_CLAUSES] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

let TAB_STEP_LE8 = prove
 (`!tb L inp bw ctl nctl budget cfr st m used t k u cw (s:S) stk c.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ rd_rel bw ctl nctl cfr m inp c /\ rd_tab_apart L bw /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok le8_next t /\ tisa_run le8_next t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),s,stk) /\
         (if c + 8 <= LENGTH inp
          then tisa_fword u 18 = word 1 /\
               le8 (tisa_fword u 19) = list_of_seq (\j. EL (c + j) inp) 8 /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp (c + 8)
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_FRAME) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; `inp:num list`; `c:num`]
               RD_STEP_LE8_0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TAB_RD_STEP_KEEP THEN
  MAP_EVERY EXISTS_TAC [`budget:int64`; `le8_next`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[LE8_NEXT_LEAF_WF; LE8_NEXT_RW] THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     ACCEPT_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)) ORELSE
     (CONJ_TAC THENL [ACCEPT_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)); ALL_TAC])
     else failwith "") THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* END's plan over the tables (pl_end_a .. pl_end_d, reader_end.ml), piece  *)
(* by piece: the relations after each FIRED piece, the tables kept.          *)
(* ------------------------------------------------------------------------- *)

let TAB_TB = `tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;;

(* A plan step's helpers: the next step's run named; its payload written   *)
(* through; a step that did not FIRE ends the plan with its outcome.         *)
let TAB_NEXT_TAC t k u =
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN t (X_CHOOSE_THEN k (X_CHOOSE_THEN u STRIP_ASSUME_TAC)));;
let TAB_PAYLOAD_TAC u =
  FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = mk_comb(`val:int64->num`,
                             list_mk_comb(`tisa_fword`, [u; `19`]))
                        then RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "TAB_PAYLOAD_TAC");;
let TAB_REFUSED_TAC =
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  ASM_REWRITE_TAC[];;
let TAB_AFTER k u = list_mk_comb(`drv_after`, [`ctl:int64`; k; u]);;

(* a: the header seen; T25 the FNV-1a 64 of the RST bytes before END. *)
let END_A_TAB = prove
 (`!tb L progs bw ctl nctl budget cfr i m used r cw (s:S) stk inp c.
     progs 3 = eqw /\ progs 22 = fnv /\ 25 < nctl /\ cw 22 = val fnv_offset /\
     drv_sem progs bw ctl budget cfr pl_end_a i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> cw 20 = 1 /\ cw 21 <= LENGTH inp /\
              tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r)))
                (pl_set (pl_set cw 24 1) 25 (val(fnv1a fnv_offset (list_of_seq (\j. EL j inp) (cw 21)))),s,stk) /\
              rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cw:num->num) 1 = 1 /\ cw 0 = 0` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "tab_rel" (concl th))) THEN
    REWRITE_TAC[tab_rel] THEN STRIP_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_end_a; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [TAB_TB; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                 `budget:int64`; `cfr:int64`; pl_end_a_st1; `m:int64->byte`; `used:int64`;
                 `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`; `s:S`; `stk:num list`; `c:num`]
                TAB_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(cw:num->num) 20 = 1` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [TAB_PAYLOAD_TAC `u1:tisa_state`; TAB_REFUSED_TAC] THEN
  TAB_NEXT_TAC `t2:tisa_state` `k2:num` `u2:tisa_state` THEN
  MP_TAC(ISPECL [TAB_TB; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                 `budget:int64`; `cfr:int64`; pl_end_a_st2; TAB_AFTER pl_end_a_st1 `u1:tisa_state`; `used:int64`;
                 `t2:tisa_state`; `k2:num`; `u2:tisa_state`; `pl_set cw 24 1`; `s:S`; `stk:num list`; `c:num`]
                TAB_STEP_FNV) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `pl_set cw 24 1 0 = 0 /\ pl_set cw 24 1 21 = (cw:num->num) 21 /\ pl_set cw 24 1 22 = cw 22`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; WORD_VAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  ASM_CASES_TAC `tisa_fword u2 18 = word 1` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `tisa_fword u2 19`)) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[]]);;

(* b: the count at the cursor is CNT. *)
let END_B_TAB = prove
 (`!tb L progs bw ctl nctl budget cfr i m used r cw (s:S) stk inp c.
     progs 3 = eqw /\ rd_progs_ok progs /\ 27 < nctl /\ rd_tab_apart L bw /\
     drv_sem progs bw ctl budget cfr pl_end_b i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> leb_fires (rd_from inp c) (cw 17) /\
              tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r))) (pl_set (pl_set cw 26 (cw 17)) 27 (cw 17),s,stk) /\
              rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + LENGTH(leb_enc (cw 17))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_progs_ok] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_end_b; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [TAB_TB; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                 `budget:int64`; `cfr:int64`; pl_end_b_st1; `m:int64->byte`; `used:int64`;
                 `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`; `s:S`; `stk:num list`; `c:num`]
                TAB_STEP_LEB) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC))) THENL
   [TAB_PAYLOAD_TAC `u1:tisa_state`; TAB_REFUSED_TAC] THEN
  TAB_NEXT_TAC `t2:tisa_state` `k2:num` `u2:tisa_state` THEN
  MP_TAC(ISPECL [TAB_TB; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                 `budget:int64`; `cfr:int64`; pl_end_b_st2; TAB_AFTER pl_end_b_st1 `u1:tisa_state`; `used:int64`;
                 `t2:tisa_state`; `k2:num`; `u2:tisa_state`; `pl_set cw 26 v`; `s:S`; `stk:num list`;
                 `c + LENGTH(leb_enc v)`] TAB_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
  (* the comparison: word 26 is v, word 17 is CNT *)
  SUBGOAL_THEN `pl_set cw 26 v 26 = v /\ pl_set cw 26 v 17 = (cw:num->num) 17` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_CASES_TAC `v = (cw:num->num) 17` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [TAB_PAYLOAD_TAC `u2:tisa_state` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `v = (cw:num->num) 17`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[];
    TAB_REFUSED_TAC]);;

(* c: the 8 bytes at the cursor are T25's, little-endian. *)
let END_C_TAB = prove
 (`!tb L progs bw ctl nctl budget cfr i m used r cw (s:S) stk inp c.
     progs 3 = eqw /\ progs 29 = le8_next /\ 29 < nctl /\ rd_tab_apart L bw /\
     drv_sem progs bw ctl budget cfr pl_end_c i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> c + 8 <= LENGTH inp /\ le8 (word(cw 25)) = list_of_seq (\j. EL (c + j) inp) 8 /\
              tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r))) (pl_set (pl_set cw 28 (cw 25)) 29 (cw 25),s,stk) /\
              rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + 8))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_end_c; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [TAB_TB; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                 `budget:int64`; `cfr:int64`; pl_end_c_st1; `m:int64->byte`; `used:int64`;
                 `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`; `s:S`; `stk:num list`; `c:num`]
                TAB_STEP_LE8) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `c + 8 <= LENGTH(inp:num list)` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ALL_TAC; TAB_REFUSED_TAC] THEN
  TAB_NEXT_TAC `t2:tisa_state` `k2:num` `u2:tisa_state` THEN
  MP_TAC(ISPECL [TAB_TB; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                 `budget:int64`; `cfr:int64`; pl_end_c_st2; TAB_AFTER pl_end_c_st1 `u1:tisa_state`; `used:int64`;
                 `t2:tisa_state`; `k2:num`; `u2:tisa_state`; `pl_set cw 28 (val(tisa_fword u1 19))`; `s:S`;
                 `stk:num list`; `c + 8`] TAB_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `pl_set cw 28 (val(tisa_fword u1 19)) 25 = (cw:num->num) 25 /\
                pl_set cw 28 (val(tisa_fword u1 19)) 28 = val(tisa_fword u1 19)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  (* the checksum is T25 exactly when the 8 bytes read are its *)
  ASM_CASES_TAC `(cw:num->num) 25 = val(tisa_fword u1 19)` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [TAB_PAYLOAD_TAC `u2:tisa_state` THEN
    SUBGOAL_THEN `word((cw:num->num) 25):int64 = tisa_fword u1 19` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(cw:num->num) 25 = val(tisa_fword u1 19)`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[];
    TAB_REFUSED_TAC]);;

(* d: the input ends at the cursor; ENDW := 1. *)
let END_D_TAB = prove
 (`!tb L progs bw ctl nctl budget cfr i m used r cw (s:S) stk inp c.
     progs 3 = eqw /\ progs 30 = at_end /\ 30 < nctl /\
     drv_sem progs bw ctl budget cfr pl_end_d i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> c = LENGTH inp /\
              ?x. tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r))) (pl_set (pl_set cw 30 x) 19 1,s,stk) /\
                  rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cw:num->num) 1 = 1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "tab_rel" (concl th))) THEN
    REWRITE_TAC[tab_rel] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_end_d; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [TAB_TB; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                 `budget:int64`; `cfr:int64`; pl_end_d_st1; `m:int64->byte`; `used:int64`;
                 `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`; `s:S`; `stk:num list`; `c:num`]
                TAB_STEP_AT_END) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  TRY(ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_CASES_TAC `c = LENGTH(inp:num list)` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ALL_TAC; TAB_REFUSED_TAC] THEN
  TAB_NEXT_TAC `t2:tisa_state` `k2:num` `u2:tisa_state` THEN
  MP_TAC(ISPECL [TAB_TB; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                 `budget:int64`; `cfr:int64`; pl_end_d_st2; TAB_AFTER pl_end_d_st1 `u1:tisa_state`; `used:int64`;
                 `t2:tisa_state`; `k2:num`; `u2:tisa_state`; `pl_set cw 30 (val(tisa_fword u1 19))`; `s:S`;
                 `stk:num list`; `LENGTH(inp:num list)`] TAB_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `pl_set cw 30 (val(tisa_fword u1 19)) 1 = 1` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN TAB_PAYLOAD_TAC `u2:tisa_state` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `val(tisa_fword u1 19)` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The END plan over the tables, composed from its pieces.                   *)
(* ------------------------------------------------------------------------- *)

(* The control words of the tab_rel assumption on memory mem. *)
let tab_cw_of mem (asl,w) =
  let th = find (fun th -> is_const_app "tab_rel" (concl th) && el 7 (snd(strip_comb(concl th))) = mem)
                (map snd asl) in
  fst(dest_pair(el 8 (snd(strip_comb(concl th)))));;

(* A piece's run: its theorem at the drv_sem assumption of its plan, the     *)
(* control words and memory the relation holds there, the cursor given.      *)
let TAB_END_APPLY_TAC th plan mem cursor =
  W(fun g -> let cwv = tab_cw_of mem g in
    FIRST_ASSUM(fun dc -> if is_const_app "drv_sem" (concl dc) &&
                             (try el 5 (snd(strip_comb(concl dc))) = plan with _ -> false) then
      let args = snd(strip_comb(concl dc)) in
      MP_TAC(ISPECL [TAB_TB; `L:tabdesc list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                     `budget:int64`; `cfr:int64`; el 6 args; el 7 args; el 8 args; el 9 args; cwv; `s:S`;
                     `stk:num list`; `inp:num list`; cursor] th)
      else failwith "TAB_END_APPLY_TAC")) THEN
  ASM_REWRITE_TAC[] THEN TRY(ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN STRIP_TAC THEN PL_SET_NUM_TAC;;

(* The END record over the tables: a FIRED run had the header, and the input *)
(* from the cursor is the count CNT and the checksum of the bytes before   *)
(* RST, to its end; the relations hold after it with ENDW = 1 (other words *)
(* below 24 kept), the cursor at the input's end.                            *)
let END_TAB = prove
 (`!tb L progs bw ctl nctl budget cfr i m used r cw (s:S) stk inp c.
     progs 3 = eqw /\ progs 22 = fnv /\ rd_progs_ok progs /\ progs 29 = le8_next /\ progs 30 = at_end /\
     30 < nctl /\ cw 22 = val fnv_offset /\ rd_tab_apart L bw /\
     drv_sem progs bw ctl budget cfr pl_plan_end i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> cw 20 = 1 /\ cw 21 <= LENGTH inp /\
              rd_from inp c = APPEND (leb_enc (cw 17))
                                     (le8 (fnv1a fnv_offset (list_of_seq (\j. EL j inp) (cw 21)))) /\
              ?cw'. cw' 19 = 1 /\ (!j. j < 24 /\ ~(j = 19) ==> cw' j = cw j) /\
                    tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r))) (cw',s,stk) /\
                    rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (LENGTH inp))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_plan_end; DRV_SEM_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `ra:int64#num#(int64->byte)#int64` STRIP_ASSUME_TAC) THEN
  (* a: the header seen; T25 the checksum of the bytes before RST *)
  TAB_END_APPLY_TAC END_A_TAB `pl_end_a` `m:int64->byte` `c:num` THEN
  END_PIECE_CASE_TAC `ra:int64#num#(int64->byte)#int64` THEN
  (* b: the count is CNT *)
  END_NEXT_TAC `ra:int64#num#(int64->byte)#int64` `rb:int64#num#(int64->byte)#int64` THEN
  TAB_END_APPLY_TAC END_B_TAB `pl_end_b` `FST(SND(SND(ra:int64#num#(int64->byte)#int64)))` `c:num` THEN
  END_PIECE_CASE_TAC `rb:int64#num#(int64->byte)#int64` THEN
  (* c: the 8 bytes after it are T25's *)
  END_NEXT_TAC `rb:int64#num#(int64->byte)#int64` `rc:int64#num#(int64->byte)#int64` THEN
  TAB_END_APPLY_TAC END_C_TAB `pl_end_c` `FST(SND(SND(rb:int64#num#(int64->byte)#int64)))`
    `c + LENGTH(leb_enc((cw:num->num) 17))` THEN
  END_PIECE_CASE_TAC `rc:int64#num#(int64->byte)#int64` THEN
  (* d: the input ends there; ENDW := 1 *)
  FIRST_ASSUM(fun th -> if concl th = `SND(SND(SND(rc:int64#num#(int64->byte)#int64))) = used`
                        then RULE_ASSUM_TAC(PURE_REWRITE_RULE[th]) else failwith "") THEN
  TAB_END_APPLY_TAC END_D_TAB `pl_end_d` `FST(SND(SND(rc:int64#num#(int64->byte)#int64)))`
    `(c + LENGTH(leb_enc((cw:num->num) 17))) + 8` THEN
  (* the conclusion *)
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    lhand(concl th) = `FST(r:int64#num#(int64->byte)#int64) = word 1`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_VAL]) THEN
  CONJ_TAC THENL
   [(* the bytes from the cursor: the count's encoding, then the checksum's 8 *)
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[leb_fires] o check (fun th -> is_const_app "leb_fires" (concl th))) THEN
    DISCH_THEN(X_CHOOSE_TAC `rest:num list` o CONJUNCT2) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RD_FROM_APPEND) THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN REWRITE_TAC[rd_from] THEN
    SUBGOAL_THEN `LENGTH(inp:num list) - (c + LENGTH(leb_enc((cw:num->num) 17))) = 8` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    (* ENDW set, the other words below 24 kept *)
    W(fun g -> EXISTS_TAC (tab_cw_of `FST(SND(SND(r:int64#num#(int64->byte)#int64)))` g)) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC(TOP_DEPTH_CONV PL_SET_NUM_CONV) THEN REFL_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[pl_set] THEN
      REPEAT(COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN REFL_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) = `LENGTH(inp:num list)` then
        RULE_ASSUM_TAC(PURE_REWRITE_RULE[th]) else failwith "") THEN
      FIRST_ASSUM ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The header's reader steps (const_next against slot 60, pol_max): on the   *)
(* reader alone, then over the tables, which they keep whatever the outcome.*)
(* ------------------------------------------------------------------------- *)

let RD_STEP_CONST_NEXT0 = prove
 (`!bw ctl nctl budget cfr st m used t k u inp c.
     rd_rel bw ctl nctl cfr m inp c /\ 48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\ rd_hdr_rel bw cfr m /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok const_next t /\ tisa_run const_next t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 3 st) = 60 /\ val(EL 17 st) < nctl
     ==> tisa_fword u 21 = used /\
         (if c + LENGTH holr_hdr_const <= LENGTH inp /\
             list_of_seq (\j. EL (c + j) inp) (LENGTH holr_hdr_const) = holr_hdr_const
          then tisa_fword u 18 = word 1 /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp (c + LENGTH holr_hdr_const)
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD_INP0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`] RD_CHILD_HDR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DRV_CHILD_RECEIPT) THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_hdr_rel] o
    check (fun th -> is_const_app "rd_hdr_rel" (concl th))) THEN
  SUBGOAL_THEN `val(tisa_len t 0) = LENGTH(inp:num list)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(tisa_len t 2) = LENGTH holr_hdr_const` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC PL_CONST_NEXT_SPEC THEN REWRITE_TAC[pl_const_next_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  REWRITE_TAC[HOLR_HDR_CONST_CAP] THEN
  ASM_CASES_TAC `c + LENGTH holr_hdr_const <= val((bw:num->int64) 55)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `c + LENGTH holr_hdr_const <= LENGTH(inp:num list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `region_range t 0`)) (concl th)
                        then REWRITE_TAC[MP (SPECL [`c:num`; `LENGTH holr_hdr_const`] th)
                                            (ASSUME `c + LENGTH holr_hdr_const <= LENGTH(inp:num list)`)]
                        else failwith "") THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* What const_next keeps: everything outside the state and the payload word. *)
  SUBGOAL_THEN `!a. ~drv_stack cfr a /\ ~drv_in a (bw 58) (val(bw 59)) /\
                    ~drv_in a (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8
                    ==> drv_after ctl st u a = (m:int64->byte) a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RD_CONST_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `used:int64`;
                          `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* rd_rel: the input kept; the cursor past the constant. *)
  REWRITE_TAC[rd_rel] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `drv_in (word_add (bw 54) (word i)) (bw 54) (val(bw 55:int64))` ASSUME_TAC THENL
     [REWRITE_TAC[drv_in] THEN MP_TAC(SPECL [`bw 54:int64`; `i:num`] TISA_VAL_OFFSET) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `word_add (bw 54) (word i):int64`]
                 RD_INP_ADDR0) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `drv_after ctl st u (word_add (bw 54) (word i)) = (m:int64->byte) (word_add (bw 54) (word i))`
      SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~drv_in (word_add (bw 54) (word i):int64) ctl (8 * nctl)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC DRV_CTL_WORD_IN THEN EXISTS_TAC `val(EL 17 (st:int64 list))` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    SUBGOAL_THEN `tisa_base u 1 = tisa_base t 1` ASSUME_TAC THENL
     [MP_TAC(SPECL [`const_next`; `t:tisa_state`; `k:num`; `u:tisa_state`; `1`] TISA_RUN_REGIONS) THEN
      ASM_REWRITE_TAC[CONST_NEXT_LEAF_WF; CONST_NEXT_READABLE] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `drv_word (drv_after ctl st u) (word_add (bw 58) (word 0)) =
                  drv_word (tmem u) (word_add (bw 58) (word 0))` ASSUME_TAC THENL
     [MATCH_MP_TAC DRV_WORD_AREA THEN EXISTS_TAC `val(bw 59:int64)` THEN
      REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `a:int64` THEN DISCH_TAC THEN REWRITE_TAC[drv_after] THEN
      MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN
      MP_TAC(SPECL [`ctl:int64`; `8 * val(EL 17 (st:int64 list))`] TISA_VAL_OFFSET) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] RD_ST_ADDR0) THEN
      ASM_REWRITE_TAC[drv_in] THEN STRIP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[pl_mw; MULT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `drv_word (tmem u) (word_add (bw 58) (word 0)) = pl_w u 1 0` SUBST1_TAC THENL
     [REWRITE_TAC[pl_w; tisa_read; drv_word; MULT_CLAUSES] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

let TAB_STEP_CONST_NEXT = prove
 (`!tb L inp bw ctl nctl budget cfr st m used t k u cw (s:S) stk c.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ rd_rel bw ctl nctl cfr m inp c /\ rd_tab_apart L bw /\
     rd_hdr_rel bw cfr m /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok const_next t /\ tisa_run const_next t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 3 st) = 60 /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),s,stk) /\
         (if c + LENGTH holr_hdr_const <= LENGTH inp /\
             list_of_seq (\j. EL (c + j) inp) (LENGTH holr_hdr_const) = holr_hdr_const
          then tisa_fword u 18 = word 1 /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp (c + LENGTH holr_hdr_const)
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_FRAME) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; `inp:num list`; `c:num`]
               RD_STEP_CONST_NEXT0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TAB_RD_STEP_KEEP THEN
  MAP_EVERY EXISTS_TAC [`budget:int64`; `const_next`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[CONST_NEXT_LEAF_WF; CONST_NEXT_RW] THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     ACCEPT_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)) ORELSE
     (CONJ_TAC THENL [ACCEPT_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)); ALL_TAC])
     else failwith "") THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let RD_STEP_POL_MAX0 = prove
 (`!bw ctl nctl budget cfr st m used t k u cw inp c.
     rd_rel bw ctl nctl cfr m inp c /\ 48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\
     pl_cwords ctl nctl m cw /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok pol_max t /\ tisa_run pol_max t = TStop k u /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         (if cw(val(EL 11 st)) <= 2
          then tisa_fword u 18 = word 1 /\
               val(tisa_fword u 19) = MAX (cw(val(EL 10 st))) (cw(val(EL 11 st))) /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RD_CHILD_ARGS0_TAC THEN
  MP_TAC PL_POL_MAX_SPEC THEN REWRITE_TAC[pl_pol_max_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `tisa_fword t 22` VAL_BOUND_64) THEN MP_TAC(ISPEC `tisa_fword t 23` VAL_BOUND_64) THEN
    ASM_REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN ARITH_TAC;
    MATCH_MP_TAC RD_STEP_RO0 THEN
    MAP_EVERY EXISTS_TAC [`pol_max`; `budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`] THEN
    ASM_REWRITE_TAC[POL_MAX_LEAF_WF; POL_MAX_DECLS; NO_DECLS_RW] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

let TAB_STEP_POL_MAX = prove
 (`!tb L inp bw ctl nctl budget cfr st m used t k u cw (s:S) stk c.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok pol_max t /\ tisa_run pol_max t = TStop k u /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),s,stk) /\
         (if cw(val(EL 11 st)) <= 2
          then tisa_fword u 18 = word 1 /\
               val(tisa_fword u 19) = MAX (cw(val(EL 10 st))) (cw(val(EL 11 st))) /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_FRAME) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; `cw:num->num`;
                `inp:num list`; `c:num`] RD_STEP_POL_MAX0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TAB_REL_RO_STEP THEN
  MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `pol_max`; `k:num`] THEN
  ASM_REWRITE_TAC[POL_MAX_LEAF_WF; POL_MAX_DECLS; NO_DECLS_RW] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The header plan over the tables (pl_hdr_b .. pl_hdr_g, reader_hdr.ml).    *)
(* ------------------------------------------------------------------------- *)

(* The words 0 and 1 hold 0 and 1. *)
let TAB_HDR_K01_TAC =
  SUBGOAL_THEN `(cw:num->num) 1 = 1 /\ cw 0 = 0` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> is_const_app "tab_rel" (concl th))) THEN
    REWRITE_TAC[tab_rel] THEN STRIP_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC];;

let tab_step_args st m u0 t k u cw c =
  [TAB_TB; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
   `cfr:int64`; st; m; `used:int64`; t; k; u; cw; `s:S`; `stk:num list`; c];;

(* b: the constant at the cursor. *)
let HDR_B_TAB = prove
 (`!tb L progs bw ctl nctl budget cfr i m used r cw (s:S) stk inp c.
     progs 31 = const_next /\ 25 < nctl /\ rd_hdr_rel bw cfr m /\ rd_tab_apart L bw /\
     drv_sem progs bw ctl budget cfr pl_hdr_b i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> c + LENGTH holr_hdr_const <= LENGTH inp /\
              list_of_seq (\j. EL (c + j) inp) (LENGTH holr_hdr_const) = holr_hdr_const /\
              ?x. tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r))) (pl_set cw 25 x,s,stk) /\
                  rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + LENGTH holr_hdr_const))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN HDR_ONE_STEP_TAC pl_hdr_b THEN
  MP_TAC(ISPECL (tab_step_args (pl_st 0 pl_hdr_b) `m:int64->byte` `u0:tisa_state` `t1:tisa_state` `k1:num`
                   `u1:tisa_state` `cw:num->num` `c:num`) TAB_STEP_CONST_NEXT) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  TRY(ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN STRIP_TAC THENL
   [HDR_END_FIRED_TAC THEN EXISTS_TAC `val(tisa_fword u1 19)` THEN ASM_REWRITE_TAC[];
    HDR_END_STOP_TAC]);;

(* a: no header before (HDR 0). *)
let HDR_A_TAB = prove
 (`!tb L progs bw ctl nctl budget cfr i m used r cw (s:S) stk inp c.
     progs 3 = eqw /\ 24 < nctl /\
     drv_sem progs bw ctl budget cfr pl_hdr_a i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> cw 20 = 0 /\
              tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r))) (pl_set cw 24 0,s,stk) /\
              rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN TAB_HDR_K01_TAC THEN HDR_ONE_STEP_TAC pl_hdr_a THEN
  MP_TAC(ISPECL (tab_step_args (pl_st 0 pl_hdr_a) `m:int64->byte` `u0:tisa_state` `t1:tisa_state` `k1:num`
                   `u1:tisa_state` `cw:num->num` `c:num`) TAB_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  TRY(ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN STRIP_TAC THENL
   [TAB_PAYLOAD_TAC `u1:tisa_state` THEN HDR_END_FIRED_TAC THEN
    FIRST_X_ASSUM(fun th -> if concl th = `(cw:num->num) 20 = 0`
      then REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "") THEN ASM_REWRITE_TAC[];
    HDR_END_STOP_TAC]);;

(* g: HDR := 1 (always FIRED). *)
let HDR_G_TAB = prove
 (`!tb L progs bw ctl nctl budget cfr i m used r cw (s:S) stk inp c.
     progs 3 = eqw /\ 24 < nctl /\
     drv_sem progs bw ctl budget cfr pl_hdr_g i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r))) (pl_set cw 20 1,s,stk) /\
              rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN TAB_HDR_K01_TAC THEN HDR_ONE_STEP_TAC pl_hdr_g THEN
  MP_TAC(ISPECL (tab_step_args (pl_st 0 pl_hdr_g) `m:int64->byte` `u0:tisa_state` `t1:tisa_state` `k1:num`
                   `u1:tisa_state` `cw:num->num` `c:num`) TAB_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  TRY(ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC]) THEN
  STRIP_TAC THEN TAB_PAYLOAD_TAC `u1:tisa_state` THEN HDR_END_FIRED_TAC);;

(* The first step of a two-step piece (leb_next): its value v, or the plan    *)
(* stopped REFUSED there.                                                      *)
let TAB_HDR_LEB_FIRST_TAC def =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[def; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL (tab_step_args (pl_st 0 def) `m:int64->byte` `u0:tisa_state` `t1:tisa_state` `k1:num`
                   `u1:tisa_state` `cw:num->num` `c:num`) TAB_STEP_LEB) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  TRY(ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC))) THENL
   [TAB_PAYLOAD_TAC `u1:tisa_state`; HDR_END_STOP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
    STRIP_ASSUME_TAC)));;

let tab_hdr_second_args def =
  tab_step_args (pl_st 1 def) (TAB_AFTER (pl_st 0 def) `u1:tisa_state`) `u0:tisa_state` `t2:tisa_state` `k2:num`
    `u2:tisa_state` `pl_set cw 26 v` `c + LENGTH(leb_enc v)`;;

(* c (k = 1, the version's first number) and d (k = 0, its second, and the  *)
(* flags): the number at the cursor is k.                                    *)
let hdr_v_tab_goal def k =
  let kt = mk_small_numeral k in
  let g = `!tb L progs bw ctl nctl budget cfr i m used r cw (s:S) stk inp c.
     progs 3 = eqw /\ rd_progs_ok progs /\ 27 < nctl /\ rd_tab_apart L bw /\
     drv_sem progs bw ctl budget cfr PIECE i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> leb_fires (rd_from inp c) KK /\
              tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r))) (pl_set (pl_set cw 26 KK) 27 KK,s,stk) /\
              rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + LENGTH(leb_enc KK)))` in
  subst [lhs(concl def), mk_var("PIECE", `:(int64 list)list`); kt, mk_var("KK", `:num`)] g;;

let HDR_V_TAB def k =
  let kt = mk_small_numeral k in
  prove(hdr_v_tab_goal def k,
    REPEAT GEN_TAC THEN REWRITE_TAC[rd_progs_ok] THEN STRIP_TAC THEN TAB_HDR_K01_TAC THEN
    TAB_HDR_LEB_FIRST_TAC def THEN
    MP_TAC(ISPECL (tab_hdr_second_args def) TAB_STEP_EQW) THEN
    CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC]) THEN
    SUBGOAL_THEN (mk_conj(`pl_set cw 26 v 26 = v`, mk_eq(list_mk_icomb "pl_set" [`cw:num->num`; `26`; `v:num`; kt], kt)))
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC (mk_eq(`v:num`, kt)) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [TAB_PAYLOAD_TAC `u2:tisa_state` THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = mk_eq(`v:num`, kt))) THEN
      HDR_END_FIRED_TAC;
      HDR_END_STOP_TAC]);;

let HDR_V1_TAB = HDR_V_TAB pl_hdr_v1 1;;
let HDR_V0_TAB = HDR_V_TAB pl_hdr_v0 0;;

(* p: validate the policy into candidate word 25; POL is committed later. *)
let HDR_P_TAB = prove
 (`!tb L progs bw ctl nctl budget cfr i m used r cw (s:S) stk inp c.
     progs 20 = pol_max /\ rd_progs_ok progs /\ 26 < nctl /\ rd_tab_apart L bw /\
     drv_sem progs bw ctl budget cfr pl_hdr_p i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> ?p. p <= 2 /\ leb_fires (rd_from inp c) p /\
                  tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r)))
                    (pl_set (pl_set cw 26 p) 25 (MAX (cw 7) p),s,stk) /\
                  rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + LENGTH(leb_enc p)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_progs_ok] THEN STRIP_TAC THEN
  TAB_HDR_LEB_FIRST_TAC pl_hdr_p THEN
  MP_TAC(ISPECL (tab_hdr_second_args pl_hdr_p) TAB_STEP_POL_MAX) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  TRY(ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC]) THEN
  SUBGOAL_THEN `pl_set cw 26 v 26 = v /\ pl_set cw 26 v 7 = (cw:num->num) 7` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_CASES_TAC `v <= 2` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [TAB_PAYLOAD_TAC `u2:tisa_state` THEN HDR_END_FIRED_TAC THEN EXISTS_TAC `v:num` THEN ASM_REWRITE_TAC[];
    HDR_END_STOP_TAC]);;

(* The header plan over the tables: a FIRED run saw no header before (HDR   *)
(* 0); the input from the cursor is the header after its opcode for a      *)
(* policy p <= 2; the relations hold after it with HDR = 1, POL raised to p, *)
(* the other words below 24 kept, the cursor past the header.               *)
let PL_HDR_TAB = prove
 (`!tb L progs bw ctl nctl budget cfr i m used r cw (s:S) stk inp c.
     progs 3 = eqw /\ rd_progs_ok progs /\ progs 31 = const_next /\ progs 20 = pol_max /\ 27 < nctl /\
     rd_hdr_rel bw cfr m /\ rd_tab_apart L bw /\
     drv_sem progs bw ctl budget cfr pl_plan_hdr i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> cw 20 = 0 /\
              ?p cw'. p <= 2 /\ (?rest. rd_from inp c = APPEND (TL (holr_body p 0 [])) rest) /\
                      cw' 20 = 1 /\ cw' 7 = MAX (cw 7) p /\
                      (!j. j < 24 /\ ~(j = 7) /\ ~(j = 20) ==> cw' j = cw j) /\
                      tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r))) (cw',s,stk) /\
                      rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + LENGTH (TL (holr_body p 0 []))))`,
  let rv s = mk_var(s, `:int64#num#(int64->byte)#int64`) in
  let mem s = mk_icomb(`FST:(int64->byte)#int64->int64->byte`,
                mk_icomb(`SND:num#(int64->byte)#int64->(int64->byte)#int64`,
                  mk_icomb(`SND:int64#num#(int64->byte)#int64->num#(int64->byte)#int64`, rv s))) in
  let c1 = `c + LENGTH holr_hdr_const` in
  let c2 = `(c + LENGTH holr_hdr_const) + LENGTH(leb_enc 1)` in
  let c3 = `((c + LENGTH holr_hdr_const) + LENGTH(leb_enc 1)) + LENGTH(leb_enc 0)` in
  let c4 = `(((c + LENGTH holr_hdr_const) + LENGTH(leb_enc 1)) + LENGTH(leb_enc 0)) + LENGTH(leb_enc p)` in
  let c5 = `((((c + LENGTH holr_hdr_const) + LENGTH(leb_enc 1)) + LENGTH(leb_enc 0)) + LENGTH(leb_enc p)) +
            LENGTH(leb_enc 0)` in
  let choose_named n ty = FIRST_X_ASSUM(X_CHOOSE_THEN (mk_var(n, ty)) STRIP_ASSUME_TAC o
    check (fun th -> is_exists(concl th) && fst(dest_var(fst(dest_exists(concl th)))) = n)) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_plan_hdr; DRV_SEM_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN (rv "rb") STRIP_ASSUME_TAC) THEN
  (* b: the constant *)
  TAB_END_APPLY_TAC HDR_B_TAB `pl_hdr_b` `m:int64->byte` `c:num` THEN
  END_PIECE_CASE_TAC (rv "rb") THEN choose_named "x" `:num` THEN
  (* a: no header before *)
  END_NEXT_TAC (rv "rb") (rv "ra") THEN
  TAB_END_APPLY_TAC HDR_A_TAB `pl_hdr_a` (mem "rb") c1 THEN
  END_PIECE_CASE_TAC (rv "ra") THEN
  (* the version 1 0 *)
  END_NEXT_TAC (rv "ra") (rv "r1") THEN
  TAB_END_APPLY_TAC HDR_V1_TAB `pl_hdr_v1` (mem "ra") c1 THEN
  END_PIECE_CASE_TAC (rv "r1") THEN
  END_NEXT_TAC (rv "r1") (rv "r0") THEN
  TAB_END_APPLY_TAC HDR_V0_TAB `pl_hdr_v0` (mem "r1") c2 THEN
  END_PIECE_CASE_TAC (rv "r0") THEN
  (* the policy *)
  END_NEXT_TAC (rv "r0") (rv "rp") THEN
  TAB_END_APPLY_TAC HDR_P_TAB `pl_hdr_p` (mem "r0") c3 THEN
  END_PIECE_CASE_TAC (rv "rp") THEN choose_named "p" `:num` THEN
  (* the flags *)
  END_NEXT_TAC (rv "rp") (rv "rf") THEN
  TAB_END_APPLY_TAC HDR_V0_TAB `pl_hdr_v0` (mem "rp") c4 THEN
  END_PIECE_CASE_TAC (rv "rf") THEN
  (* The flags passed: publish the validated policy, then mark HDR. *)
  END_NEXT_TAC (rv "rf") (rv "rc") THEN
  TAB_END_APPLY_TAC HDR_COMMIT_TAB `pl_hdr_commit` (mem "rf") c5 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `FST(rc:int64#num#(int64->byte)#int64) = word 1`]) THEN
  (* HDR := 1: the last piece's run is r *)
  FIRST_ASSUM(fun th -> if concl th = mk_eq(mk_icomb(`SND:(int64->byte)#int64->int64`,
                                              mk_icomb(`SND:num#(int64->byte)#int64->(int64->byte)#int64`,
                                                mk_icomb(`SND:int64#num#(int64->byte)#int64->num#(int64->byte)#int64`,
                                                  rv "rc"))), `used:int64`)
                        then RULE_ASSUM_TAC(PURE_REWRITE_RULE[th]) else failwith "") THEN
  TAB_END_APPLY_TAC HDR_G_TAB `pl_hdr_g` (mem "rc") c5 THEN
  (* the conclusion *)
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    lhand(concl th) = `FST(r:int64#num#(int64->byte)#int64) = word 1`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`inp:num list`; `c:num`; `p:num`] HDR_BYTES) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> RULE_ASSUM_TAC(PURE_REWRITE_RULE[th]))) THEN
  TRY(CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  W(fun g -> MAP_EVERY EXISTS_TAC [`p:num`; tab_cw_of `FST(SND(SND(r:int64#num#(int64->byte)#int64)))` g]) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    CONV_TAC(TOP_DEPTH_CONV PL_SET_NUM_CONV) THEN REFL_TAC;
    CONV_TAC(TOP_DEPTH_CONV PL_SET_NUM_CONV) THEN REFL_TAC;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[pl_set] THEN
    REPEAT(COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN REFL_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

(* Every theorem this file states, for the audits. *)
let reader_plans_tab_theorems =
 ["RD_STEP_AT_END0", RD_STEP_AT_END0; "TAB_STEP_AT_END", TAB_STEP_AT_END; "RD_CHILD_INP0", RD_CHILD_INP0;
  "RD_STEP_FNV0", RD_STEP_FNV0; "TAB_STEP_FNV", TAB_STEP_FNV; "RD_STEP_LE8_0", RD_STEP_LE8_0;
  "TAB_STEP_LE8", TAB_STEP_LE8; "END_A_TAB", END_A_TAB; "END_B_TAB", END_B_TAB; "END_C_TAB", END_C_TAB;
  "END_D_TAB", END_D_TAB; "END_TAB", END_TAB; "RD_STEP_CONST_NEXT0", RD_STEP_CONST_NEXT0;
  "TAB_STEP_CONST_NEXT", TAB_STEP_CONST_NEXT; "RD_STEP_POL_MAX0", RD_STEP_POL_MAX0;
  "TAB_STEP_POL_MAX", TAB_STEP_POL_MAX; "HDR_B_TAB", HDR_B_TAB; "HDR_A_TAB", HDR_A_TAB; "HDR_G_TAB", HDR_G_TAB;
  "HDR_V1_TAB", HDR_V1_TAB; "HDR_V0_TAB", HDR_V0_TAB; "HDR_P_TAB", HDR_P_TAB; "PL_HDR_TAB", PL_HDR_TAB];;
