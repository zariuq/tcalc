(* ========================================================================= *)
(* The reader beside the general table layer. The reader's step lemmas      *)
(* restated on the reader's relation alone, from its layout and the driver  *)
(* frame's bounds (RD_*0: no plan_rel); with the tables' frame              *)
(* (tables_reader.ml) they give each reader step over tab_rel and rd_rel   *)
(* together, the tables kept whatever the outcome (TAB_STEP_CUR, _LEB, _EQW, *)
(* _INC); and from them the decode plan (DD_TAB) and the one-operand prefix *)
(* (PREFIX_OP0_TAB) over any table interface and layout. Names are never   *)
(* dropped: every native step, and every path, keeps the drops of space 0  *)
(* empty (NAT_STEP_NAMES_KEPT, NAT_PATH_NAMES_KEPT).                         *)
(*                                                                           *)
(* Loaded after tables_reader.ml.                                            *)
(* ========================================================================= *)

(* Addresses of the reader's regions, from the reader's layout and the      *)
(* driver frame's bound alone.                                               *)
let RD_ADDR0_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RD_LAYOUT_AT) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  FIRST_ASSUM(fun th -> if is_const_app "drv_in" (concl th) then
     let [_; b; n] = snd(strip_comb(concl th)) in
     REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [b; n] THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC DRV_APART_IN THEN MAP_EVERY EXISTS_TAC [b; n] THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC DRV_APART_IN THEN MAP_EVERY EXISTS_TAC [b; n] THEN ASM_REWRITE_TAC[]]
     else failwith "");;

let RD_INP_ADDR0 = prove
 (`!bw ctl nctl cfr a.
     rd_layout bw ctl nctl cfr /\ 48 <= val cfr /\ drv_in a (bw 54) (val(bw 55))
     ==> ~drv_stack cfr a /\ ~drv_in a ctl (8 * nctl) /\ ~drv_in a (bw 58) (val(bw 59))`,
  RD_ADDR0_TAC);;

let RD_ST_ADDR0 = prove
 (`!bw ctl nctl cfr a.
     rd_layout bw ctl nctl cfr /\ 48 <= val cfr /\ drv_in a (bw 58) (val(bw 59))
     ==> ~drv_stack cfr a /\ ~drv_in a ctl (8 * nctl) /\ ~drv_in a (bw 54) (val(bw 55))`,
  RD_ADDR0_TAC);;

let RD_CHILD0 = prove
 (`!bw ctl nctl budget cfr st m used t inp c.
     drv_child bw ctl budget cfr st m used t /\ 48 <= val cfr /\
     rd_rel bw ctl nctl cfr m inp c /\ val(EL 1 st) = 54 /\ val(EL 2 st) = 58
     ==> tisa_base t 0 = bw 54 /\ tisa_len t 0 = bw 55 /\ tisa_base t 1 = bw 58 /\ tisa_len t 1 = bw 59 /\
         pl_cursor t = c /\ region_from t 0 (pl_cursor t) = rd_from inp c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `drv_base`)) (concl th) then
     MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC `0` th)) THEN MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC `1` th))
     else failwith "") THEN
  ASM_REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!a. drv_in a (bw 54) (val(bw 55)) \/ drv_in a (bw 58) (val(bw 59)) ==> tmem t a = (m:int64->byte) a`
    ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
      check (fun th -> is_const_app "drv_child" (concl th))) THEN
    FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
       ASSUME_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)) else failwith "") THENL
     [MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] RD_INP_ADDR0);
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] RD_ST_ADDR0)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_rel] o
    check (fun th -> is_const_app "rd_rel" (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  SUBGOAL_THEN `pl_cursor t = c` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && is_const_app "pl_mw" (lhs(concl th)))) THEN
    REWRITE_TAC[pl_cursor; pl_w; pl_mw; tisa_read; GSYM drv_word] THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC DRV_WORD_AREA THEN EXISTS_TAC `val(bw 59:int64)` THEN
    REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[region_from; rd_from; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[region_byte; tisa_read; READ_BYTES_1] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `tmem t (word_add (bw 54) (word(c + n)):int64) = (m:int64->byte) (word_add (bw 54) (word(c + n)))`
    SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN REWRITE_TAC[drv_in] THEN
    MP_TAC(SPECL [`bw 54:int64`; `c + n:num`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `val((m:int64->byte) (word_add (bw 54) (word(c + n)))) < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(m:int64->byte) (word_add (bw 54) (word(c + n)))` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* A step without writable regions keeps the reader's relation. *)
let RD_STEP_RO0 = prove
 (`!prog bw ctl nctl budget cfr st m used t k u inp c.
     rd_rel bw ctl nctl cfr m inp c /\ 48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\
     drv_child bw ctl budget cfr st m used t /\ tisa_leaf_wf prog /\ tisa_entry_ok prog t /\
     tisa_run prog t = TStop k u /\ val(EL 17 st) < nctl /\ (!r. ~tisa_rw (tisa_decls prog) r)
     ==> rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RD_REL_AGREE THEN EXISTS_TAC `m:int64->byte` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     ASSUME_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)) else failwith "") THEN
  SUBGOAL_THEN `~drv_stack cfr a /\ ~drv_in a ctl (8 * nctl)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] RD_INP_ADDR0);
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] RD_ST_ADDR0)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DRV_STEP_KEEPS THEN
  MAP_EVERY EXISTS_TAC [`prog:tisa_prog`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                        `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~drv_in (a:int64) ctl (8 * nctl)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC DRV_CTL_WORD_IN THEN EXISTS_TAC `val(EL 17 (st:int64 list))` THEN ASM_REWRITE_TAC[]);;

let RD_STEP_CUR0 = prove
 (`!bw ctl nctl budget cfr st m used t k u inp c.
     rd_rel bw ctl nctl cfr m inp c /\ 48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok cur t /\ tisa_run cur t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 17 st) < nctl
     ==> tisa_fword u 18 = word 1 /\ tisa_fword u 21 = used /\ val(tisa_fword u 19) = c /\
         rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DRV_CHILD_RECEIPT) THEN
  MP_TAC PL_CUR_SPEC THEN REWRITE_TAC[pl_cur_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM pl_cursor];
    MATCH_MP_TAC RD_STEP_RO0 THEN
    MAP_EVERY EXISTS_TAC [`cur`; `budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`] THEN
    ASM_REWRITE_TAC[CUR_LEAF_WF; CUR_RW]]);;

let RD_STEP_LEB0 = prove
 (`!bw ctl nctl budget cfr st m used t k u inp c.
     rd_rel bw ctl nctl cfr m inp c /\ 48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok leb_next t /\ tisa_run leb_next t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 17 st) < nctl
     ==> tisa_fword u 21 = used /\
         ((?v. leb_fires (rd_from inp c) v /\ tisa_fword u 18 = word 1 /\ val(tisa_fword u 19) = v /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp (c + LENGTH(leb_enc v))) \/
          ((!v. ~leb_fires (rd_from inp c) v) /\ tisa_fword u 18 = word 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DRV_CHILD_RECEIPT) THEN
  MP_TAC PL_LEB_NEXT_SPEC THEN REWRITE_TAC[pl_leb_next_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && is_const_app "region_from" (lhs(concl th))
                        then REWRITE_TAC[th] else failwith "") THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC o
    check (fun th -> is_disj(concl th))) THENL
   [ALL_TAC; DISJ2_TAC THEN ASM_REWRITE_TAC[]] THEN
  DISJ1_TAC THEN EXISTS_TAC `v:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RD_FROM_FIRES_LE) THEN
  SUBGOAL_THEN `v < 2 EXP 62` ASSUME_TAC THENL
   [ASM_MESON_TAC[leb_fires]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  (* What leb_next keeps: everything outside the state and the payload word. *)
  SUBGOAL_THEN `!a. ~drv_stack cfr a /\ ~drv_in a (bw 58) (val(bw 59)) /\
                    ~drv_in a (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8
                    ==> drv_after ctl st u a = (m:int64->byte) a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RD_LEB_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `used:int64`;
                          `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `v < 2 EXP 62` THEN ARITH_TAC;
    (* rd_rel: the input kept; the cursor advanced. *)
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
      (* the cursor: the state's word 0 after the run, the payload elsewhere *)
      SUBGOAL_THEN `tisa_base u 1 = tisa_base t 1` ASSUME_TAC THENL
       [MP_TAC(SPECL [`leb_next`; `t:tisa_state`; `k:num`; `u:tisa_state`; `1`] TISA_RUN_REGIONS) THEN
        ASM_REWRITE_TAC[LEB_NEXT_LEAF_WF; LEB_NEXT_READABLE] THEN SIMP_TAC[];
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
      ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]]);;

let RD_CHILD_ARGS0_TAC =
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

let RD_STEP_EQW0 = prove
 (`!bw ctl nctl budget cfr st m used t k u cw inp c.
     rd_rel bw ctl nctl cfr m inp c /\ 48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\
     pl_cwords ctl nctl m cw /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok eqw t /\ tisa_run eqw t = TStop k u /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         (if cw(val(EL 10 st)) = cw(val(EL 11 st))
          then tisa_fword u 18 = word 1 /\ val(tisa_fword u 19) = cw(val(EL 10 st)) /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RD_CHILD_ARGS0_TAC THEN
  MP_TAC PL_EQW_SPEC THEN REWRITE_TAC[pl_eqw_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `tisa_fword t 22 = tisa_fword t 23 <=>
                (cw:num->num)(val(EL 10 (st:int64 list))) = cw(val(EL 11 st))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM VAL_EQ]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun eq -> FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[eq] o check (is_cond o concl))) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(cw:num->num)(val(EL 11 (st:int64 list))) = val(tisa_fword u 19)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  FIRST [MATCH_MP_TAC RD_STEP_RO0 THEN
         MAP_EVERY EXISTS_TAC [`eqw`; `budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`] THEN
         ASM_REWRITE_TAC[EQW_LEAF_WF; EQW_DECLS; NO_DECLS_RW] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
         ASM_MESON_TAC[]]);;

let RD_STEP_INC0 = prove
 (`!bw ctl nctl budget cfr st m used t k u cw inp c.
     rd_rel bw ctl nctl cfr m inp c /\ 48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\
     pl_cwords ctl nctl m cw /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok inc t /\ tisa_run inc t = TStop k u /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         (if cw(val(EL 10 st)) + 1 < 2 EXP 62
          then tisa_fword u 18 = word 1 /\ val(tisa_fword u 19) = cw(val(EL 10 st)) + 1 /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c
          else tisa_fword u 18 = word 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RD_CHILD_ARGS0_TAC THEN
  MP_TAC PL_INC_SPEC THEN REWRITE_TAC[pl_inc_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `(cw:num->num)(val(EL 10 (st:int64 list))) + 1 < 2 EXP 62` THEN ARITH_TAC;
    MATCH_MP_TAC RD_STEP_RO0 THEN
    MAP_EVERY EXISTS_TAC [`inc`; `budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`] THEN
    ASM_REWRITE_TAC[INC_LEAF_WF; INC_RW] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* The layout's facts a reader step needs. *)
let TAB_REL_FRAME = prove
 (`!tb L inp bw ctl nctl cfr m cw (s:S) stk.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk)
     ==> 48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\ pl_cwords ctl nctl m cw /\
         (!k. k <= 6 ==> cw k = k) /\ 7 <= nctl /\ tab_layout L bw ctl nctl cfr`,
  REWRITE_TAC[tab_rel; tab_layout] THEN SIMP_TAC[]);;

(* cur over the tables and the reader: FIRED, the cursor in the step's word. *)
let TAB_STEP_CUR = prove
 (`!tb L inp bw ctl nctl budget cfr st m used t k u cw (s:S) stk c.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok cur t /\ tisa_run cur t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st)
     ==> tisa_fword u 18 = word 1 /\ tisa_fword u 21 = used /\
         tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u) (pl_set cw (val(EL 17 st)) c,s,stk) /\
         rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_FRAME) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; `inp:num list`; `c:num`]
               RD_STEP_CUR0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && lhs(concl th) = `val(tisa_fword u 19)`)) THEN
  MATCH_MP_TAC TAB_REL_RO_STEP THEN
  MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `cur`; `k:num`] THEN
  ASM_REWRITE_TAC[CUR_LEAF_WF; CUR_RW]);;

(* leb_next over the tables and the reader: the tables kept whatever the    *)
(* outcome; FIRED with the value at the cursor, or REFUSED.                  *)
let TAB_STEP_LEB = prove
 (`!tb L inp bw ctl nctl budget cfr st m used t k u cw (s:S) stk c.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ rd_rel bw ctl nctl cfr m inp c /\ rd_tab_apart L bw /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok leb_next t /\ tisa_run leb_next t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),s,stk) /\
         ((?v. leb_fires (rd_from inp c) v /\ tisa_fword u 18 = word 1 /\ val(tisa_fword u 19) = v /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp (c + LENGTH(leb_enc v))) \/
          ((!v. ~leb_fires (rd_from inp c) v) /\ tisa_fword u 18 = word 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_FRAME) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; `inp:num list`; `c:num`]
               RD_STEP_LEB0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TAB_RD_STEP_KEEP THEN
  MAP_EVERY EXISTS_TAC [`budget:int64`; `leb_next`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[LEB_NEXT_LEAF_WF; LEB_NEXT_RW] THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     ACCEPT_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)) ORELSE
     (CONJ_TAC THENL [ACCEPT_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)); ALL_TAC])
     else failwith "") THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let TAB_STEP_EQW = prove
 (`!tb L inp bw ctl nctl budget cfr st m used t k u cw (s:S) stk c.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok eqw t /\ tisa_run eqw t = TStop k u /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),s,stk) /\
         (if cw(val(EL 10 st)) = cw(val(EL 11 st))
          then tisa_fword u 18 = word 1 /\ val(tisa_fword u 19) = cw(val(EL 10 st)) /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_FRAME) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; `cw:num->num`;
                `inp:num list`; `c:num`] RD_STEP_EQW0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TAB_REL_RO_STEP THEN
  MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `eqw`; `k:num`] THEN
  ASM_REWRITE_TAC[EQW_LEAF_WF; EQW_DECLS; NO_DECLS_RW] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

let TAB_STEP_INC = prove
 (`!tb L inp bw ctl nctl budget cfr st m used t k u cw (s:S) stk c.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok inc t /\ tisa_run inc t = TStop k u /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),s,stk) /\
         (if cw(val(EL 10 st)) + 1 < 2 EXP 62
          then tisa_fword u 18 = word 1 /\ val(tisa_fword u 19) = cw(val(EL 10 st)) + 1 /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c
          else tisa_fword u 18 = word 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_FRAME) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; `cw:num->num`;
                `inp:num list`; `c:num`] RD_STEP_INC0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TAB_REL_RO_STEP THEN
  MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `inc`; `k:num`] THEN
  ASM_REWRITE_TAC[INC_LEAF_WF; INC_RW] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

let DD_TAB = prove
 (`!tb L inp progs bw ctl nctl budget cfr i m used r cw (s:S) stk c.
     rd_progs_ok progs /\ 21 < nctl /\ rd_tab_apart L bw /\
     drv_sem progs bw ctl budget cfr pl_plan_dd i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1 <=> ?op. leb_fires (rd_from inp c) op) /\
         (FST r = word 0 <=> !op. ~leb_fires (rd_from inp c) op) /\
         (FST r = word 1
          ==> ?op. leb_fires (rd_from inp c) op /\
                   tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r))) (pl_set (pl_set cw 21 c) 18 op,s,stk) /\
                   rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + LENGTH(leb_enc op)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_progs_ok] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_plan_dd; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
                      (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`; `L:tabdesc list`; `inp:num list`;
                 `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_plan_dd_st1;
                 `m:int64->byte`; `used:int64`; `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`;
                 `s:S`; `stk:num list`; `c:num`] TAB_STEP_CUR) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
                      (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`; `L:tabdesc list`; `inp:num list`;
                 `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_plan_dd_st2;
                 list_mk_comb(`drv_after`, [`ctl:int64`; pl_plan_dd_st1; `u1:tisa_state`]);
                 `used:int64`; `t2:tisa_state`; `k2:num`; `u2:tisa_state`; `pl_set cw 21 c`;
                 `s:S`; `stk:num list`; `c:num`] TAB_STEP_LEB) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let PREFIX_OP0_TAB = prove
 (`!tb L inp progs bw ctl nctl budget cfr i m used r cw (s:S) stk c.
     progs 3 = eqw /\ rd_progs_ok progs /\ 24 < nctl /\ rd_tab_apart L bw /\
     drv_sem progs bw ctl budget cfr pl_prefix_op0 i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1 <=> cw 20 = 1 /\ ?t. leb_fires (rd_from inp c) t) /\
         (FST r = word 0 <=> ~(cw 20 = 1 /\ ?t. leb_fires (rd_from inp c) t)) /\
         (FST r = word 1
          ==> ?t. leb_fires (rd_from inp c) t /\
                  tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r))) (pl_set (pl_set cw 24 1) 8 t,s,stk) /\
                  rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + LENGTH(leb_enc t)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_progs_ok] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cw:num->num) 1 = 1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "tab_rel" (concl th))) THEN
    REWRITE_TAC[tab_rel] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_prefix_op0; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
                      (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`; `L:tabdesc list`; `inp:num list`;
                 `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_prefix_op0_st1;
                 `m:int64->byte`; `used:int64`; `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`;
                 `s:S`; `stk:num list`; `c:num`] TAB_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(cw:num->num) 20 = 1` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `val(tisa_fword u1 19)`
                          then RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "");
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
                      (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`; `L:tabdesc list`; `inp:num list`;
                 `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_prefix_op0_st2;
                 list_mk_comb(`drv_after`, [`ctl:int64`; pl_prefix_op0_st1; `u1:tisa_state`]);
                 `used:int64`; `t2:tisa_state`; `k2:num`; `u2:tisa_state`; `pl_set cw 24 1`;
                 `s:S`; `stk:num list`; `c:num`] TAB_STEP_LEB) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Names are never dropped: every native step keeps the drops of space 0   *)
(* empty (its drops are of spaces 1, 2 and 3).                              *)
let NAT_STEP_NAMES_KEPT = prove
 (`!ns r ns'. nat_step ns r ns'
     ==> (!j. ~MEM (0,j) (FST(SND(SND(SND(SND(SND(SND(SND(SND ns))))))))))
     ==> (!j. ~MEM (0,j) (FST(SND(SND(SND(SND(SND(SND(SND(SND ns'))))))))))`,
  MATCH_MP_TAC nat_step_INDUCT THEN REWRITE_TAC[FST; SND; MEM; PAIR_EQ; ARITH_EQ] THEN SIMP_TAC[]);;

let NAT_PATH_NAMES_KEPT = prove
 (`!recs ns ns'. tc_path nat_step recs ns ns'
     ==> (!j. ~MEM (0,j) (FST(SND(SND(SND(SND(SND(SND(SND(SND ns))))))))))
     ==> (!j. ~MEM (0,j) (FST(SND(SND(SND(SND(SND(SND(SND(SND ns'))))))))))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[tc_path] THENL
   [MESON_TAC[]; ASM_MESON_TAC[NAT_STEP_NAMES_KEPT]]);;

(* ------------------------------------------------------------------------- *)
(* skip (leaf 28): the cursor advanced by a word's value, over the reader  *)
(* and then over the tables.                                                 *)
(* ------------------------------------------------------------------------- *)

let SKIP_RW = prove
 (`!r. tisa_rw (tisa_decls skip) r <=> r = 1`, RD_RW_CASES_TAC SKIP_DECLS);;
let SKIP_READABLE = prove
 (`!r. tisa_readable (tisa_decls skip) r <=> r = 0 \/ r = 1`, RD_RW_CASES_TAC SKIP_DECLS);;

(* skip writes only the state and the step's payload word. *)
let RD_SKIP_KEEPS = prove
 (`!bw ctl nctl budget cfr st m used t k u a.
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok skip t /\ tisa_run skip t = TStop k u /\
     val(EL 2 st) = 58 /\ val ctl + 8 * nctl <= 2 EXP 64 /\ val(EL 17 st) < nctl /\
     ~drv_stack cfr a /\ ~drv_in a (bw 58) (val(bw 59)) /\
     ~drv_in a (word_add ctl (word(8 * val(EL 17 st)))) 8
     ==> drv_after ctl st u a = m a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
  MAP_EVERY EXISTS_TAC [`skip`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                        `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[SKIP_LEAF_WF; SKIP_RW] THEN
  X_GEN_TAC `r:num` THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* skip by the step's first argument: FIRED with the cursor advanced when   *)
(* that stays in the input, else REFUSED.                                    *)
let RD_STEP_SKIP0 = prove
 (`!bw ctl nctl budget cfr st m used t k u cw inp c.
     rd_rel bw ctl nctl cfr m inp c /\ 48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\
     pl_cwords ctl nctl m cw /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok skip t /\ tisa_run skip t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         (if c + cw(val(EL 10 st)) <= LENGTH inp
          then tisa_fword u 18 = word 1 /\ val(tisa_fword u 19) = c + cw(val(EL 10 st)) /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp (c + cw(val(EL 10 st)))
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RD_CHILD_ARGS0_TAC THEN
  SUBGOAL_THEN `val(EL 17 (st:int64 list)) < nctl` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  MP_TAC PL_SKIP_SPEC THEN REWRITE_TAC[pl_skip_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `c + (cw:num->num)(val(EL 10 (st:int64 list))) < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* What skip keeps: everything outside the state and the payload word. *)
  SUBGOAL_THEN `!a. ~drv_stack cfr a /\ ~drv_in a (bw 58) (val(bw 59)) /\
                    ~drv_in a (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8
                    ==> drv_after ctl st u a = (m:int64->byte) a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RD_SKIP_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `used:int64`;
                          `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* rd_rel: the input kept; the cursor advanced. *)
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
    (* the cursor: the state's word 0 after the run, the payload elsewhere *)
    SUBGOAL_THEN `tisa_base u 1 = tisa_base t 1` ASSUME_TAC THENL
     [MP_TAC(SPECL [`skip`; `t:tisa_state`; `k:num`; `u:tisa_state`; `1`] TISA_RUN_REGIONS) THEN
      ASM_REWRITE_TAC[SKIP_LEAF_WF; SKIP_READABLE] THEN SIMP_TAC[];
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
    ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]]);;

(* skip over the tables and the reader: the tables kept whatever the        *)
(* outcome; FIRED with the cursor advanced, or REFUSED.                      *)
let TAB_STEP_SKIP = prove
 (`!tb L inp bw ctl nctl budget cfr st m used t k u cw (s:S) stk c.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ rd_rel bw ctl nctl cfr m inp c /\ rd_tab_apart L bw /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok skip t /\ tisa_run skip t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),s,stk) /\
         (if c + cw(val(EL 10 st)) <= LENGTH inp
          then tisa_fword u 18 = word 1 /\ val(tisa_fword u 19) = c + cw(val(EL 10 st)) /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp (c + cw(val(EL 10 st)))
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_FRAME) THEN
  SUBGOAL_THEN `val(EL 17 (st:int64 list)) < nctl` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; `cw:num->num`;
                `inp:num list`; `c:num`] RD_STEP_SKIP0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TAB_RD_STEP_KEEP THEN
  MAP_EVERY EXISTS_TAC [`budget:int64`; `skip`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[SKIP_LEAF_WF; SKIP_RW] THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     ACCEPT_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)) ORELSE
     (CONJ_TAC THENL [ACCEPT_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)); ALL_TAC])
     else failwith "") THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* NAME's operand: a length in LEB128, then that many bytes. The prefix     *)
(* reads the length to OP1 and the offset of the bytes to OP0, and moves    *)
(* the cursor past them with skip (leaf 28).                                 *)
(* ------------------------------------------------------------------------- *)

let name_fires = new_definition
 `name_fires bs (v:num list) <=>
    LENGTH v < 2 EXP 62 /\ ?rest. bs = APPEND (APPEND (leb_enc (LENGTH v)) v) rest`;;

let NAME_FIRES_LEB = prove
 (`!bs v. name_fires bs v ==> leb_fires bs (LENGTH v)`,
  REWRITE_TAC[name_fires; leb_fires; GSYM APPEND_ASSOC] THEN MESON_TAC[]);;

let NAME_FIRES_UNIQUE = prove
 (`!bs v1 v2. name_fires bs v1 /\ name_fires bs v2 ==> v1 = v2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(v1:num list) = LENGTH(v2:num list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NAME_FIRES_LEB; LEB_FIRES_UNIQUE]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_const_app "name_fires" o concl))) THEN
  REWRITE_TAC[name_fires; GSYM APPEND_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r1:num list` SUBST1_TAC)) THEN
  REWRITE_TAC[APPEND_LCANCEL_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `r2:num list`)) THEN
  MP_TAC(ISPECL [`v1:num list`; `v2:num list`; `r1:num list`; `r2:num list`] APPEND_SAME_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* A name at c lies in the input. *)
let NAME_FIRES_LE = prove
 (`!inp c v. name_fires (rd_from inp c) v ==> (c + LENGTH(leb_enc(LENGTH v))) + LENGTH v <= LENGTH inp`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RD_FROM_FIRES_LE o MATCH_MP NAME_FIRES_LEB) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[name_fires]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `rest:num list` MP_TAC)) THEN
  DISCH_THEN(MP_TAC o AP_TERM `LENGTH:num list->num`) THEN
  REWRITE_TAC[rd_from; LENGTH_LIST_OF_SEQ; LENGTH_APPEND] THEN ARITH_TAC);;

(* The name's bytes are the input's at the offset past its length. *)
let NAME_FIRES_KEY = prove
 (`!inp c v. name_fires (rd_from inp c) v
     ==> tab_key inp (c + LENGTH(leb_enc(LENGTH v))) (LENGTH v) = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[name_fires; GSYM APPEND_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `rest:num list` ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RD_FROM_APPEND) THEN
  MP_TAC(ISPECL [`\j. EL ((c + LENGTH(leb_enc(LENGTH(v:num list)))) + j) (inp:num list)`;
                 `LENGTH(inp:num list) - (c + LENGTH(leb_enc(LENGTH(v:num list))))`; `v:num list`]
                LIST_OF_SEQ_PREFIX) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> ((a <=> b) ==> c)`) THEN CONJ_TAC THENL
   [EXISTS_TAC `rest:num list` THEN REWRITE_TAC[GSYM rd_from] THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN REWRITE_TAC[tab_key; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ]]);;

(* A length at c whose bytes lie in the input is a name. *)
let NAME_FIRES_READ = prove
 (`!inp c len. leb_fires (rd_from inp c) len /\ (c + LENGTH(leb_enc len)) + len <= LENGTH inp
     ==> LENGTH(tab_key inp (c + LENGTH(leb_enc len)) len) = len /\
         name_fires (rd_from inp c) (tab_key inp (c + LENGTH(leb_enc len)) len)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(tab_key inp (c + LENGTH(leb_enc len)) len) = len` ASSUME_TAC THENL
   [REWRITE_TAC[tab_key; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[name_fires] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [leb_fires] o check (is_const_app "leb_fires" o concl)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `rest0:num list`)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RD_FROM_APPEND) THEN
  MP_TAC(ISPECL [`inp:num list`; `c + LENGTH(leb_enc len)`; `tab_key inp (c + LENGTH(leb_enc len)) len`]
                RD_FROM_PREFIX) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REWRITE_TAC[tab_key]; ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `rd_from inp ((c + LENGTH(leb_enc len)) + len)` THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC]);;

(* The prefix: the header seen [REFUSED otherwise]; the length to OP1       *)
(* [REFUSED when no minimal LEB128 lies at the cursor]; the offset to OP0;  *)
(* the cursor past the bytes [REFUSED when the input ends first]. skip's    *)
(* payload goes to the temporary 24.                                         *)
let pl_prefix_name = new_definition(mk_eq(`pl_prefix_name:(int64 list)list`,
  mk_list([pl_step 3 [] 20 1 [] 24; pl_step 26 pl_RD 0 0 [] 9; pl_step 25 pl_RD 0 0 [] 8;
           pl_step 28 pl_RD 9 0 [] 24], `:int64 list`)));;
let pl_prefix_name_st k = el k (dest_list(rhs(concl pl_prefix_name)));;

let PL_SET_NAME_OP1 = prove
 (`!cw len c1. pl_set (pl_set (pl_set cw 24 1) 9 len) 8 c1 9 = len`,
  REWRITE_TAC[pl_set] THEN CONV_TAC(DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV) THEN REWRITE_TAC[]);;

let PREFIX_NAME_TAB = prove
 (`!tb L inp progs bw ctl nctl budget cfr i m used r cw (s:S) stk c.
     progs 3 = eqw /\ rd_progs_ok progs /\ progs 28 = skip /\ 24 < nctl /\ rd_tab_apart L bw /\
     drv_sem progs bw ctl budget cfr pl_prefix_name i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1 <=> cw 20 = 1 /\ ?v. name_fires (rd_from inp c) v) /\
         (FST r = word 0 <=> ~(cw 20 = 1 /\ ?v. name_fires (rd_from inp c) v)) /\
         (FST r = word 1
          ==> ?v. name_fires (rd_from inp c) v /\
                  tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r)))
                    (pl_set (pl_set (pl_set (pl_set cw 24 1) 9 (LENGTH v)) 8 (c + LENGTH(leb_enc(LENGTH v))))
                            24 ((c + LENGTH(leb_enc(LENGTH v))) + LENGTH v),s,stk) /\
                  rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp ((c + LENGTH(leb_enc(LENGTH v))) + LENGTH v))`,
  let tbty = `tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
                 (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)` in
  let after k u = list_mk_comb(`drv_after`, [`ctl:int64`; pl_prefix_name_st k; u]) in
  let refused =
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
    ASM_REWRITE_TAC[] in
  let payload u = FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = mk_comb(`val:int64->num`,
                                             list_mk_comb(`tisa_fword`, [u; `19`]))
                                        then RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "") in
  let next t k u =
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN t (X_CHOOSE_THEN k (X_CHOOSE_THEN u STRIP_ASSUME_TAC))) in
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_progs_ok] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cw:num->num) 1 = 1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "tab_rel" (concl th))) THEN
    REWRITE_TAC[tab_rel] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  (* 1: the header seen *)
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_prefix_name; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [tbty; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                 `budget:int64`; `cfr:int64`; pl_prefix_name_st 0; `m:int64->byte`; `used:int64`;
                 `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`; `s:S`; `stk:num list`; `c:num`]
                TAB_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(cw:num->num) 20 = 1` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [payload `u1:tisa_state`; refused] THEN
  (* 2: the length to OP1 *)
  next `t2:tisa_state` `k2:num` `u2:tisa_state` THEN
  MP_TAC(ISPECL [tbty; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                 `budget:int64`; `cfr:int64`; pl_prefix_name_st 1; after 0 `u1:tisa_state`; `used:int64`;
                 `t2:tisa_state`; `k2:num`; `u2:tisa_state`; `pl_set cw 24 1`; `s:S`; `stk:num list`; `c:num`]
                TAB_STEP_LEB) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `len:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC))) THENL
   [payload `u2:tisa_state`;
    (* no length at the cursor: no name there *)
    refused THEN ASM_MESON_TAC[NAME_FIRES_LEB]] THEN
  (* 3: the offset to OP0 *)
  next `t3:tisa_state` `k3:num` `u3:tisa_state` THEN
  MP_TAC(ISPECL [tbty; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                 `budget:int64`; `cfr:int64`; pl_prefix_name_st 2; after 1 `u2:tisa_state`; `used:int64`;
                 `t3:tisa_state`; `k3:num`; `u3:tisa_state`; `pl_set (pl_set cw 24 1) 9 len`; `s:S`;
                 `stk:num list`; `c + LENGTH(leb_enc len)`] TAB_STEP_CUR) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  (* 4: the cursor past the bytes *)
  next `t4:tisa_state` `k4:num` `u4:tisa_state` THEN
  MP_TAC(ISPECL [tbty; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                 `budget:int64`; `cfr:int64`; pl_prefix_name_st 3; after 2 `u3:tisa_state`; `used:int64`;
                 `t4:tisa_state`; `k4:num`; `u4:tisa_state`;
                 `pl_set (pl_set (pl_set cw 24 1) 9 len) 8 (c + LENGTH(leb_enc len))`; `s:S`;
                 `stk:num list`; `c + LENGTH(leb_enc len)`] TAB_STEP_SKIP) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[PL_SET_NAME_OP1] THEN
  ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  COND_CASES_TAC THEN STRIP_TAC THENL
   [(* the bytes lie in the input: FIRED with the name they spell *)
    payload `u4:tisa_state` THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
    MP_TAC(SPECL [`inp:num list`; `c:num`; `len:num`] NAME_FIRES_READ) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    EXISTS_TAC `tab_key inp (c + LENGTH(leb_enc len)) len` THEN ASM_REWRITE_TAC[];
    (* the input ends inside them: REFUSED, and no name at c *)
    refused THEN REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `v:num list` THEN DISCH_TAC THEN
    SUBGOAL_THEN `LENGTH(v:num list) = len` ASSUME_TAC THENL
     [MATCH_MP_TAC LEB_FIRES_UNIQUE THEN EXISTS_TAC `rd_from inp c` THEN ASM_SIMP_TAC[NAME_FIRES_LEB];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP NAME_FIRES_LE) THEN ASM_REWRITE_TAC[]]);;

(* Every theorem this file states, for the audits. *)
let reader_tab_theorems =
 ["RD_INP_ADDR0", RD_INP_ADDR0;
  "RD_ST_ADDR0", RD_ST_ADDR0;
  "RD_CHILD0", RD_CHILD0;
  "RD_STEP_RO0", RD_STEP_RO0;
  "RD_STEP_CUR0", RD_STEP_CUR0;
  "RD_STEP_LEB0", RD_STEP_LEB0;
  "RD_STEP_EQW0", RD_STEP_EQW0;
  "RD_STEP_INC0", RD_STEP_INC0;
  "TAB_REL_FRAME", TAB_REL_FRAME;
  "TAB_STEP_CUR", TAB_STEP_CUR;
  "TAB_STEP_LEB", TAB_STEP_LEB;
  "TAB_STEP_EQW", TAB_STEP_EQW;
  "TAB_STEP_INC", TAB_STEP_INC;
  "DD_TAB", DD_TAB;
  "PREFIX_OP0_TAB", PREFIX_OP0_TAB;
  "NAT_STEP_NAMES_KEPT", NAT_STEP_NAMES_KEPT;
  "NAT_PATH_NAMES_KEPT", NAT_PATH_NAMES_KEPT;
  "SKIP_RW", SKIP_RW;
  "SKIP_READABLE", SKIP_READABLE;
  "RD_SKIP_KEEPS", RD_SKIP_KEEPS;
  "RD_STEP_SKIP0", RD_STEP_SKIP0;
  "TAB_STEP_SKIP", TAB_STEP_SKIP;
  "NAME_FIRES_LEB", NAME_FIRES_LEB;
  "NAME_FIRES_UNIQUE", NAME_FIRES_UNIQUE;
  "NAME_FIRES_LE", NAME_FIRES_LE;
  "NAME_FIRES_KEY", NAME_FIRES_KEY;
  "NAME_FIRES_READ", NAME_FIRES_READ;
  "PL_SET_NAME_OP1", PL_SET_NAME_OP1;
  "PREFIX_NAME_TAB", PREFIX_NAME_TAB];;
