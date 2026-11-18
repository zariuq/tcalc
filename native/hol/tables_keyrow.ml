(* ========================================================================= *)
(* row_word on a keyed table: the interner's rows region, with its count    *)
(* region, is a row table of two-word rows (TAB_KEY_RTAB), so row_word's   *)
(* semantics over a row table applies (TAB_SEM_ROWW) and the leaf          *)
(* implements its meaning on any KeyTab of the layout (TAB_IMPL_ROWW_KEY).  *)
(*                                                                           *)
(* Loaded after tables_leaves.ml.                                            *)
(* ========================================================================= *)

let TAB_KEY_RTAB = prove
 (`!(trow:num->S->num->num list) (tn:num->S->num) twd tdrop tapp tput inp L bw ctl nctl cfr j m (s:S).
     tab_layout L bw ctl nctl cfr /\ MEM (KeyTab j) L /\
     tab_mem (trow,tn,twd,tdrop,tapp,tput) inp bw m s (KeyTab j)
     ==> pl_rtab bw j (j + 4) 2 m (\i w. EL w (trow j s i)) (tn (j + 4) s)`,
  let norm = CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES; GSYM ADD_ASSOC] THENC NUM_REDUCE_CONV) in
  let lt3 r = ARITH_RULE(mk_comb(mk_comb(`(<):num->num->bool`, r), `3`)) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONV_RULE(DEPTH_CONV BETA_CONV) o REWRITE_RULE[tab_dslots; ALL] o
              MATCH_MP TAB_DESC_SLOTS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th) &&
                                                    can (find_term ((=) `tab_slots`)) (concl th))) THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`] TAB_LAYOUT_SLOT) THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j + 4`] TAB_LAYOUT_SLOT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "tab_mem" (concl th))) THEN
  REWRITE_TAC[tab_mem] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `tisa_base`)) (concl th) then
    MAP_EVERY (fun r -> STRIP_ASSUME_TAC(norm (MP (SPEC r th) (lt3 r)))) [`0`; `2`]
    else failwith "") THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `tmem`)) (concl th) then
    MAP_EVERY (fun r -> ASSUME_TAC(norm (REWRITE_RULE[lt3 r] (SPEC r th)))) [`0`; `2`]
    else failwith "") THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ADD_ASSOC]) THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [intern_ok] o
              check (fun th -> is_const_app "intern_ok" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN DISCH_TAC THEN
  REWRITE_TAC[pl_rtab] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_mw; MULT_CLAUSES; WORD_ADD_0] THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && can (find_term ((=) `intern_count`)) (concl th)
                          then SUBST1_TAC(SYM th) else failwith "") THEN
    AP_TERM_TAC THEN REWRITE_TAC[intern_count; tisa_read; GSYM drv_word] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:int64->byte`; `tmem t`; `bw(j + 4):int64`; `val(bw(j + 4 + 1):int64)`; `0`]
                  DRV_WORD_AREA) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[LT_IMP_LE] THEN ASM_MESON_TAC[];
    ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `intern_word`)) (concl th)
       then REWRITE_TAC[MATCH_MP th (ASSUME `i < (tn:num->S->num) (j + 4) s`)] else failwith "") THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o REWRITE_RULE[ARITH_RULE `w < 2 <=> w = 0 \/ w = 1`] o
      check (fun th -> concl th = `w < 2`)) THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[pl_mw; intern_word; tisa_read; GSYM drv_word] THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC DRV_WORD_AREA THEN EXISTS_TAC `val(bw(j + 1):int64)` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[LT_IMP_LE] THEN ASM_ARITH_TAC]);;

let TAB_IMPL_ROWW_KEY = prove
 (`!(trow:num->S->num->num list) (tn:num->S->num) (twd:num->num) (tdrop:num->S->num->bool)
    (tapp:num->num->S->num list->S->bool) (tput:num->num->S->num->num->num->S->bool) L inp progs bw ctl nctl budget cfr st j.
     progs 4 = row_word /\ val(EL 0 st) = 4 /\ val(EL 1 st) = j /\ val(EL 2 st) = j + 4 /\
     MEM (KeyTab j) L /\ twd j = 2 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tab_impl (tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr) (trow,tn,twd,tdrop,tapp,tput) inp
                  progs bw ctl budget cfr st`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TAB_IMPL_RO THEN EXISTS_TAC `row_word` THEN
  ASM_REWRITE_TAC[ROW_WORD_LEAF_WF; PL_ROW_WORD_STATUS] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_DECLS_RO THEN REWRITE_TAC[ROW_WORD_DECLS; ALL] THEN CONV_TAC NUM_REDUCE_CONV;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN TAB_LEAF_AT_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_rel]) THEN
    SUBGOAL_THEN `pl_rtab bw j (j + 4) 2 m (\i w. EL w ((trow:num->S->num->num list) j s i)) (tn (j + 4) s)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC TAB_KEY_RTAB THEN
      MAP_EVERY EXISTS_TAC [`twd:num->num`; `tdrop:num->S->num->bool`; `tapp:num->num->S->num list->S->bool`;
                            `tput:num->num->S->num->num->num->S->bool`;
                            `inp:num list`; `L:tabdesc list`; `ctl:int64`; `nctl:num`; `cfr:int64`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> if is_const_app "ALL" (concl th) && tab_has_const "tab_mem" (concl th)
        then MATCH_MP_TAC(REWRITE_RULE[GSYM ALL_MEM] th) else failwith "") THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    TAB_DESC_TAC `KeyTab j` THEN
    MATCH_MP_TAC TAB_SEM_ROWW THEN
    W(fun (asl,_) ->
      let dc = concl(find (fun th -> is_const_app "drv_child" (concl th)) (map snd asl)) in
      let args = snd(strip_comb dc) in
      MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                            `cfr:int64`; el 5 args; el 6 args; el 7 args; `j:num`; `j + 4`]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]);;

(* Every theorem this file states, for the audits. *)
let tables_keyrow_theorems =
 ["TAB_KEY_RTAB", TAB_KEY_RTAB; "TAB_IMPL_ROWW_KEY", TAB_IMPL_ROWW_KEY];;
