(* The checker table frame for the binding walk and its private work region. *)
needs "native/hol/tables_abs_semantics.ml";;
needs "native/hol/bind_walk_table_contract.ml";;

let BW_ROWS_DISTINCT = prove
 (`!s. intern_ok s ==> keys_distinct (bw_rows s (val(intern_count s)))`,
  GEN_TAC THEN REWRITE_TAC[intern_ok;intern_distinct;intern_has;keys_distinct;LENGTH_BW_ROWS] THEN
  STRIP_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    is_const_app "EL" (lhs(concl th)))) THEN
  ASM_SIMP_TAC[EL_BW_ROWS;bw_row;PAIR_EQ;GSYM VAL_EQ] THEN
  MP_TAC(SPECL [`val(intern_word s (2 * i))`;`8`] DIVISION) THEN
  MP_TAC(SPECL [`val(intern_word s (2 * j))`;`8`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC);;

let BW_ROWS_COUNT_BOUND = prove
 (`!s. intern_ok s ==> LENGTH(bw_rows s (val(intern_count s))) < 2 EXP 60`,
  GEN_TAC THEN REWRITE_TAC[intern_ok;LENGTH_BW_ROWS] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `val(intern_count s) <= val(tisa_len s 0) DIV 16`) THEN
  MP_TAC(ISPEC `tisa_len s 0` VAL_BOUND_64) THEN
  SIMP_TAC[LE_RDIV_EQ;ARITH_EQ] THEN ARITH_TAC);;

let BW_EXT_APPEND = prove
 (`!D D'. bw_ext D D' ==> ?md. D' = APPEND D md`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_ext] THEN STRIP_TAC THEN
  SUBGOAL_THEN `D' = list_of_seq (\i. EL i D') (LENGTH(D':(num#num#num)list))` SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ;LENGTH_LIST_OF_SEQ] THEN SIMP_TAC[EL_LIST_OF_SEQ];
    ASM_REWRITE_TAC[LIST_OF_SEQ_PREFIX]]);;

let BW_RESULT_ROWS = prove
 (`!s k u. bw_result s k u /\ intern_ok s
     ==> ?md. bw_rows u (val(intern_count u)) = APPEND (bw_rows s (val(intern_count s))) md /\
              (~(k = 1) ==> md = [])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_result] o
    check (fun th -> concl th = `bw_result s k u`)) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[intern_ok] o
    check (fun th -> concl th = `intern_ok s`)) THEN
  ASM_CASES_TAC `k = 1` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BW_EXT_APPEND THEN
    MATCH_MP_TAC BW_ROWS_EXT THEN ASM_MESON_TAC[];
    EXISTS_TAC `[]:(num#num#num)list` THEN REWRITE_TAC[APPEND_NIL] THEN
    SUBGOAL_THEN `intern_count u = intern_count s` SUBST1_TAC THENL
     [ASM_MESON_TAC[];MATCH_MP_TAC BW_ROWS_EQ THEN ASM_MESON_TAC[]]]);;

let TAB_WALK_DB_MEM = prove
 (`!inp bw m ctx nms tys ntms dbs ths nmap ymap drops pol.
     (!i. i < LENGTH dbs ==> FST(EL i dbs) < 8)
     ==> (tab_mem hol_tables inp bw m (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (KeyTab 6) <=>
          16 <= val(bw 7) /\ 8 <= val(bw 9) /\ 8 <= val(bw 11) /\ pl_itab bw 6 m dbs)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ITAB_KEY_HOL] THEN
  REWRITE_TAC[hol_tables;tab_mem;hol_trow;hol_twd;hol_tw;hol_tn] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV LIST_OF_SEQ_CONV) THEN REWRITE_TAC[CONS_11;hol_tw;ARITH_EQ]);;

let TAB_WALK_DB_FRAME = prove
 (`!ctx nms tys ntms dbs dbs' ths nmap ymap drops pol.
     tab_frame hol_tables 6 10 (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
                              (ctx,nms,tys,ntms,dbs',ths,nmap,ymap,drops,pol)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_frame;hol_tables] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM;hol_trow] THEN HOL_FRAME_TAC;
    X_GEN_TAC `c:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[hol_tn];
    REWRITE_TAC[FUN_EQ_THM;hol_tdrop]]);;

let BW_ITAB_OF_STATE = prove
 (`!bw j m s.
     (!r. r < 3 ==> tisa_base s r = bw(j + 2 * r) /\ tisa_len s r = bw(j + 2 * r + 1)) /\
     (!r a. r < 3 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1))) ==> tmem s a = m a) /\
     intern_ok s
     ==> pl_itab bw j m (bw_rows s (val(intern_count s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_itab;LENGTH_BW_ROWS] THEN
  EXISTS_TAC `s:tisa_state` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_BW_ROWS;bw_row]);;

let TAB_REL_UPDATE_WORK = prove
 (`!tb L inp bw ctl nctl cfr m m' cw (s:S) s' stk p v d0 j c.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ tab_wf L /\ MEM d0 L /\ tab_table d0 j c /\
     p < nctl /\ 6 < p /\
     (!a. ~drv_stack cfr a /\ ~drv_in a (word_add ctl (word(8 * p))) 8 /\
          ~drv_in a (bw 42) (val(bw 43)) /\
          (!j'. MEM j' (tab_dslots d0) ==> ~drv_in a (bw j') (val(bw(j' + 1))))
          ==> m' a = m a) /\
     drv_word m' (word_add ctl (word(8 * p))) = v /\
     tab_frame tb j c s s' /\ tab_mem tb inp bw m' s' d0 /\
     (!jm wd. MEM (MarkTab jm j c wd) L ==> tab_mem tb inp bw m' s' (MarkTab jm j c wd))
     ==> tab_rel tb L inp bw ctl nctl cfr m' (pl_set cw p (val v),s',stk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_rel] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  SUBGOAL_THEN `!j'. MEM j' (tab_dslots d0) ==> MEM j' (tab_slots L)` ASSUME_TAC THENL
   [ASM_MESON_TAC[TAB_SLOTS_DESC]; ALL_TAC] THEN
  (* agreement on the described slots that are not d0's *)
  SUBGOAL_THEN `!j' a. MEM j' (tab_slots L) /\ ~(j' = 42) /\ ~MEM j' (tab_dslots d0) /\ drv_in a (bw j') (val(bw(j' + 1)))
                       ==> m' a = (m:int64->byte) a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_stack`)) (concl th) && can (find_term ((=) `m':int64->byte`)) (concl th))) THEN
    MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j':num`;
                  `p:num`; `a:int64`] TAB_SLOT_ADDR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DRV_APART_IN THEN
      MAP_EVERY EXISTS_TAC [`bw(j':num):int64`;`val(bw(j' + 1):int64)`] THEN
      ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`j':num`;`42`] o check (fun th ->
        length(fst(strip_forall(concl th))) = 2 && tab_has_const "drv_apart" (concl th))) THEN
      REWRITE_TAC[ARITH_RULE `42 + 1 = 43`] THEN
      ASM_SIMP_TAC[TAB_SLOTS_STK];ALL_TAC] THEN
    X_GEN_TAC `j'':num` THEN DISCH_TAC THEN
    MATCH_MP_TAC DRV_APART_IN THEN
    MAP_EVERY EXISTS_TAC [`bw(j':num):int64`; `val(bw(j' + 1):int64)`] THEN ASM_REWRITE_TAC[] THEN
    DISJ1_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      let vs,_ = strip_forall(concl th) in length vs = 2 && can (find_term ((=) `drv_apart`)) (concl th))) THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_set] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC PL_CWORDS_SET THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_stack`)) (concl th) && can (find_term ((=) `m':int64->byte`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC TAB_CTL_ADDR THEN
      MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC DRV_APART_IN THEN
      MAP_EVERY EXISTS_TAC [`ctl:int64`;`8 * nctl`] THEN ASM_REWRITE_TAC[] THEN
      DISJ2_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `42` o check (fun th ->
        length(fst(strip_forall(concl th))) = 1 && tab_has_const "drv_apart" (concl th))) THEN
      REWRITE_TAC[ARITH_RULE `42 + 1 = 43`] THEN
      ASM_SIMP_TAC[TAB_SLOTS_STK];
      X_GEN_TAC `j'':num` THEN DISCH_TAC THEN MATCH_MP_TAC DRV_APART_IN THEN
      MAP_EVERY EXISTS_TAC [`ctl:int64`; `8 * nctl`] THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
      ASM_MESON_TAC[]];
    UNDISCH_TAC `ALL (tab_mem tb inp bw (m:int64->byte) (s:S)) L` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN X_GEN_TAC `d:tabdesc` THEN DISCH_TAC THEN
    ASM_CASES_TAC `d:tabdesc = d0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `?jm wd. d = MarkTab jm j c wd` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `jm:num` (X_CHOOSE_THEN `wd:num` SUBST_ALL_TAC)) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `tab_avoid d j c` ASSUME_TAC THENL
     [MATCH_MP_TAC TAB_AVOID_WF THEN
      MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `d0:tabdesc`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`d:tabdesc`; `tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
                                  (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
                   `inp:num list`; `bw:num->int64`; `m':int64->byte`; `j:num`; `c:num`; `s:S`; `s':S`]
                  TAB_MEM_FRAME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC TAB_MEM_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `j':num` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `MEM (j':num) (tab_slots L) /\ ~(j' = 42) /\ ~MEM j' (tab_dslots d0)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL [ASM_MESON_TAC[TAB_SLOTS_DESC];
      FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_wf]) THEN ASM_MESON_TAC[TAB_STK_NOT_DESC];ALL_TAC] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(d:tabdesc = d0)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC TAB_SLOTS_DISJOINT THEN
      MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `j':num`] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_wf]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LT_IMP_LE THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o GSYM o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `tab_slots`)) (concl th) && can (find_term ((=) `drv_in`)) (concl th) &&
        can (find_term ((=) `m':int64->byte`)) (concl th))) THEN
      EXISTS_TAC `j':num` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC PL_STK_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `L:tabdesc list` TAB_SLOTS_STK) THEN STRIP_TAC THEN
    SUBGOAL_THEN `~MEM 40 (tab_dslots d0)` ASSUME_TAC THENL
     [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_wf]) THEN ASM_MESON_TAC[TAB_STK_NOT_DESC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LT_IMP_LE THEN
      SUBGOAL_THEN `val(bw 40:int64) + val(bw(40 + 1):int64) < 2 EXP 64` MP_TAC THENL
       [ASM_SIMP_TAC[]; CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[]];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `tab_slots`)) (concl th) && can (find_term ((=) `drv_in`)) (concl th) &&
        can (find_term ((=) `m':int64->byte`)) (concl th))) THEN
      EXISTS_TAC `40` THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[ARITH_EQ]]]);;

let TAB_KEY_AFTER = prove
 (`!L bw ctl nctl budget cfr st m used t k u j prog.
     tab_layout L bw ctl nctl cfr /\
     MEM j (tab_slots L) /\ MEM (j + 2) (tab_slots L) /\ MEM (j + 4) (tab_slots L) /\
     drv_child bw ctl budget cfr st m used t /\
     val(EL 1 st) = j /\ val(EL 2 st) = j + 2 /\ val(EL 3 st) = j + 4 /\ val(EL 17 st) < nctl /\
     tisa_leaf_wf prog /\ tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
     ==> (!r. r < 3 ==> tisa_base u r = bw(j + 2 * r) /\ tisa_len u r = bw(j + 2 * r + 1)) /\
         (!r a. r < 3 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1)))
                ==> tmem u a = drv_after ctl st u a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `j:num`] TAB_I16_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. r < 3 ==> MEM (j + 2 * r) (tab_slots L)` ASSUME_TAC THENL
   [TAB_I16_SLOTS_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[tisa_base; tisa_len] THEN
    MP_TAC(SPECL [`prog:tisa_prog`; `t:tisa_state`; `k:num`; `u:tisa_state`; `2 * r`] PL_RUN_FRAME) THEN
    MP_TAC(SPECL [`prog:tisa_prog`; `t:tisa_state`; `k:num`; `u:tisa_state`; `2 * r + 1`] PL_RUN_FRAME) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM tisa_base; GSYM tisa_len] THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[drv_after] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
    MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j + 2 * r`;
                  `val(EL 17 (st:int64 list))`; `a:int64`] TAB_SLOT_ADDR) THEN
    ASM_SIMP_TAC[GSYM ADD_ASSOC] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`ctl:int64`; `8 * val(EL 17 (st:int64 list))`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    UNDISCH_TAC `~drv_in (a:int64) (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8` THEN
    ASM_REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC]);;

let HOL_WALK_SLOTS = prove
 (`MEM 6 (tab_slots hol_layout) /\ MEM 8 (tab_slots hol_layout) /\ MEM 10 (tab_slots hol_layout)`,
  MP_TAC(MATCH_MP TAB_DESC_SLOTS (el 1 (CONJUNCTS HOL_LAYOUT_MEMS))) THEN
  REWRITE_TAC[tab_dslots;ALL] THEN CONV_TAC NUM_REDUCE_CONV);;

let TAB_WALK_CHILD_ROWS = prove
 (`!inp bw ctl nctl budget cfr m used cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t.
     tab_rel hol_tables hol_layout inp bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     (!i. i < LENGTH dbs ==> FST(EL i dbs) < 8) /\
     drv_child bw ctl budget cfr (EL 8 pl_plan_abs) m used t
     ==> intern_ok t /\ bw_rows t (val(intern_count t)) = dbs`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[tab_rel] o check (is_const_app "tab_rel" o concl)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `KeyTab 6` o REWRITE_RULE[GSYM ALL_MEM] o
    check (fun th -> is_const_app "ALL" (concl th) && tab_has_const "tab_mem" (concl th))) THEN
  ASM_SIMP_TAC[HOL_LAYOUT_MEMS;TAB_WALK_DB_MEM] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`hol_layout:tabdesc list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;
    `cfr:int64`;`EL 8 pl_plan_abs:int64 list`;`m:int64->byte`;`used:int64`;`t:tisa_state`;`6`] TAB_I16_CHILD) THEN
  ASM_REWRITE_TAC[ABS_PLAN_BINDING;HOL_WALK_SLOTS;MAP] THEN CONV_TAC STEP_EL_CONV2 THEN
  ASM_REWRITE_TAC[HOL_WALK_SLOTS;ABS_PLAN_BINDING] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`6`;`m:int64->byte`;`dbs:(num#num#num)list`;`t:tisa_state`] PL_ITAB_STATE) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LIST_EQ;LENGTH_BW_ROWS] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_BW_ROWS;bw_row]);;

let TAB_WALK_CHILD_ARGS = prove
 (`!inp bw ctl nctl budget cfr m used cw (s:nstate) stk t.
     tab_rel hol_tables hol_layout inp bw ctl nctl cfr m (cw,s,stk) /\ 32 < nctl /\
     drv_child bw ctl budget cfr (EL 8 pl_plan_abs) m used t
     ==> val(tisa_fword t 22) = cw 28 /\ val(tisa_fword t 23) = cw 29 /\
         val(tregs t 1) = cw 31 /\ tisa_fword t 21 = used /\ tisa_fword t 20 = budget`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[tab_rel] o check (is_const_app "tab_rel" o concl)) THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;
    `EL 8 pl_plan_abs:int64 list`;`m:int64->byte`;`used:int64`;`t:tisa_state`;`cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN SUBGOAL_THEN
     `f = 10 \/ f = 11 \/ f = 12 \/ f = 13 \/ f = 14 \/ f = 15 \/ f = 16 \/ f = 17` MP_TAC THENL
     [ASM_ARITH_TAC;DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
      REWRITE_TAC[ABS_PLAN_BINDING;MAP] THEN CONV_TAC STEP_EL_CONV2 THEN ASM_ARITH_TAC];
    REWRITE_TAC[ABS_PLAN_BINDING;MAP] THEN CONV_TAC STEP_EL_CONV2 THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `1` o check (fun th ->
      is_forall(concl th) && can(find_term ((=) `tregs t`)) (concl th))) THEN
    CONV_TAC STEP_EL_CONV2 THEN ASM_REWRITE_TAC[]]);;

let TAB_WALK_KEEPS = prove
 (`!bw ctl nctl budget cfr m used t k u a.
     drv_child bw ctl budget cfr (EL 8 pl_plan_abs) m used t /\
     tisa_entry_ok bind_walk t /\ tisa_run bind_walk t = TStop k u /\
     val ctl + 8 * nctl <= 2 EXP 64 /\ 32 < nctl /\ ~drv_stack cfr a /\
     ~drv_in a (word_add ctl (word(8 * 32))) 8 /\
     (!j. MEM j [6;8;10;42] ==> ~drv_in a (bw j) (val(bw(j+1))))
     ==> drv_after ctl (EL 8 pl_plan_abs) u a = m a`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC DRV_STEP_KEEPS THEN
  MAP_EVERY EXISTS_TAC [`bind_walk:tisa_prog`;`bw:num->int64`;`nctl:num`;`budget:int64`;
    `cfr:int64`;`used:int64`;`t:tisa_state`;`k:num`] THEN
  ASM_REWRITE_TAC[BIND_WALK_LEAF_WF;BIND_WALK_RW;ABS_PLAN_BINDING;MAP] THEN
  CONV_TAC STEP_EL_CONV2 THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ALL_TAC; ACCEPT_TAC(REWRITE_RULE[ARITH_RULE `8 * 32 = 256`]
     (ASSUME `~drv_in a (word_add ctl (word(8 * 32))) 8`))] THEN
  X_GEN_TAC `r:num` THEN
  REWRITE_TAC[ARITH_RULE `r < 4 <=> r = 0 \/ r = 1 \/ r = 2 \/ r = 3`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[drv_base;drv_len] THEN CONV_TAC STEP_EL_CONV2 THEN
  W(fun (asl,w) ->
    let slot = rand(el 1 (snd(strip_comb(dest_neg w)))) in
    let frame = snd(find (fun (_,th) -> is_forall(concl th) &&
       tab_has_const "MEM" (concl th) && tab_has_const "drv_in" (concl th)) asl) in
    MP_TAC(SPEC slot frame)) THEN
  REWRITE_TAC[MEM] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let TAB_WALK_OUT_VIEWS = prove
 (`!bw ctl nctl budget cfr m used t k u.
     tab_layout hol_layout bw ctl nctl cfr /\ 32 < nctl /\
     drv_child bw ctl budget cfr (EL 8 pl_plan_abs) m used t /\
     tisa_entry_ok bind_walk t /\ tisa_run bind_walk t = TStop k u
     ==> (!r. r < 3 ==> tisa_base u r = bw(6 + 2 * r) /\ tisa_len u r = bw(6 + 2 * r + 1)) /\
         (!r a. r < 3 /\ drv_in a (bw(6 + 2 * r)) (val(bw(6 + 2 * r + 1)))
                ==> tmem u a = drv_after ctl (EL 8 pl_plan_abs) u a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`hol_layout:tabdesc list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;
    `cfr:int64`;`EL 8 pl_plan_abs:int64 list`;`m:int64->byte`;`used:int64`;`t:tisa_state`;
    `k:num`;`u:tisa_state`;`6`;`bind_walk:tisa_prog`] TAB_KEY_AFTER) THEN
  ASM_REWRITE_TAC[ABS_PLAN_BINDING;MAP;BIND_WALK_LEAF_WF] THEN CONV_TAC STEP_EL_CONV2 THEN
  ASM_REWRITE_TAC[HOL_WALK_SLOTS;ABS_PLAN_BINDING;MAP]);;

let TAB_WALK_UPDATE = prove
 (`!inp bw ctl nctl budget cfr m used cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t k u.
     tab_rel hol_tables hol_layout inp bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     32 < nctl /\ drv_child bw ctl budget cfr (EL 8 pl_plan_abs) m used t /\
     tisa_entry_ok bind_walk t /\ tisa_run bind_walk t = TStop k u /\ intern_ok u
     ==> tab_rel hol_tables hol_layout inp bw ctl nctl cfr (drv_after ctl (EL 8 pl_plan_abs) u)
          (pl_set cw 32 (val(tisa_fword u 19)),
           (ctx,nms,tys,ntms,bw_rows u (val(intern_count u)),ths,nmap,ymap,drops,pol),stk)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_LAYOUT o check (is_const_app "tab_rel" o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[tab_rel] o check (is_const_app "tab_rel" o concl)) THEN
  ASSUME_TAC(el 1 (CONJUNCTS HOL_LAYOUT_MEMS)) THEN TAB_DESC_TAC `KeyTab 6` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[hol_tables;tab_mem] o
    check (fun th -> is_const_app "tab_mem" (concl th) && rand(concl th) = `KeyTab 6`)) THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;
    `m:int64->byte`;`used:int64`;`t:tisa_state`;`k:num`;`u:tisa_state`] TAB_WALK_OUT_VIEWS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC TAB_REL_UPDATE_WORK THEN
  MAP_EVERY EXISTS_TAC [`m:int64->byte`;`(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`;
                       `KeyTab 6`;`6`;`10`] THEN
  ASM_REWRITE_TAC[HOL_LAYOUT_WF;TAB_WALK_DB_FRAME;tab_table;distinctness "tabdesc";ARITH_RULE `6 + 4 = 10 /\ 6 < 32`;ARITH_EQ] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TAB_WALK_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`;`nctl:num`;`budget:int64`;`cfr:int64`;`used:int64`;`t:tisa_state`;`k:num`] THEN
    ASM_REWRITE_TAC[MEM;tab_dslots;ARITH_RULE `6+2=8 /\ 6+4=10`;ARITH_EQ] THEN
    X_GEN_TAC `j':num` THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    CONV_TAC NUM_REDUCE_CONV THEN TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
    W(fun (asl,w) ->
      let slot = rand(el 1 (snd(strip_comb(dest_neg w)))) in
      let frame = snd(find (fun (_,th) -> is_forall(concl th) &&
        tab_has_const "tab_dslots" (concl th) && tab_has_const "drv_in" (concl th)) asl) in
      MP_TAC(SPEC slot frame)) THEN
    REWRITE_TAC[tab_dslots;MEM] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    REWRITE_TAC[drv_after;ABS_PLAN_BINDING;MAP] THEN CONV_TAC STEP_EL_CONV2 THEN
    REWRITE_TAC[DRV_WORD_WRITE_SAME];
    SUBGOAL_THEN `!i. i < LENGTH(bw_rows u (val(intern_count u)))
                       ==> FST(EL i (bw_rows u (val(intern_count u)))) < 8` ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_BW_ROWS] THEN SIMP_TAC[EL_BW_ROWS;bw_row;FST;MOD_LT_EQ;ARITH_EQ];
      ASM_SIMP_TAC[TAB_WALK_DB_MEM] THEN MATCH_MP_TAC BW_ITAB_OF_STATE THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[hol_layout;hol_layout_old;APPEND;MEM;injectivity "tabdesc";distinctness "tabdesc"] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let PL_ABS_WALK_POST = prove
 (`!ctx nms tys dbs s k u name ty body x TY TB.
     pl_tabs_ok ctx nms tys dbs /\ intern_ok s /\
     bw_rows s (val(intern_count s)) = dbs /\
     bw_ctx nms tys name ty TY /\ EL name nms = x /\ fddb nms tys dbs body TB /\
     val(tisa_fword s 22) = name /\ val(tisa_fword s 23) = ty /\ val(tregs s 1) = body /\
     bw_result s k u /\ bw_rows_valid nms tys (bw_rows u (val(intern_count u)))
     ==> ?md. bw_rows u (val(intern_count u)) = APPEND dbs md /\
         (~(k = 1) ==> md = []) /\ intern_ok u /\
         pl_tabs_ok ctx nms tys (APPEND dbs md) /\
         (k = 1 ==> fddb nms tys (APPEND dbs md) (val(tisa_fword u 19))
                       (hdbAbs TY (hbind (x,TY) 0 TB)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`s:tisa_state`;`k:num`;`u:tisa_state`] BW_RESULT_ROWS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `md:(num#num#num)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `md:(num#num#num)list` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_result] o
    check (fun th -> concl th = `bw_result s k u`)) THEN
  SUBGOAL_THEN `intern_ok u` ASSUME_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_tabs_ok;nat_keys] o
     check (is_const_app "pl_tabs_ok" o concl)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_rows_valid;BW_KEY_OK_HOL] o
     check (is_const_app "bw_rows_valid" o concl)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP BW_ROWS_DISTINCT o check (fun th -> concl th = `intern_ok u`)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP BW_ROWS_COUNT_BOUND o check (fun th -> concl th = `intern_ok u`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `bw_rows u (val(intern_count u)) = APPEND dbs md`]) THEN
    ASM_REWRITE_TAC[pl_tabs_ok;nat_keys;ASSUME `bw_rows u (val(intern_count u)) = APPEND dbs md`] THEN MESON_TAC[];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      tab_has_const "bw_final" (concl th))) THEN ASM_REWRITE_TAC[bw_final] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`nms:string list`;`tys:(num#num#num)list`;`TY:holtype`;`TB:hdbterm`] o
      check (fun th -> is_forall(concl th) && tab_has_const "hdbAbs" (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* The driver's binding-walk call with the checker table relation. *)
let TAB_ABS_WALK_RUN = prove
 (`!inp bw ctl nctl budget cfr m used cw ctx nms tys ntms dbs ths nmap ymap drops pol stk
      v b x ty body st k u.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     tab_rel hol_tables hol_layout inp bw ctl nctl cfr m
       (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     fdtm nms tys ntms v (TmVar x ty) /\ fdtm nms tys ntms b body /\
     cw 28 = FST(SND(EL v ntms)) /\ cw 29 = ntm_ty(EL v ntms) /\ cw 31 = ntm_db(EL b ntms) /\
     32 < nctl /\ drv_child bw ctl budget cfr (EL 8 pl_plan_abs) m used st /\
     tisa_entry_ok bind_walk st /\ tisa_run bind_walk st = TStop k u
     ==> ?md.
         tab_rel hol_tables hol_layout inp bw ctl nctl cfr (drv_after ctl (EL 8 pl_plan_abs) u)
           (pl_set cw 32 (val(tisa_fword u 19)),
            (ctx,nms,tys,ntms,APPEND dbs md,ths,nmap,ymap,drops,pol),stk) /\
         (~(k = 1) ==> md = []) /\
         pl_tabs_ok ctx nms tys (APPEND dbs md) /\
         (k = 1 ==> fddb nms tys (APPEND dbs md) (val(tisa_fword u 19))
                       (hdbAbs ty (hbind (x,ty) 0 (hdb body)))) /\
         tisa_fword u 18 = word k /\ (k = 1 \/ k = 2 \/ k = 3 \/ k = 4) /\
         val used <= val(tisa_fword u 21) /\ val(tisa_fword u 21) <= val budget`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL ([`cw:num->num`] @ pl_ns_vars @
    [`stk:num list`;`v:num`;`b:num`;`x:string`;`ty:holtype`;`body:holterm`]) PL_ABS_WALK_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN PL_ROWS_TAC THEN
  MP_TAC(SPECL([`inp:num list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;
                `m:int64->byte`;`used:int64`;`cw:num->num`] @ pl_ns_vars @
                [`stk:num list`;`st:tisa_state`]) TAB_WALK_CHILD_ROWS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`inp:num list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;
    `m:int64->byte`;`used:int64`;`cw:num->num`;
    `(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`;`stk:num list`;`st:tisa_state`] TAB_WALK_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `bwt_input nms tys st` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bwt_input] THEN MAP_EVERY EXISTS_TAC [`ty:holtype`;`hdb body`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`st:tisa_state`;`k:num`;`u:tisa_state`] BIND_WALK_TABLE_RUN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  PL_INV_ASM(fun inv -> ASSUME_TAC(MATCH_MP PL_TABS_OK inv)) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && tab_has_const "bw_rows_valid" (concl th) &&
       tab_has_const "bwt_input" (concl th) then
      ASSUME_TAC(MATCH_MP (SPECL [`nms:string list`;`tys:(num#num#num)list`] th)
        (ASSUME `bwt_input nms tys st`))
    else failwith "binding-walk row postcondition") THEN
  MP_TAC(SPECL [`ctx:hupdate list`;`nms:string list`;`tys:(num#num#num)list`;
    `dbs:(num#num#num)list`;`st:tisa_state`;`k:num`;`u:tisa_state`;
    `FST(SND(EL v (ntms:(num#num#num#num#num)list)))`;`ntm_ty(EL v ntms)`;`ntm_db(EL b ntms)`;
    `x:string`;`ty:holtype`;`hdb body`] PL_ABS_WALK_POST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `md:(num#num#num)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `md:(num#num#num)list` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL([`inp:num list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;
                `m:int64->byte`;`used:int64`;`cw:num->num`] @ pl_ns_vars @
                [`stk:num list`;`st:tisa_state`;`k:num`;`u:tisa_state`]) TAB_WALK_UPDATE) THEN
  ASM_REWRITE_TAC[]);;
