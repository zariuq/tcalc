(* ========================================================================= *)
(* append_row over the interface. An interface appends as its laws say     *)
(* (tab_app_ok): the count at c grows by one, the new row is the row given, *)
(* the rows below it are kept, and nothing else changes (tab_frame). Then   *)
(* append_row on a row table of a well-formed layout implements its        *)
(* meaning (TAB_IMPL_APPEND): FIRED, the table and its marks hold one more *)
(* row; otherwise only the payload word changes.                            *)
(*                                                                           *)
(* Loaded after tables_update.ml and tables_leaves.ml.                       *)
(* ========================================================================= *)

let tab_app_ok = new_definition
 `tab_app_ok ((trow,tn,twd,tdrop,tapp,tput):(num->S->num->num list)#(num->S->num)#(num->num)#
                                        (num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) <=>
    !j c s r s'. tapp j c s r s'
                 ==> tn c s' = tn c s + 1 /\ trow j s' (tn c s) = r /\
                     (!i. i < tn c s ==> trow j s' i = trow j s i) /\
                     tab_frame (trow,tn,twd,tdrop,tapp,tput) j c s s'`;;

(* The memory after a step, in a described slot bound to the step's region *)
(* r: the leaf's words.                                                      *)
let TAB_AFTER_WORD = prove
 (`!L bw ctl nctl budget cfr st m used t prog k u r j i.
     tab_layout L bw ctl nctl cfr /\ drv_child bw ctl budget cfr st m used t /\
     tisa_leaf_wf prog /\ tisa_entry_ok prog t /\ tisa_run prog t = TStop k u /\
     r < 9 /\ val(EL (1 + r) st) = j /\ MEM j (tab_slots L) /\ 8 * i + 8 <= val(bw(j + 1)) /\
     val(EL 17 st) < nctl
     ==> pl_mw (drv_after ctl st u) (bw j) i = val(pl_w u r i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `r:num`; `j:num`] PL_CHILD_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `tisa_base u r = (bw:num->int64) j` ASSUME_TAC THENL
   [REWRITE_TAC[tisa_base] THEN
    MP_TAC(SPECL [`prog:tisa_prog`; `t:tisa_state`; `k:num`; `u:tisa_state`; `2 * r`] PL_RUN_FRAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[GSYM tisa_base];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pl_mw; pl_w; tisa_read; GSYM drv_word] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  REWRITE_TAC[drv_after] THEN MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`]
               TAB_LAYOUT_SLOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  MP_TAC(SPECL [`ctl:int64`; `8 * val(EL 17 (st:int64 list))`] TISA_VAL_OFFSET) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`bw(j:num):int64`; `8 * i`; `q:num`] PL_ADDR_VAL) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `drv_apart (bw(j:num)) (val(bw(j + 1):int64)) ctl (8 * nctl)` THEN
  REWRITE_TAC[drv_apart] THEN ASM_ARITH_TAC);;

(* A row table read through a function that agrees on its rows' words. *)
let PL_RTAB_CONG = prove
 (`!bw jr jc wd m f g n.
     (!i w. i < n /\ w < wd ==> f i w = g i w)
     ==> (pl_rtab bw jr jc wd m f n <=> pl_rtab bw jr jc wd m g n)`,
  REWRITE_TAC[pl_rtab] THEN MESON_TAC[]);;

(* A row table in a memory whose count word and row-region words are       *)
(* another's.                                                               *)
let PL_RTAB_WORDS = prove
 (`!bw jr jc wd m m' f n.
     pl_rtab bw jr jc wd m f n /\ pl_mw m' (bw jc) 0 = pl_mw m (bw jc) 0 /\
     (!x. 8 * x + 8 <= val(bw(jr + 1)) ==> pl_mw m' (bw jr) x = pl_mw m (bw jr) x)
     ==> pl_rtab bw jr jc wd m' f n`,
  REWRITE_TAC[pl_rtab] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `8 * (wd * i + w) + 8 <= val(bw(jr + 1):int64)` (fun th -> ASM_SIMP_TAC[th]) THEN
  MP_TAC(SPECL [`wd:num`; `i:num`; `w:num`; `n:num`] PL_ROW_WORD_BOUND) THEN ASM_ARITH_TAC);;

(* A word of the five a step offers an appended row. *)
let TAB_EL5_VAL = prove
 (`!w (x0:int64) x1 x2 x3 x4.
     w < 5 ==> val(EL w [x0; x1; x2; x3; x4]) = EL w [val x0; val x1; val x2; val x3; val x4]`,
  REWRITE_TAC[ARITH_RULE `w < 5 <=> w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* The marks of a table one row longer, the new id live. *)
let TAB_MARKS_EXTEND = prove
 (`!m (b:int64) len n (dr:num->bool).
     8 * (n + 1) <= len /\ 8 * n <= len /\
     (!i. i < n ==> (pl_mw m b i = 0 <=> ~dr i)) /\
     (!i. n <= i /\ 8 * i + 8 <= len ==> pl_mw m b i = 0) /\ (!i. n <= i ==> ~dr i)
     ==> (!i. i < n + 1 ==> (pl_mw m b i = 0 <=> ~dr i)) /\
         (!i. n + 1 <= i /\ 8 * i + 8 <= len ==> pl_mw m b i = 0) /\ (!i. n + 1 <= i ==> ~dr i)`,
  REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC `i < n:num` THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `i = n:num` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `pl_mw m (b:int64) n = 0` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        is_eq(rand(snd(dest_forall(concl th)))))) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        is_neg(rand(snd(dest_forall(concl th)))))) THEN ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        is_eq(rand(snd(dest_forall(concl th)))))) THEN ASM_ARITH_TAC;
    ASM_MESON_TAC[ARITH_RULE `n + 1 <= i ==> n <= i`]]);;

(* ------------------------------------------------------------------------- *)
(* The bridge.                                                               *)
(* ------------------------------------------------------------------------- *)

(* The memory after the step at slot j, word i, bound to the step's region  *)
(* r, from the TAB_AFTER_WORD assumption.                                    *)
let TAB_AFTER_TAC r j i =
  FIRST_ASSUM(MP_TAC o SPECL [r; j; i] o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `drv_after`)) (concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

(* For marks jm of the table at j, c: jm is a described slot apart from j  *)
(* and c, and the memory after the step agrees with m there.               *)
let TAB_MARKS_AT_TAC wd' =
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_wf]) THEN
  SUBGOAL_THEN `~(jm:num = j) /\ ~(jm:num = c)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN
    (SUBGOAL_THEN (subst [wd',`wd':num`] `MarkTab jm j c wd' = RowTab j c wd'`) MP_TAC THENL
     [MATCH_MP_TAC TAB_SLOTS_DISJOINT THEN MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `jm:num`] THEN
      ASM_REWRITE_TAC[tab_dslots; MEM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[distinctness "tabdesc"; GSYM(distinctness "tabdesc")]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `MEM (jm:num) (tab_slots L)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`L:tabdesc list`; subst [wd',`wd':num`] `MarkTab jm j c wd'`] TAB_DESC_SLOTS) THEN
    ASM_REWRITE_TAC[tab_dslots; ALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. drv_in a (bw(jm:num)) (val(bw(jm + 1):int64)) ==> drv_after ctl st u a = (m:int64->byte) a`
    ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_stack`)) (concl th) && can (find_term ((=) `drv_after`)) (concl th))) THEN
    MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `jm:num`;
                  `val(EL 17 (st:int64 list))`; `a:int64`] TAB_SLOT_ADDR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC DRV_APART_IN THEN
    MAP_EVERY EXISTS_TAC [`bw(jm:num):int64`; `val(bw(jm + 1):int64)`] THEN ASM_REWRITE_TAC[] THEN
    DISJ1_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      let vs,_ = strip_forall(concl th) in length vs = 2 && can (find_term ((=) `drv_apart`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC];;

let TAB_IMPL_APPEND = prove
 (`!(trow:num->S->num->num list) (tn:num->S->num) (twd:num->num) (tdrop:num->S->num->bool)
    (tapp:num->num->S->num list->S->bool) (tput:num->num->S->num->num->num->S->bool) L inp progs bw ctl nctl budget cfr st j c wd.
     progs 6 = append_row /\ val(EL 0 st) = 6 /\ val(EL 1 st) = j /\ val(EL 2 st) = c /\
     MEM (RowTab j c wd) L /\ tab_wf L /\ tab_app_ok (trow,tn,twd,tdrop,tapp,tput) /\ twd j = wd /\
     1 <= wd /\ wd <= 5 /\ (!s r. LENGTH r = wd ==> ?s'. tapp j c s r s') /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tab_impl (tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr) (trow,tn,twd,tdrop,tapp,tput) inp
                  progs bw ctl budget cfr st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tab_impl; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:int64->byte`; `used:int64`; `cw:num->num`; `s:S`; `stk:num list`;
                       `t:tisa_state`; `k:num`; `u:tisa_state`] THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_rel]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  TAB_DESC_TAC `RowTab j c wd` THEN
  (* the step's width word is the table's: the leaf is enabled *)
  SUBGOAL_THEN `(cw:num->num)(val(EL 12 (st:int64 list))) = wd` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "tab_leaf" (concl th))) THEN
    REWRITE_TAC[tab_leaf; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[tab_append] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(EL 17 (st:int64 list)) < nctl` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) && can (find_term ((=) `10`)) (concl th))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  (* the child's arguments, width, regions and count word *)
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `1` o check (fun th -> is_forall(concl th) && can (find_term ((=) `tregs`)) (concl th))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `0`; `j:num`] PL_CHILD_REGION) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `c:num`] PL_CHILD_REGION) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `c:num`; `0`] TAB_CHILD_W) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_rtab] o check (fun th -> is_const_app "pl_rtab" (concl th))) THEN
  (* the memory after the step: m off the stack, the two regions and the payload word; the leaf's words in them *)
  SUBGOAL_THEN `!a. ~drv_stack cfr a /\ ~drv_in a (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8 /\
                    ~drv_in a (bw(j:num)) (val(bw(j + 1):int64)) /\ ~drv_in a (bw(c:num)) (val(bw(c + 1):int64))
                    ==> drv_after ctl st u a = (m:int64->byte) a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`append_row`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                          `used:int64`; `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[APPEND_ROW_LEAF_WF; APPEND_ROW_DECLS; tisa_rw; LENGTH] THEN
    X_GEN_TAC `r:num` THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `r < 2 <=> r = 0 \/ r = 1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `append_row`; `k:num`;
                `u:tisa_state`] TAB_AFTER_WORD) THEN
  ASM_REWRITE_TAC[APPEND_ROW_LEAF_WF] THEN DISCH_TAC THEN
  (* the leaf's specification, by whether the row fits *)
  MP_TAC PL_APPEND_ROW_SPEC THEN REWRITE_TAC[pl_append_row_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o CONJUNCT2 o CONJUNCT2)
                             (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `8 * wd * ((tn:num->S->num) c (s:S) + 1) <= val(bw(j + 1):int64)` THEN ASM_REWRITE_TAC[] THENL
   [(* FIRED: the row is appended *)
    DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k = 1`)) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`s:S`; `tab_row (cw:num->num) (st:int64 list) wd`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `tapp:num->num->S->num list->S->bool`)) (concl th))) THEN
    ANTS_TAC THENL [REWRITE_TAC[tab_row; LENGTH_LIST_OF_SEQ]; DISCH_THEN(X_CHOOSE_TAC `s':S`)] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`j:num`; `c:num`; `s:S`; `tab_row (cw:num->num) (st:int64 list) wd`; `s':S`] o
      REWRITE_RULE[tab_app_ok] o check (fun th -> is_const_app "tab_app_ok" (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(tn:num->S->num) c s + 1 < 2 EXP 60` ASSUME_TAC THENL
     [SUBGOAL_THEN `(8 * wd) * ((tn:num->S->num) c s + 1) < (8 * wd) * 2 EXP 60` MP_TAC THENL
       [REWRITE_TAC[GSYM MULT_ASSOC] THEN ASM_ARITH_TAC; REWRITE_TAC[LT_MULT_LCANCEL] THEN ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`1`; `s':S`] THEN REPEAT CONJ_TAC THENL
     [TAB_LEAF_AT_TAC THEN REWRITE_TAC[tab_append] THEN ASM_REWRITE_TAC[];
      ARITH_TAC;
      REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(tn:num->S->num) c s = val(tisa_fword u 19)` (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC TAB_REL_UPDATE THEN
    MAP_EVERY EXISTS_TAC [`m:int64->byte`; `s:S`; `RowTab j c wd`; `j:num`; `c:num`] THEN
    ASM_REWRITE_TAC[tab_table] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[tab_dslots; MEM] THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `drv_stack`)) (concl th) && can (find_term ((=) `drv_after`)) (concl th))) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [(* the table, one row longer *)
      REWRITE_TAC[tab_mem] THEN ASM_REWRITE_TAC[pl_rtab] THEN REPEAT CONJ_TAC THENL
       [TAB_AFTER_TAC `1` `c:num` `0` THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC PL_VAL_WORD_LT THEN ASM_ARITH_TAC;
        REPEAT STRIP_TAC THEN TAB_AFTER_TAC `0` `j:num` `wd * i + w` THEN
        ANTS_TAC THENL
         [MP_TAC(SPECL [`wd:num`; `i:num`; `w:num`; `(tn:num->S->num) c s + 1`] PL_ROW_WORD_BOUND) THEN
          ASM_ARITH_TAC;
          DISCH_THEN SUBST1_TAC] THEN
        ASM_CASES_TAC `i < (tn:num->S->num) c s` THENL
         [SUBGOAL_THEN `wd * i + w < wd * (tn:num->S->num) c s` ASSUME_TAC THENL
           [MP_TAC(SPECL [`wd:num`; `i:num`; `w:num`; `(tn:num->S->num) c s`] PL_ROW_WORD_BOUND) THEN
            ASM_ARITH_TAC;
            ALL_TAC] THEN
          ASM_SIMP_TAC[] THEN
          MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                        `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `0`; `j:num`;
                        `wd * i + w`] TAB_CHILD_W) THEN
          CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
          ANTS_TAC THENL
           [MP_TAC(SPECL [`wd:num`; `i:num`; `w:num`; `(tn:num->S->num) c s`] PL_ROW_WORD_BOUND) THEN
            ASM_ARITH_TAC;
            STRIP_TAC THEN ASM_SIMP_TAC[]];
          SUBGOAL_THEN `i = (tn:num->S->num) c s` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[] THEN
          SUBGOAL_THEN `w < 5` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[TAB_EL5_VAL; tab_row; EL_LIST_OF_SEQ] THEN
          ASM_SIMP_TAC[ARITH] THEN CONV_TAC NUM_REDUCE_CONV];
        REPEAT STRIP_TAC THEN ASM_CASES_TAC `i < (tn:num->S->num) c s` THENL
         [ASM_SIMP_TAC[];
          SUBGOAL_THEN `i = (tn:num->S->num) c s` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          ASM_REWRITE_TAC[tab_row; LENGTH_LIST_OF_SEQ]]];
      ALL_TAC] THEN
    (* its marks, the new id live *)
    MAP_EVERY X_GEN_TAC [`jm:num`; `wd':num`] THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_wf]) THEN
    SUBGOAL_THEN `wd':num = wd` SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `RowTab j c wd' = RowTab j c wd` MP_TAC THENL
       [MATCH_MP_TAC TAB_SLOTS_DISJOINT THEN MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `j:num`] THEN
        ASM_REWRITE_TAC[tab_dslots; MEM] THEN ASM_MESON_TAC[];
        REWRITE_TAC[injectivity "tabdesc"] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    TAB_MARKS_AT_TAC `wd:num` THEN
    TAB_DESC_TAC `MarkTab jm j c wd` THEN
    SUBGOAL_THEN `!i. 8 * i + 8 <= val(bw(jm + 1):int64)
                      ==> pl_mw (drv_after ctl st u) (bw jm) i = pl_mw (m:int64->byte) (bw jm) i` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MW_REGION THEN EXISTS_TAC `val(bw(jm + 1):int64)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LT_IMP_LE THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(tdrop:num->S->num->bool) jm s' = tdrop jm s` SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o REWRITE_RULE[tab_frame] o check (fun th -> is_const_app "tab_frame" (concl th))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `8 * ((tn:num->S->num) c s + 1) <= val(bw(jm + 1):int64)` ASSUME_TAC THENL
     [SUBGOAL_THEN `wd * (8 * ((tn:num->S->num) c s + 1)) <= wd * val(bw(jm + 1):int64)` MP_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `val(bw(j + 1):int64)` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `8 * wd * ((tn:num->S->num) c s + 1) <= val(bw(j + 1):int64)` THEN ARITH_TAC;
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:int64->byte`; `bw(jm:num):int64`; `val(bw(jm + 1):int64)`; `(tn:num->S->num) c s`;
                   `(tdrop:num->S->num->bool) jm s`] TAB_MARKS_EXTEND) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `8 * i + 8 <= val(bw(jm + 1):int64)` (fun th -> ASM_SIMP_TAC[th]) THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]];
    (* not FIRED: only the payload word changes *)
    DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k = 2`)) THEN
    MAP_EVERY EXISTS_TAC [`2`; `s:S`] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL [TAB_LEAF_AT_TAC THEN REWRITE_TAC[tab_append] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TAB_REL_UPDATE THEN
    MAP_EVERY EXISTS_TAC [`m:int64->byte`; `s:S`; `RowTab j c wd`; `j:num`; `c:num`] THEN
    ASM_REWRITE_TAC[tab_table; tab_frame; tab_dslots; MEM] THEN REPEAT CONJ_TAC THENL
     [MESON_TAC[];
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `drv_stack`)) (concl th) && can (find_term ((=) `drv_after`)) (concl th))) THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME];
      REWRITE_TAC[tab_mem] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PL_RTAB_WORDS THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[pl_rtab] THEN CONJ_TAC THENL
       [TAB_AFTER_TAC `1` `c:num` `0` THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `x:num` THEN DISCH_TAC THEN TAB_AFTER_TAC `0` `j:num` `x:num` THEN DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[] THEN
        MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                      `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `0`; `j:num`;
                      `x:num`] TAB_CHILD_W) THEN
        CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`jm:num`; `wd':num`] THEN DISCH_TAC THEN
      TAB_MARKS_AT_TAC `wd':num` THEN
      MATCH_MP_TAC TAB_MEM_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o SPEC `MarkTab jm j c wd'` o REWRITE_RULE[GSYM ALL_MEM] o
          check (fun th -> is_const_app "ALL" (concl th) && tab_has_const "tab_mem" (concl th))) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[tab_dslots; ALL] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LT_IMP_LE THEN ASM_SIMP_TAC[]]]]);;

(* Every theorem this file states, for the audits. *)
let tables_append_theorems =
 ["TAB_AFTER_WORD", TAB_AFTER_WORD; "PL_RTAB_CONG", PL_RTAB_CONG; "PL_RTAB_WORDS", PL_RTAB_WORDS;
  "TAB_EL5_VAL", TAB_EL5_VAL; "TAB_MARKS_EXTEND", TAB_MARKS_EXTEND; "TAB_IMPL_APPEND", TAB_IMPL_APPEND];;
