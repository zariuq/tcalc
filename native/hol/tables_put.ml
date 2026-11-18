needs "native/hol/put_word_mark_tail.ml";;

(* ========================================================================= *)
(* put_word and pol_max over the interface. A word written to the marks at  *)
(* jm (the rows counted at c) sets that id's mark, dropped for any word but *)
(* 0, and keeps every other view (tab_put_mark_ok). A state s' that differs *)
(* from s only in the marks at jm is seen the same by every description but *)
(* those marks (TAB_MEM_MFRAME), so a step that changes, among the described *)
(* regions and the control words, only the marks region at jm and its      *)
(* payload word keeps tab_rel once those marks hold of the new memory and   *)
(* state (TAB_REL_UPDATE_MARK). Then put_word on the marks of a row table   *)
(* of a well-formed layout implements its meaning (TAB_IMPL_PUTW_MARK), and *)
(* pol_max, which reads no region, implements its own (TAB_IMPL_POLMAX).    *)
(*                                                                           *)
(* Loaded after tables_append.ml.                                            *)
(* ========================================================================= *)

(* A description other than marks at jm reads the same views of s and s'. *)
let TAB_MEM_MFRAME = prove
 (`!d tb inp bw m jm (s:S) s'.
     (!j'. FST tb j' s' = FST tb j' s) /\ (!c'. FST(SND tb) c' s' = FST(SND tb) c' s) /\
     (!jm'. ~(jm' = jm) ==> FST(SND(SND(SND tb))) jm' s' = FST(SND(SND(SND tb))) jm' s) /\
     ~(?j c wd. d = MarkTab jm j c wd)
     ==> (tab_mem tb inp bw m s' d <=> tab_mem tb inp bw m s d)`,
  MATCH_MP_TAC tabdesc_INDUCT THEN REWRITE_TAC[FORALL_PAIR_THM; FST; SND; tab_mem; injectivity "tabdesc";
                                               distinctness "tabdesc"] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`a1:num`; `a2:num`; `a3:num`]) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_imp(snd(dest_forall(concl th)))
                          then REWRITE_TAC[MATCH_MP th (ASSUME (mk_neg(mk_eq(`a0:num`, `jm:num`))))]
                          else failwith "") THEN
  REWRITE_TAC[]);;

(* A step that writes the marks at jm. *)
let TAB_REL_UPDATE_MARK = prove
 (`!tb L inp bw ctl nctl cfr m m' cw (s:S) s' stk p v jm j c wd.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ tab_wf L /\ MEM (MarkTab jm j c wd) L /\
     p < nctl /\ 6 < p /\
     (!a. ~drv_stack cfr a /\ ~drv_in a (word_add ctl (word(8 * p))) 8 /\
          (!j'. MEM j' (tab_dslots (MarkTab jm j c wd)) ==> ~drv_in a (bw j') (val(bw(j' + 1))))
          ==> m' a = m a) /\
     drv_word m' (word_add ctl (word(8 * p))) = v /\
     (!j'. FST tb j' s' = FST tb j' s) /\ (!c'. FST(SND tb) c' s' = FST(SND tb) c' s) /\
     (!jm'. ~(jm' = jm) ==> FST(SND(SND(SND tb))) jm' s' = FST(SND(SND(SND tb))) jm' s) /\
     tab_mem tb inp bw m' s' (MarkTab jm j c wd)
     ==> tab_rel tb L inp bw ctl nctl cfr m' (pl_set cw p (val v),s',stk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_rel] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  SUBGOAL_THEN `!j'. MEM j' (tab_dslots (MarkTab jm j c wd)) ==> MEM j' (tab_slots L)` ASSUME_TAC THENL
   [ASM_MESON_TAC[TAB_SLOTS_DESC]; ALL_TAC] THEN
  (* agreement on the described slots other than the marks' *)
  SUBGOAL_THEN `!j' a. MEM j' (tab_slots L) /\ ~MEM j' (tab_dslots (MarkTab jm j c wd)) /\ drv_in a (bw j') (val(bw(j' + 1)))
                       ==> m' a = (m:int64->byte) a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_stack`)) (concl th) && can (find_term ((=) `m':int64->byte`)) (concl th))) THEN
    MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j':num`;
                  `p:num`; `a:int64`] TAB_SLOT_ADDR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
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
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC TAB_CTL_ADDR THEN
      MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `j'':num` THEN DISCH_TAC THEN MATCH_MP_TAC DRV_APART_IN THEN
      MAP_EVERY EXISTS_TAC [`ctl:int64`; `8 * nctl`] THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
      ASM_MESON_TAC[]];
    UNDISCH_TAC `ALL (tab_mem tb inp bw (m:int64->byte) (s:S)) L` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN X_GEN_TAC `d:tabdesc` THEN DISCH_TAC THEN
    ASM_CASES_TAC `d:tabdesc = MarkTab jm j c wd` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(?j1 c1 wd1. d = MarkTab jm j1 c1 wd1)` ASSUME_TAC THENL
     [STRIP_TAC THEN UNDISCH_TAC `~(d:tabdesc = MarkTab jm j c wd)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC TAB_SLOTS_DISJOINT THEN MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `jm:num`] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_wf]) THEN
      ASM_REWRITE_TAC[tab_dslots; MEM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`d:tabdesc`; `tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
                                  (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
                   `inp:num list`; `bw:num->int64`; `m':int64->byte`; `jm:num`; `s:S`; `s':S`]
                  TAB_MEM_MFRAME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC TAB_MEM_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `j':num` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `MEM (j':num) (tab_slots L) /\ ~MEM j' (tab_dslots (MarkTab jm j c wd))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[TAB_SLOTS_DESC]; ALL_TAC] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(d:tabdesc = MarkTab jm j c wd)` THEN REWRITE_TAC[] THEN
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
    SUBGOAL_THEN `~MEM 40 (tab_dslots (MarkTab jm j c wd))` ASSUME_TAC THENL
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
      EXISTS_TAC `40` THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The bridges.                                                              *)
(* ------------------------------------------------------------------------- *)

(* The marks at jm hold of memory m' and state s' when every word inside   *)
(* the region is m's but word i, which is v, and s' drops i exactly when   *)
(* v is not 0, its other marks those of s.                                  *)
let TAB_MARKS_PUT = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput inp bw m m' (s:S) s' jm j c wd i v.
     tab_mem (trow,tn,twd,tdrop,tapp,tput) inp bw m s (MarkTab jm j c wd) /\ i < tn c s /\
     (!x. 8 * x + 8 <= val(bw(jm + 1)) /\ ~(x = i) ==> pl_mw m' (bw jm) x = pl_mw m (bw jm) x) /\
     pl_mw m' (bw jm) i = v /\ tn c s' = tn c s /\
     (!i'. tdrop jm s' i' <=> if i' = i then ~(v = 0) else tdrop jm s i')
     ==> tab_mem (trow,tn,twd,tdrop,tapp,tput) inp bw m' s' (MarkTab jm j c wd)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_mem] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `x:num` THEN STRIP_TAC THENL
   [ASM_CASES_TAC `x:num = i` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `8 * x + 8 <= val(bw(jm + 1):int64)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    SUBGOAL_THEN `~(x:num = i)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN `~(x:num = i)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_SIMP_TAC[]]);;

let PUT_WORD_RW = prove
 (`!r. tisa_rw (tisa_decls put_word) r <=> r = 0`,
  GEN_TAC THEN REWRITE_TAC[PUT_WORD_DECLS; tisa_rw; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `r < 2` THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP(ARITH_RULE `r < 2 ==> r = 0 \/ r = 1`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[FST] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* put_word on the marks at jm of a row table of a well-formed layout, the  *)
(* interface's word write at jm obeying tab_put_mark_ok and its width 1.    *)
let TAB_IMPL_PUTW_MARK = prove
 (`!(trow:num->S->num->num list) (tn:num->S->num) (twd:num->num) (tdrop:num->S->num->bool)
    (tapp:num->num->S->num list->S->bool) (tput:num->num->S->num->num->num->S->bool)
    L inp progs bw ctl nctl budget cfr st jm j c wd.
     progs 9 = put_word /\ val(EL 0 st) = 9 /\ val(EL 1 st) = jm /\ val(EL 2 st) = c /\
     MEM (MarkTab jm j c wd) L /\ tab_wf L /\ tab_put_mark_ok (trow,tn,twd,tdrop,tapp,tput) jm c /\
     twd jm = 1 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tab_impl (tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr) (trow,tn,twd,tdrop,tapp,tput) inp
                  progs bw ctl budget cfr st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tab_impl; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:int64->byte`; `used:int64`; `cw:num->num`; `s:S`; `stk:num list`;
                       `t:tisa_state`; `k:num`; `u:tisa_state`] THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_rel]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  SUBGOAL_THEN `MEM (RowTab j c wd) L` ASSUME_TAC THENL [ASM_MESON_TAC[tab_wf]; ALL_TAC] THEN
  TAB_DESC_TAC `MarkTab jm j c wd` THEN TAB_DESC_TAC `RowTab j c wd` THEN
  SUBGOAL_THEN
   `tab_mem (trow,tn,twd,tdrop,tapp,tput) inp bw m (s:S) (MarkTab jm j c wd)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `MarkTab jm j c wd` o REWRITE_RULE[GSYM ALL_MEM] o
      check (fun th -> is_const_app "ALL" (concl th) && tab_has_const "tab_mem" (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the step's width word is 1: the leaf is enabled *)
  SUBGOAL_THEN `(cw:num->num)(val(EL 12 (st:int64 list))) = 1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "tab_leaf" (concl th))) THEN
    REWRITE_TAC[tab_leaf; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[tab_putw] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(EL 17 (st:int64 list)) < nctl` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) && can (find_term ((=) `10`)) (concl th))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  (* the child's arguments, stride, regions and count word *)
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `1` o check (fun th -> is_forall(concl th) && can (find_term ((=) `tregs`)) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `2` o check (fun th -> is_forall(concl th) && can (find_term ((=) `tregs`)) (concl th))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `c:num`; `0`] TAB_CHILD_W) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `0`; `jm:num`] PL_CHILD_REGION) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_rtab] o check (fun th -> is_const_app "pl_rtab" (concl th))) THEN
  (* the marks region's words before the step, through the child *)
  SUBGOAL_THEN `!x. 8 * x + 8 <= val(bw(jm + 1):int64) ==> val(pl_w t 0 x) = pl_mw m (bw jm) x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                  `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `0`; `jm:num`; `x:num`] TAB_CHILD_W) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the memory after the step: m off the stack, the marks region and the payload word *)
  SUBGOAL_THEN `!a. ~drv_stack cfr a /\ ~drv_in a (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8 /\
                    ~drv_in a (bw(jm:num)) (val(bw(jm + 1):int64))
                    ==> drv_after ctl st u a = (m:int64->byte) a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`put_word`;`bw:num->int64`;`nctl:num`;`budget:int64`;`cfr:int64`;
                          `used:int64`;`t:tisa_state`;`k:num`] THEN
    ASM_REWRITE_TAC[PUT_WORD_LEAF_WF;PUT_WORD_RW;FORALL_UNWIND_THM2;drv_base;drv_len] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `put_word`; `k:num`;
                `u:tisa_state`] TAB_AFTER_WORD) THEN
  ASM_REWRITE_TAC[PUT_WORD_LEAF_WF] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. 8 * x + 8 <= val(bw(jm + 1):int64) ==> pl_mw (drv_after ctl st u) (bw jm) x = val(pl_w u 0 x)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `jm:num`; `x:num`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `drv_after`)) (concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* The full table frame includes words beyond the published count. *)
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] PUT_WORD_TABLE_KEPT) THEN
  ASM_REWRITE_TAC[GSYM pl_w] THEN DISCH_THEN(LABEL_TAC "put_word_table_frame") THEN
  (* the leaf's specification, by whether the row lies in the table *)
  MP_TAC PL_PUT_WORD_SPEC THEN REWRITE_TAC[pl_put_word_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o CONJUNCT2 o CONJUNCT2)
                             (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `cw(val(EL 10 (st:int64 list))) < (tn:num->S->num) c (s:S) /\ cw(val(EL 13 st)) = 0` THEN
  ASM_REWRITE_TAC[ARITH_RULE `x < 1 <=> x = 0`; MULT_CLAUSES; ADD_CLAUSES] THENL
   [(* FIRED: the mark written *)
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th) &&
                    can (find_term ((=) `(cw:num->num)(val(EL 13 (st:int64 list)))`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k = 1`)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_put_mark_ok] o
                check (fun th -> is_const_app "tab_put_mark_ok" (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:S`; `cw(val(EL 10 (st:int64 list))):num`; `cw(val(EL 11 (st:int64 list))):num`] o
                  check (fun th -> is_forall(concl th) && can (find_term is_exists) (concl th) &&
                                   can (find_term ((=) `tput:num->num->S->num->num->num->S->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `s':S`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:S`; `cw(val(EL 10 (st:int64 list))):num`; `cw(val(EL 11 (st:int64 list))):num`;
                                  `s':S`] o check (fun th -> is_forall(concl th) && not(can (find_term is_exists) (concl th)) &&
                                   can (find_term ((=) `tput:num->num->S->num->num->num->S->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`1`; `s':S`] THEN REPEAT CONJ_TAC THENL
     [TAB_LEAF_AT_TAC THEN REWRITE_TAC[tab_putw] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ARITH_TAC;
      REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(cw:num->num)(val(EL 11 (st:int64 list))) = val(tisa_fword u 19)`
      (fun th -> ONCE_REWRITE_TAC[th]) THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC TAB_REL_UPDATE_MARK THEN
    MAP_EVERY EXISTS_TAC [`m:int64->byte`; `s:S`; `jm:num`; `j:num`; `c:num`; `wd:num`] THEN
    ASM_REWRITE_TAC[FST; SND; tab_dslots; MEM] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC TAB_MARKS_PUT THEN
    MAP_EVERY EXISTS_TAC [`m:int64->byte`; `s:S`; `cw(val(EL 10 (st:int64 list))):num`;
                          `cw(val(EL 11 (st:int64 list))):num`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MULT_CLAUSES;ADD_CLAUSES];
      SUBGOAL_THEN `8 * cw(val(EL 10 (st:int64 list))) + 8 <= val(bw(jm + 1):int64)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    (* UNSUPPORTED: every word kept *)
    DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k = 2`)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`2`; `s:S`] THEN REPEAT CONJ_TAC THENL
     [TAB_LEAF_AT_TAC THEN REWRITE_TAC[tab_putw;ARITH_RULE `x < 1 <=> x = 0`] THEN ASM_REWRITE_TAC[ARITH_EQ];
      ARITH_TAC;
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC TAB_REL_UPDATE_MARK THEN
    MAP_EVERY EXISTS_TAC [`m:int64->byte`; `s:S`; `jm:num`; `j:num`; `c:num`; `wd:num`] THEN
    ASM_REWRITE_TAC[FST; SND; tab_dslots; MEM] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[tab_mem] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `8 * x + 8 <= val(bw(jm + 1):int64)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    ASM_SIMP_TAC[]]);;

(* The regions put_word writes (its table) and pol_max writes (none). *)
let POL_MAX_RO = prove
 (`!r. ~tisa_rw (tisa_decls pol_max) r`,
  REWRITE_TAC[POL_MAX_DECLS; tisa_rw; LENGTH] THEN ARITH_TAC);;

(* pol_max reads no region. *)
let PL_POL_MAX_STATUS = prove
 (`!t k u. tisa_entry_ok pol_max t /\ tisa_run pol_max t = TStop k u
           ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\ k < 8`,
  PL_STATUS_TAC PL_POL_MAX_SPEC pl_pol_max_spec);;

let TAB_IMPL_POLMAX = prove
 (`!(trow:num->S->num->num list) (tn:num->S->num) (twd:num->num) (tdrop:num->S->num->bool)
    (tapp:num->num->S->num list->S->bool) (tput:num->num->S->num->num->num->S->bool) L inp progs bw ctl nctl
    budget cfr st.
     progs 20 = pol_max /\ val(EL 0 st) = 20 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\
     6 < val(EL 17 st)
     ==> tab_impl (tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr) (trow,tn,twd,tdrop,tapp,tput) inp
                  progs bw ctl budget cfr st`,
  TAB_PURE_BRIDGE_TAC `pol_max` POL_MAX_LEAF_WF POL_MAX_DECLS PL_POL_MAX_STATUS PL_POL_MAX_SPEC
    (CONJ pl_pol_max_spec tab_polmax) THEN
  MATCH_MP_TAC PL_VAL_WORD_LT THEN REWRITE_TAC[ARITH_RULE `MAX a b < n <=> a < n /\ b < n`] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `tisa_fword t 22` VAL_BOUND_64) THEN ASM_REWRITE_TAC[];
    MP_TAC(SPEC `tisa_fword t 23` VAL_BOUND_64) THEN ASM_REWRITE_TAC[]]);;

(* Every theorem this file states, for the audits. *)
let tables_put_theorems =
 ["TAB_MEM_MFRAME", TAB_MEM_MFRAME; "TAB_REL_UPDATE_MARK", TAB_REL_UPDATE_MARK; "TAB_MARKS_PUT", TAB_MARKS_PUT;
  "TAB_IMPL_PUTW_MARK", TAB_IMPL_PUTW_MARK; "PUT_WORD_RW", PUT_WORD_RW; "POL_MAX_RO", POL_MAX_RO;
  "PL_POL_MAX_STATUS", PL_POL_MAX_STATUS; "TAB_IMPL_POLMAX", TAB_IMPL_POLMAX];;
