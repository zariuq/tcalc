(* ========================================================================= *)
(* Steps that write one table. A layout is well formed (tab_wf) when its   *)
(* slots are distinct and every marks description belongs to a row table  *)
(* of the layout; then distinct descriptions have disjoint slots           *)
(* (TAB_SLOTS_DISJOINT). A state s' that differs from s at most in the rows *)
(* at slot j and the count at slot c (tab_frame) is seen the same by every  *)
(* description that reads neither (tab_avoid, TAB_MEM_FRAME). So a step    *)
(* that changes, among the described regions and the control words, only  *)
(* the regions of one table description d0 (rows at j, count at c) and its *)
(* payload word keeps tab_rel once d0 and the marks of d0 hold of the new  *)
(* memory and state (TAB_REL_UPDATE).                                       *)
(*                                                                           *)
(* Loaded after tables_frame.ml.                                             *)
(* ========================================================================= *)

let tab_wf = new_definition
 `tab_wf L <=> PAIRWISE (\x y. ~(x = y)) (tab_slots L) /\
               (!jm j c wd. MEM (MarkTab jm j c wd) L ==> MEM (RowTab j c wd) L)`;;

(* s' differs from s at most in the rows at slot j and the count at slot c. *)
let tab_frame = new_definition
 `tab_frame ((trow,tn,twd,tdrop,tapp,tput):(num->S->num->num list)#(num->S->num)#(num->num)#
                                       (num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool))
            j c (s:S) (s':S) <=>
    (!j'. ~(j' = j) ==> trow j' s' = trow j' s) /\ (!c'. ~(c' = c) ==> tn c' s' = tn c' s) /\
    (!jm. tdrop jm s' = tdrop jm s)`;;

(* The rows and counts a description reads are neither j's rows nor c's    *)
(* count.                                                                    *)
let tab_avoid = define
 `(tab_avoid (RowTab j' c' wd) j c <=> ~(j' = j) /\ ~(c' = c)) /\
  (tab_avoid (KeyTab j') j c <=> ~(j' = j) /\ ~(j' + 4 = c)) /\
  (tab_avoid (MarkTab jm j' c' wd) j c <=> ~(c' = c)) /\
  (tab_avoid (NameTab j') j c <=> ~(j' = j) /\ ~(j' + 6 = c)) /\
  (tab_avoid (InTab j') j c <=> T)`;;

let TAB_MEM_FRAME = prove
 (`!d tb inp bw m j c (s:S) s'.
     tab_frame tb j c s s' /\ tab_avoid d j c
     ==> (tab_mem tb inp bw m s' d <=> tab_mem tb inp bw m s d)`,
  MATCH_MP_TAC tabdesc_INDUCT THEN REWRITE_TAC[FORALL_PAIR_THM; tab_frame; tab_avoid; tab_mem] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* Two descriptions of a layout with distinct slots that share a slot are   *)
(* one.                                                                      *)
let TAB_SLOTS_DISJOINT = prove
 (`!L d d' x. PAIRWISE (\x y. ~(x = y)) (tab_slots L) /\ MEM d L /\ MEM d' L /\
              MEM x (tab_dslots d) /\ MEM x (tab_dslots d') ==> d = d'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; TAB_SLOTS_CLAUSES; PAIRWISE_APPEND] THEN
  ASM_MESON_TAC[TAB_SLOTS_DESC]);;

(* No description of a layout with distinct slots holds the stack's or the  *)
(* work region's slot.                                                        *)
let TAB_STK_NOT_DESC = prove
 (`!L d. PAIRWISE (\x y. ~(x = y)) (tab_slots L) /\ MEM d L
         ==> ~MEM 40 (tab_dslots d) /\ ~MEM 42 (tab_dslots d)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; TAB_SLOTS_CLAUSES; PAIRWISE_APPEND] THEN
  ASM_MESON_TAC[TAB_SLOTS_STK]);;

(* A table description: its rows at slot j, its count at slot c. *)
let tab_table = new_definition
 `tab_table d0 j c <=> (?wd. d0 = RowTab j c wd) \/ d0 = KeyTab j /\ c = j + 4 \/ d0 = NameTab j /\ c = j + 6`;;

let TAB_TABLE_SLOTS = prove
 (`!d0 j c. tab_table d0 j c ==> MEM j (tab_dslots d0) /\ MEM c (tab_dslots d0)`,
  REWRITE_TAC[tab_table] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[tab_dslots; MEM] THEN ARITH_TAC);;

(* In a well-formed layout, a description other than the table d0 and the  *)
(* marks of d0 reads neither d0's rows nor its count.                        *)
let TAB_AVOID_WF = prove
 (`!L d d0 j c.
     tab_wf L /\ MEM d L /\ MEM d0 L /\ ~(d = d0) /\ tab_table d0 j c /\
     ~(?jm wd. d = MarkTab jm j c wd)
     ==> tab_avoid d j c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_wf] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_TABLE_SLOTS) THEN
  SUBGOAL_THEN `!x. MEM x (tab_dslots d) ==> ~MEM x (tab_dslots d0)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `~(d:tabdesc = d0)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC TAB_SLOTS_DISJOINT THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `MEM (d:tabdesc) L` THEN UNDISCH_TAC `~(?jm wd. d = MarkTab jm j c wd)` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) && can (find_term ((=) `tab_dslots`)) (concl th) &&
                                          not(can (find_term ((=) `L:tabdesc list`)) (concl th)))) THEN
  SPEC_TAC(`d:tabdesc`,`d:tabdesc`) THEN
  MATCH_MP_TAC tabdesc_INDUCT THEN REWRITE_TAC[tab_avoid; tab_dslots; MEM] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`j':num`; `c':num`; `wd':num`] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    X_GEN_TAC `j':num` THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`jm:num`; `j':num`; `c':num`; `wd':num`] THEN REWRITE_TAC[injectivity "tabdesc"] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `RowTab j' c wd' = d0` ASSUME_TAC THENL
     [MATCH_MP_TAC TAB_SLOTS_DISJOINT THEN MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `c:num`] THEN
      ASM_REWRITE_TAC[tab_dslots; MEM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `tab_table d0 j c` THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[tab_table; injectivity "tabdesc"; distinctness "tabdesc"] THEN STRIP_TAC THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `j':num` THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A step that writes the regions of one table.                              *)
(* ------------------------------------------------------------------------- *)

let TAB_REL_UPDATE = prove
 (`!tb L inp bw ctl nctl cfr m m' cw (s:S) s' stk p v d0 j c.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ tab_wf L /\ MEM d0 L /\ tab_table d0 j c /\
     p < nctl /\ 6 < p /\
     (!a. ~drv_stack cfr a /\ ~drv_in a (word_add ctl (word(8 * p))) 8 /\
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
  SUBGOAL_THEN `!j' a. MEM j' (tab_slots L) /\ ~MEM j' (tab_dslots d0) /\ drv_in a (bw j') (val(bw(j' + 1)))
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
    SUBGOAL_THEN `MEM (j':num) (tab_slots L) /\ ~MEM j' (tab_dslots d0)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[TAB_SLOTS_DESC]; ALL_TAC] THEN DISCH_TAC THEN
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
      EXISTS_TAC `40` THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[]]]);;

(* Every theorem this file states, for the audits. *)
let tables_update_theorems =
 ["TAB_MEM_FRAME", TAB_MEM_FRAME; "TAB_SLOTS_DISJOINT", TAB_SLOTS_DISJOINT; "TAB_STK_NOT_DESC", TAB_STK_NOT_DESC;
  "TAB_TABLE_SLOTS", TAB_TABLE_SLOTS; "TAB_AVOID_WF", TAB_AVOID_WF; "TAB_REL_UPDATE", TAB_REL_UPDATE];;
