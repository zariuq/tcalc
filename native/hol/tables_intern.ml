(* ========================================================================= *)
(* intern16 over the interface: on an intern16 table of a well-formed       *)
(* layout whose interface appends as its laws say, intern16 implements its  *)
(* meaning (TAB_IMPL_I16): FIRED, the key's row was found or appended,     *)
(* absent before; otherwise the table is kept (intern16_kept) and only the  *)
(* payload word changes.                                                     *)
(*                                                                           *)
(* Loaded after tables_append.ml and intern16_kept.ml.                       *)
(* ========================================================================= *)

(* The three regions of an intern16 table at slot j, bound to a step's      *)
(* regions 0..2. *)
let TAB_I16_SLOTS_TAC =
  REWRITE_TAC[ARITH_RULE `r < 3 <=> r = 0 \/ r = 1 \/ r = 2`] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[ADD_CLAUSES];;

(* The child of an intern16 step on the table at slot j: its regions are   *)
(* the table's, within the address space, and hold the memory's bytes.     *)
let TAB_I16_CHILD = prove
 (`!L bw ctl nctl budget cfr st m used t j.
     tab_layout L bw ctl nctl cfr /\
     MEM j (tab_slots L) /\ MEM (j + 2) (tab_slots L) /\ MEM (j + 4) (tab_slots L) /\
     drv_child bw ctl budget cfr st m used t /\
     val(EL 1 st) = j /\ val(EL 2 st) = j + 2 /\ val(EL 3 st) = j + 4
     ==> (!r. r < 3 ==> tisa_base t r = bw(j + 2 * r) /\ tisa_len t r = bw(j + 2 * r + 1)) /\
         (!r. r < 3 ==> val(bw(j + 2 * r)) + val(bw(j + 2 * r + 1)) < 2 EXP 64) /\
         (!r a. r < 3 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1))) ==> tmem t a = m a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. r < 3 ==> val(EL (1 + r) (st:int64 list)) = j + 2 * r /\ MEM (j + 2 * r) (tab_slots L)`
    ASSUME_TAC THENL [TAB_I16_SLOTS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!r. r < 3 ==> val(bw(j + 2 * r)) + val(bw(j + 2 * r + 1)) < 2 EXP 64 /\
                              drv_apart (word_sub cfr (word 48)) 304 (bw(j + 2 * r)) (val(bw(j + 2 * r + 1)))`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j + 2 * r`]
                 TAB_LAYOUT_SLOT) THEN
    ASM_SIMP_TAC[GSYM ADD_ASSOC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    (MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                   `m:int64->byte`; `used:int64`; `t:tisa_state`; `r:num`; `j + 2 * r`] PL_CHILD_REGION) THEN
     ASM_SIMP_TAC[GSYM ADD_ASSOC] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
      check (fun th -> is_const_app "drv_child" (concl th))) THEN
    MATCH_MP_TAC DRV_IN_NOT_STACK THEN
    MAP_EVERY EXISTS_TAC [`bw(j + 2 * r):int64`; `val(bw(j + 2 * r + 1):int64)`] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN ASM_SIMP_TAC[]]);;

(* After the step: the leaf's final state has the same regions, and its     *)
(* memory there is the memory the driver keeps.                              *)
let TAB_I16_AFTER = prove
 (`!L bw ctl nctl budget cfr st m used t k u j.
     tab_layout L bw ctl nctl cfr /\
     MEM j (tab_slots L) /\ MEM (j + 2) (tab_slots L) /\ MEM (j + 4) (tab_slots L) /\
     drv_child bw ctl budget cfr st m used t /\
     val(EL 1 st) = j /\ val(EL 2 st) = j + 2 /\ val(EL 3 st) = j + 4 /\ val(EL 17 st) < nctl /\
     tisa_entry_ok intern16 t /\ tisa_run intern16 t = TStop k u
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
    MP_TAC(SPECL [`intern16`; `t:tisa_state`; `k:num`; `u:tisa_state`; `2 * r`] PL_RUN_FRAME) THEN
    MP_TAC(SPECL [`intern16`; `t:tisa_state`; `k:num`; `u:tisa_state`; `2 * r + 1`] PL_RUN_FRAME) THEN
    ASM_REWRITE_TAC[INTERN16_LEAF_WF] THEN
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

(* Rewrites the interner's words of t, below the old count, to those of u. *)
let TAB_I16_U_WORDS_TAC bnds =
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `intern_word u`)) (concl th) &&
                           can (find_term ((=) `intern_word t`)) (concl th)
     then REWRITE_TAC(map (fun b -> GSYM(MATCH_MP th (ASSUME b))) bnds) else failwith "TAB_I16_U_WORDS_TAC");;

let TAB_IMPL_I16 = prove
 (`!(trow:num->S->num->num list) (tn:num->S->num) (twd:num->num) (tdrop:num->S->num->bool)
    (tapp:num->num->S->num list->S->bool) (tput:num->num->S->num->num->num->S->bool) L inp progs bw ctl nctl budget cfr st j.
     progs 0 = intern16 /\ val(EL 0 st) = 0 /\ val(EL 1 st) = j /\ val(EL 2 st) = j + 2 /\
     val(EL 3 st) = j + 4 /\ MEM (KeyTab j) L /\ tab_wf L /\ tab_app_ok (trow,tn,twd,tdrop,tapp,tput) /\
     (!s r. LENGTH r = 2 ==> ?s'. tapp j (j + 4) s r s') /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tab_impl (tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr) (trow,tn,twd,tdrop,tapp,tput) inp
                  progs bw ctl budget cfr st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tab_impl; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:int64->byte`; `used:int64`; `cw:num->num`; `s:S`; `stk:num list`;
                       `t:tisa_state`; `k:num`; `u:tisa_state`] THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_rel]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  TAB_DESC_TAC `KeyTab j` THEN
  SUBGOAL_THEN `val(EL 17 (st:int64 list)) < nctl` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) && can (find_term ((=) `10`)) (concl th))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `j:num`] TAB_I16_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the child holds the table's interner *)
  MP_TAC(SPECL [`t':tisa_state`; `t:tisa_state`] INTERN16_SAME_REGIONS) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `2` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `t':tisa_state`)) (concl th) && can (find_term ((=) `tisa_base`)) (concl th))) THEN
      CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `drv_in a (bw(j + 2 * r):int64) (val(bw(j + 2 * r + 1):int64))` ASSUME_TAC THENL
       [REWRITE_TAC[drv_in] THEN UNDISCH_TAC `val(a:int64) < val(tisa_base t' r) + val(tisa_len t' r)` THEN
        UNDISCH_TAC `val(tisa_base t' r) <= val(a:int64)` THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(fun th -> let c = concl th in
         if is_forall c && length(fst(strip_forall c)) = 2 && can (find_term ((=) `tmem t`)) c
         then MP_TAC(SPECL [`r:num`; `a:int64`] th) else failwith "") THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      FIRST_ASSUM(fun th -> let c = concl th in
         if is_forall c && length(fst(strip_forall c)) = 2 && can (find_term ((=) `tmem t'`)) c
         then MP_TAC(SPECL [`r:num`; `a:int64`] th) else failwith "") THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC[]];
    STRIP_TAC] THEN
  SUBGOAL_THEN `val(intern_count t) = (tn:num->S->num) (j + 4) s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < (tn:num->S->num) (j + 4) s
                    ==> trow j s i = [val(intern_word t (2 * i)); val(intern_word t (2 * i + 1))]` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `2 * i < 2 * val(intern_count t') /\ 2 * i + 1 < 2 * val(intern_count t')` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) && can (find_term ((=) `intern_word t'`)) (concl th) &&
                                               can (find_term ((=) `trow:num->S->num->num list`)) (concl th))) THEN
  (* the run: its outcome, fuel, and final state *)
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] INTERN16_TISA_RUN_KEPT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(intern_count u) < 2 EXP 60` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [intern_ok] o check (fun th -> concl th = `intern_ok u`)) THEN
    MP_TAC(ISPEC `tisa_len u 0` VAL_BOUND_64) THEN SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`intern16`; `t:tisa_state`; `k:num`; `u:tisa_state`] TISA_RUN_STATUS) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[intern16; intern16_prologue; intern16_body; tisa_root; tisa_returns] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `k < 8 /\ ~(k = 0)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`intern16`; `t:tisa_state`; `k:num`; `u:tisa_state`] TISA_RUN_FUEL) THEN
  ASM_REWRITE_TAC[INTERN16_LEAF_WF] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`;
                `j:num`] TAB_I16_AFTER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the memory after the step: m off the stack, the table's regions and the payload word *)
  SUBGOAL_THEN `!a. ~drv_stack cfr a /\ ~drv_in a (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8 /\
                    (!j'. MEM j' (tab_dslots (KeyTab j)) ==> ~drv_in a (bw j') (val(bw(j' + 1):int64)))
                    ==> drv_after ctl st u a = (m:int64->byte) a` ASSUME_TAC THENL
   [REWRITE_TAC[tab_dslots; MEM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`intern16`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                          `used:int64`; `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[INTERN16_LEAF_WF; REWRITE_RULE[INTERN16_DECLS] INTERN16_REGION_KINDS; INTERN16_DECLS] THEN
    X_GEN_TAC `r:num` THEN REWRITE_TAC[ARITH_RULE `r < 3 <=> r = 0 \/ r = 1 \/ r = 2`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* an intern16 table has no marks *)
  SUBGOAL_THEN `!jm wd. ~MEM (MarkTab jm j (j + 4) wd) L` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_wf]) THEN
    SUBGOAL_THEN `RowTab j (j + 4) wd = KeyTab j` MP_TAC THENL
     [MATCH_MP_TAC TAB_SLOTS_DISJOINT THEN MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `j:num`] THEN
      ASM_REWRITE_TAC[tab_dslots; MEM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[distinctness "tabdesc"]];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 1` THENL
   [(* FIRED *)
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k = 1`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && lhand(concl th) = `1 = 1`)) THEN
    REWRITE_TAC[intern16_post] THEN STRIP_TAC THENL
     [(* found: the key's row was there *)
      SUBGOAL_THEN `val(tisa_fword u 19) < (tn:num->S->num) (j + 4) s` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `2 * val(tisa_fword u 19) < 2 * val(intern_count t) /\
                    2 * val(tisa_fword u 19) + 1 < 2 * val(intern_count t)` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(trow:num->S->num->num list) j s (val(tisa_fword u 19)) =
                    [cw(val(EL 10 (st:int64 list))); cw(val(EL 11 st))]` ASSUME_TAC THENL
       [ASM_SIMP_TAC[] THEN
        TAB_I16_U_WORDS_TAC [`2 * val(tisa_fword u 19) < 2 * val(intern_count t)`;
                             `2 * val(tisa_fword u 19) + 1 < 2 * val(intern_count t)`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`1`; `s:S`] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONJ_TAC THENL [TAB_LEAF_AT_TAC THEN REWRITE_TAC[tab_intern] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
                      ALL_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC TAB_REL_UPDATE THEN
      MAP_EVERY EXISTS_TAC [`m:int64->byte`; `s:S`; `KeyTab j`; `j:num`; `j + 4`] THEN
      ASM_REWRITE_TAC[tab_table; tab_frame] THEN
      CONJ_TAC THENL [REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME]; ALL_TAC] THEN
      REWRITE_TAC[tab_mem] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:tisa_state` THEN ASM_SIMP_TAC[] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `2 * i < 2 * val(intern_count t) /\ 2 * i + 1 < 2 * val(intern_count t)` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      TAB_I16_U_WORDS_TAC [`2 * i < 2 * val(intern_count t)`; `2 * i + 1 < 2 * val(intern_count t)`];
      (* appended: absent before, now at the count *)
      MP_TAC(SPECL [`t:tisa_state`; `u:tisa_state`] INTERN16_TISA_RUN_APPEND_ABSENT) THEN
      ASM_REWRITE_TAC[intern_has] THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`s:S`; `[(cw:num->num)(val(EL 10 (st:int64 list))); cw(val(EL 11 st))]`] o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `tapp:num->num->S->num list->S->bool`)) (concl th))) THEN
      ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `s':S`)] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`j:num`; `j + 4`; `s:S`;
                                  `[(cw:num->num)(val(EL 10 (st:int64 list))); cw(val(EL 11 st))]`; `s':S`] o
        REWRITE_RULE[tab_app_ok] o check (fun th -> is_const_app "tab_app_ok" (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`1`; `s':S`] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONJ_TAC THENL
       [TAB_LEAF_AT_TAC THEN REWRITE_TAC[tab_intern] THEN ASM_REWRITE_TAC[LT_REFL] THEN REPEAT CONJ_TAC THENL
         [ASM_ARITH_TAC;
          X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[CONS_11] THEN
          REWRITE_TAC[GSYM(ASSUME `val(tisa_fword t 22) = (cw:num->num)(val(EL 10 (st:int64 list)))`);
                      GSYM(ASSUME `val(tisa_fword t 23) = (cw:num->num)(val(EL 11 (st:int64 list)))`); VAL_EQ] THEN
          ASM_SIMP_TAC[];
          ASM_ARITH_TAC];
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(tn:num->S->num) (j + 4) s = val(tisa_fword u 19)` (fun th -> ONCE_REWRITE_TAC[th]) THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC TAB_REL_UPDATE THEN
      MAP_EVERY EXISTS_TAC [`m:int64->byte`; `s:S`; `KeyTab j`; `j:num`; `j + 4`] THEN
      ASM_REWRITE_TAC[tab_table] THEN
      CONJ_TAC THENL [REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME]; ALL_TAC] THEN
      REWRITE_TAC[tab_mem] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:tisa_state` THEN ASM_SIMP_TAC[] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i < (tn:num->S->num) (j + 4) s` THENL
       [ASM_SIMP_TAC[] THEN
        SUBGOAL_THEN `2 * i < 2 * val(intern_count t) /\ 2 * i + 1 < 2 * val(intern_count t)` STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        TAB_I16_U_WORDS_TAC [`2 * i < 2 * val(intern_count t)`; `2 * i + 1 < 2 * val(intern_count t)`];
        SUBGOAL_THEN `i = (tn:num->S->num) (j + 4) s` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `val(tisa_fword u 19) = (tn:num->S->num) (j + 4) s`
          (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[CONS_11]]];
    (* not FIRED: the table is kept *)
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_neg(lhand(concl th)))) THEN
    ASM_REWRITE_TAC[intern16_kept] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `s:S`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [TAB_LEAF_AT_TAC THEN REWRITE_TAC[tab_intern] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TAB_REL_UPDATE THEN
    MAP_EVERY EXISTS_TAC [`m:int64->byte`; `s:S`; `KeyTab j`; `j:num`; `j + 4`] THEN
    ASM_REWRITE_TAC[tab_table; tab_frame] THEN
    CONJ_TAC THENL [REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME]; ALL_TAC] THEN
    REWRITE_TAC[tab_mem] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:tisa_state` THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `2 * i < 2 * val(intern_count t) /\ 2 * i + 1 < 2 * val(intern_count t) /\
                  2 * i < 2 * (tn:num->S->num) (j + 4) s /\ 2 * i + 1 < 2 * tn (j + 4) s` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

(* Every theorem this file states, for the audits. *)
let tables_intern_theorems =
 ["TAB_I16_CHILD", TAB_I16_CHILD; "TAB_I16_AFTER", TAB_I16_AFTER; "TAB_IMPL_I16", TAB_IMPL_I16];;
