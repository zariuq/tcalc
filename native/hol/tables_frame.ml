(* ========================================================================= *)
(* The memory relation's frame. A memory that agrees with another on a     *)
(* description's regions holds the description as the other does          *)
(* (TAB_MEM_AGREE). A step that changes, among the described regions and   *)
(* the control words, only its payload word keeps tab_rel with the payload *)
(* set (TAB_REL_KEEP); so does every read-only leaf (TAB_REL_RO_STEP), and  *)
(* a read-only leaf whose outcome and payload are its meaning's implements  *)
(* it (TAB_IMPL_RO). A child's region bound to a described slot reads the   *)
(* memory's words (TAB_CHILD_W).                                            *)
(*                                                                           *)
(* Loaded after tables_rel.ml and tables_drv.ml.                            *)
(* ========================================================================= *)

let TAB_SLOTS_CLAUSES = prove
 (`tab_slots [] = [40; 42] /\
   (!d L. tab_slots (CONS d L) = APPEND (tab_dslots d) (tab_slots L))`,
  REWRITE_TAC[tab_slots; ITLIST]);;

let TAB_SLOTS_DESC = prove
 (`!L d j. MEM d L /\ MEM j (tab_dslots d) ==> MEM j (tab_slots L)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; TAB_SLOTS_CLAUSES; MEM_APPEND] THEN ASM_MESON_TAC[]);;

let TAB_SLOTS_STK = prove
 (`!L. MEM 40 (tab_slots L) /\ MEM 42 (tab_slots L)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[TAB_SLOTS_CLAUSES; MEM_APPEND; MEM] THEN CONV_TAC NUM_REDUCE_CONV);;

(* The layout's facts about one slot. *)
let TAB_LAYOUT_SLOT = prove
 (`!L bw ctl nctl cfr j.
     tab_layout L bw ctl nctl cfr /\ MEM j (tab_slots L)
     ==> val(bw j) + val(bw(j + 1)) < 2 EXP 64 /\
         drv_apart (bw j) (val(bw(j + 1))) ctl (8 * nctl) /\
         drv_apart (word_sub cfr (word 48)) 304 (bw j) (val(bw(j + 1)))`,
  REWRITE_TAC[tab_layout] THEN MESON_TAC[]);;

(* An address of a described slot's region is neither in the driver's stack *)
(* window nor in control word p.                                             *)
let TAB_SLOT_ADDR = prove
 (`!L bw ctl nctl cfr j p a.
     tab_layout L bw ctl nctl cfr /\ MEM j (tab_slots L) /\ p < nctl /\ drv_in a (bw j) (val(bw(j + 1)))
     ==> ~drv_stack cfr a /\ ~drv_in a (word_add ctl (word(8 * p))) 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`]
               TAB_LAYOUT_SLOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN CONJ_TAC THENL
   [MATCH_MP_TAC DRV_IN_NOT_STACK THEN
    MAP_EVERY EXISTS_TAC [`bw(j:num):int64`; `val(bw(j + 1):int64)`] THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`ctl:int64`; `8 * p`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    UNDISCH_TAC `drv_apart (bw(j:num)) (val(bw(j + 1):int64)) ctl (8 * nctl)` THEN
    UNDISCH_TAC `drv_in (a:int64) (bw(j:num)) (val(bw(j + 1):int64))` THEN
    ASM_REWRITE_TAC[drv_apart; drv_in] THEN ASM_ARITH_TAC]);;

(* A control-word address is not in the driver's stack window. *)
let TAB_CTL_ADDR = prove
 (`!L bw ctl nctl cfr a. tab_layout L bw ctl nctl cfr /\ drv_in a ctl (8 * nctl) ==> ~drv_stack cfr a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_layout] THEN STRIP_TAC THEN
  MATCH_MP_TAC DRV_IN_NOT_STACK THEN
  MAP_EVERY EXISTS_TAC [`ctl:int64`; `8 * nctl`] THEN ASM_REWRITE_TAC[]);;

(* Byte i of a region of n bytes lies in it. *)
let TAB_IN_BYTE = prove
 (`!(b:int64) n i. val b + n <= 2 EXP 64 /\ i < n ==> drv_in (word_add b (word i)) b n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[drv_in] THEN
  MP_TAC(SPECL [`b:int64`; `i:num`] TISA_VAL_OFFSET) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Memory agreement.                                                        *)
(* ------------------------------------------------------------------------- *)

let TAB_MEM_AGREE = prove
 (`!d tb inp bw m m' (s:S).
     tab_mem tb inp bw m s d /\
     ALL (\j. val(bw j) + val(bw(j + 1)) <= 2 EXP 64 /\
              !a. drv_in a (bw j) (val(bw(j + 1))) ==> m' a = m a) (tab_dslots d)
     ==> tab_mem tb inp bw m' s d`,
  let REGIONS_TAC cases =
    MAP_EVERY X_GEN_TAC [`r:num`; `a:int64`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r:num`; `a:int64`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `tmem t`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) && is_const_app "<" (concl th) &&
                                              rand(rator(concl th)) = `r:num`)) THEN
    REWRITE_TAC[cases] THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ADD_ASSOC]) THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC) in
  MATCH_MP_TAC tabdesc_INDUCT THEN REWRITE_TAC[FORALL_PAIR_THM; tab_mem; tab_dslots; ALL] THEN
  REPEAT CONJ_TAC THENL
   [(* RowTab *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_RTAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[];
    (* KeyTab *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `t:tisa_state` THEN ASM_REWRITE_TAC[] THEN
    REGIONS_TAC (ARITH_RULE `r < 3 <=> r = 0 \/ r = 1 \/ r = 2`);
    (* MarkTab *)
    MAP_EVERY X_GEN_TAC [`jm:num`; `j:num`; `c:num`; `wd:num`] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `!i. 8 * i + 8 <= val(bw(jm + 1):int64)
                      ==> pl_mw m' (bw(jm:num)) i = pl_mw (m:int64->byte) (bw jm) i` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MW_REGION THEN EXISTS_TAC `val(bw(jm + 1):int64)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THENL
     [SUBGOAL_THEN `8 * i + 8 <= val(bw(jm + 1):int64)` (fun th -> ASM_SIMP_TAC[th]) THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[]];
    (* NameTab *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `t:tisa_state` THEN ASM_REWRITE_TAC[] THEN
    REGIONS_TAC (ARITH_RULE `r < 4 <=> r = 0 \/ r = 1 \/ r = 2 \/ r = 3`);
    (* InTab *)
    X_GEN_TAC `j:num` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `m'(word_add (bw(j:num)) (word i)) = (m:int64->byte)(word_add (bw j) (word i))` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC TAB_IN_BYTE THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `i < LENGTH (inp:num list)` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]]]);;

(* A memory that changes, among the described regions and the control      *)
(* words, only control word p (above the bootstrap words) keeps the        *)
(* relation, with p's new value.                                            *)
let TAB_REL_KEEP = prove
 (`!tb L inp bw ctl nctl cfr m m' cw (s:S) stk p v.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ p < nctl /\ 6 < p /\
     (!a. ~drv_stack cfr a /\ ~drv_in a (word_add ctl (word(8 * p))) 8 ==> m' a = m a) /\
     drv_word m' (word_add ctl (word(8 * p))) = v
     ==> tab_rel tb L inp bw ctl nctl cfr m' (pl_set cw p (val v),s,stk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_rel] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!j a. MEM j (tab_slots L) /\ drv_in a (bw j) (val(bw(j + 1))) ==> m' a = (m:int64->byte) a`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC TAB_SLOT_ADDR THEN
    MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `bw:num->int64`; `nctl:num`; `j:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_set] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC PL_CWORDS_SET THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `drv_stack`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TAB_CTL_ADDR THEN
    MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`] THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `ALL (tab_mem tb inp bw (m:int64->byte) (s:S)) L` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN X_GEN_TAC `d:tabdesc` THEN DISCH_TAC THEN
    MATCH_MP_TAC TAB_MEM_AGREE THEN EXISTS_TAC `m:int64->byte` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `MEM (j:num) (tab_slots L)` ASSUME_TAC THENL [ASM_MESON_TAC[TAB_SLOTS_DESC]; ALL_TAC] THEN
    BETA_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LT_IMP_LE THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `tab_slots`)) (concl th) && can (find_term ((=) `drv_in`)) (concl th))) THEN
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC PL_STK_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `L:tabdesc list` TAB_SLOTS_STK) THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LT_IMP_LE THEN
      SUBGOAL_THEN `val(bw 40:int64) + val(bw(40 + 1):int64) < 2 EXP 64` MP_TAC THENL
       [ASM_SIMP_TAC[]; CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[]];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `tab_slots`)) (concl th) && can (find_term ((=) `drv_in`)) (concl th))) THEN
      EXISTS_TAC `40` THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[]]]);;

(* A leaf without read-write regions keeps the relation, with the payload  *)
(* in the step's word.                                                       *)
let TAB_REL_RO_STEP = prove
 (`!tb L inp bw ctl nctl budget cfr st m used t prog k u cw (s:S) stk.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     drv_child bw ctl budget cfr st m used t /\ tisa_leaf_wf prog /\ tisa_entry_ok prog t /\
     tisa_run prog t = TStop k u /\ (!r. ~tisa_rw (tisa_decls prog) r) /\ val(EL 17 st) < nctl /\
     6 < val(EL 17 st)
     ==> tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),s,stk)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TAB_REL_KEEP THEN EXISTS_TAC `m:int64->byte` THEN
  ASM_REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME] THEN
  X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM drv_after] THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
  MAP_EVERY EXISTS_TAC [`prog:tisa_prog`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                        `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "tab_rel" (concl th))) THEN
  REWRITE_TAC[tab_rel; tab_layout] THEN SIMP_TAC[]);;

(* A read-only leaf implements its meaning when its outcome and payload are *)
(* the meaning's, at the same tables.                                        *)
let TAB_IMPL_RO = prove
 (`!tb L inp progs bw ctl nctl budget cfr st prog.
     progs (val(EL 0 st)) = prog /\ tisa_leaf_wf prog /\ (!r. ~tisa_rw (tisa_decls prog) r) /\
     (!t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
              ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\ k < 8) /\
     val(EL 17 st) < nctl /\ 6 < val(EL 17 st) /\
     (!m used cw (s:S) stk t k u.
        tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ drv_child bw ctl budget cfr st m used t /\
        tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
        ==> tab_leaf tb inp st (cw,s,stk) k (val(tisa_fword u 19)) s)
     ==> tab_impl (tab_rel tb L inp bw ctl nctl cfr) tb inp progs bw ctl budget cfr st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tab_impl; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:int64->byte`; `used:int64`; `cw:num->num`; `s:S`; `stk:num list`;
                       `t:tisa_state`; `k:num`; `u:tisa_state`] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `s:S`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `tisa_fword u 18`)) (concl th) &&
                     not(can (find_term (fun t -> is_const t && fst(dest_const t) = "tab_leaf")) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[FST; SND] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`m:int64->byte`; `used:int64`; `t:tisa_state`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `21` o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
      check (fun th -> is_const_app "drv_child" (concl th))) THEN
    REWRITE_TAC[drv_fw] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC TAB_REL_RO_STEP THEN
    MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`;
                          `prog:tisa_prog`; `k:num`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The child state of a step against the relation.                          *)
(* ------------------------------------------------------------------------- *)

(* Word i of a child's region r, bound to a described slot j, is the        *)
(* memory's.                                                                 *)
let TAB_CHILD_W = prove
 (`!L bw ctl nctl budget cfr st m used t r j i.
     drv_child bw ctl budget cfr st m used t /\ tab_layout L bw ctl nctl cfr /\
     r < 9 /\ val(EL (1 + r) st) = j /\ MEM j (tab_slots L) /\ 8 * i + 8 <= val(bw(j + 1))
     ==> tisa_base t r = bw j /\ tisa_len t r = bw(j + 1) /\ val(pl_w t r i) = pl_mw m (bw j) i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[drv_base; drv_len] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pl_w; pl_mw] THEN AP_TERM_TAC THEN
  REWRITE_TAC[tisa_read; GSYM drv_word] THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
    check (fun th -> is_const_app "drv_child" (concl th))) THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`]
               TAB_LAYOUT_SLOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  MATCH_MP_TAC DRV_IN_NOT_STACK THEN
  MAP_EVERY EXISTS_TAC [`bw(j:num):int64`; `val(bw(j + 1):int64)`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DRV_IN_OFFSET THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* Every theorem this file states, for the audits. *)
let tables_frame_theorems =
 ["TAB_SLOTS_CLAUSES", TAB_SLOTS_CLAUSES; "TAB_SLOTS_DESC", TAB_SLOTS_DESC; "TAB_SLOTS_STK", TAB_SLOTS_STK;
  "TAB_LAYOUT_SLOT", TAB_LAYOUT_SLOT; "TAB_SLOT_ADDR", TAB_SLOT_ADDR; "TAB_CTL_ADDR", TAB_CTL_ADDR;
  "TAB_IN_BYTE", TAB_IN_BYTE; "TAB_MEM_AGREE", TAB_MEM_AGREE; "TAB_REL_KEEP", TAB_REL_KEEP;
  "TAB_REL_RO_STEP", TAB_REL_RO_STEP; "TAB_IMPL_RO", TAB_IMPL_RO; "TAB_CHILD_W", TAB_CHILD_W];;
