(* ========================================================================= *)
(* The leaves over the input: fnv on the input region of the layout         *)
(* implements its meaning (TAB_IMPL_FNV): FIRED with the FNV-1a of the       *)
(* input's bytes it names, REFUSED exactly when they lie outside the input, *)
(* UNSUPPORTED past the loop's cap.                                           *)
(*                                                                           *)
(* Loaded after tables_intern.ml and reader_end.ml.                          *)
(* ========================================================================= *)

(* A child's region 0 bound to the input: any range inside the input reads *)
(* the input's bytes.                                                         *)
let TAB_CHILD_INP = prove
 (`!L inp bw ctl nctl budget cfr st m used t ji.
     drv_child bw ctl budget cfr st m used t /\ tab_layout L bw ctl nctl cfr /\
     MEM ji (tab_slots L) /\ LENGTH inp = val(bw(ji + 1)) /\
     (!i. i < LENGTH inp ==> val(m(word_add (bw ji) (word i))) = EL i inp) /\ val(EL 1 st) = ji
     ==> tisa_base t 0 = bw ji /\ tisa_len t 0 = bw(ji + 1) /\
         (!off n. off + n <= LENGTH inp
                  ==> region_range t 0 off n = list_of_seq (\j. EL (off + j) inp) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `drv_base`)) (concl th) then
     MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC `0` th)) else failwith "") THEN
  ASM_REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `ji:num`]
               TAB_LAYOUT_SLOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[region_range; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `n':num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[region_byte; tisa_read; READ_BYTES_1] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `drv_in (word_add (bw(ji:num)) (word(off + n')):int64) (bw ji) (val(bw(ji + 1):int64))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC TAB_IN_BYTE THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `tmem t (word_add (bw(ji:num)) (word(off + n')):int64) =
                (m:int64->byte) (word_add (bw ji) (word(off + n')))` SUBST1_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
      check (fun th -> is_const_app "drv_child" (concl th))) THEN
    MATCH_MP_TAC DRV_IN_NOT_STACK THEN
    MAP_EVERY EXISTS_TAC [`bw(ji:num):int64`; `val(bw(ji + 1):int64)`] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `val((m:int64->byte) (word_add (bw(ji:num)) (word(off + n')))) < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(m:int64->byte) (word_add (bw(ji:num)) (word(off + n')))` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* fnv's outcome, status and receipt. *)
let TAB_FNV_STATUS = prove
 (`!t k u. tisa_entry_ok fnv t /\ tisa_run fnv t = TStop k u
           ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\ k < 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] FNV_STATUS) THEN
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] FNV_FRAME) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let TAB_IMPL_FNV = prove
 (`!(trow:num->S->num->num list) (tn:num->S->num) (twd:num->num) (tdrop:num->S->num->bool)
    (tapp:num->num->S->num list->S->bool) (tput:num->num->S->num->num->num->S->bool) L inp progs bw ctl nctl budget cfr st ji.
     progs 22 = fnv /\ val(EL 0 st) = 22 /\ val(EL 1 st) = ji /\ MEM (InTab ji) L /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tab_impl (tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr) (trow,tn,twd,tdrop,tapp,tput) inp
                  progs bw ctl budget cfr st`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TAB_IMPL_RO THEN EXISTS_TAC `fnv` THEN
  ASM_REWRITE_TAC[FNV_LEAF_WF; FNV_RO; TAB_FNV_STATUS] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN TAB_LEAF_AT_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_rel]) THEN
  TAB_DESC_TAC `InTab ji` THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                `cfr:int64`; `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `ji:num`]
               TAB_CHILD_INP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(tisa_len t 0) = LENGTH(inp:num list)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `tregs t 1 = word(cw(val(EL 12 (st:int64 list))))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tregs`)) (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC PL_FNV_SPEC THEN REWRITE_TAC[pl_fnv_spec; pl_leaf_ok] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[tab_fnv; tab_key] THEN
  ASM_CASES_TAC `(cw:num->num)(val(EL 10 (st:int64 list))) + cw(val(EL 11 st)) <= LENGTH(inp:num list)` THEN
  ASM_REWRITE_TAC[NOT_LT] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* intern_name: the child holds the table's names interner.                  *)
(* ------------------------------------------------------------------------- *)

(* A state with a names interner's regions (1..4) where s has them, and s's *)
(* bytes in them, holds s's interner: well-formed when s's is, with s's     *)
(* count and rows.                                                           *)
let NAME_SAME_REGIONS = prove
 (`!s t. (!r. 1 <= r /\ r < 5 ==> tisa_base t r = tisa_base s r /\ tisa_len t r = tisa_len s r) /\
         (!r. 1 <= r /\ r < 5 ==> val(tisa_base s r) + val(tisa_len s r) < 2 EXP 64) /\
         16 <= val(tisa_len s 4) /\
         (!r a. 1 <= r /\ r < 5 /\ val(tisa_base s r) <= val a /\ val a < val(tisa_base s r) + val(tisa_len s r)
                ==> tmem t a = tmem s a) /\
         name_ok s
         ==> name_ok t /\ name_count t = name_count s /\
             (!i. i < val(name_count s) ==> name_row_bytes t i = name_row_bytes s i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r off w. 1 <= r /\ r < 5 /\ off + w <= val(tisa_len s r)
                          ==> tisa_read t (word_add (tisa_base s r) (word off)) w =
                              tisa_read s (word_add (tisa_base s r) (word off)) w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_read] THEN AP_TERM_TAC THEN
    REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `2 EXP 64`)) (concl th))) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base s r) (word off):int64) = val(tisa_base s r) + off` ASSUME_TAC THENL
     [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`word_add (tisa_base s r) (word off):int64`; `k:num`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `tisa_base t 1 = tisa_base s 1 /\ tisa_base t 2 = tisa_base s 2 /\ tisa_base t 3 = tisa_base s 3 /\
                tisa_base t 4 = tisa_base s 4 /\ tisa_len t 1 = tisa_len s 1 /\ tisa_len t 2 = tisa_len s 2 /\
                tisa_len t 3 = tisa_len s 3 /\ tisa_len t 4 = tisa_len s 4` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[ARITH]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [name_ok] o check (fun th -> concl th = `name_ok s`)) THEN
  SUBGOAL_THEN `name_count t = name_count s /\ name_used t = name_used s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[name_count; name_used] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`4`; `0`; `8`] (ASSUME `!r off w. 1 <= r /\ r < 5 /\ off + w <= val(tisa_len s r)
                          ==> tisa_read t (word_add (tisa_base s r) (word off)) w =
                              tisa_read s (word_add (tisa_base s r) (word off)) w`)) THEN
      REWRITE_TAC[WORD_ADD_0; ARITH] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MP_TAC(SPECL [`4`; `8`; `8`] (ASSUME `!r off w. 1 <= r /\ r < 5 /\ off + w <= val(tisa_len s r)
                          ==> tisa_read t (word_add (tisa_base s r) (word off)) w =
                              tisa_read s (word_add (tisa_base s r) (word off)) w`)) THEN
      REWRITE_TAC[ARITH] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `16 * val(name_count s) <= val(tisa_len s 1)` ASSUME_TAC THENL
   [UNDISCH_TAC `val(name_count s) <= val(tisa_len s 1) DIV 16` THEN SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < 2 * val(name_count s) ==> name_word t i = name_word s i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[name_word] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
    REWRITE_TAC[ARITH] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. k < val(name_used s) ==> region_byte t 2 k = region_byte s 2 k` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[region_byte] THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
    REWRITE_TAC[ARITH] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < val(name_count s) ==> name_row_bytes t i = name_row_bytes s i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC NAME_ROW_BYTES_TRANSFER THEN EXISTS_TAC `val(name_used s)` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NAME_OK_TRANSFER THEN EXISTS_TAC `s:tisa_state` THEN
  ASM_REWRITE_TAC[name_slots] THEN
  X_GEN_TAC `p:int64` THEN DISCH_TAC THEN REWRITE_TAC[name_slot] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
  REWRITE_TAC[ARITH] THEN
  UNDISCH_TAC `val(p:int64) < val(word_ushr (tisa_len s 3) 3)` THEN
  REWRITE_TAC[GSYM name_slots; NAME_SLOTS_VAL] THEN
  MP_TAC(SPECL [`val(tisa_len s 3:int64)`; `8`] DIVISION) THEN ARITH_TAC);;

(* The regions of a names table at slot j, bound to a step's regions 1..4. *)
let TAB_NAME_SLOTS_TAC =
  REWRITE_TAC[ARITH_RULE `r < 4 <=> r = 0 \/ r = 1 \/ r = 2 \/ r = 3`] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[ADD_CLAUSES];;

(* The child of an intern_name step on the names table at slot j: its      *)
(* regions 1..4 are the table's, within the address space, and hold the    *)
(* memory's bytes.                                                           *)
let TAB_NAME_CHILD = prove
 (`!L bw ctl nctl budget cfr st m used t j.
     tab_layout L bw ctl nctl cfr /\
     MEM j (tab_slots L) /\ MEM (j + 2) (tab_slots L) /\ MEM (j + 4) (tab_slots L) /\ MEM (j + 6) (tab_slots L) /\
     drv_child bw ctl budget cfr st m used t /\
     val(EL 2 st) = j /\ val(EL 3 st) = j + 2 /\ val(EL 4 st) = j + 4 /\ val(EL 5 st) = j + 6
     ==> (!r. r < 4 ==> tisa_base t (r + 1) = bw(j + 2 * r) /\ tisa_len t (r + 1) = bw(j + 2 * r + 1)) /\
         (!r. r < 4 ==> val(bw(j + 2 * r)) + val(bw(j + 2 * r + 1)) < 2 EXP 64) /\
         (!r a. r < 4 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1))) ==> tmem t a = m a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. r < 4 ==> val(EL (1 + (r + 1)) (st:int64 list)) = j + 2 * r /\ MEM (j + 2 * r) (tab_slots L)`
    ASSUME_TAC THENL [TAB_NAME_SLOTS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!r. r < 4 ==> val(bw(j + 2 * r)) + val(bw(j + 2 * r + 1)) < 2 EXP 64 /\
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
                   `m:int64->byte`; `used:int64`; `t:tisa_state`; `r + 1`; `j + 2 * r`] PL_CHILD_REGION) THEN
     ASM_SIMP_TAC[GSYM ADD_ASSOC] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
      check (fun th -> is_const_app "drv_child" (concl th))) THEN
    MATCH_MP_TAC DRV_IN_NOT_STACK THEN
    MAP_EVERY EXISTS_TAC [`bw(j + 2 * r):int64`; `val(bw(j + 2 * r + 1):int64)`] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN ASM_SIMP_TAC[]]);;

(* After the step: the leaf's final state has the same regions 1..4, and   *)
(* its memory there is the memory the driver keeps.                          *)
let TAB_NAME_AFTER = prove
 (`!L bw ctl nctl budget cfr st m used t k u j.
     tab_layout L bw ctl nctl cfr /\
     MEM j (tab_slots L) /\ MEM (j + 2) (tab_slots L) /\ MEM (j + 4) (tab_slots L) /\ MEM (j + 6) (tab_slots L) /\
     drv_child bw ctl budget cfr st m used t /\
     val(EL 2 st) = j /\ val(EL 3 st) = j + 2 /\ val(EL 4 st) = j + 4 /\ val(EL 5 st) = j + 6 /\
     val(EL 17 st) < nctl /\ tisa_entry_ok intern_name t /\ tisa_run intern_name t = TStop k u
     ==> (!r. r < 4 ==> tisa_base u (r + 1) = bw(j + 2 * r) /\ tisa_len u (r + 1) = bw(j + 2 * r + 1)) /\
         (!r a. r < 4 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1)))
                ==> tmem u a = drv_after ctl st u a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `j:num`] TAB_NAME_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. r < 4 ==> MEM (j + 2 * r) (tab_slots L)` ASSUME_TAC THENL
   [TAB_NAME_SLOTS_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[tisa_base; tisa_len] THEN
    MP_TAC(SPECL [`intern_name`; `t:tisa_state`; `k:num`; `u:tisa_state`; `2 * (r + 1)`] PL_RUN_FRAME) THEN
    MP_TAC(SPECL [`intern_name`; `t:tisa_state`; `k:num`; `u:tisa_state`; `2 * (r + 1) + 1`] PL_RUN_FRAME) THEN
    ASM_REWRITE_TAC[NAME_LEAF_WF] THEN
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

(* A byte read equal in two states is the same byte. *)
let TISA_READ1_EQ = prove
 (`!s t (a:int64). tisa_read s a 1 = tisa_read t a 1 ==> tmem s a = tmem t a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_read; READ_BYTES_1] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `val(tmem s (a:int64)) < 2 EXP 64 /\ val(tmem t (a:int64)) < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `tmem s (a:int64)` VAL_BOUND); MP_TAC(ISPEC `tmem t (a:int64)` VAL_BOUND)] THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT; VAL_EQ]]);;

(* A FIRED intern_name keeps the rows below the old count. *)
let NAME_POST_ROWS = prove
 (`!t u. name_ok t /\ name_post t u
         ==> !i. i < val(name_count t) ==> name_row_bytes u i = name_row_bytes t i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[name_ok; name_post] THEN STRIP_TAC THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NAME_ROW_BYTES_TRANSFER THEN EXISTS_TAC `val(name_used t)` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) THEN ASM_SIMP_TAC[]);;

(* Finishing a child's frame leaves the bytes of a described slot's region. *)
let TAB_FINST_KEEP = prove
 (`!L bw ctl nctl budget cfr st m used t k v j a.
     drv_child bw ctl budget cfr st m used t /\ tab_layout L bw ctl nctl cfr /\
     MEM j (tab_slots L) /\ drv_in a (bw j) (val(bw(j + 1)))
     ==> tmem (tisa_finst k v t) a = tmem t a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_READ1_EQ THEN
  MATCH_MP_TAC NAME_FINST_READ THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`]
               TAB_LAYOUT_SLOT) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~drv_stack cfr (a:int64)` MP_TAC THENL
   [MATCH_MP_TAC DRV_IN_NOT_STACK THEN
    MAP_EVERY EXISTS_TAC [`bw(j:num):int64`; `val(bw(j + 1):int64)`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `drv_in (a:int64) (bw(j:num)) (val(bw(j + 1):int64))` THEN
  REWRITE_TAC[drv_stack; drv_in] THEN ASM_ARITH_TAC);;

(* Uses the assumption !r a. r < 4 /\ drv_in a (bw(j + 2r)) .. ==> lhs a = rhs a whose  *)
(* equation's left side mentions the given constant prefix, at r.            *)
let TAB_REGION_ASSUM_TAC tm =
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_forall c && length(fst(strip_forall c)) = 2 && can (find_term ((=) tm)) c &&
       can (find_term ((=) `drv_in`)) c
    then MATCH_MP_TAC th THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] else failwith "TAB_REGION_ASSUM_TAC");;

let TAB_IMPL_NAME = prove
 (`!(trow:num->S->num->num list) (tn:num->S->num) (twd:num->num) (tdrop:num->S->num->bool)
    (tapp:num->num->S->num list->S->bool) (tput:num->num->S->num->num->num->S->bool) L inp progs bw ctl nctl budget cfr st ji j.
     progs 23 = intern_name /\ val(EL 0 st) = 23 /\ val(EL 1 st) = ji /\
     val(EL 2 st) = j /\ val(EL 3 st) = j + 2 /\ val(EL 4 st) = j + 4 /\ val(EL 5 st) = j + 6 /\
     MEM (InTab ji) L /\ MEM (NameTab j) L /\ tab_wf L /\ tab_app_ok (trow,tn,twd,tdrop,tapp,tput) /\
     (!s r. ALL (\b. b < 256) r ==> ?s'. tapp j (j + 6) s r s') /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tab_impl (tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr) (trow,tn,twd,tdrop,tapp,tput) inp
                  progs bw ctl budget cfr st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tab_impl; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:int64->byte`; `used:int64`; `cw:num->num`; `s:S`; `stk:num list`;
                       `t:tisa_state`; `k:num`; `u:tisa_state`] THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_rel]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  TAB_DESC_TAC `NameTab j` THEN TAB_DESC_TAC `InTab ji` THEN
  SUBGOAL_THEN `val(EL 17 (st:int64 list)) < nctl` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) && can (find_term ((=) `10`)) (concl th))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                `cfr:int64`; `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `ji:num`]
               TAB_CHILD_INP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `j:num`] TAB_NAME_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the child holds the table's interner *)
  SUBGOAL_THEN `!r'. 1 <= r' /\ r' < 5
                     ==> tisa_base t r' = tisa_base t' r' /\ tisa_len t r' = tisa_len t' r' /\
                         val(tisa_base t' r') + val(tisa_len t' r') < 2 EXP 64 /\
                         (!a. val(tisa_base t' r') <= val a /\ val a < val(tisa_base t' r') + val(tisa_len t' r')
                              ==> tmem t a = tmem t' a)` ASSUME_TAC THENL
   [X_GEN_TAC `r':num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?r. r < 4 /\ r' = r + 1` (X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC `r' - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `drv_in a (bw(j + 2 * r):int64) (val(bw(j + 2 * r + 1):int64))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[drv_in]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t':tisa_state`; `t:tisa_state`] NAME_SAME_REGIONS) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `t':tisa_state`)) (concl th) && can (find_term ((=) `tisa_base`)) (concl th) &&
      can (find_term ((=) `bw:num->int64`)) (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `val(name_count t) = (tn:num->S->num) (j + 6) s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < (tn:num->S->num) (j + 6) s ==> trow j s i = name_row_bytes t i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i < val(name_count t')` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) && can (find_term ((=) `name_row_bytes t'`)) (concl th) &&
                                               can (find_term ((=) `trow:num->S->num->num list`)) (concl th))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) && can (find_term ((=) `name_row_bytes t'`)) (concl th) &&
                                               can (find_term ((=) `name_row_bytes t`)) (concl th))) THEN
  (* intern_name's domain: given a name inside the input, v1 is its FNV-1a *)
  SUBGOAL_THEN `(cw:num->num)(val(EL 10 (st:int64 list))) + cw(val(EL 11 st)) <= LENGTH(inp:num list)
                ==> cw(val(EL 12 st)) = val(fnv1a fnv_offset (tab_key inp (cw(val(EL 10 st))) (cw(val(EL 11 st)))))`
     ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "tab_leaf" (concl th))) THEN
    REWRITE_TAC[tab_leaf; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[tab_name] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* the run: its result, outcome, fuel and final state *)
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] NAME_RUN) THEN ASM_REWRITE_TAC[name_result] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] NAME_STATUS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`intern_name`; `t:tisa_state`; `k:num`; `u:tisa_state`] TISA_RUN_FUEL) THEN
  ASM_REWRITE_TAC[NAME_LEAF_WF] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`;
                `j:num`] TAB_NAME_AFTER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the memory after the step: m off the stack, the table's regions and the payload word *)
  SUBGOAL_THEN `!a. ~drv_stack cfr a /\ ~drv_in a (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8 /\
                    (!j'. MEM j' (tab_dslots (NameTab j)) ==> ~drv_in a (bw j') (val(bw(j' + 1):int64)))
                    ==> drv_after ctl st u a = (m:int64->byte) a` ASSUME_TAC THENL
   [REWRITE_TAC[tab_dslots; MEM] THEN X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `drv_in`)) (concl th) &&
                               length(fst(strip_forall(concl th))) = 1 && can (find_term ((=) `j + 6`)) (concl th)
      then MAP_EVERY (fun x -> ASSUME_TAC(REWRITE_RULE[] (SPEC x th))) [`j:num`; `j + 2`; `j + 4`; `j + 6`]
      else failwith "") THEN
    MATCH_MP_TAC DRV_STEP_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`intern_name`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                          `used:int64`; `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[NAME_LEAF_WF; NAME_DECLS; tisa_rw; LENGTH] THEN
    X_GEN_TAC `r:num` THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `r < 5 <=> r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4`] THEN
    REWRITE_TAC[IMP_CONJ] THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[FST] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* a names table has no marks *)
  SUBGOAL_THEN `!jm wd. ~MEM (MarkTab jm j (j + 6) wd) L` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_wf]) THEN
    SUBGOAL_THEN `RowTab j (j + 6) wd = NameTab j` MP_TAC THENL
     [MATCH_MP_TAC TAB_SLOTS_DISJOINT THEN MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `j:num`] THEN
      ASM_REWRITE_TAC[tab_dslots; MEM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[distinctness "tabdesc"]];
    ALL_TAC] THEN
  (* a step that did not fire leaves the table's regions *)
  SUBGOAL_THEN `~(k = 1) ==> !r a. r < 4 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1)))
                                   ==> drv_after ctl st u a = (m:int64->byte) a` ASSUME_TAC THENL
   [DISCH_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `tmem u a` THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN TAB_REGION_ASSUM_TAC `tmem u`; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `tmem t a` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && is_neg(lhand(concl th)) &&
                                 can (find_term ((=) `tisa_finst`)) (concl th)
         then REWRITE_TAC[MP th (ASSUME `~(k = 1)`)] else failwith "") THEN
      MATCH_MP_TAC TAB_FINST_KEEP THEN
      MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                            `cfr:int64`; `st:int64 list`; `m:int64->byte`; `used:int64`; `j + 2 * r`] THEN
      ASM_REWRITE_TAC[GSYM ADD_ASSOC] THEN
      UNDISCH_TAC `r < 4` THEN SPEC_TAC(`r:num`,`r:num`) THEN TAB_NAME_SLOTS_TAC;
      TAB_REGION_ASSUM_TAC `tmem t`];
    ALL_TAC] THEN
  ASM_CASES_TAC `(cw:num->num)(val(EL 10 (st:int64 list))) + cw(val(EL 11 st)) <= LENGTH(inp:num list)` THENL
   [ALL_TAC;
    (* outside the input: REFUSED, the tables kept *)
    SUBGOAL_THEN `k = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `~(0 = 1)`]) THEN
    MAP_EVERY EXISTS_TAC [`0`; `s:S`] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL [TAB_LEAF_AT_TAC THEN REWRITE_TAC[tab_name] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TAB_REL_UPDATE THEN
    MAP_EVERY EXISTS_TAC [`m:int64->byte`; `s:S`; `NameTab j`; `j:num`; `j + 6`] THEN
    ASM_REWRITE_TAC[tab_table; tab_frame] THEN
    CONJ_TAC THENL [REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME]; ALL_TAC] THEN
    REWRITE_TAC[tab_mem] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:tisa_state` THEN ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(m:int64->byte) a` THEN CONJ_TAC THENL
     [TAB_REGION_ASSUM_TAC `tmem t`;
      CONV_TAC SYM_CONV THEN TAB_REGION_ASSUM_TAC `drv_after ctl st u`]] THEN
  (* inside the input: the hash is the name's *)
  FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can (find_term ((=) `fnv_offset`)) (concl th)
     then ASSUME_TAC(MP th (ASSUME `(cw:num->num)(val(EL 10 (st:int64 list))) + cw(val(EL 11 st)) <= LENGTH(inp:num list)`))
     else failwith "") THEN
  SUBGOAL_THEN `name_key t = tab_key inp (cw(val(EL 10 (st:int64 list)))) (cw(val(EL 11 st)))` ASSUME_TAC THENL
   [REWRITE_TAC[name_key; tab_key] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `name_hash_ok t` ASSUME_TAC THENL
   [REWRITE_TAC[name_hash_ok; name_hash] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `1` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tregs`)) (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM WORD_VAL] THEN AP_TERM_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && lhand(concl th) = `name_hash_ok t`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(name_count u) < 2 EXP 60` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [name_ok] o check (fun th -> concl th = `name_ok u`)) THEN
    MP_TAC(ISPEC `tisa_len u 1` VAL_BOUND_64) THEN SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 1` THENL
   [ALL_TAC;
    (* inside, not FIRED: the tables kept *)
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `~(k = 1)` &&
                               can (find_term ((=) `drv_after ctl st u`)) (concl th)
      then ASSUME_TAC(MP th (ASSUME `~(k = 1)`)) else failwith "") THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `s:S`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [TAB_LEAF_AT_TAC THEN REWRITE_TAC[tab_name; tab_intern] THEN ASM_REWRITE_TAC[] THEN
                    ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TAB_REL_UPDATE THEN
    MAP_EVERY EXISTS_TAC [`m:int64->byte`; `s:S`; `NameTab j`; `j:num`; `j + 6`] THEN
    ASM_REWRITE_TAC[tab_table; tab_frame] THEN
    CONJ_TAC THENL [REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME]; ALL_TAC] THEN
    REWRITE_TAC[tab_mem] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:tisa_state` THEN ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(m:int64->byte) a` THEN CONJ_TAC THENL
     [TAB_REGION_ASSUM_TAC `tmem t`;
      CONV_TAC SYM_CONV THEN TAB_REGION_ASSUM_TAC `drv_after ctl st u`]] THEN
  (* FIRED *)
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k = 1`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && lhand(concl th) = `1 = 1`)) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`; `u:tisa_state`] NAME_POST_ROWS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [name_post] o check (fun th -> is_const_app "name_post" (concl th))) THENL
   [(* found *)
    FIRST_ASSUM(fun th -> if concl th = `name_count u = name_count t`
      then ASSUME_TAC(AP_TERM `val:int64->num` th) else failwith "") THEN
    SUBGOAL_THEN `val(tisa_fword u 19) < (tn:num->S->num) (j + 6) s` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(trow:num->S->num->num list) j s (val(tisa_fword u 19)) =
                  tab_key inp (cw(val(EL 10 (st:int64 list)))) (cw(val(EL 11 st)))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `name_key t`)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term ((=) `name_row_bytes u`)) (lhs(concl th)) && rhs(concl th) = `name_key t`)) THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`1`; `s:S`] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL [TAB_LEAF_AT_TAC THEN REWRITE_TAC[tab_name; tab_intern] THEN ASM_REWRITE_TAC[] THEN
                    ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TAB_REL_UPDATE THEN
    MAP_EVERY EXISTS_TAC [`m:int64->byte`; `s:S`; `NameTab j`; `j:num`; `j + 6`] THEN
    ASM_REWRITE_TAC[tab_table; tab_frame] THEN
    CONJ_TAC THENL [REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME]; ALL_TAC] THEN
    REWRITE_TAC[tab_mem] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:tisa_state` THEN ASM_SIMP_TAC[] THEN
    FIRST_ASSUM ACCEPT_TAC;
    (* appended *)
    MP_TAC(SPECL [`t:tisa_state`; `u:tisa_state`] NAME_APPEND_ABSENT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `ALL (\b. b < 256) (tab_key inp (cw(val(EL 10 (st:int64 list)))) (cw(val(EL 11 st))))`
      ASSUME_TAC THENL
     [REWRITE_TAC[tab_key; GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
      SUBGOAL_THEN `(cw:num->num)(val(EL 10 (st:int64 list))) + i < LENGTH(inp:num list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `EL:num->num list->num`)) (concl th) &&
                                can (find_term ((=) `m:int64->byte`)) (concl th)
         then REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(cw:num->num)(val(EL 10 (st:int64 list))) + i < LENGTH(inp:num list)`))]
         else failwith "") THEN
      MP_TAC(ISPEC `(m:int64->byte)(word_add (bw(ji:num)) (word((cw:num->num)(val(EL 10 (st:int64 list))) + i)))`
                   VAL_BOUND) THEN
      REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`s:S`; `tab_key inp (cw(val(EL 10 (st:int64 list)))) (cw(val(EL 11 st)))`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `tapp:num->num->S->num list->S->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `s':S`)] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`j:num`; `j + 6`; `s:S`;
                                `tab_key inp (cw(val(EL 10 (st:int64 list)))) (cw(val(EL 11 st)))`; `s':S`] o
      REWRITE_RULE[tab_app_ok] o check (fun th -> is_const_app "tab_app_ok" (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`1`; `s':S`] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL
     [TAB_LEAF_AT_TAC THEN REWRITE_TAC[tab_name; tab_intern] THEN ASM_REWRITE_TAC[LT_REFL] THEN
      REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && lhs(concl th) = `name_key t`)) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(tn:num->S->num) (j + 6) s = val(tisa_fword u 19)` (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TAB_REL_UPDATE THEN
    MAP_EVERY EXISTS_TAC [`m:int64->byte`; `s:S`; `NameTab j`; `j:num`; `j + 6`] THEN
    ASM_REWRITE_TAC[tab_table] THEN
    CONJ_TAC THENL [REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME]; ALL_TAC] THEN
    REWRITE_TAC[tab_mem] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:tisa_state` THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i < (tn:num->S->num) (j + 6) s` THENL
     [ASM_SIMP_TAC[];
      SUBGOAL_THEN `i = (tn:num->S->num) (j + 6) s` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `val(tisa_fword u 19) = (tn:num->S->num) (j + 6) s`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[]]]);;

(* Every theorem this file states, for the audits. *)
let tables_name_theorems =
 ["TAB_CHILD_INP", TAB_CHILD_INP; "TAB_FNV_STATUS", TAB_FNV_STATUS; "TAB_IMPL_FNV", TAB_IMPL_FNV;
  "NAME_SAME_REGIONS", NAME_SAME_REGIONS; "TAB_NAME_CHILD", TAB_NAME_CHILD; "TAB_NAME_AFTER", TAB_NAME_AFTER;
  "TISA_READ1_EQ", TISA_READ1_EQ; "NAME_POST_ROWS", NAME_POST_ROWS; "TAB_FINST_KEEP", TAB_FINST_KEEP;
  "TAB_IMPL_NAME", TAB_IMPL_NAME];;
