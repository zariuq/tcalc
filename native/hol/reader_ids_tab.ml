(* The counted HOLR operand reader in the record driver's memory relation. *)

needs "native/leaves/ids_next/ids_next_spec.ml";;
needs "native/hol/kernel_table_frames_load.ml";;

(* Uniqueness of canonical decoding. *)

let RD_ID_PAYLOAD_UNIQUE = prove
 (`!n bs xs rest ys tail.
      rd_id_payload n bs xs rest /\ rd_id_payload n bs ys tail
      ==> xs = ys /\ rest = tail`,
  INDUCT_TAC THENL
   [REWRITE_TAC[RD_ID_PAYLOAD_NIL] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `xs:num list` list_CASES) THENL
     [REWRITE_TAC[rd_id_payload; LENGTH; NOT_SUC];
      REWRITE_TAC[RD_ID_PAYLOAD_CONS] THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `next:num list` STRIP_ASSUME_TAC))
        ASSUME_TAC) THEN
      SUBGOAL_THEN `leb_fires (bs:num list) h` ASSUME_TAC THENL
       [REWRITE_TAC[leb_fires] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(SPECL
        [`n:num`;`bs:num list`;`ys:num list`;`tail:num list`;`h:num`;`next:num list`]
        RD_ID_PAYLOAD_PEEL) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `ys':num list` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      REWRITE_TAC[CONS_11] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `next:num list`) THEN ASM_REWRITE_TAC[]]]);;

let RD_ID_LIST_UNIQUE = prove
 (`!bs n tail ids rest n' tail' ids' rest'.
      leb_fires bs n /\ bs = APPEND (leb_enc n) tail /\ rd_id_payload n tail ids rest /\
      leb_fires bs n' /\ bs = APPEND (leb_enc n') tail' /\ rd_id_payload n' tail' ids' rest'
      ==> ids = ids' /\ rest = rest'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n':num = n` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[LEB_FIRES_UNIQUE]; ALL_TAC] THEN
  SUBGOAL_THEN `tail':num list = tail` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[RD_ID_PAYLOAD_CANCEL]; ALL_TAC] THEN
  MATCH_MP_TAC (SPECL
    [`n:num`;`tail:num list`;`ids:num list`;`rest:num list`;`ids':num list`;`rest':num list`]
    RD_ID_PAYLOAD_UNIQUE) THEN ASM_REWRITE_TAC[]);;

(* Read the successful operand stack through the driver. *)

(* A successful counted read binds the driver scratch stack to the decoded
   sequence. The payload is written to a disjoint control word. *)
let TAB_IDS_STACK = prove
 (`!L bw ctl nctl budget cfr st m used t u.
     tab_layout L bw ctl nctl cfr /\ drv_child bw ctl budget cfr st m used t /\
     tisa_entry_ok ids_next t /\ tisa_run ids_next t = TStop 1 u /\
     val(EL 3 st) = 40 /\ val(EL 17 st) < nctl
     ==> ?xs rest. ids_loads t xs rest /\
                   tisa_fword u 19 = word(LENGTH xs) /\
                   pl_stk bw (drv_after ctl st u) xs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`st:int64 list`;
                 `m:int64->byte`;`used:int64`;`t:tisa_state`;`2`;`40`] PL_CHILD_REGION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`1`;`u:tisa_state`] IDS_NEXT_RUN) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ids_next_post] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:num list` (X_CHOOSE_THEN `rest:num list` STRIP_ASSUME_TAC) o CONJUNCT2) THEN
  MAP_EVERY EXISTS_TAC [`xs:num list`;`rest:num list`] THEN
  SUBGOAL_THEN `8 * LENGTH(xs:num list) <= val(bw 41:int64)` ASSUME_TAC THENL
   [ASM_CASES_TAC `8 * LENGTH(xs:num list) <= val(bw 41:int64)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[pl_stk] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
    `budget:int64`;`cfr:int64`;`st:int64 list`;`m:int64->byte`;`used:int64`;
    `t:tisa_state`;`ids_next`;`1`;`u:tisa_state`;`2`;`40`;`i:num`] TAB_AFTER_WORD) THEN
  ANTS_TAC THENL
   [STRIP_ASSUME_TAC(SPEC `L:tabdesc list` TAB_SLOTS_STK) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[IDS_NEXT_LEAF_WF] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[pl_w; GSYM ids_slot] THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN
  let valid = CONJUNCT1(CONJUNCT2(REWRITE_RULE[IDS_LOADS_HOLR]
    (ASSUME `ids_loads t xs rest`))) in
  let member = MP (ISPECL [`xs:num list`;`i:num`] MEM_EL)
                  (ASSUME `i < LENGTH(xs:num list)`) in
  MP_TAC(MP (SPEC `EL i (xs:num list)` (REWRITE_RULE[GSYM ALL_MEM] valid)) member) THEN ARITH_TAC);;

(* Preserve all described tables and unaffected control words. *)

let IDS_REGION_CASES_TAC =
  GEN_TAC THEN REWRITE_TAC[IDS_NEXT_DECLS; tisa_rw; tisa_readable; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r = 1` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r = 2` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[FST] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;;

let IDS_NEXT_RW = prove
 (`!r. tisa_rw (tisa_decls ids_next) r <=> r = 1 \/ r = 2`,
  IDS_REGION_CASES_TAC);;

let IDS_DRIVER_KEEPS = prove
 (`!bw ctl nctl budget cfr st m used t k u a.
     drv_child bw ctl budget cfr st m used t /\
     tisa_entry_ok ids_next t /\ tisa_run ids_next t = TStop k u /\
     val(EL 2 st) = 58 /\ val(EL 3 st) = 40 /\
     val ctl + 8 * nctl <= 2 EXP 64 /\ val(EL 17 st) < nctl /\
     ~drv_stack cfr a /\ ~drv_in a (bw 58) (val(bw 59)) /\ ~drv_in a (bw 40) (val(bw 41)) /\
     ~drv_in a (word_add ctl (word(8 * val(EL 17 st)))) 8
     ==> drv_after ctl st u a = m a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
  MAP_EVERY EXISTS_TAC [`ids_next`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                        `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[IDS_NEXT_LEAF_WF; IDS_NEXT_RW] THEN GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[drv_base; drv_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let TAB_REL_AGREE_OPERANDS = prove
 (`!tb L inp bw ctl nctl cfr m m' cw (s:S) stk stk' p v.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ p < nctl /\ 6 < p /\
     (!d j a. MEM d L /\ MEM j (tab_dslots d) /\ drv_in a (bw j) (val(bw(j + 1)))
              ==> m' a = m a) /\
     (!a. drv_in a ctl (8 * nctl) /\ ~drv_in a (word_add ctl (word(8 * p))) 8 ==> m' a = m a) /\
     drv_word m' (word_add ctl (word(8 * p))) = v /\
     pl_stk bw m' stk'
     ==> tab_rel tb L inp bw ctl nctl cfr m' (pl_set cw p (val v),s,stk')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_rel] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[tab_layout] o
              check (is_const_app "tab_layout" o concl)) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_set] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    MATCH_MP_TAC PL_CWORDS_SET THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `d:tabdesc` THEN DISCH_TAC THEN
    MATCH_MP_TAC TAB_MEM_AGREE THEN EXISTS_TAC `m:int64->byte` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[ALL_MEM]; ALL_TAC] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LT_IMP_LE THEN ASM_MESON_TAC[TAB_SLOTS_DESC];
      REPEAT STRIP_TAC THEN ASM_MESON_TAC[]]]);;

(* The reader can replace the operand stack and update the cursor and one
   control word. Table descriptions that do not use that stack keep their
   entire contents. *)
let TAB_IDS_KEEP = prove
 (`!tb L inp bw ctl nctl budget cfr st m used t k u cw (s:S) stk stk'.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     rd_layout bw ctl nctl cfr /\ rd_tab_apart L bw /\
     (!d. MEM d L ==> ~MEM 40 (tab_dslots d)) /\
     drv_child bw ctl budget cfr st m used t /\
     tisa_entry_ok ids_next t /\ tisa_run ids_next t = TStop k u /\
     val(EL 2 st) = 58 /\ val(EL 3 st) = 40 /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st) /\
     pl_stk bw (drv_after ctl st u) stk'
     ==> tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
          (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),s,stk')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC TAB_REL_AGREE_OPERANDS THEN
  MAP_EVERY EXISTS_TAC [`m:int64->byte`; `stk:num list`] THEN
  ASM_REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME] THEN REWRITE_TAC[GSYM drv_after] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[tab_rel] o check (is_const_app "tab_rel" o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[tab_layout] o check (is_const_app "tab_layout" o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rd_layout] o check (is_const_app "rd_layout" o concl)) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`d:tabdesc`; `j:num`; `a:int64`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `MEM j (tab_slots L) /\ ~(j = 40)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[TAB_SLOTS_DESC]; ALL_TAC] THEN
    MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`;
                 `j:num`; `val(EL 17 (st:int64 list))`; `a:int64`] TAB_SLOT_ADDR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC IDS_DRIVER_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                          `used:int64`; `t:tisa_state`; `k:num`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `j = 54` THENL
       [SUBST_ALL_TAC(ASSUME `j = 54`) THEN
        RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
        MATCH_MP_TAC DRV_APART_IN THEN
        MAP_EVERY EXISTS_TAC [`bw 54:int64`; `val(bw 55:int64)`] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC DRV_APART_IN THEN
        MAP_EVERY EXISTS_TAC [`bw(j:num):int64`; `val(bw(j + 1):int64)`] THEN
        ASM_MESON_TAC[rd_tab_apart]];
      MATCH_MP_TAC DRV_APART_IN THEN
      MAP_EVERY EXISTS_TAC [`bw(j:num):int64`; `val(bw(j + 1):int64)`] THEN
      MP_TAC(SPEC `L:tabdesc list` TAB_SLOTS_STK) THEN
      SUBGOAL_THEN `MEM 40 (tab_slots L) ==> drv_apart (bw j) (val(bw(j + 1))) (bw 40) (val(bw(40 + 1)))`
        MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[]];
    X_GEN_TAC `a:int64` THEN STRIP_TAC THEN MATCH_MP_TAC IDS_DRIVER_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                          `used:int64`; `t:tisa_state`; `k:num`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC TAB_CTL_ADDR THEN MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `bw:num->int64`;
                              `ctl:int64`; `nctl:num`] THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[RD_CTL_NOT_RD];
      MATCH_MP_TAC DRV_APART_IN THEN MAP_EVERY EXISTS_TAC [`ctl:int64`; `8 * nctl`] THEN
      MP_TAC(SPEC `L:tabdesc list` TAB_SLOTS_STK) THEN
      SUBGOAL_THEN `MEM 40 (tab_slots L) ==> drv_apart (bw 40) (val(bw(40 + 1))) ctl (8 * nctl)`
        MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[]]]);;

(* Read the cursor and preserve the input bytes. *)

let IDS_NEXT_READABLE = prove
 (`!r. tisa_readable (tisa_decls ids_next) r <=> r = 0 \/ r = 1 \/ r = 2`,
  IDS_REGION_CASES_TAC);;

let RD_IDS_PREFIX_LENGTH = prove
 (`!inp c ids rest. rd_from inp c = APPEND (holr_ids ids) rest
     ==> c + LENGTH(holr_ids ids) <= LENGTH inp`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:num list->num`) THEN
  REWRITE_TAC[rd_from; LENGTH_LIST_OF_SEQ; LENGTH_APPEND] THEN
  MP_TAC(SPEC `LENGTH(ids:num list)` LEB_ENC_LENGTH_POS) THEN
  REWRITE_TAC[holr_ids; LENGTH_APPEND] THEN ARITH_TAC);;

let IDS_LOADS_UNIQUE = prove
 (`!t xs rest ys tail. ids_loads t xs rest /\ ids_loads t ys tail ==> xs = ys /\ rest = tail`,
  REWRITE_TAC[ids_loads; ids_count_good] THEN
  MESON_TAC[RD_ID_LIST_UNIQUE; leb_fires]);;

(* The input remains the same byte string. The next cursor is the physical
   word of the reader state, after the driver places its receipt elsewhere. *)
let RD_IDS_AFTER_CURSOR = prove
 (`!bw ctl nctl budget cfr st m used t k u inp c.
     rd_rel bw ctl nctl cfr m inp c /\ 48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\
     drv_child bw ctl budget cfr st m used t /\
     tisa_entry_ok ids_next t /\ tisa_run ids_next t = TStop k u /\
     val(EL 2 st) = 58 /\ val(EL 3 st) = 40 /\ val(EL 17 st) < nctl
     ==> rd_rel bw ctl nctl cfr (drv_after ctl st u) inp (val(ids_initial_cursor u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[rd_rel] (ASSUME `rd_rel bw ctl nctl cfr m inp c`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[rd_layout] (ASSUME `rd_layout bw ctl nctl cfr`)) THEN
  REWRITE_TAC[rd_rel] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ABBREV_TAC `a = word_add (bw 54) (word i):int64` THEN
    SUBGOAL_THEN `drv_in a (bw 54) (val(bw 55))` ASSUME_TAC THENL
     [EXPAND_TAC "a" THEN MATCH_MP_TAC TAB_IN_BYTE THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`nctl:num`;`cfr:int64`;`a:int64`] RD_INP_ADDR0) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `drv_after ctl st u a = (m:int64->byte) a` SUBST1_TAC THENL
     [MATCH_MP_TAC IDS_DRIVER_KEEPS THEN
      MAP_EVERY EXISTS_TAC [`bw:num->int64`;`nctl:num`;`budget:int64`;`cfr:int64`;
                            `used:int64`;`t:tisa_state`;`k:num`] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC DRV_APART_IN THEN MAP_EVERY EXISTS_TAC [`bw 54:int64`;`val(bw 55:int64)`] THEN
        (let inp_slots = CONJUNCT2(CONJUNCT2(CONJUNCT1(
           MATCH_MP RD_LAYOUT_AT (ASSUME `rd_layout bw ctl nctl cfr`)))) in
         MP_TAC(SPEC `40` inp_slots) THEN
         REWRITE_TAC[pl_slots; MEM] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[]);
        ASM_MESON_TAC[DRV_CTL_WORD_IN]];
      EXPAND_TAC "a" THEN ASM_SIMP_TAC[]];
    SUBGOAL_THEN `tisa_base u 1 = (bw:num->int64) 58` ASSUME_TAC THENL
     [MP_TAC(SPECL [`ids_next`;`t:tisa_state`;`k:num`;`u:tisa_state`;`1`] TISA_RUN_REGIONS) THEN
      ASM_REWRITE_TAC[IDS_NEXT_READABLE; IDS_NEXT_LEAF_WF] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
      MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`st:int64 list`;
                     `m:int64->byte`;`used:int64`;`t:tisa_state`;`1`;`58`] PL_CHILD_REGION) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `drv_word (drv_after ctl st u) (bw 58) = drv_word (tmem u) (bw 58)` ASSUME_TAC THENL
     [MATCH_MP_TAC DRV_WORD_AREA0 THEN EXISTS_TAC `val(bw 59:int64)` THEN
      REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `a:int64` THEN DISCH_TAC THEN REWRITE_TAC[drv_after] THEN
      MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN REWRITE_TAC[GSYM drv_in] THEN
      CONJ_TAC THENL
       [MP_TAC(SPECL [`ctl:int64`;`8 * val(EL 17 (st:int64 list))`] TISA_VAL_OFFSET) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
        ASM_MESON_TAC[DRV_CTL_WORD_IN; RD_ST_ADDR0]];
      ASM_REWRITE_TAC[pl_mw; MULT_CLAUSES; WORD_ADD_0; ids_initial_cursor; tisa_read; GSYM drv_word]]]);;

(* Classify every result of the counted reader. *)

let rd_ids_read = new_definition
 `rd_ids_read inp c xs rest <=>
    rd_from inp c = APPEND (holr_ids xs) rest /\
    ALL (\x. x < 2 EXP 62) xs /\ LENGTH xs < 2 EXP 62`;;

let rd_ids_post = new_definition
 `rd_ids_post inp c capacity k stk c' (pay:int64) <=>
    (k = 0 /\ ~(?xs rest. rd_ids_read inp c xs rest) /\ c' = c) \/
    (?xs rest. rd_ids_read inp c xs rest /\
      if 8 * LENGTH xs <= capacity
      then k = 1 /\ stk = xs /\ c' = c + LENGTH(holr_ids xs) /\ pay = word(LENGTH xs)
      else k = 2 /\ c' = c)`;;

let TAB_STEP_IDS = prove
 (`!tb L inp bw ctl nctl budget cfr st m used t k u cw (s:S) stk c.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ rd_rel bw ctl nctl cfr m inp c /\
     rd_tab_apart L bw /\ (!d. MEM d L ==> ~MEM 40 (tab_dslots d)) /\
     drv_child bw ctl budget cfr st m used t /\
     tisa_entry_ok ids_next t /\ tisa_run ids_next t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 3 st) = 40 /\
     val(EL 17 st) < nctl /\ 6 < val(EL 17 st)
     ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = used /\
         ?stk' c'. rd_ids_post inp c (val(bw 41)) k stk' c' (tisa_fword u 19) /\
           tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
             (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),s,stk') /\
           rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c'`,
  let FRAME_TAC =
    CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_FRAME) THEN
  ASSUME_TAC(CONJUNCT1(REWRITE_RULE[rd_rel] (ASSUME `rd_rel bw ctl nctl cfr m inp c`))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DRV_CHILD_RECEIPT) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP TISA_RUN_STATUS) THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;
                `st:int64 list`;`m:int64->byte`;`used:int64`;`t:tisa_state`;`inp:num list`;`c:num`] RD_CHILD0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`st:int64 list`;
                `m:int64->byte`;`used:int64`;`t:tisa_state`;`2`;`40`] PL_CHILD_REGION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!xs rest. rd_ids_read inp c xs rest <=> ids_loads t xs rest` ASSUME_TAC THENL
   [REWRITE_TAC[rd_ids_read; IDS_LOADS_HOLR; ids_count_input; GSYM PL_IDS_CURSOR] THEN
    REWRITE_TAC[ASSUME `region_from t 0 (pl_cursor t) = rd_from inp c`];
    ALL_TAC] THEN
  SUBGOAL_THEN `rd_rel bw ctl nctl cfr (drv_after ctl st u) inp (val(ids_initial_cursor u))` ASSUME_TAC THENL
   [MATCH_MP_TAC RD_IDS_AFTER_CURSOR THEN
    MAP_EVERY EXISTS_TAC [`budget:int64`;`m:int64->byte`;`used:int64`;`t:tisa_state`;`k:num`;`c:num`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!stk'. pl_stk bw (drv_after ctl st u) stk'
          ==> tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
               (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),(s:S),stk')` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC TAB_IDS_KEEP THEN
    MAP_EVERY EXISTS_TAC [`budget:int64`;`m:int64->byte`;`used:int64`;`t:tisa_state`;`k:num`;`stk:num list`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_stk bw (drv_after ctl st u) []` ASSUME_TAC THENL
   [REWRITE_TAC[pl_stk; LENGTH; MULT_CLAUSES; LE_0; LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] IDS_NEXT_RUN) THEN
  ASM_REWRITE_TAC[ids_next_post] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC) THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
    SUBGOAL_THEN `val(ids_initial_cursor u) = c` ASSUME_TAC THENL
     [SUBST1_TAC(ASSUME `ids_initial_cursor u = ids_initial_cursor t`) THEN
      REWRITE_TAC[GSYM PL_IDS_CURSOR; ASSUME `pl_cursor t = c`];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`[]:num list`;`val(ids_initial_cursor u)`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[rd_ids_post] THEN DISJ1_TAC THEN ASM_REWRITE_TAC[];
      FRAME_TAC];
    FIRST_X_ASSUM(X_CHOOSE_THEN `xs:num list` (X_CHOOSE_THEN `rest:num list` STRIP_ASSUME_TAC)) THEN
    (let read = SPECL [`xs:num list`;`rest:num list`]
       (ASSUME `!xs rest. rd_ids_read inp c xs rest <=> ids_loads t xs rest`) in
     ASSUME_TAC(EQ_MP (SYM read) (ASSUME `ids_loads t xs rest`))) THEN
    ASM_CASES_TAC `8 * LENGTH(xs:num list) <= val(bw 41:int64)` THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `val(ids_initial_cursor u) = c + LENGTH(holr_ids xs)` ASSUME_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o check (fun th ->
          is_eq(concl th) && lhs(concl th) = `ids_initial_cursor u`)) THEN
        ASM_REWRITE_TAC[GSYM PL_IDS_CURSOR; holr_ids; holr_flat; LENGTH_APPEND; ADD_ASSOC] THEN
        MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN
        SUBGOAL_THEN `c + LENGTH(holr_ids xs) <= LENGTH(inp:num list)` MP_TAC THENL
         [MATCH_MP_TAC RD_IDS_PREFIX_LENGTH THEN EXISTS_TAC `rest:num list` THEN
          ASM_MESON_TAC[rd_ids_read];
          MP_TAC(ISPEC `bw 55:int64` VAL_BOUND_64) THEN
          UNDISCH_TAC `rd_rel bw ctl nctl cfr m inp c` THEN REWRITE_TAC[rd_rel] THEN
          REWRITE_TAC[holr_ids; holr_flat; LENGTH_APPEND] THEN ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(SPECL [`L:tabdesc list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;
        `cfr:int64`;`st:int64 list`;`m:int64->byte`;`used:int64`;`t:tisa_state`;`u:tisa_state`] TAB_IDS_STACK) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `ys:num list` (X_CHOOSE_THEN `tail:num list` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `ys:num list = xs` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[IDS_LOADS_UNIQUE]; ALL_TAC] THEN
      (let frame = ASSUME `!stk'. pl_stk bw (drv_after ctl st u) stk'
              ==> tab_rel tb L inp bw ctl nctl cfr (drv_after ctl st u)
                   (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),(s:S),stk')` in
       ASSUME_TAC(REWRITE_RULE[ASSUME `tisa_fword u 19 = word(LENGTH(xs:num list))`] frame)) THEN
      MAP_EVERY EXISTS_TAC [`xs:num list`;`val(ids_initial_cursor u)`] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[rd_ids_post] THEN DISJ2_TAC THEN
        MAP_EVERY EXISTS_TAC [`xs:num list`;`rest:num list`] THEN ASM_REWRITE_TAC[];
        FRAME_TAC];
      SUBGOAL_THEN `val(ids_initial_cursor u) = c` ASSUME_TAC THENL
       [SUBST1_TAC(ASSUME `ids_initial_cursor u = ids_initial_cursor t`) THEN
        REWRITE_TAC[GSYM PL_IDS_CURSOR; ASSUME `pl_cursor t = c`];
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`[]:num list`;`val(ids_initial_cursor u)`] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[rd_ids_post] THEN DISJ2_TAC THEN
        MAP_EVERY EXISTS_TAC [`xs:num list`;`rest:num list`] THEN ASM_REWRITE_TAC[];
        FRAME_TAC]]]);;

(* Install the counted operand read in the driver plan. *)

(* Reader leaf 27 receives input, cursor state and operand stack.
   Control word 12 holds the returned number of decoded IDs. *)
let pl_ids_next_step = new_definition
  (mk_eq(`pl_ids_next_step:int64 list`, pl_step 27 [54;58;40] 0 0 [] 12));;

let RD_IDS_POST_CODE = prove
 (`!inp c cap k stk c' pay.
     rd_ids_post inp c cap k stk c' pay ==> (k = 0 \/ k = 1 \/ k = 2)`,
  REWRITE_TAC[rd_ids_post] THEN REPEAT GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC THENL
   [ASM_MESON_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_THEN `xs:num list` (X_CHOOSE_THEN `rest:num list` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THEN ASM_MESON_TAC[]]);;

let IDS_STEP_DRV = prove
 (`!tb L inp progs bw ctl nctl budget cfr i m used res cw (s:S) stk c.
     progs 27 = ids_next /\ 12 < nctl /\
     drv_sem progs bw ctl budget cfr [pl_ids_next_step] i m used res /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ rd_rel bw ctl nctl cfr m inp c /\
     rd_tab_apart L bw /\ (!d. MEM d L ==> ~MEM 40 (tab_dslots d))
     ==> if val budget < val used then res = (word 3,i,m,used)
         else ?k stk' c' pay.
           SND(SND(SND res)) = used /\ FST res = word k /\
           FST(SND res) = (if k = 1 then i + 1 else i) /\
           rd_ids_post inp c (val(bw 41)) k stk' c' pay /\
           tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND res))) (pl_set cw 12 (val pay),s,stk') /\
           rd_rel bw ctl nctl cfr (FST(SND(SND res))) inp c'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_const_app "drv_sem" o concl)) THEN
  REWRITE_TAC[drv_sem; pl_ids_next_step] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:tisa_state` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
     (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
     `L:tabdesc list`;`inp:num list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;
     lhand(concl pl_ids_next_step);`m:int64->byte`;`used:int64`;`t:tisa_state`;`k:num`;`u:tisa_state`;
     `cw:num->num`;`s:S`;`stk:num list`;`c:num`] TAB_STEP_IDS) THEN
  REWRITE_TAC[pl_ids_next_step] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `stk':num list` (X_CHOOSE_THEN `c':num` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(tisa_fword u 18 = word 1) <=> k = 1` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP RD_IDS_POST_CODE) THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FST; SND] THEN MAP_EVERY EXISTS_TAC
    [`k:num`;`stk':num list`;`c':num`;`tisa_fword u 19`] THEN ASM_REWRITE_TAC[]);;
