(* A staged row stores its key and the slot it will occupy. These functions
   describe the logical contents of the work log and the committed table. *)

let ty_log_lookup = new_recursive_definition list_RECURSION
 `(ty_log_lookup ([]:(A#num)list) n i v = (v:num)) /\
  (ty_log_lookup (CONS (e:A#num) log) n i v =
     ty_log_lookup log (SUC n) i (if i = SND e then SUC n else v))`;;

let ty_log_slot = new_definition
 `ty_log_slot (log:(A#num)list) n (slots:num->num) i =
    if slots i = 0 then ty_log_lookup log n i 0 else slots i`;;

let ty_log_commit = new_recursive_definition list_RECURSION
 `(ty_log_commit ([]:(A#num)list) rows (slots:num->num) = (rows,slots)) /\
  (ty_log_commit (CONS (e:A#num) log) rows slots =
    ty_log_commit log (APPEND rows [FST e])
      (\i. if i = SND e then SUC(LENGTH rows) else slots i))`;;

let ty_log_ok = new_definition
 `ty_log_ok (log:(A#num)list) bound (slots:num->num) <=>
    ALL (\e. SND e < bound /\ slots(SND e) = 0) log /\
    PAIRWISE (\e f. ~(SND e = SND f)) log`;;

let TY_LOG_LOOKUP_ZERO = prove
 (`!(log:(A#num)list) n i v.
      ty_log_lookup log n i v = 0 <=> v = 0 /\ ~MEM i (MAP SND log)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ty_log_lookup; MAP; MEM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_SUC]);;

let TY_LOG_LOOKUP_UNTOUCHED = prove
 (`!(log:(A#num)list) n i v.
      ~MEM i (MAP SND log) ==> ty_log_lookup log n i v = v`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ty_log_lookup; MAP; MEM; DE_MORGAN_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let TY_LOG_LOOKUP_RESERVED = prove
 (`!(log:(A#num)list) n v j.
      PAIRWISE (\e f. ~(SND e = SND f)) log /\ j < LENGTH log
      ==> ty_log_lookup log n (SND(EL j log)) v = SUC(n + j)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LT];
    REWRITE_TAC[LENGTH; PAIRWISE] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    STRUCT_CASES_THEN SUBST_ALL_TAC (SPEC `j:num` num_CASES) THENL
     [REWRITE_TAC[EL; HD; ty_log_lookup; ADD_0] THEN
      MATCH_MP_TAC TY_LOG_LOOKUP_UNTOUCHED THEN
      RULE_ASSUM_TAC (REWRITE_RULE[GSYM ALL_MEM]) THEN
      REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[];
      REWRITE_TAC[EL; TL; ty_log_lookup; ARITH_RULE `n + SUC j = SUC n + j`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE[LT_SUC]) THEN ASM_REWRITE_TAC[]]]);;

let TY_LOG_SLOT_EMPTY = prove
 (`!(log:(A#num)list) n slots i.
      ty_log_slot log n slots i = 0 <=>
      slots i = 0 /\ ~MEM i (MAP SND log)`,
  REWRITE_TAC[ty_log_slot] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[TY_LOG_LOOKUP_ZERO]);;

let TY_LOG_SLOT_RESERVED = prove
 (`!(log:(A#num)list) n slots bound j.
      ty_log_ok log bound slots /\ j < LENGTH log
      ==> ty_log_slot log n slots (SND(EL j log)) = SUC(n + j)`,
  REWRITE_TAC[ty_log_ok] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `slots(SND(EL j (log:(A#num)list))) = 0` ASSUME_TAC THENL
   [MP_TAC(SPEC `j:num`
      (REWRITE_RULE[GSYM ALL_EL] (ASSUME `ALL (\e:A#num. SND e < bound /\ slots(SND e) = 0) log`))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ASM_REWRITE_TAC[ty_log_slot] THEN MATCH_MP_TAC TY_LOG_LOOKUP_RESERVED THEN
    ASM_REWRITE_TAC[]]);;

let TY_LOG_RESERVE = prove
 (`!(log:(A#num)list) n slots bound (key:A) i.
      ty_log_ok log bound slots /\ i < bound /\ ty_log_slot log n slots i = 0
      ==> ty_log_ok (APPEND log [(key,i)]) bound slots`,
  REWRITE_TAC[ty_log_ok; TY_LOG_SLOT_EMPTY; ALL_APPEND; ALL; SND;
              PAIRWISE_APPEND; PAIRWISE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[MEM; SND] THEN
  MAP_EVERY X_GEN_TAC [`e:A#num`;`f:A#num`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[SND] THEN UNDISCH_TAC `~MEM (i:num) (MAP SND (log:(A#num)list))` THEN
  REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]);;

let TY_LOG_FITS = prove
 (`!(log:(A#num)list) slots bound.
      ty_log_ok log bound slots ==> LENGTH log <= bound`,
  REWRITE_TAC[ty_log_ok] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CARD(set_of_list(MAP SND (log:(A#num)list))) = LENGTH log`
    (SUBST1_TAC o SYM) THENL
   [MP_TAC(ISPEC `MAP SND (log:(A#num)list)` HAS_SIZE_SET_OF_LIST) THEN
    ASM_REWRITE_TAC[PAIRWISE_MAP; HAS_SIZE; FINITE_SET_OF_LIST; LENGTH_MAP];
    MATCH_MP_TAC(REWRITE_RULE[FINITE_NUMSEG_LT; CARD_NUMSEG_LT]
      (ISPECL [`set_of_list(MAP SND (log:(A#num)list))`; `{i:num | i < bound}`] CARD_SUBSET)) THEN
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST; IN_ELIM_THM; MEM_MAP] THEN
    RULE_ASSUM_TAC (REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[]]);;

let TY_LOG_COMMIT = prove
 (`!(log:(A#num)list) rows slots.
      ty_log_commit log rows slots =
      (APPEND rows (MAP FST log),
       \i. ty_log_lookup log (LENGTH rows) i (slots i))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ty_log_commit; ty_log_lookup; MAP; APPEND_NIL; APPEND;
                  LENGTH_APPEND; LENGTH; ADD_CLAUSES; GSYM APPEND_ASSOC; ETA_AX]);;

let TY_LOG_COMMIT_VIEW = prove
 (`!(log:(A#num)list) rows slots bound.
      ty_log_ok log bound slots ==>
      ty_log_commit log rows slots =
      (APPEND rows (MAP FST log), ty_log_slot log (LENGTH rows) slots)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ty_log_ok; TY_LOG_COMMIT; PAIR_EQ] THEN
  STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; ty_log_slot] THEN
  X_GEN_TAC `i:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TY_LOG_LOOKUP_UNTOUCHED THEN
  UNDISCH_TAC `ALL (\e:A#num. SND e < bound /\ slots(SND e) = 0) log` THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN ASM_MESON_TAC[]);;

let TY_LOG_COMMIT_ROW = prove
 (`!(log:(A#num)list) rows slots j.
      LENGTH(FST(ty_log_commit log rows slots)) = LENGTH rows + LENGTH log /\
      (j < LENGTH rows ==> EL j (FST(ty_log_commit log rows slots)) = EL j rows) /\
      (j < LENGTH log ==> EL (LENGTH rows + j) (FST(ty_log_commit log rows slots)) =
                          FST(EL j log))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TY_LOG_COMMIT; FST; LENGTH_APPEND; LENGTH_MAP] THEN
  SIMP_TAC[EL_APPEND; EL_MAP;
           ARITH_RULE `~(n + j < n) /\ (n + j) - n = j`]);;

let TY_LOG_COMMIT_APPEND = prove
 (`!(log:(A#num)list) extra rows slots.
       ty_log_commit (APPEND log extra) rows slots =
       ty_log_commit extra (FST(ty_log_commit log rows slots))
                           (SND(ty_log_commit log rows slots))`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; ty_log_commit; FST; SND]);;

(* A reservation at the first empty slot supplies a probe witness for the
   new row after publication. All already occupied slots retain their words. *)
let TY_LOG_COMMIT_PROBE = prove
 (`!(log:(A#num)list) rows slots limit (key:A) (probe:num->num) d.
      ty_log_ok log limit slots /\ probe d < limit /\
      ty_log_slot log (LENGTH rows) slots (probe d) = 0 /\
      (!j. j < d ==> ~(ty_log_slot log (LENGTH rows) slots (probe j) = 0))
      ==> let later = APPEND log [(key,probe d)] in
          let table = SND(ty_log_commit later rows slots) in
          ty_log_ok later limit slots /\
          table(probe d) = SUC(LENGTH rows + LENGTH log) /\
          (!j. j < d ==> ~(table(probe j) = 0)) /\
          (!p. ~(ty_log_slot log (LENGTH rows) slots p = 0)
               ==> table p = ty_log_slot log (LENGTH rows) slots p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `ty_log_ok (APPEND (log:(A#num)list) [(key,(probe:num->num) d)]) limit slots`
    ASSUME_TAC THENL
   [MATCH_MP_TAC TY_LOG_RESERVE THEN EXISTS_TAC `LENGTH(rows:A list)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[TY_LOG_COMMIT_APPEND; ty_log_commit; FST; SND] THEN
  (let before = MP (SPECL [`log:(A#num)list`; `rows:A list`; `slots:num->num`;
                             `limit:num`] TY_LOG_COMMIT_VIEW)
                    (ASSUME `ty_log_ok (log:(A#num)list) limit slots`) in
   ASM_REWRITE_TAC[before; FST; SND; LENGTH_APPEND; LENGTH_MAP]) THEN
  SUBGOAL_THEN `!p. ~(ty_log_slot (log:(A#num)list) (LENGTH(rows:A list)) slots p = 0)
                    ==> ~(p = (probe:num->num) d)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ASM_SIMP_TAC[]]);;

(* Commit reads three words from each 32-byte entry and writes one row and
   one slot. The complete log fits the same loop bound as the hash probes. *)
let TY_LOG_COMMIT_BOUNDS = prove
 (`!(log:(A#num)list) slots old nr nh nw.
      ty_log_ok log (nh DIV 8) slots /\ nh DIV 8 <= 16777216 /\
      old + LENGTH log <= nr DIV 16 /\ 128 <= nw /\ LENGTH log <= (nw - 128) DIV 32
      ==> LENGTH log <= 16777216 /\
          (!i. i < LENGTH log
               ==> 16 * (old + i) + 16 <= nr /\
                   8 * SND(EL i log) + 8 <= nh /\
                   128 + 32 * i + 24 <= nw)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `~(8 = 0) /\ ~(16 = 0) /\ ~(32 = 0)`] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP TY_LOG_FITS) THEN ASM_ARITH_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    (let geometry = CONJUNCT1(REWRITE_RULE[ty_log_ok]
       (ASSUME `ty_log_ok (log:(A#num)list) (nh DIV 8) slots`)) in
     MP_TAC(SPEC `i:num` (REWRITE_RULE[GSYM ALL_EL] geometry))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `SUC(SND(EL i (log:(A#num)list))) <= nh DIV 8` MP_TAC THENL
     [ASM_ARITH_TAC;
      SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `~(8 = 0)`; ADD1] THEN ASM_ARITH_TAC]]);;

let TY_LOG_COLLISION_CONTROL = prove
 (`ty_log_slot [((11,0),4)] 6 (\i:num. 0) 4 = 7 /\
   ~ty_log_ok [((11,0),4); ((11,6),4)] 8 (\i:num. 0)`,
  REWRITE_TAC[ty_log_slot; ty_log_lookup; ty_log_ok; ALL; PAIRWISE; SND; MEM] THEN
  CONV_TAC NUM_REDUCE_CONV);;
