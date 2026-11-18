(* Physical invariants of the counted publication loop. Rows and slots are
   installed from the frozen work log before the type count is published. *)

needs "native/leaves/ty_list/ty_list_commit_row.ml";;

let ty_list_regions_apart = new_definition
 `ty_list_regions_apart st r q <=>
    val(tisa_base st r) + val(tisa_len st r) <= val(tisa_base st q) \/
    val(tisa_base st q) + val(tisa_len st q) <= val(tisa_base st r)`;;

let ty_list_frame_apart = new_definition
 `ty_list_frame_apart st r <=>
    val(tisa_base st r) + val(tisa_len st r) <= val(tregs st 0) \/
    val(tregs st 0) + 192 <= val(tisa_base st r)`;;

let ty_list_commit_geometry = new_definition
 `ty_list_commit_geometry st <=>
    val(tregs st 0) + 192 <= 2 EXP 64 /\
    (!r. r < 3 \/ r = 7
         ==> val(tisa_base st r) + val(tisa_len st r) < 2 EXP 64 /\
             ty_list_frame_apart st r) /\
    (!r. r < 3 ==> ty_list_regions_apart st r 7) /\
    ty_list_regions_apart st 0 1 /\
    ty_list_regions_apart st 0 2 /\ ty_list_regions_apart st 1 2 /\
    8 <= val(tisa_len st 2) /\ 256 <= val(tisa_len st 7)`;;

let ty_list_outside = new_definition
 `ty_list_outside st r (a:int64) <=>
    val a < val(tisa_base st r) \/
    val(tisa_base st r) + val(tisa_len st r) <= val a`;;

let ty_list_commit_view = new_definition
 `ty_list_commit_view st u <=>
    tregs u 0 = tregs st 0 /\
    (!a. ty_list_outside st 0 a /\ ty_list_outside st 1 a ==> tmem u a = tmem st a)`;;

let TY_LIST_COMMIT_VIEW_FWORD = prove
 (`!st u i. ty_list_commit_geometry st /\ ty_list_commit_view st u /\ i < 24
             ==> tisa_fword u i = tisa_fword st i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ty_list_commit_geometry; ty_list_commit_view] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[tisa_fword; tisa_frame; tisa_read] THEN
  AP_TERM_TAC THEN REWRITE_TAC[READ_BYTES_EQ] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o SPEC
    `word_add (word_add (tregs st 0) (word(8 * i))) (word j):int64` o
    check (fun th -> can (find_term ((=) `ty_list_outside`)) (concl th))) THEN
  REWRITE_TAC[ty_list_outside; TISA_WORD_ADD_OFFSETS] THEN
  SUBGOAL_THEN
   `val(word_add (tregs st 0) (word(8 * i + j)):int64) = val(tregs st 0) + 8 * i + j`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM ADD_ASSOC] THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if can (find_term ((=) `ty_list_frame_apart`)) (concl th)
    then MAP_EVERY (fun r -> MP_TAC(SPEC r th)) [`0:num`; `1:num`]
    else NO_TAC) THEN
  REWRITE_TAC[ty_list_frame_apart] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let TY_LIST_COMMIT_VIEW_REGIONS = prove
 (`!st u r. ty_list_commit_geometry st /\ ty_list_commit_view st u /\ r < 12
      ==> tisa_base u r = tisa_base st r /\ tisa_len u r = tisa_len st r`,
  REWRITE_TAC[tisa_base; tisa_len] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TY_LIST_COMMIT_VIEW_FWORD THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let TY_LIST_COMMIT_VIEW_GEOMETRY = prove
 (`!st u. ty_list_commit_geometry st /\ ty_list_commit_view st u
               ==> ty_list_commit_geometry u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. r < 12 ==> tisa_base u r = tisa_base st r /\ tisa_len u r = tisa_len st r`
   ASSUME_TAC THENL [ASM_MESON_TAC[TY_LIST_COMMIT_VIEW_REGIONS]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[ty_list_commit_geometry] o
    check (fun th -> fst(strip_comb(concl th)) = `ty_list_commit_geometry`)) THEN
  REWRITE_TAC[ty_list_commit_geometry; ty_list_frame_apart; ty_list_regions_apart] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ty_list_commit_view] o
    check (fun th -> fst(strip_comb(concl th)) = `ty_list_commit_view`)) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 12 /\ 1 < 12 /\ 2 < 12 /\ 7 < 12`;
    ARITH_RULE `r < 3 \/ r = 7 ==> r < 12`; ARITH_RULE `r < 3 ==> r < 12`]);;

let TY_LIST_COMMIT_VIEW_WORD = prove
 (`!st u r offset.
      ty_list_commit_geometry st /\ ty_list_commit_view st u /\ (r = 2 \/ r = 7) /\
      offset + 8 <= val(tisa_len st r)
      ==> ty_list_word u r offset = ty_list_word st r offset`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `tisa_base u r = tisa_base st r` ASSUME_TAC THENL
   [SUBGOAL_THEN `r < 12` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_MESON_TAC[TY_LIST_COMMIT_VIEW_REGIONS]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ty_list_commit_view] o
    check (fun th -> fst(strip_comb(concl th)) = `ty_list_commit_view`)) THEN
  ASM_REWRITE_TAC[ty_list_word; tisa_read] THEN
  AP_TERM_TAC THEN REWRITE_TAC[READ_BYTES_EQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o SPEC
    `word_add (word_add (tisa_base st r) (word offset)) (word i):int64` o
    check (fun th -> can (find_term ((=) `ty_list_outside`)) (concl th))) THEN
  REWRITE_TAC[ty_list_outside; TISA_WORD_ADD_OFFSETS] THEN
  SUBGOAL_THEN
   `val(word_add (tisa_base st r) (word(offset + i)):int64) = val(tisa_base st r) + (offset + i)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN
    FIRST_ASSUM(MP_TAC o SPEC `r:num` o CONJUNCT1 o CONJUNCT2 o
      REWRITE_RULE[ty_list_commit_geometry] o
      check (fun th -> fst(strip_comb(concl th)) = `ty_list_commit_geometry`)) THEN
    ASM_MESON_TAC[ARITH_RULE `r = 2 \/ r = 7 ==> r < 3 \/ r = 7`;
      ARITH_RULE `b + n < m /\ off + 8 <= n /\ i < 8 ==> b + off + i < m`;
      ADD_ASSOC];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ty_list_commit_geometry] o
    check (fun th -> fst(strip_comb(concl th)) = `ty_list_commit_geometry`)) THEN
  FIRST_ASSUM(fun th ->
    if can (find_term ((=) `ty_list_regions_apart`)) (concl th) && is_forall(concl th)
    then MAP_EVERY (fun r -> MP_TAC(SPEC r th)) [`0:num`; `1:num`]
    else NO_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ty_list_regions_apart]) THEN
  REWRITE_TAC[ty_list_regions_apart] THEN
  UNDISCH_TAC `r = 2 \/ r = 7` THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_ARITH_TAC);;

let TY_LIST_COMMIT_GEOMETRY_ENTRY = prove
 (`!st. tisa_entry_ok ty_list st ==> ty_list_commit_geometry st`,
  GEN_TAC THEN
  REWRITE_TAC[ty_list; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_pair_ok;
    tisa_region_ok; tisa_frame; tisa_init_ok; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `~(val(tisa_len st 0) = 0) /\ ~(val(tisa_len st 1) = 0) /\
    ~(val(tisa_len st 2) = 0) /\ ~(val(tisa_len st 7) = 0)`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `8 <= n \/ 16 <= n \/ 256 <= n ==> ~(n = 0)`];
    RULE_ASSUM_TAC(REWRITE_RULE(map ASSUME
      [`~(val(tisa_len st 0) = 0)`; `~(val(tisa_len st 1) = 0)`;
       `~(val(tisa_len st 2) = 0)`; `~(val(tisa_len st 7) = 0)`])) THEN
    REWRITE_TAC[ty_list_commit_geometry; ty_list_frame_apart; ty_list_regions_apart] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN REWRITE_TAC[ARITH_RULE `r < 3 <=> r = 0 \/ r = 1 \/ r = 2`] THEN
    GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC[]]);;

let TY_LIST_COMMIT_VIEW_SETREG = prove
 (`!st u r (w:int64). ~(r = 0)
        ==> (ty_list_commit_view st (tisa_setreg r w u) <=> ty_list_commit_view st u)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ty_list_commit_view; TISA_TMEM_SETREG; TISA_TREGS_SETREG;
                                       EQ_SYM_EQ]);;

let TY_LIST_COMMIT_VIEW_TRANS = prove
 (`!st u v. ty_list_commit_geometry st /\ ty_list_commit_view st u /\ ty_list_commit_view u v
      ==> ty_list_commit_view st v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(tisa_base u 0 = tisa_base st 0 /\ tisa_len u 0 = tisa_len st 0) /\
                tisa_base u 1 = tisa_base st 1 /\ tisa_len u 1 = tisa_len st 1`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[TY_LIST_COMMIT_VIEW_REGIONS; ARITH_RULE `0 < 12 /\ 1 < 12`];
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[ty_list_commit_view; ty_list_outside] o
      check (fun th -> concl th = `ty_list_commit_view st u`)) THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[ty_list_commit_view; ty_list_outside] o
      check (fun th -> concl th = `ty_list_commit_view u v`)) THEN
    ASM_REWRITE_TAC[ty_list_commit_view; ty_list_outside] THEN MESON_TAC[]]);;

let ty_list_reserved_slot = new_definition
 `ty_list_reserved_slot st i = val(ty_list_word st 7 (128 + 32 * i + 16))`;;

let ty_list_commit_ready = new_definition
 `ty_list_commit_ready st old n <=>
    ty_list_commit_geometry st /\
    ty_list_word st 2 0 = word old /\
    ty_list_word st 7 24 = word old /\ ty_list_word st 7 48 = word n /\
    n <= 16777216 /\ 16 * (old + n) <= val(tisa_len st 0) /\
    128 + 32 * n <= val(tisa_len st 7) /\
    (!i. i < n ==> 8 * ty_list_reserved_slot st i + 8 <= val(tisa_len st 1))`;;

let TY_LIST_READY_ITER_BOUNDS = prove
 (`!st old n i.
      ty_list_commit_ready st old n /\ i < n
      ==> 16 * (old + i) + 16 <= val(tisa_len st 0) /\
          8 * ty_list_reserved_slot st i + 8 <= val(tisa_len st 1) /\
          128 + 32 * i + 24 <= val(tisa_len st 7)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ty_list_commit_ready] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_SIMP_TAC[] THEN ASM_ARITH_TAC);;

let TY_LIST_READY_AFTER_VIEW = prove
 (`!st u old n. ty_list_commit_ready st old n /\ ty_list_commit_view st u
      ==> ty_list_commit_ready u old n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ty_list_commit_ready] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `!r. r < 12 ==> tisa_base u r = tisa_base st r /\ tisa_len u r = tisa_len st r`
   ASSUME_TAC THENL [ASM_MESON_TAC[TY_LIST_COMMIT_VIEW_REGIONS]; ALL_TAC] THEN
  SUBGOAL_THEN `8 <= val(tisa_len st 2) /\ 256 <= val(tisa_len st 7)`
   STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ty_list_commit_geometry]; ALL_TAC] THEN
  SUBGOAL_THEN `!r k. (r = 2 \/ r = 7) /\ k + 8 <= val(tisa_len st r)
               ==> ty_list_word u r k = ty_list_word st r k` ASSUME_TAC THENL
   [ASM_MESON_TAC[TY_LIST_COMMIT_VIEW_WORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ty_list_commit_geometry u` ASSUME_TAC THENL
   [ASM_MESON_TAC[TY_LIST_COMMIT_VIEW_GEOMETRY]; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 12 /\ 1 < 12 /\ 2 < 12 /\ 7 < 12`;
    ARITH_RULE `8 <= n ==> 0 + 8 <= n`;
    ARITH_RULE `256 <= n ==> 24 + 8 <= n /\ 48 + 8 <= n`] THEN
  REWRITE_TAC[ty_list_reserved_slot] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(128 + 32 * j + 16) + 8 <= val(tisa_len st 7)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[] THEN ASM_SIMP_TAC[GSYM ty_list_reserved_slot]]);;

let TY_LIST_READY_RESERVED_SLOT = prove
 (`!st u old n i.
      ty_list_commit_ready st old n /\ ty_list_commit_view st u /\ i < n
      ==> ty_list_reserved_slot u i = ty_list_reserved_slot st i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `old:num`; `n:num`; `i:num`] TY_LIST_READY_ITER_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ty_list_word u 7 (128 + 32 * i + 16) = ty_list_word st 7 (128 + 32 * i + 16)`
   (fun th -> REWRITE_TAC[ty_list_reserved_slot; th]) THEN
  MATCH_MP_TAC TY_LIST_COMMIT_VIEW_WORD THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[ty_list_commit_ready]; ASM_ARITH_TAC]);;

let TY_LIST_ROW_MEMORY_VIEW = prove
 (`!st u old i slot. tregs u 0 = tregs st 0 /\ tmem u = tmem st
           ==> ty_list_commit_row_memory u old i slot = ty_list_commit_row_memory st old i slot`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TISA_SAME_VIEW) THEN
  ASM_SIMP_TAC[ty_list_commit_row_memory; ty_list_word; TISA_TMEM_STORE]);;

let TY_LIST_READY_ROW_VIEW = prove
 (`!st old n i. ty_list_commit_ready st old n /\ i < n /\ tregs st 5 = word i
      ==> tisa_wp ty_list_commit_row
           (\u. ty_list_commit_view st u /\ tregs u 6 = tregs st 6 /\
                tmem u = ty_list_commit_row_memory st old i (ty_list_reserved_slot st i))
           (\k u. F) st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `old:num`; `n:num`; `i:num`] TY_LIST_READY_ITER_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ty_list_commit_ready; ty_list_commit_geometry] o
    check (fun th -> fst(strip_comb(concl th)) = `ty_list_commit_ready`)) THEN
  SUBGOAL_THEN
   `(val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64 /\ ty_list_frame_apart st 0) /\
    val(tisa_base st 1) + val(tisa_len st 1) < 2 EXP 64 /\
    val(tisa_base st 7) + val(tisa_len st 7) < 2 EXP 64 /\
    ty_list_regions_apart st 0 7`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `0 < 3 /\ 1 < 3 /\ 7 = 7`]; ALL_TAC] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  EXISTS_TAC
   `\u. tregs u 0 = tregs st 0 /\ tregs u 5 = word i /\ tregs u 6 = tregs st 6 /\
        tmem u = ty_list_commit_row_memory st old i (ty_list_reserved_slot st i)` THEN
  EXISTS_TAC `\k:num u:tisa_state. F` THEN BETA_TAC THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `u:tisa_state` THEN STRIP_TAC THEN REWRITE_TAC[ty_list_commit_view] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC TY_LIST_COMMIT_ROW_FRAME THEN
    ASM_REWRITE_TAC[GSYM ty_list_outside];
    MATCH_MP_TAC TY_LIST_COMMIT_ROW_WP THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ty_list_frame_apart; ty_list_regions_apart]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ty_list_reserved_slot; WORD_VAL]]);;

let ty_list_commit_prefix = new_recursive_definition num_RECURSION
 `(ty_list_commit_prefix st old 0 = tmem st) /\
  (ty_list_commit_prefix st old (SUC i) =
    ty_list_commit_row_memory (TState (tregs st) (ty_list_commit_prefix st old i))
      old i (ty_list_reserved_slot st i))`;;

let ty_list_commit_at = new_definition
 `ty_list_commit_at st old n i u <=>
    ty_list_commit_view st u /\ tregs u 6 = word n /\
    tmem u = ty_list_commit_prefix st old i`;;

let TY_LIST_COMMIT_ITER_WP = prove
 (`!st old n i u.
      ty_list_commit_ready st old n /\ i < n /\ ty_list_commit_at st old n i u
      ==> tisa_wp ty_list_commit_row (ty_list_commit_at st old n (SUC i))
                   (\k s. F) (tisa_setreg 5 (word i) u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ty_list_commit_at] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `v = tisa_setreg 5 (word i) u` THEN
  SUBGOAL_THEN `ty_list_commit_view st v /\ tregs v 5 = word i /\ tregs v 6 = word n`
   STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN
    SIMP_TAC[TY_LIST_COMMIT_VIEW_SETREG; TISA_TREGS_SETREG;
      ARITH_RULE `~(5 = 0) /\ ~(6 = 5)`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ty_list_commit_ready v old n /\ ty_list_commit_geometry st` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC (SPECL [`st:tisa_state`; `v:tisa_state`; `old:num`; `n:num`]
                     TY_LIST_READY_AFTER_VIEW) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[ty_list_commit_ready] o
        check (fun th -> concl th = `ty_list_commit_ready st old n`))];
    ALL_TAC] THEN
  SUBGOAL_THEN `ty_list_reserved_slot v i = ty_list_reserved_slot st i` ASSUME_TAC THENL
   [MATCH_MP_TAC (SPECL [`st:tisa_state`; `v:tisa_state`; `old:num`; `n:num`; `i:num`]
                   TY_LIST_READY_RESERVED_SLOT) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ty_list_commit_row_memory v old i (ty_list_reserved_slot v i) =
    ty_list_commit_prefix st old (SUC i)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ty_list_commit_prefix] THEN MATCH_MP_TAC TY_LIST_ROW_MEMORY_VIEW THEN
    REWRITE_TAC[tregs; tmem] THEN EXPAND_TAC "v" THEN
    REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[ty_list_commit_view] o
      check (fun th -> concl th = `ty_list_commit_view st u`));
    ALL_TAC] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  EXISTS_TAC
   `\s. ty_list_commit_view v s /\ tregs s 6 = tregs v 6 /\
        tmem s = ty_list_commit_row_memory v old i (ty_list_reserved_slot v i)` THEN
  EXISTS_TAC `\k:num s:tisa_state. F` THEN BETA_TAC THEN REWRITE_TAC[ty_list_commit_at] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:tisa_state` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (SPECL [`st:tisa_state`; `v:tisa_state`; `s:tisa_state`]
                   TY_LIST_COMMIT_VIEW_TRANS) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (SPECL [`v:tisa_state`; `old:num`; `n:num`; `i:num`]
                   TY_LIST_READY_ROW_VIEW) THEN ASM_REWRITE_TAC[]]);;

let TY_LIST_COMMIT_LOOP_WP = prove
 (`!st old n v.
      ty_list_commit_ready st old n /\ ty_list_commit_at st old n 0 v
      ==> tisa_wp (TCountLoop 5 6 16777216 ty_list_commit_row)
           (ty_list_commit_at st old n n) (\k u. F) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(tregs v 6) = n /\ ~(16777216 < n)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ty_list_commit_at] o
      check (fun th -> fst(strip_comb(concl th)) = `ty_list_commit_at`)) THEN
    SUBGOAL_THEN `n <= 16777216` ASSUME_TAC THENL
     [ASM_MESON_TAC[ty_list_commit_ready]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC TISA_WP_COUNT_LOOP THEN
  EXISTS_TAC `\N i u. N = n /\ ty_list_commit_at st old n i u` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[GSYM ADD1; ETA_AX] THEN
    MATCH_MP_TAC TY_LIST_COMMIT_ITER_WP THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[ty_list_commit_at] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[TISA_TMEM_SETREG; TISA_TREGS_SETREG; TY_LIST_COMMIT_VIEW_SETREG;
      ARITH_RULE `~(5 = 0) /\ ~(6 = 5)`]]);;
