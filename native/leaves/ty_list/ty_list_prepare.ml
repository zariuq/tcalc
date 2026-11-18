(* The type-list procedure validates and reserves all insertions before it
   enters the publisher. The preparation phase may write only its work
   region and the ABI result frame. *)

needs "native/leaves/ty_list/ty_list_program.ml";;

let ty_list_prepare = new_definition
 `ty_list_prepare =
    TSeq ty_list_validate_layout
      (TSeq ty_list_validate_all
        (TSeq ty_list_prepare_table
          (TSeq ty_list_search
            (TSeq (TInstr (TImm TyU64 8 (word 1)))
              (TSeq (TSeq (TInstr (TLoadFrame TyPtr 9 14))
                          (TInstr (TStore 8 7 9 (&112:int) 8)))
                    ty_list_plan_all)))))`;;

let TY_LIST_SEQ_ASSOC = prove
 (`!r f g. tisa_then (tisa_then r f) g =
            tisa_then r (\s. tisa_then (f s) g)`,
  MATCH_MP_TAC tisa_result_INDUCT THEN REWRITE_TAC[tisa_then]);;

let TY_LIST_SPLIT_EXEC = prove
 (`!st. tisa_exec (tisa_root ty_list) st =
        tisa_then (tisa_exec ty_list_prepare st) (tisa_exec ty_list_publish)`,
  REWRITE_TAC[ty_list; tisa_root; ty_list_prepare; tisa_exec; TY_LIST_SEQ_ASSOC] THEN
  REWRITE_TAC[ETA_AX]);;

let ty_list_scratch_decls = new_definition
 `ty_list_scratch_decls =
    [(1,16,8); (1,8,8); (1,8,8); (1,0,8); (1,8,8); (1,0,8); (1,0,8); (2,256,8)]`;;

let TY_LIST_PREPARE_WF = prove
 (`tisa_stmt_ok ty_list_scratch_decls ty_list_prepare`,
  REWRITE_TAC[ty_list_prepare; ty_list_validate_layout; ty_list_validate_all;
    ty_list_validate_operand; ty_list_prepare_table; ty_list_search;
    ty_list_probe; ty_list_lookup_log; ty_list_plan_insertion;
    ty_list_check_occupied; ty_list_plan_all; ty_list_plan_operand;
    tisa_stmt_ok; tisa_instr_ok] THEN
  CONV_TAC(TOP_DEPTH_CONV(CHANGED_CONV(LEAF_DECL_KIND_CONV ty_list_scratch_decls)
                           ORELSEC NUM_RED_CONV)) THEN
  REWRITE_TAC[]);;

let TY_LIST_REGION_CASES_TAC =
  GEN_TAC THEN ASM_CASES_TAC `r < 8` THENL
   [MP_TAC(ARITH_RULE
      `r < 8 ==> r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/
                 r = 5 \/ r = 6 \/ r = 7`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[FST; SND] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];;

let TY_LIST_PREPARE_READABLE = prove
 (`!r. tisa_readable ty_list_scratch_decls r <=>
       tisa_readable (tisa_decls ty_list) r`,
  REWRITE_TAC[tisa_readable; ty_list_scratch_decls; TY_LIST_DECLS; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN TY_LIST_REGION_CASES_TAC);;

let TY_LIST_PREPARE_RW = prove
 (`!r. tisa_rw ty_list_scratch_decls r <=> r = 7`,
  REWRITE_TAC[tisa_rw; ty_list_scratch_decls; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN TY_LIST_REGION_CASES_TAC);;

let TY_LIST_PREPARE_ENTRY = prove
 (`!st. tisa_entry_ok ty_list st ==> tisa_frame_sep ty_list_scratch_decls st`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `tisa_frame_sep (tisa_decls ty_list) st` MP_TAC THENL
   [MP_TAC(REWRITE_RULE[GSYM(SPEC `ty_list` TISA_PROG_CASES)]
     (SPECL [`tisa_decls ty_list`; `tisa_inits ty_list`; `tisa_root ty_list`;
       `st:tisa_state`] TISA_ENTRY_FRAME_SEP)) THEN
    ASM_REWRITE_TAC[TY_LIST_DECLS; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[tisa_frame_sep; TY_LIST_PREPARE_READABLE; TY_LIST_PREPARE_RW;
                TY_LIST_DECLS; ty_list_scratch_decls; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `tisa_rw (tisa_decls ty_list) 7` MP_TAC THENL
     [CONV_TAC(LEAF_DECL_KIND_CONV TY_LIST_DECLS);
      REWRITE_TAC[TY_LIST_DECLS] THEN ASM_MESON_TAC[]]]);;

let TY_LIST_PREPARE_FRAME = prove
 (`!st. tisa_entry_ok ty_list st
        ==> tisa_keeps ty_list_scratch_decls st
              (tisa_state_of (tisa_exec ty_list_prepare st))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_KEEPS_EXEC THEN
  ASM_SIMP_TAC[TY_LIST_PREPARE_ENTRY; TY_LIST_PREPARE_WF]);;

let TY_LIST_PREPARE_STOPS = prove
 (`!st k u. tisa_entry_ok ty_list st /\ tisa_exec ty_list_prepare st = TStop k u
      ==> tisa_run ty_list st = TStop k u /\
          tisa_keeps ty_list_scratch_decls st u`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[tisa_run; TY_LIST_SPLIT_EXEC; tisa_then] THEN
  MP_TAC(SPEC `st:tisa_state` TY_LIST_PREPARE_FRAME) THEN
  ASM_REWRITE_TAC[tisa_state_of]);;

let TY_LIST_TABLE_APART = prove
 (`!st r. tisa_entry_ok ty_list st /\ r < 3 /\ ~(val(tisa_len st r) = 0)
      ==> (val(tisa_len st 7) = 0 \/
           val(tisa_base st r) + val(tisa_len st r) <= val(tisa_base st 7) \/
           val(tisa_base st 7) + val(tisa_len st 7) <= val(tisa_base st r)) /\
          (val(tisa_base st r) + val(tisa_len st r) <= val(tregs st 0) \/
           val(tregs st 0) + 192 <= val(tisa_base st r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ARITH_RULE `r < 3 ==> r = 0 \/ r = 1 \/ r = 2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  UNDISCH_TAC `tisa_entry_ok ty_list st` THEN
  REWRITE_TAC[ty_list; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_pair_ok;
              tisa_region_ok; tisa_frame; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_MESON_TAC[]);;

let TY_LIST_PREPARE_TABLE_FRAME = prove
 (`!st r a. tisa_entry_ok ty_list st /\ r < 3 /\
       val(tisa_base st r) <= val(a:int64) /\
       val a < val(tisa_base st r) + val(tisa_len st r)
      ==> tmem(tisa_state_of(tisa_exec ty_list_prepare st)) a = tmem st a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `r:num`] TY_LIST_TABLE_APART) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP TY_LIST_PREPARE_FRAME) THEN
  REWRITE_TAC[tisa_keeps; tisa_writable; TY_LIST_PREPARE_RW; UNWIND_THM2] THEN
  DISCH_THEN(MATCH_MP_TAC o SPEC `a:int64` o CONJUNCT2) THEN ASM_ARITH_TAC);;

let TY_LIST_PREPARE_STOP_TABLES = prove
 (`!st k u. tisa_entry_ok ty_list st /\ tisa_exec ty_list_prepare st = TStop k u
      ==> tisa_run ty_list st = TStop k u /\
          !r a. r < 3 /\ val(tisa_base st r) <= val(a:int64) /\
                val a < val(tisa_base st r) + val(tisa_len st r)
                ==> tmem u a = tmem st a`,
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[TY_LIST_PREPARE_STOPS];
    MP_TAC(SPECL [`st:tisa_state`; `r:num`; `a:int64`] TY_LIST_PREPARE_TABLE_FRAME) THEN
    ASM_REWRITE_TAC[tisa_state_of]]);;

let TY_LIST_EARLY_PUBLISH_REJECTED = prove
 (`~tisa_stmt_ok ty_list_scratch_decls
         (TSeq ty_list_prepare (TInstr (TStore 8 2 8 (&0:int) 9)))`,
  REWRITE_TAC[tisa_stmt_ok; tisa_instr_ok; TY_LIST_PREPARE_RW] THEN
  CONV_TAC NUM_REDUCE_CONV);;
