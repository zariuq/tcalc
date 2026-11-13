(* ========================================================================= *)
(* The fuel receipt of a run: it never falls, and it stays within the        *)
(* allowance (TISA_RUN_FUEL). A run writes frame word 21 (fuel_used) only by *)
(* FUND, which adds within the allowance (frame word 20, which no run        *)
(* writes); its stores lie in read-write regions, apart from the frame, and  *)
(* its outcomes write words 18 and 19.                                       *)
(*                                                                           *)
(* The proof follows tisa_p1_frame.ml's TISA_KEEPS_* lemmas, with the        *)
(* relation tisa_fuel_le: the run keeps what tisa_keeps keeps, the allowance *)
(* is unchanged, and from a receipt within the allowance the receipt does    *)
(* not fall and stays within it.                                             *)
(* ========================================================================= *)

let tisa_fuel_ok = new_definition
 `tisa_fuel_ok t <=> val(tisa_fword t 21) <= val(tisa_fword t 20)`;;

let tisa_fuel_le = new_definition
 `tisa_fuel_le decls t t' <=>
    tisa_keeps decls t t' /\ tisa_fword t' 20 = tisa_fword t 20 /\
    (tisa_fuel_ok t ==> val(tisa_fword t 21) <= val(tisa_fword t' 21) /\ tisa_fuel_ok t')`;;

(* ------------------------------------------------------------------------- *)
(* Frame words under stores and register writes.                            *)
(* ------------------------------------------------------------------------- *)

(* A store none of whose bytes lies in frame word j keeps it. *)
let TISA_FWORD_STORE_APART = prove
 (`!t (a:int64) w (v:int64) j.
     val(tregs t 0) + 192 <= 2 EXP 64 /\ j < 24 /\ val a + w <= 2 EXP 64 /\
     (!b:int64. val a <= val b /\ val b < val a + w
                ==> ~(val(tregs t 0) + 8 * j <= val b /\ val b < val(tregs t 0) + 8 * j + 8))
     ==> tisa_fword (tisa_store a w v t) j = tisa_fword t j`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[tisa_fword; tisa_read; tisa_frame; tisa_store; tregs; tmem] THEN
  AP_TERM_TAC THEN REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC TISA_WRITE_BYTES_OUTSIDE THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word_add (word_add (tregs t 0) (word(8 * j))) (word k):int64) =
                val(tregs t 0) + 8 * j + k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word_add (word_add (tregs t 0) (word(8 * j))) (word k):int64`) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* Frame word j after writing frame word i: v when i = j, unchanged else. *)
let TISA_FWORD_SETFWORD = prove
 (`!t i j (v:int64).
     val(tregs t 0) + 192 <= 2 EXP 64 /\ i < 24 /\ j < 24
     ==> tisa_fword (tisa_setfword i v t) j = if i = j then v else tisa_fword t j`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[tisa_fword; tisa_read; tisa_setfword; tisa_store; tisa_frame; tregs; tmem] THEN
    SUBGOAL_THEN `val(word_add (tregs t 0) (word(8 * j)):int64) + 8 <= 2 EXP 64` ASSUME_TAC THENL
     [SUBGOAL_THEN `val(word_add (tregs t 0) (word(8 * j)):int64) = val(tregs t 0) + 8 * j`
      SUBST1_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      ASM_SIMP_TAC[TISA_READ_SAME_WRITE; WORD_VAL]];
    REWRITE_TAC[tisa_setfword; tisa_frame] THEN MATCH_MP_TAC TISA_FWORD_STORE_APART THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(word_add (tregs t 0) (word(8 * i)):int64) = val(tregs t 0) + 8 * i`
    SUBST1_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let TISA_FWORD_SETREG = prove
 (`!t d (v:int64) j. ~(d = 0) ==> tisa_fword (tisa_setreg d v t) j = tisa_fword t j`,
  SIMP_TAC[tisa_fword; tisa_read; tisa_frame; tisa_setreg; tregs; tmem]);;

(* ------------------------------------------------------------------------- *)
(* The relation: reflexive, transitive, kept by the primitive steps.         *)
(* ------------------------------------------------------------------------- *)

let TISA_FUEL_LE_REFL = prove
 (`!decls t. tisa_fuel_le decls t t`,
  REWRITE_TAC[tisa_fuel_le; TISA_KEEPS_REFL; LE_REFL]);;

let TISA_FUEL_LE_TRANS = prove
 (`!decls t t' t''.
        tisa_frame_sep decls t /\ tisa_fuel_le decls t t' /\ tisa_fuel_le decls t' t''
        ==> tisa_fuel_le decls t t''`,
  REWRITE_TAC[tisa_fuel_le] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[TISA_KEEPS_TRANS];
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[LE_TRANS];
    ASM_MESON_TAC[]]);;

let TISA_FUEL_LE_SETREG = prove
 (`!decls t d v. ~(d = 0) ==> tisa_fuel_le decls t (tisa_setreg d v t)`,
  SIMP_TAC[tisa_fuel_le; TISA_KEEPS_SETREG; TISA_FWORD_SETREG; tisa_fuel_ok; LE_REFL]);;

(* A store inside read-write region r, which lies apart from the frame. *)
let TISA_FUEL_LE_STORE = prove
 (`!decls t (a:int64) w (v:int64) r.
        tisa_frame_sep decls t /\ tisa_rw decls r /\ val a + w <= 2 EXP 64 /\
        (!b:int64. val a <= val b /\ val b < val a + w
                   ==> val(tisa_base t r) <= val b /\ val b < val(tisa_base t r) + val(tisa_len t r))
        ==> tisa_fuel_le decls t (tisa_store a w v t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(val(tisa_len t r) = 0 \/
                 val(tisa_base t r) + val(tisa_len t r) <= val(tregs t 0) \/
                 val(tregs t 0) + 192 <= val(tisa_base t r)) /\
                val(tregs t 0) + 192 <= 2 EXP 64` (CONJUNCTS_THEN ASSUME_TAC) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[tisa_frame_sep]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[tisa_fuel_le; tisa_fuel_ok] THEN
  SUBGOAL_THEN `!j. 20 <= j /\ j < 22 ==> tisa_fword (tisa_store a w v t) j = tisa_fword t j`
  (fun th -> SIMP_TAC[th; ARITH; LE_REFL]) THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_FWORD_STORE_APART THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY ASM_ARITH_TAC THEN
    X_GEN_TAC `b:int64` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `b:int64` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_base t r`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC TISA_KEEPS_STORE THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_writable] THEN DISJ1_TAC THEN
  EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Writing status or ret_val. *)
let TISA_FUEL_LE_SETFWORD_LOW = prove
 (`!decls t j v. tisa_frame_sep decls t /\ 18 <= j /\ j <= 19
                 ==> tisa_fuel_le decls t (tisa_setfword j v t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(tregs t 0) + 192 <= 2 EXP 64` ASSUME_TAC THENL
   [ASM_MESON_TAC[tisa_frame_sep]; ALL_TAC] THEN
  REWRITE_TAC[tisa_fuel_le; tisa_fuel_ok] THEN
  ASM_SIMP_TAC[TISA_KEEPS_SETFWORD; ARITH_RULE `j <= 19 ==> j <= 21`] THEN
  ASM_SIMP_TAC[TISA_FWORD_SETFWORD; ARITH_RULE `j <= 19 ==> j < 24`; ARITH] THEN
  ASM_SIMP_TAC[ARITH_RULE `j <= 19 ==> ~(j = 20) /\ ~(j = 21)`; LE_REFL]);;

let TISA_FUEL_LE_FAIL = prove
 (`!decls t k. tisa_frame_sep decls t
               ==> tisa_fuel_le decls t (tisa_state_of (tisa_fail k t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_fail; tisa_state_of] THEN
  MATCH_MP_TAC TISA_FUEL_LE_TRANS THEN EXISTS_TAC `tisa_setfword 18 (word k) t` THEN
  ASM_SIMP_TAC[TISA_FUEL_LE_SETFWORD_LOW; ARITH] THEN
  MATCH_MP_TAC TISA_FUEL_LE_SETFWORD_LOW THEN REWRITE_TAC[ARITH] THEN
  MP_TAC(SPECL [`decls:(num#num#num)list`; `t:tisa_state`; `tisa_setfword 18 (word k) t`]
               TISA_KEEPS_WRITABLE) THEN
  ASM_SIMP_TAC[TISA_KEEPS_SETFWORD; ARITH]);;

let TISA_FUEL_LE_FINISH = prove
 (`!decls t out v. tisa_frame_sep decls t
                   ==> tisa_fuel_le decls t (tisa_state_of (tisa_finish out v t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_finish; tisa_state_of] THEN
  MATCH_MP_TAC TISA_FUEL_LE_TRANS THEN EXISTS_TAC `tisa_setfword 18 (word out) t` THEN
  ASM_SIMP_TAC[TISA_FUEL_LE_SETFWORD_LOW; ARITH] THEN
  MATCH_MP_TAC TISA_FUEL_LE_SETFWORD_LOW THEN REWRITE_TAC[ARITH] THEN
  MP_TAC(SPECL [`decls:(num#num#num)list`; `t:tisa_state`; `tisa_setfword 18 (word out) t`]
               TISA_KEEPS_WRITABLE) THEN
  ASM_SIMP_TAC[TISA_KEEPS_SETFWORD; ARITH]);;

(* FUND u: the receipt rises by u within the allowance, or EXHAUSTED. *)
let TISA_FUEL_LE_FUND = prove
 (`!decls t u. tisa_frame_sep decls t
               ==> tisa_fuel_le decls t (tisa_state_of (tisa_fund u t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_fund] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[TISA_FUEL_LE_FAIL] THEN REWRITE_TAC[tisa_state_of] THEN
  SUBGOAL_THEN `val(tregs t 0) + 192 <= 2 EXP 64` ASSUME_TAC THENL
   [ASM_MESON_TAC[tisa_frame_sep]; ALL_TAC] THEN
  REWRITE_TAC[tisa_fuel_le; tisa_fuel_ok] THEN
  ASM_SIMP_TAC[TISA_KEEPS_SETFWORD; TISA_FWORD_SETFWORD; ARITH] THEN
  DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  MP_TAC(ISPECL [`tisa_fword t 20`; `tisa_fword t 21`] VAL_WORD_SUB_CASES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    can (find_term ((=) `word_sub (tisa_fword t 20) (tisa_fword t 21)`)) (concl th))) THEN
  SUBGOAL_THEN `val(word_add (tisa_fword t 21) (word u):int64) = val(tisa_fword t 21) + u`
  SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN MP_TAC(ISPEC `tisa_fword t 20` VAL_BOUND_64) THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instructions, loops, statements, runs.                                    *)
(* ------------------------------------------------------------------------- *)

let TISA_FUEL_LE_SEP = prove
 (`!decls t t'. tisa_frame_sep decls t /\ tisa_fuel_le decls t t' ==> tisa_frame_sep decls t'`,
  REWRITE_TAC[tisa_fuel_le] THEN MESON_TAC[TISA_KEEPS_WRITABLE]);;

let TISA_FUEL_LE_INSTR = prove
 (`!decls i t. tisa_instr_ok decls i /\ tisa_frame_sep decls t
               ==> tisa_fuel_le decls t (tisa_state_of (tisa_instr i t))`,
  GEN_TAC THEN MATCH_MP_TAC tisa_instr_INDUCT THEN
  REWRITE_TAC[tisa_instr_ok; tisa_instr] THEN REPEAT STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[tisa_state_of; TISA_FUEL_LE_FAIL; TISA_FUEL_LE_SETREG] THEN
  (* the store, TStore a0 a1 a2 a3 a4: its bytes lie in read-write region a1 *)
  MATCH_MP_TAC TISA_FUEL_LE_STORE THEN EXISTS_TAC `a1:num` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tisa_inside]) THEN
  SUBGOAL_THEN `val(tisa_base t a1) + val(tisa_len t a1) < 2 EXP 64` ASSUME_TAC THENL
   [ASM_MESON_TAC[TISA_SEP_BOUND; TISA_RW_READABLE]; ALL_TAC] THEN
  MP_TAC(SPECL [`tisa_ea t a2 a3`; `a0:num`; `tisa_base t a1`; `tisa_len t a1`] TISA_IWORD_RANGE) THEN
  ASM_REWRITE_TAC[]);;

let TISA_FUEL_LE_THEN = prove
 (`!decls t r f.
        tisa_frame_sep decls t /\ tisa_fuel_le decls t (tisa_state_of r) /\
        (!u. r = TCont u ==> tisa_fuel_le decls u (tisa_state_of (f u)))
        ==> tisa_fuel_le decls t (tisa_state_of (tisa_then r f))`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:tisa_result` TISA_RESULT_CASES) THEN
  REWRITE_TAC[tisa_then; tisa_state_of; injectivity "tisa_result"; distinctness "tisa_result"] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TISA_FUEL_LE_TRANS THEN EXISTS_TAC `a:tisa_state` THEN
  ASM_MESON_TAC[]);;

let TISA_FUEL_LE_COUNT_ITER = prove
 (`!m decls f x j t.
        ~(x = 0) /\ tisa_frame_sep decls t /\
        (!u. tisa_frame_sep decls u ==> tisa_fuel_le decls u (tisa_state_of (f u)))
        ==> tisa_fuel_le decls t (tisa_state_of (tisa_count_iter m f x j t))`,
  INDUCT_TAC THEN REWRITE_TAC[tisa_count_iter] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[tisa_state_of; TISA_FUEL_LE_SETREG]; ALL_TAC] THEN
  ABBREV_TAC `t1 = tisa_setreg x (word j) t` THEN
  SUBGOAL_THEN `tisa_fuel_le decls t t1 /\ tisa_frame_sep decls t1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t1" THEN ASM_SIMP_TAC[TISA_FUEL_LE_SETREG] THEN
    ASM_MESON_TAC[TISA_FUEL_LE_SEP; TISA_FUEL_LE_SETREG];
    ALL_TAC] THEN
  MATCH_MP_TAC TISA_FUEL_LE_TRANS THEN EXISTS_TAC `t1:tisa_state` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TISA_FUEL_LE_THEN THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `u:tisa_state` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[TISA_FUEL_LE_SEP; tisa_state_of]);;

let TISA_FUEL_LE_EARLY_CHECK = prove
 (`!decls k t g.
        tisa_frame_sep decls t /\
        (tisa_bool (tregs t k) /\ ~(tregs t k = word 0)
         ==> tisa_fuel_le decls t (tisa_state_of (g t)))
        ==> tisa_fuel_le decls t (tisa_state_of (tisa_early_check k t g))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_early_check] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[TISA_FUEL_LE_FAIL; tisa_state_of; TISA_FUEL_LE_REFL] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let TISA_FUEL_LE_EARLY_ITER = prove
 (`!m decls f x k j t.
        ~(x = 0) /\ tisa_frame_sep decls t /\
        (!u. tisa_frame_sep decls u ==> tisa_fuel_le decls u (tisa_state_of (f u)))
        ==> tisa_fuel_le decls t (tisa_state_of (tisa_early_iter m f x k j t))`,
  INDUCT_TAC THEN REWRITE_TAC[tisa_early_iter] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[tisa_state_of; TISA_FUEL_LE_SETREG]; ALL_TAC] THEN
  ABBREV_TAC `t1 = tisa_setreg x (word j) t` THEN
  SUBGOAL_THEN `tisa_fuel_le decls t t1 /\ tisa_frame_sep decls t1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t1" THEN ASM_SIMP_TAC[TISA_FUEL_LE_SETREG] THEN
    ASM_MESON_TAC[TISA_FUEL_LE_SEP; TISA_FUEL_LE_SETREG];
    ALL_TAC] THEN
  MATCH_MP_TAC TISA_FUEL_LE_TRANS THEN EXISTS_TAC `t1:tisa_state` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TISA_FUEL_LE_EARLY_CHECK THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC TISA_FUEL_LE_THEN THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `u:tisa_state` THEN DISCH_TAC THEN
  SUBGOAL_THEN `tisa_frame_sep decls u` ASSUME_TAC THENL
   [ASM_MESON_TAC[TISA_FUEL_LE_SEP; tisa_state_of]; ALL_TAC] THEN
  MATCH_MP_TAC TISA_FUEL_LE_EARLY_CHECK THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let TISA_FUEL_LE_EXEC = prove
 (`!S decls t. tisa_stmt_ok decls S /\ tisa_frame_sep decls t
               ==> tisa_fuel_le decls t (tisa_state_of (tisa_exec S t))`,
  MATCH_MP_TAC tisa_stmt_INDUCT THEN REWRITE_TAC[tisa_stmt_ok; tisa_exec] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[tisa_state_of; TISA_FUEL_LE_REFL];
    MESON_TAC[TISA_FUEL_LE_INSTR];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_FUEL_LE_THEN THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `u:tisa_state` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[TISA_FUEL_LE_SEP; tisa_state_of];
    REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[TISA_FUEL_LE_FAIL];
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[TISA_FUEL_LE_FAIL] THEN
    MATCH_MP_TAC TISA_FUEL_LE_COUNT_ITER THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[TISA_FUEL_LE_FAIL] THEN
    MATCH_MP_TAC TISA_FUEL_LE_EARLY_ITER THEN ASM_SIMP_TAC[];
    SIMP_TAC[TISA_FUEL_LE_FINISH];
    SIMP_TAC[TISA_FUEL_LE_FUND]]);;

(* A run's receipt: not below the receipt it started from, and within the
   allowance. *)
let TISA_RUN_FUEL = prove
 (`!prog t k u.
     tisa_leaf_wf prog /\ tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
     ==> val(tisa_fword t 21) <= val(tisa_fword u 21) /\
         val(tisa_fword u 21) <= val(tisa_fword t 20)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[TISA_PROG_CASES] THEN
  REWRITE_TAC[tisa_leaf_wf; tisa_decls; tisa_inits; tisa_root] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `tisa_frame_sep (tisa_decls prog) t` ASSUME_TAC THENL
   [ASM_MESON_TAC[TISA_ENTRY_FRAME_SEP]; ALL_TAC] THEN
  SUBGOAL_THEN `tisa_fuel_ok t` ASSUME_TAC THENL
   [UNDISCH_TAC `tisa_entry_ok (TProg (tisa_decls prog) (tisa_inits prog) (tisa_root prog)) t` THEN
    SIMP_TAC[tisa_entry_ok; tisa_fuel_ok];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `tisa_run`)) (concl th))) THEN
  ASM_REWRITE_TAC[tisa_run; tisa_root] THEN DISCH_TAC THEN
  SUBGOAL_THEN `tisa_fuel_le (tisa_decls prog) t
                 (tisa_state_of (tisa_then (tisa_exec (tisa_root prog) t) (\st'. tisa_fail 2 st')))`
  MP_TAC THENL
   [MATCH_MP_TAC TISA_FUEL_LE_THEN THEN ASM_SIMP_TAC[TISA_FUEL_LE_EXEC] THEN
    X_GEN_TAC `w:tisa_state` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC TISA_FUEL_LE_FAIL THEN
    MP_TAC(SPECL [`tisa_root prog`; `tisa_decls prog`; `t:tisa_state`] TISA_FUEL_LE_EXEC) THEN
    ASM_REWRITE_TAC[tisa_state_of] THEN ASM_MESON_TAC[TISA_FUEL_LE_SEP];
    ASM_REWRITE_TAC[tisa_state_of; tisa_fuel_le; tisa_fuel_ok] THEN MESON_TAC[]]);;
