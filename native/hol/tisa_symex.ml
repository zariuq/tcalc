(* ========================================================================= *)
(* Functional proofs of t-ISA p1 programs over a symbolic state: accessors   *)
(* through register and memory updates, reads through disjoint and equal    *)
(* writes, and an invariant rule for counted loops.                         *)
(* ========================================================================= *)

needs "tisa/hol/tisa_p1_frame.ml";;

let TISA_RESULT_DISTINCT = distinctness "tisa_result";;
let TISA_RESULT_INJ = injectivity "tisa_result";;
let TISA_TY_DISTINCT_ALL = distinctness "tisa_ty";;

(* ------------------------------------------------------------------------- *)
(* Registers and memory through updates.                                     *)
(* ------------------------------------------------------------------------- *)

let TISA_TREGS_SETREG = prove
 (`!d (v:int64) st i. tregs (tisa_setreg d v st) i = if i = d then v else tregs st i`,
  REWRITE_TAC[tisa_setreg; tregs]);;

let TISA_TMEM_SETREG = prove
 (`!d (v:int64) st. tmem (tisa_setreg d v st) = tmem st`,
  REWRITE_TAC[tisa_setreg; tmem]);;

let TISA_TREGS_STORE = prove
 (`!(a:int64) w (v:int64) st. tregs (tisa_store a w v st) = tregs st`,
  REWRITE_TAC[tisa_store; tregs]);;

let TISA_TMEM_STORE = prove
 (`!(a:int64) w (v:int64) st.
        tmem (tisa_store a w v st) = write (bytes(a,w)) (val v) (tmem st)`,
  REWRITE_TAC[tisa_store; tmem]);;

(* Two states with the same frame register and memory read the same words.  *)
let TISA_SAME_VIEW = prove
 (`!s t. tregs s 0 = tregs t 0 /\ tmem s = tmem t
         ==> (!a w. tisa_read s a w = tisa_read t a w) /\
             tisa_frame s = tisa_frame t /\
             (!i. tisa_fword s i = tisa_fword t i) /\
             (!r. tisa_base s r = tisa_base t r) /\
             (!r. tisa_len s r = tisa_len t r)`,
  SIMP_TAC[tisa_read; tisa_frame; tisa_fword; tisa_base; tisa_len]);;

(* ------------------------------------------------------------------------- *)
(* Reads through writes: disjoint byte ranges, and the same range.          *)
(* ------------------------------------------------------------------------- *)

let TISA_READ_DISJOINT_WRITE = prove
 (`!(a:int64) k (c:int64) j n (m:int64->byte).
        ~(k = 0) /\ val a + k <= 2 EXP 64 /\ val c + j <= 2 EXP 64 /\
        (val a + k <= val c \/ val c + j <= val a)
        ==> read (bytes(a,k)) (write (bytes(c,j)) n m) = read (bytes(a,k)) m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_READ_OUTSIDE_WRITE THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_64] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let TISA_READ_SAME_WRITE = prove
 (`!(c:int64) n (m:int64->byte).
        val c + 8 <= 2 EXP 64
        ==> word(read (bytes(c,8)) (write (bytes(c,8)) n m)):int64 = word n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:int64`; `8`; `c:int64`; `8`; `n:num`; `m:int64->byte`]
         TISA_READ_INSIDE_WRITE) THEN
  REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES; EXP; DIV_1] THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * 8 = 64`; MOD_MOD_REFL; WORD_EQ; DIMINDEX_64; CONG]);;

(* ------------------------------------------------------------------------- *)
(* Counted loops: an invariant kept by every completed body run carries     *)
(* through the loop, and every stop of a body is a stop of the loop.        *)
(* ------------------------------------------------------------------------- *)

let TISA_COUNT_ITER_INV = prove
 (`!(f:tisa_state->tisa_result) x (Inv:tisa_state->bool) (Post:num->tisa_state->bool).
     (!st j. Inv st ==> Inv (tisa_setreg x (word j) st)) /\
     (!st s. Inv st /\ f st = TCont s ==> Inv s) /\
     (!st k s. Inv st /\ f st = TStop k s ==> Post k s)
     ==> !m j st. Inv st
                  ==> (!s. tisa_count_iter m f x j st = TCont s ==> Inv s) /\
                      (!k s. tisa_count_iter m f x j st = TStop k s ==> Post k s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN REWRITE_TAC[tisa_count_iter; TISA_RESULT_DISTINCT; TISA_RESULT_INJ] THENL
   [ASM_MESON_TAC[];
    MP_TAC(ISPEC `(f:tisa_state->tisa_result) (tisa_setreg x (word j) st)`
           TISA_RESULT_CASES) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[tisa_then; TISA_RESULT_DISTINCT; TISA_RESULT_INJ] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Specifications of statements: from states satisfying P, a run that        *)
(* continues ends in Q, and a run that stops with outcome k ends in R k.     *)
(* Proved statements are reused through their specifications.               *)
(* ------------------------------------------------------------------------- *)

let tisa_spec = new_definition
 `tisa_spec (P:tisa_state->bool) S (Q:tisa_state->bool) (R:num->tisa_state->bool) <=>
    !st. P st ==> (!s. tisa_exec S st = TCont s ==> Q s) /\
                  (!k s. tisa_exec S st = TStop k s ==> R k s)`;;

let tisa_failst = new_definition
 `tisa_failst k st = tisa_setfword 19 (word k) (tisa_setfword 18 (word k) st)`;;

let tisa_finst = new_definition
 `tisa_finst out (v:int64) st = tisa_setfword 19 v (tisa_setfword 18 (word out) st)`;;

let TISA_FAIL_STOP = prove
 (`!k st. tisa_fail k st = TStop k (tisa_failst k st)`,
  REWRITE_TAC[tisa_fail; tisa_failst]);;

let TISA_FINISH_STOP = prove
 (`!out v st. tisa_finish out v st = TStop out (tisa_finst out v st)`,
  REWRITE_TAC[tisa_finish; tisa_finst]);;

let TISA_SPEC_CONSEQ = prove
 (`!P P' S Q Q' R R'.
     tisa_spec P S Q R /\ (!st. P' st ==> P st) /\ (!st. Q st ==> Q' st) /\
     (!k st. R k st ==> R' k st)
     ==> tisa_spec P' S Q' R'`,
  REWRITE_TAC[tisa_spec] THEN MESON_TAC[]);;

let TISA_SPEC_SKIP = prove
 (`!P Q R. (!st. P st ==> Q st) ==> tisa_spec P TSkip Q R`,
  REWRITE_TAC[tisa_spec; tisa_exec; TISA_RESULT_DISTINCT; TISA_RESULT_INJ] THEN
  MESON_TAC[]);;

let TISA_SPEC_SEQ = prove
 (`!P M Q R a b. tisa_spec P a M R /\ tisa_spec M b Q R ==> tisa_spec P (TSeq a b) Q R`,
  REWRITE_TAC[tisa_spec; tisa_exec] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `st:tisa_state` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `tisa_exec a st` TISA_RESULT_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[tisa_then; TISA_RESULT_DISTINCT; TISA_RESULT_INJ] THEN
  ASM_MESON_TAC[]);;

let TISA_SPEC_INSTR = prove
 (`!P Q R i.
     (!st. P st ==> (!s. tisa_instr i st = TCont s ==> Q s) /\
                    (!k s. tisa_instr i st = TStop k s ==> R k s))
     ==> tisa_spec P (TInstr i) Q R`,
  REWRITE_TAC[tisa_spec; tisa_exec]);;

let TISA_SPEC_RETURN = prove
 (`!P Q R out r.
     (!st. P st ==> R out (tisa_finst out (tregs st r) st))
     ==> tisa_spec P (TReturn out r) Q R`,
  REWRITE_TAC[tisa_spec; tisa_exec; TISA_FINISH_STOP; TISA_RESULT_DISTINCT;
              TISA_RESULT_INJ] THEN MESON_TAC[]);;

let TISA_SPEC_IF = prove
 (`!P Q R c a b.
     (!st. P st /\ ~tisa_bool (tregs st c) ==> R 3 (tisa_failst 3 st)) /\
     tisa_spec (\st. P st /\ tisa_bool (tregs st c) /\ ~(tregs st c = word 0)) a Q R /\
     tisa_spec (\st. P st /\ tisa_bool (tregs st c) /\ tregs st c = word 0) b Q R
     ==> tisa_spec P (TIf c a b) Q R`,
  REWRITE_TAC[tisa_spec; tisa_exec] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `st:tisa_state` THEN DISCH_TAC THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[TISA_FAIL_STOP; TISA_RESULT_DISTINCT; TISA_RESULT_INJ] THEN
  ASM_MESON_TAC[]);;

(* A counted loop: Inv N j holds before the iteration with index j, of N in  *)
(* all; the body runs with x = j; at the end x = N.                          *)
let TISA_SPEC_COUNT_LOOP = prove
 (`!P Q R (Inv:num->num->tisa_state->bool) x n cap body.
     (!st. P st /\ cap < val(tregs st n) ==> R 2 (tisa_failst 2 st)) /\
     (!st. P st /\ ~(cap < val(tregs st n)) ==> Inv (val(tregs st n)) 0 st) /\
     (!N j. j < N
            ==> tisa_spec (\st. ?st0. Inv N j st0 /\ st = tisa_setreg x (word j) st0)
                          body (Inv N (j + 1)) R) /\
     (!N st. Inv N N st ==> Q (tisa_setreg x (word N) st))
     ==> tisa_spec P (TCountLoop x n cap body) Q R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tisa_spec; tisa_exec] THEN
  X_GEN_TAC `st:tisa_state` THEN DISCH_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[TISA_FAIL_STOP; TISA_RESULT_DISTINCT; TISA_RESULT_INJ] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Inv:num->num->tisa_state->bool) (val(tregs st n)) 0 st` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `N = val(tregs st n)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!m j s0. j + m = N /\ Inv N j s0
             ==> (!s. tisa_count_iter m (\st'. tisa_exec body st') x j s0 = TCont s ==> Q s) /\
                 (!k s. tisa_count_iter m (\st'. tisa_exec body st') x j s0 = TStop k s ==> R k s)`
   (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[ADD_CLAUSES]) THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[tisa_count_iter; TISA_RESULT_DISTINCT; TISA_RESULT_INJ] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `j:num = N`)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`N:num`; `j:num`] o
    check (fun th -> can (find_term ((=) `tisa_spec`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[tisa_spec]] THEN
  DISCH_THEN(MP_TAC o SPEC `tisa_setreg x (word j) s0`) THEN
  ANTS_TAC THENL [EXISTS_TAC `s0:tisa_state` THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `tisa_exec body (tisa_setreg x (word j) s0)` TISA_RESULT_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_TAC `s1:tisa_state`)
     (X_CHOOSE_THEN `k1:num` (X_CHOOSE_TAC `s1:tisa_state`))) THEN
  ASM_REWRITE_TAC[tisa_then; TISA_RESULT_DISTINCT; TISA_RESULT_INJ] THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `tisa_count_iter`)) (concl th) && is_forall (concl th))) THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Path enumeration: a run's equation becomes a disjunction of paths, each  *)
(* with its path condition and its final result.                            *)
(* ------------------------------------------------------------------------- *)

let TISA_FRAME_SETREG = prove
 (`!d (v:int64) st. ~(d = 0) ==> tisa_frame (tisa_setreg d v st) = tisa_frame st`,
  SIMP_TAC[tisa_frame; TISA_TREGS_SETREG]);;

let TISA_READ_SETREG = prove
 (`!d (v:int64) st a w. tisa_read (tisa_setreg d v st) a w = tisa_read st a w`,
  REWRITE_TAC[tisa_read; TISA_TMEM_SETREG]);;

let TISA_FWORD_SETREG = prove
 (`!d (v:int64) st i. ~(d = 0) ==> tisa_fword (tisa_setreg d v st) i = tisa_fword st i`,
  SIMP_TAC[tisa_fword; TISA_FRAME_SETREG; TISA_READ_SETREG]);;

let TISA_BASE_SETREG = prove
 (`!d (v:int64) st r. ~(d = 0) ==> tisa_base (tisa_setreg d v st) r = tisa_base st r`,
  SIMP_TAC[tisa_base; TISA_FWORD_SETREG]);;

let TISA_LEN_SETREG = prove
 (`!d (v:int64) st r. ~(d = 0) ==> tisa_len (tisa_setreg d v st) r = tisa_len st r`,
  SIMP_TAC[tisa_len; TISA_FWORD_SETREG]);;

let TISA_INSIDE_SETREG = prove
 (`!d (v:int64) st r e w.
        ~(d = 0) ==> (tisa_inside (tisa_setreg d v st) r e w <=> tisa_inside st r e w)`,
  SIMP_TAC[tisa_inside; TISA_BASE_SETREG; TISA_LEN_SETREG]);;

let TISA_COND_EQ = prove
 (`!c (x:A) y z. (if c then x else y) = z <=> c /\ x = z \/ ~c /\ y = z`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let TISA_EXEC_SEQ_EQ = prove
 (`!a b st r.
     tisa_exec (TSeq a b) st = r <=>
     (?s1. tisa_exec a st = TCont s1 /\ tisa_exec b s1 = r) \/
     (?k s1. tisa_exec a st = TStop k s1 /\ r = TStop k s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_exec] THEN
  MP_TAC(ISPEC `tisa_exec a st` TISA_RESULT_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[tisa_then; TISA_RESULT_DISTINCT; TISA_RESULT_INJ] THEN
  MESON_TAC[]);;

let TISA_EXEC_INSTR_EQ = prove
 (`!i st r. tisa_exec (TInstr i) st = r <=> tisa_instr i st = r`,
  REWRITE_TAC[tisa_exec]);;

let TISA_EXEC_IF_EQ = prove
 (`!c a b st r.
     tisa_exec (TIf c a b) st = r <=>
     ~tisa_bool (tregs st c) /\ r = TStop 3 (tisa_failst 3 st) \/
     tisa_bool (tregs st c) /\ tregs st c = word 0 /\ tisa_exec b st = r \/
     tisa_bool (tregs st c) /\ ~(tregs st c = word 0) /\ tisa_exec a st = r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_exec; TISA_FAIL_STOP] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let TISA_EXEC_RETURN_EQ = prove
 (`!out x st r.
     tisa_exec (TReturn out x) st = r <=> r = TStop out (tisa_finst out (tregs st x) st)`,
  REWRITE_TAC[tisa_exec; TISA_FINISH_STOP] THEN MESON_TAC[]);;

let TISA_EXEC_SKIP_EQ = prove
 (`!st r. tisa_exec TSkip st = r <=> r = TCont st`,
  REWRITE_TAC[tisa_exec] THEN MESON_TAC[]);;

(* Rewrites a run equation of a concrete loop-free statement into its paths. *)
let TISA_PATH_THMS =
  [TISA_EXEC_SEQ_EQ; TISA_EXEC_INSTR_EQ; TISA_EXEC_IF_EQ; TISA_EXEC_RETURN_EQ;
   TISA_EXEC_SKIP_EQ; tisa_instr; TISA_FAIL_STOP; TISA_COND_EQ;
   TISA_RESULT_DISTINCT; TISA_RESULT_INJ; TISA_TY_DISTINCT_ALL; tisa_norm;
   tisa_shift; tisa_narrow; tisa_shift64; tisa_compare; tisa_compare_at; tisa_rhs;
   tisa_index; tisa_binop; TISA_TREGS_SETREG; TISA_TMEM_SETREG;
   TISA_TREGS_STORE; TISA_TMEM_STORE; TISA_READ_SETREG;
   LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM; EXISTS_OR_THM; UNWIND_THM1; UNWIND_THM2;
   LEFT_OR_DISTRIB; RIGHT_OR_DISTRIB; GSYM CONJ_ASSOC];;

let TISA_PATH_SIMPS = TISA_PATH_THMS @
  [TISA_FWORD_SETREG; TISA_BASE_SETREG; TISA_LEN_SETREG; TISA_INSIDE_SETREG;
   TISA_FRAME_SETREG; ARITH_EQ; tisa_ea; tisa_addr_mid; INT_ADD_RID;
   GSYM WORD_IWORD; WORD_VAL];;

(* After the paths are split: substitute the run's result, then each named   *)
(* intermediate state by its value.                                          *)
let TISA_SUBST_STATES_TAC =
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> let c = concl th in is_eq c && is_var(rand c) &&
                     type_of(rand c) = `:tisa_state` && not(is_var(lhand c)))));;

let TISA_SUBST_RESULT_TAC =
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o
    check (fun th -> let c = concl th in is_eq c && is_var(lhand c) &&
                     type_of(lhand c) = `:tisa_result`)));;

(* Splits the paths of a run equation in the antecedent of the goal.         *)
let TISA_PATHS_TAC defs =
  REWRITE_TAC defs THEN SIMP_TAC TISA_PATH_SIMPS THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN TISA_SUBST_RESULT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TISA_RESULT_DISTINCT; TISA_RESULT_INJ]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN TISA_SUBST_STATES_TAC THEN
  ASM_SIMP_TAC TISA_PATH_SIMPS THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV WORD_REDUCE_CONV)) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> let c = concl th in
    is_eq c && is_var(lhand c) && type_of(lhand c) = `:num` && is_numeral(rand c)))) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NUM_REDUCE_CONV)) THEN
  TRY(FIRST_ASSUM CONTR_TAC);;

(* ------------------------------------------------------------------------- *)
(* The finish writes (status at frame word 18, return value at 19), and      *)
(* addresses computed by ADDR.                                               *)
(* ------------------------------------------------------------------------- *)

let TISA_FWORD_STORE_FWORD = prove
 (`!st i j (v:int64).
        val(tregs st 0) + 192 <= 2 EXP 64 /\ i < 24 /\ j < 24
        ==> tisa_fword (tisa_setfword j v st) i =
            if i = j then v else tisa_fword st i`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[tisa_setfword; tisa_fword; tisa_read; tisa_frame; TISA_TREGS_STORE;
              TISA_TMEM_STORE] THEN
  SUBGOAL_THEN `!k. k < 24 ==> val(word_add (tregs st 0) (word(8 * k)):int64) = val(tregs st 0) + 8 * k`
   (fun th -> ASSUME_TAC th) THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`word_add (tregs st 0) (word (8 * j)):int64`; `val(v:int64)`;
                   `tmem st`] TISA_READ_SAME_WRITE) THEN
    REWRITE_TAC[WORD_VAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    AP_TERM_TAC THEN MATCH_MP_TAC TISA_READ_DISJOINT_WRITE THEN
    ASM_SIMP_TAC[] THEN ASM_ARITH_TAC]);;

let TISA_FWORD_FINST = prove
 (`!st out (v:int64) i.
        val(tregs st 0) + 192 <= 2 EXP 64 /\ i < 24
        ==> tisa_fword (tisa_finst out v st) i =
            if i = 19 then v else if i = 18 then word out else tisa_fword st i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_finst] THEN
  W(fun (asl,w) -> MP_TAC(ISPECL [`tisa_setfword 18 (word out) st`; `i:num`; `19`; `v:int64`]
                    TISA_FWORD_STORE_FWORD)) THEN
  REWRITE_TAC[tisa_setfword; TISA_TREGS_STORE] THEN ANTS_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`st:tisa_state`; `i:num`; `18`; `word out:int64`] TISA_FWORD_STORE_FWORD) THEN
  REWRITE_TAC[tisa_setfword] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[]);;

(* A read of 8 bytes away from the frame is not affected by the finish.      *)
let TISA_READ_FINST = prove
 (`!st out (v:int64) (a:int64).
        val(tregs st 0) + 192 <= 2 EXP 64 /\ val a + 8 <= 2 EXP 64 /\
        (val a + 8 <= val(tregs st 0) \/ val(tregs st 0) + 192 <= val a)
        ==> tisa_read (tisa_finst out v st) a 8 = tisa_read st a 8`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[tisa_finst; tisa_setfword; tisa_read; tisa_frame; TISA_TREGS_STORE;
              TISA_TMEM_STORE] THEN
  SUBGOAL_THEN `!k. k < 24 ==> val(word_add (tregs st 0) (word(8 * k)):int64) = val(tregs st 0) + 8 * k`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `8`; `word_add (tregs st 0) (word(8 * 19)):int64`; `8`;
                 `val(v:int64)`;
                 `write (bytes(word_add (tregs st 0) (word(8 * 18)),8))
                        (val(word out:int64)) (tmem st)`]
         TISA_READ_DISJOINT_WRITE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[ARITH_RULE `19 < 24`] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC TISA_READ_DISJOINT_WRITE THEN
  ASM_SIMP_TAC[ARITH_RULE `18 < 24`] THEN ASM_ARITH_TAC);;

let TISA_ADDR_WORD = prove
 (`!(b:int64) (x:int64) s.
        iword(&(val b) + &(val x) * &2 pow s) = word_add b (word(2 EXP s * val x)):int64`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_MUL; INT_OF_NUM_ADD; GSYM WORD_IWORD] THEN
  REWRITE_TAC[WORD_ADD; WORD_VAL] THEN REWRITE_TAC[MULT_SYM]);;

let TISA_VAL_SHL1 = prove
 (`!x:int64. val x < 2 EXP 63 ==> val(word_shl x 1) = 2 * val x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SHL; DIMINDEX_64; EXP_1] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Reads through an 8-byte store: the stored value at the same address, the  *)
(* old one at a disjoint address; frame words through a store away from the *)
(* frame.                                                                    *)
(* ------------------------------------------------------------------------- *)

let TISA_READ_STORE = prove
 (`!(a:int64) (v:int64) st (b:int64).
        val a + 8 <= 2 EXP 64 /\ val b + 8 <= 2 EXP 64 /\
        (a = b \/ val a + 8 <= val b \/ val b + 8 <= val a)
        ==> tisa_read (tisa_store a 8 v st) b 8 = if a = b then v else tisa_read st b 8`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[tisa_read; TISA_TMEM_STORE] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`b:int64`; `val(v:int64)`; `tmem st`] TISA_READ_SAME_WRITE) THEN
    ASM_REWRITE_TAC[WORD_VAL];
    FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC TISA_READ_DISJOINT_WRITE THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let TISA_FWORD_STORE_OUTSIDE = prove
 (`!(a:int64) w (v:int64) st i.
        val(tregs st 0) + 192 <= 2 EXP 64 /\ i < 24 /\ val a + w <= 2 EXP 64 /\
        (val a + w <= val(tregs st 0) \/ val(tregs st 0) + 192 <= val a)
        ==> tisa_fword (tisa_store a w v st) i = tisa_fword st i`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[tisa_fword; tisa_read; tisa_frame; TISA_TREGS_STORE; TISA_TMEM_STORE] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `val(word_add (tregs st 0) (word(8 * i)):int64) = val(tregs st 0) + 8 * i`
   ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC TISA_READ_DISJOINT_WRITE THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the functional proofs of programs.                            *)
(* ------------------------------------------------------------------------- *)

let tisa_has_tm t th = can (find_term ((=) t)) (concl th);;

let tisa_find_sub p w = find_term (fun t -> try p t with Failure _ -> false) w;;

(* Linear arithmetic over the assumptions that bear on the goal: every       *)
(* arithmetic assumption without disjunctions, and the disjunctive ones that *)
(* share an atom with the goal or with an assumption that does.              *)
let TISA_ARITH_TAC =
  let bad = ["tisa_inside"; "tisa_bool"; "tisa_store"; "tisa_setreg"; "tisa_exec"] in
  let is_val t = is_comb t && (try fst(dest_const(rator t)) = "val" with Failure _ -> false) in
  let atoms tm = setify(find_terms is_val tm) in
  fun (asl,w) ->
    let ok th = let c = concl th in
      not (is_forall c) &&
      not (can (find_term (fun t -> is_const t && mem (fst(dest_const t)) bad)) c) &&
      can (find_term is_val) c in
    let cands = filter (fun (_,th) -> ok th) asl in
    let plain = filter (fun (_,th) -> not (can (find_term is_disj) (concl th))) cands
    and disj = filter (fun (_,th) -> can (find_term is_disj) (concl th)) cands in
    let g0 = atoms w in
    let g1 = itlist (fun (_,th) acc -> let a = atoms (concl th) in
                       if intersect a g0 <> [] then union a acc else acc) plain g0 in
    let rel = filter (fun (_,th) -> intersect (atoms (concl th)) g1 <> []) disj in
    (MAP_EVERY (fun (_,th) -> MP_TAC th) (plain @ rel) THEN ARITH_TAC) (asl,w);;

(* A frame word through one register update or one store away from the      *)
(* frame.                                                                    *)
let TISA_FWORD_STEP_TAC =
  W(fun (asl,w) ->
    let l = lhand w in
    let s = rand(rator l) and i = rand l in
    let h,args = strip_comb s in
    if h = `tisa_setreg` then
      let ne = EQT_ELIM(NUM_REDUCE_CONV(mk_neg(mk_eq(hd args, `0`)))) in
      GEN_REWRITE_TAC LAND_CONV
        [MATCH_MP (ISPECL [el 0 args; el 1 args; el 2 args; i] TISA_FWORD_SETREG) ne]
    else if h = `tisa_store` then
      MP_TAC(ISPECL [el 0 args; el 1 args; el 2 args; el 3 args; i] TISA_FWORD_STORE_OUTSIDE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[TISA_TREGS_STORE; TISA_TREGS_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TISA_ARITH_TAC;
        DISCH_THEN SUBST1_TAC]
    else FAIL_TAC "TISA_FWORD_STEP_TAC");;

(* An 8-byte read through one register update or one 8-byte store; equal    *)
(* and disjoint addresses are told apart by arithmetic on their values.      *)
let TISA_READ_STEP_TAC =
  W(fun (asl,w) ->
    let l = lhand w in
    let _,args0 = strip_comb l in
    let s = el 0 args0 and b = el 1 args0 in
    let h,args = strip_comb s in
    if h = `tisa_setreg` then GEN_REWRITE_TAC LAND_CONV [TISA_READ_SETREG]
    else if h = `tisa_store` && el 1 args = `8` then
      MP_TAC(ISPECL [el 0 args; el 2 args; el 3 args; b] TISA_READ_STORE) THEN
      ANTS_TAC THENL [REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TISA_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[] THEN
      TRY(COND_CASES_TAC THENL
            [FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int64->num`) THEN TISA_ARITH_TAC; ALL_TAC])
    else FAIL_TAC "TISA_READ_STEP_TAC");;
