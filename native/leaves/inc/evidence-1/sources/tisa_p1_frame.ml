(* ========================================================================= *)
(* What a run may write (SEMANTICS.txt, section 9): nothing outside the      *)
(* program's read-write regions and its own frame words (status, ret_val,    *)
(* fuel), and never v0. Programs whose stores name read-write regions and    *)
(* that never write v0 (admission ensures both) keep everything else.        *)
(* ========================================================================= *)

needs "tisa/hol/tisa_p1_memory.ml";;

(* The syntactic side, as admission ensures it: stores name read-write
   regions, loads name accessible declared regions, frame loads name one of
   the 24 frame words, and nothing writes v0. *)
let tisa_rw = new_definition
 `tisa_rw (decls:(num#num#num)list) r <=> r < LENGTH decls /\ FST(EL r decls) = 2`;;

let tisa_readable = new_definition
 `tisa_readable (decls:(num#num#num)list) r <=> r < LENGTH decls /\ ~(FST(EL r decls) = 0)`;;

let tisa_instr_ok = define
 `(tisa_instr_ok decls (TImm t d imm) <=> ~(d = 0)) /\
  (tisa_instr_ok decls (TMov t d a) <=> ~(d = 0)) /\
  (tisa_instr_ok decls (TBin bop t d a b) <=> ~(d = 0)) /\
  (tisa_instr_ok decls (TShift sop t d a s) <=> ~(d = 0)) /\
  (tisa_instr_ok decls (TExtract t d a l n) <=> ~(d = 0)) /\
  (tisa_instr_ok decls (TCmp c t d a rhs) <=> ~(d = 0)) /\
  (tisa_instr_ok decls (TSelect t d k a b) <=> ~(d = 0)) /\
  (tisa_instr_ok decls (TAddr r d p i s off) <=> ~(d = 0) /\ tisa_readable decls r) /\
  (tisa_instr_ok decls (TLoad t w r d p off) <=> ~(d = 0) /\ tisa_readable decls r) /\
  (tisa_instr_ok decls (TLoadFrame t d fi) <=> ~(d = 0) /\ fi < 24) /\
  (tisa_instr_ok decls (TStore w r p off v) <=> tisa_rw decls r)`;;

let tisa_stmt_ok = define
 `(tisa_stmt_ok decls TSkip <=> T) /\
  (tisa_stmt_ok decls (TInstr i) <=> tisa_instr_ok decls i) /\
  (tisa_stmt_ok decls (TSeq a b) <=> tisa_stmt_ok decls a /\ tisa_stmt_ok decls b) /\
  (tisa_stmt_ok decls (TIf c a b) <=> tisa_stmt_ok decls a /\ tisa_stmt_ok decls b) /\
  (tisa_stmt_ok decls (TCountLoop x n cap body) <=> ~(x = 0) /\ tisa_stmt_ok decls body) /\
  (tisa_stmt_ok decls (TEarlyLoop x n k cap body) <=> ~(x = 0) /\ tisa_stmt_ok decls body) /\
  (tisa_stmt_ok decls (TReturn out r) <=> T) /\
  (tisa_stmt_ok decls (TFund u) <=> T)`;;

let tisa_state_of = define
 `(tisa_state_of (TCont t) = t) /\ (tisa_state_of (TStop k t) = t)`;;

(* Bytes a run may write, for state t: its read-write regions and the frame
   words from status to fuel_used (bytes 144 to 175). *)
let tisa_writable = new_definition
 `tisa_writable decls t (a:int64) <=>
    (?r. tisa_rw decls r /\ val(tisa_base t r) <= val a /\
         val a < val(tisa_base t r) + val(tisa_len t r)) \/
    (val(tregs t 0) + 144 <= val a /\ val a < val(tregs t 0) + 176)`;;

(* The frame is an object, accessible regions do not wrap, and non-empty
   read-write regions lie apart from the frame (as entry validation requires). *)
let tisa_frame_sep = new_definition
 `tisa_frame_sep decls t <=>
    LENGTH decls <= 9 /\ val(tregs t 0) + 192 <= 2 EXP 64 /\
    (!r. tisa_readable decls r
         ==> val(tisa_base t r) + val(tisa_len t r) < 2 EXP 64) /\
    (!r. tisa_rw decls r
         ==> val(tisa_len t r) = 0 \/
             val(tisa_base t r) + val(tisa_len t r) <= val(tregs t 0) \/
             val(tregs t 0) + 192 <= val(tisa_base t r))`;;

let TISA_RW_READABLE = prove
 (`!decls r. tisa_rw decls r ==> tisa_readable decls r`,
  REWRITE_TAC[tisa_rw; tisa_readable] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let TISA_SEP_BOUND = prove
 (`!decls t r. tisa_frame_sep decls t /\ tisa_readable decls r
               ==> val(tisa_base t r) + val(tisa_len t r) < 2 EXP 64`,
  MESON_TAC[tisa_frame_sep]);;

(* The property preserved: v0 is kept, and every byte outside the writable
   set keeps its value (in particular the frame's region words, so the
   writable set itself is unchanged). *)
let tisa_keeps = new_definition
 `tisa_keeps decls t t' <=>
    tregs t' 0 = tregs t 0 /\
    !a. ~tisa_writable decls t a ==> tmem t' a = tmem t a`;;

(* ------------------------------------------------------------------------- *)
(* Bytes outside a write keep their values; words outside writes too.        *)
(* ------------------------------------------------------------------------- *)

let TISA_WRITE_BYTES_OUTSIDE = prove
 (`!(a:int64) w n m b.
        val a + w <= 2 EXP 64 /\ ~(val a <= val b /\ val b < val a + w)
        ==> write (bytes(a,w)) n m b = m b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[WRITE_BYTES] THEN
  SUBGOAL_THEN `~(val(word_sub b a:int64) < w)` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_64] THEN
  MP_TAC(ISPEC `b:int64` VAL_BOUND_64) THEN MP_TAC(ISPEC `a:int64` VAL_BOUND_64) THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let TISA_VAL_OFFSET = prove
 (`!(a:int64) n. val a + n < 2 EXP 64 ==> val(word_add a (word n)) = val a + n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `n MOD 2 EXP 64 = n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

(* A frame word below status lies outside every writable byte. *)
let TISA_FWORD_KEEP = prove
 (`!decls t t' i.
        tisa_frame_sep decls t /\ tisa_keeps decls t t' /\ i < 18
        ==> tisa_fword t' i = tisa_fword t i`,
  REWRITE_TAC[tisa_keeps; tisa_fword; tisa_read; tisa_frame; tisa_frame_sep] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                  can (find_term ((=) `tisa_writable`)) (concl th))) THEN
  REWRITE_TAC[tisa_writable; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  SUBGOAL_THEN
   `val(word_add (word_add (tregs t 0) (word(8 * i))) (word k):int64) = val(tregs t 0) + 8 * i + k`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  X_GEN_TAC `r:num` THEN
  ASM_CASES_TAC `tisa_rw decls r` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
                  can (find_term ((=) `tisa_rw`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Keeping is transitive, since the region words are kept.                   *)
(* ------------------------------------------------------------------------- *)

let TISA_KEEPS_REGIONS = prove
 (`!decls t t' r.
        tisa_frame_sep decls t /\ tisa_keeps decls t t' /\ tisa_readable decls r
        ==> tisa_base t' r = tisa_base t r /\ tisa_len t' r = tisa_len t r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_base; tisa_len] THEN
  MATCH_MP_TAC TISA_FWORD_KEEP THEN EXISTS_TAC `decls:(num#num#num)list` THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tisa_readable; tisa_frame_sep]) THEN ASM_ARITH_TAC);;

let TISA_KEEPS_WRITABLE = prove
 (`!decls t t'.
        tisa_frame_sep decls t /\ tisa_keeps decls t t'
        ==> (!a. tisa_writable decls t' a <=> tisa_writable decls t a) /\
            tisa_frame_sep decls t'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `tregs t' 0 = tregs t 0` ASSUME_TAC THENL
   [ASM_MESON_TAC[tisa_keeps]; ALL_TAC] THEN
  SUBGOAL_THEN `!r. tisa_readable decls r ==> tisa_base t' r = tisa_base t r /\ tisa_len t' r = tisa_len t r`
  ASSUME_TAC THENL [ASM_MESON_TAC[TISA_KEEPS_REGIONS]; ALL_TAC] THEN
  SUBGOAL_THEN `!r. tisa_rw decls r ==> tisa_base t' r = tisa_base t r /\ tisa_len t' r = tisa_len t r`
  ASSUME_TAC THENL [ASM_MESON_TAC[TISA_RW_READABLE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[tisa_writable] THEN ASM_REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    ASM_CASES_TAC `tisa_rw decls r` THEN ASM_SIMP_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[tisa_frame_sep]) THEN
    REWRITE_TAC[tisa_frame_sep] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[]]);;

let TISA_KEEPS_REFL = prove
 (`!decls t. tisa_keeps decls t t`,
  REWRITE_TAC[tisa_keeps]);;

let TISA_KEEPS_TRANS = prove
 (`!decls t t' t''.
        tisa_frame_sep decls t /\ tisa_keeps decls t t' /\ tisa_keeps decls t' t''
        ==> tisa_keeps decls t t''`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`decls:(num#num#num)list`; `t:tisa_state`; `t':tisa_state`] TISA_KEEPS_WRITABLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tisa_keeps]) THEN ASM_REWRITE_TAC[tisa_keeps] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The effects a run has.                                                    *)
(* ------------------------------------------------------------------------- *)

let TISA_KEEPS_SETREG = prove
 (`!decls t d v. ~(d = 0) ==> tisa_keeps decls t (tisa_setreg d v t)`,
  SIMP_TAC[tisa_keeps; tisa_setreg; tregs; tmem]);;

(* A store whose bytes are all writable. *)
let TISA_KEEPS_STORE = prove
 (`!decls t a w v.
        val a + w <= 2 EXP 64 /\
        (!b. val a <= val b /\ val b < val a + w ==> tisa_writable decls t b)
        ==> tisa_keeps decls t (tisa_store a w v t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_keeps; tisa_store; tregs; tmem] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_WRITE_BYTES_OUTSIDE THEN ASM_MESON_TAC[]);;

(* Writing frame word j, for j from 18 (status) to 21 (fuel_used). *)
let TISA_KEEPS_SETFWORD = prove
 (`!decls t j v.
        tisa_frame_sep decls t /\ 18 <= j /\ j <= 21
        ==> tisa_keeps decls t (tisa_setfword j v t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_setfword; tisa_frame] THEN
  MATCH_MP_TAC TISA_KEEPS_STORE THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tisa_frame_sep]) THEN
  SUBGOAL_THEN `val(word_add (tregs t 0) (word(8 * j)):int64) = val(tregs t 0) + 8 * j` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_writable] THEN DISJ2_TAC THEN ASM_ARITH_TAC);;

let TISA_KEEPS_FAIL = prove
 (`!decls t k. tisa_frame_sep decls t
               ==> tisa_keeps decls t (tisa_state_of (tisa_fail k t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_fail; tisa_state_of] THEN
  MATCH_MP_TAC TISA_KEEPS_TRANS THEN
  EXISTS_TAC `tisa_setfword 18 (word k) t` THEN
  ASM_SIMP_TAC[TISA_KEEPS_SETFWORD; ARITH_RULE `18 <= 18 /\ 18 <= 21`] THEN
  MP_TAC(SPECL [`decls:(num#num#num)list`; `t:tisa_state`; `tisa_setfword 18 (word k) t`]
               TISA_KEEPS_WRITABLE) THEN
  ASM_SIMP_TAC[TISA_KEEPS_SETFWORD; ARITH_RULE `18 <= 18 /\ 18 <= 21`] THEN
  STRIP_TAC THEN MATCH_MP_TAC TISA_KEEPS_SETFWORD THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let TISA_KEEPS_FINISH = prove
 (`!decls t out v. tisa_frame_sep decls t
                   ==> tisa_keeps decls t (tisa_state_of (tisa_finish out v t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_finish; tisa_state_of] THEN
  MATCH_MP_TAC TISA_KEEPS_TRANS THEN
  EXISTS_TAC `tisa_setfword 18 (word out) t` THEN
  ASM_SIMP_TAC[TISA_KEEPS_SETFWORD; ARITH_RULE `18 <= 18 /\ 18 <= 21`] THEN
  MP_TAC(SPECL [`decls:(num#num#num)list`; `t:tisa_state`; `tisa_setfword 18 (word out) t`]
               TISA_KEEPS_WRITABLE) THEN
  ASM_SIMP_TAC[TISA_KEEPS_SETFWORD; ARITH_RULE `18 <= 18 /\ 18 <= 21`] THEN
  STRIP_TAC THEN MATCH_MP_TAC TISA_KEEPS_SETFWORD THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instructions.                                                             *)
(* ------------------------------------------------------------------------- *)

let TISA_RESULT_CASES = prove_cases_thm tisa_result_INDUCT;;

let TISA_VAL_IWORD_INT = prove
 (`!e:int. &0 <= e /\ e < &2 pow 64 ==> &(val(iword e:int64)) = e`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_VAL_IWORD THEN ASM_REWRITE_TAC[DIMINDEX_64]);;

(* An access [e, e + w) inside a region that does not wrap. *)
let TISA_IWORD_RANGE = prove
 (`!(e:int) w b l.
        &(val(b:int64)) <= e /\ e + &w <= &(val b) + &(val(l:int64)) /\
        val b + val l < 2 EXP 64
        ==> val(iword e:int64) + w <= 2 EXP 64 /\
            !c:int64. val(iword e:int64) <= val c /\ val c < val(iword e:int64) + w
                      ==> val b <= val c /\ val c < val b + val l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&(val(iword e:int64)) = e` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_IWORD_INT THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_ADD;
                                GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_LT]) THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_ADD;
                              GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_LT]) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_POW] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_INT_ARITH_TAC; REPEAT STRIP_TAC THEN ASM_INT_ARITH_TAC]);;


let TISA_KEEPS_INSTR = prove
 (`!decls i t. tisa_instr_ok decls i /\ tisa_frame_sep decls t
               ==> tisa_keeps decls t (tisa_state_of (tisa_instr i t))`,
  GEN_TAC THEN MATCH_MP_TAC tisa_instr_INDUCT THEN
  REWRITE_TAC[tisa_instr_ok; tisa_instr] THEN REPEAT STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[tisa_state_of; TISA_KEEPS_FAIL; TISA_KEEPS_SETREG] THEN
  (* the store, TStore a0 a1 a2 a3 a4: its bytes lie in read-write region a1 *)
  MATCH_MP_TAC TISA_KEEPS_STORE THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tisa_inside]) THEN
  SUBGOAL_THEN `val(tisa_base t a1) + val(tisa_len t a1) < 2 EXP 64` ASSUME_TAC THENL
   [ASM_MESON_TAC[TISA_SEP_BOUND; TISA_RW_READABLE]; ALL_TAC] THEN
  MP_TAC(SPECL [`tisa_ea t a2 a3`; `a0:num`; `tisa_base t a1`; `tisa_len t a1`] TISA_IWORD_RANGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_writable] THEN DISJ1_TAC THEN
  EXISTS_TAC `a1:num` THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Loops, by induction on the iterations left.                               *)
(* ------------------------------------------------------------------------- *)

let TISA_KEEPS_THEN = prove
 (`!decls t r f.
        tisa_frame_sep decls t /\ tisa_keeps decls t (tisa_state_of r) /\
        (!u. r = TCont u ==> tisa_keeps decls u (tisa_state_of (f u)))
        ==> tisa_keeps decls t (tisa_state_of (tisa_then r f))`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:tisa_result` TISA_RESULT_CASES) THEN
  REWRITE_TAC[tisa_then; tisa_state_of; injectivity "tisa_result"; distinctness "tisa_result"] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TISA_KEEPS_TRANS THEN EXISTS_TAC `a:tisa_state` THEN
  ASM_MESON_TAC[]);;

let TISA_KEEPS_COUNT_ITER = prove
 (`!m decls f x j t.
        ~(x = 0) /\ tisa_frame_sep decls t /\
        (!u. tisa_frame_sep decls u ==> tisa_keeps decls u (tisa_state_of (f u)))
        ==> tisa_keeps decls t (tisa_state_of (tisa_count_iter m f x j t))`,
  INDUCT_TAC THEN REWRITE_TAC[tisa_count_iter] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[tisa_state_of; TISA_KEEPS_SETREG]; ALL_TAC] THEN
  ABBREV_TAC `t1 = tisa_setreg x (word j) t` THEN
  SUBGOAL_THEN `tisa_keeps decls t t1 /\ tisa_frame_sep decls t1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t1" THEN ASM_SIMP_TAC[TISA_KEEPS_SETREG] THEN
    ASM_MESON_TAC[TISA_KEEPS_WRITABLE; TISA_KEEPS_SETREG];
    ALL_TAC] THEN
  MATCH_MP_TAC TISA_KEEPS_TRANS THEN EXISTS_TAC `t1:tisa_state` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TISA_KEEPS_THEN THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `u:tisa_state` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[TISA_KEEPS_WRITABLE; tisa_state_of]);;

let TISA_KEEPS_EARLY_CHECK = prove
 (`!decls k t g.
        tisa_frame_sep decls t /\
        (tisa_bool (tregs t k) /\ ~(tregs t k = word 0)
         ==> tisa_keeps decls t (tisa_state_of (g t)))
        ==> tisa_keeps decls t (tisa_state_of (tisa_early_check k t g))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_early_check] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[TISA_KEEPS_FAIL; tisa_state_of; TISA_KEEPS_REFL] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let TISA_KEEPS_EARLY_ITER = prove
 (`!m decls f x k j t.
        ~(x = 0) /\ tisa_frame_sep decls t /\
        (!u. tisa_frame_sep decls u ==> tisa_keeps decls u (tisa_state_of (f u)))
        ==> tisa_keeps decls t (tisa_state_of (tisa_early_iter m f x k j t))`,
  INDUCT_TAC THEN REWRITE_TAC[tisa_early_iter] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[tisa_state_of; TISA_KEEPS_SETREG]; ALL_TAC] THEN
  ABBREV_TAC `t1 = tisa_setreg x (word j) t` THEN
  SUBGOAL_THEN `tisa_keeps decls t t1 /\ tisa_frame_sep decls t1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t1" THEN ASM_SIMP_TAC[TISA_KEEPS_SETREG] THEN
    ASM_MESON_TAC[TISA_KEEPS_WRITABLE; TISA_KEEPS_SETREG];
    ALL_TAC] THEN
  MATCH_MP_TAC TISA_KEEPS_TRANS THEN EXISTS_TAC `t1:tisa_state` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TISA_KEEPS_EARLY_CHECK THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC TISA_KEEPS_THEN THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `u:tisa_state` THEN DISCH_TAC THEN
  SUBGOAL_THEN `tisa_frame_sep decls u` ASSUME_TAC THENL
   [ASM_MESON_TAC[TISA_KEEPS_WRITABLE; tisa_state_of]; ALL_TAC] THEN
  MATCH_MP_TAC TISA_KEEPS_EARLY_CHECK THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Statements.                                                               *)
(* ------------------------------------------------------------------------- *)

let TISA_KEEPS_EXEC = prove
 (`!S decls t. tisa_stmt_ok decls S /\ tisa_frame_sep decls t
               ==> tisa_keeps decls t (tisa_state_of (tisa_exec S t))`,
  MATCH_MP_TAC tisa_stmt_INDUCT THEN REWRITE_TAC[tisa_stmt_ok; tisa_exec] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[tisa_state_of; TISA_KEEPS_REFL];
    MESON_TAC[TISA_KEEPS_INSTR];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_KEEPS_THEN THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `u:tisa_state` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[TISA_KEEPS_WRITABLE; tisa_state_of];
    REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[TISA_KEEPS_FAIL];
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[TISA_KEEPS_FAIL] THEN
    MATCH_MP_TAC TISA_KEEPS_COUNT_ITER THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[TISA_KEEPS_FAIL] THEN
    MATCH_MP_TAC TISA_KEEPS_EARLY_ITER THEN ASM_SIMP_TAC[];
    SIMP_TAC[TISA_KEEPS_FINISH];
    REWRITE_TAC[tisa_fund] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[TISA_KEEPS_FAIL; tisa_state_of; TISA_KEEPS_SETFWORD; ARITH_RULE `18 <= 21 /\ 21 <= 21`]]);;
