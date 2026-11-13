(* ========================================================================= *)
(* Completeness of intern16: the interner's table finds every row, so equal  *)
(* keys always get equal ids, and different ids mean different keys.         *)
(*                                                                           *)
(* INTERN16_SOUND (intern16.ml) says a FIRED run returns an id whose row is  *)
(* the key. This file adds the table's invariant, intern_ok: the rows below  *)
(* the count lie in the rows region, each is found by linear probing from    *)
(* its key's hash through non-empty slots to a slot holding its id plus one, *)
(* and no two hold one key. Every run from a well-formed interner, whatever *)
(* its outcome, leaves a well-formed interner (INTERN16_RUN_COMPLETE), and a *)
(* FIRED run that appended a row found no row holding the key below the old  *)
(* count (INTERN16_APPEND_ABSENT). The same hold of tisa_run.                *)
(*                                                                           *)
(* The loop body is proved with the weakest-precondition generator of        *)
(* tisa_wp.ml and the loop invariant intern16_inv; the table argument is     *)
(* INTERN_OK_APPEND, independent of t-ISA.                                   *)
(* ========================================================================= *)

needs "native/hol/intern16.ml";;
needs "native/hol/tisa_wp.ml";;

(* ------------------------------------------------------------------------- *)
(* The table: the hash intern16 computes, its probe positions, and slots.    *)
(* ------------------------------------------------------------------------- *)

let intern_hash = new_definition
 `intern_hash (k0:int64) (k1:int64) =
    word_xor (word_mul (word_xor k0 k1) (word 11400714819323198485))
             (word_ushr (word_mul (word_xor k0 k1) (word 11400714819323198485)) 29)`;;

let intern_slots = new_definition
 `intern_slots st = word_ushr (tisa_len st 1) 3`;;

let intern_pos = new_definition
 `intern_pos st (h:int64) x = word_and (word_add h (word x)) (word_sub (intern_slots st) (word 1))`;;

let intern_slot = new_definition
 `intern_slot st (p:int64) = tisa_read st (word_add (tisa_base st 1) (word(8 * val p))) 8`;;

(* Row i holds the key (k0,k1). *)
let intern_has = new_definition
 `intern_has st i (k0:int64) (k1:int64) <=>
    intern_word st (2 * i) = k0 /\ intern_word st (2 * i + 1) = k1`;;

(* Completeness: every row below the count is reachable by probing from its *)
(* key's hash through non-empty slots, and its slot holds its id plus one.  *)
let intern_complete = new_definition
 `intern_complete st <=>
    !i. i < val(intern_count st)
        ==> ?d. d < val(intern_slots st) /\
                intern_slot st (intern_pos st (intern_hash (intern_word st (2 * i))
                                                           (intern_word st (2 * i + 1))) d) =
                word(i + 1) /\
                !e. e < d
                    ==> ~(intern_slot st (intern_pos st (intern_hash (intern_word st (2 * i))
                                                                     (intern_word st (2 * i + 1))) e) =
                          word 0)`;;

(* Canonicity: no two rows below the count hold the same key. *)
let intern_distinct = new_definition
 `intern_distinct st <=>
    !i j. i < val(intern_count st) /\ j < val(intern_count st) /\
          intern_has st i (intern_word st (2 * j)) (intern_word st (2 * j + 1))
          ==> i = j`;;

(* A well-formed interner: the rows below the count lie in the rows region, *)
(* each is found by probing from its key's hash, and no two hold one key.   *)
(* The first conjunct is needed: rows past the rows region can lie in the   *)
(* frame (a rows region just below it, a count above its capacity), and the *)
(* status and return words every stop writes would then change those rows. *)
let intern_ok = new_definition
 `intern_ok st <=>
    val(intern_count st) <= val(tisa_len st 0) DIV 16 /\
    intern_complete st /\ intern_distinct st`;;

(* What one probe that continued established: the slot was not empty, and   *)
(* if it named a row below the count, that row does not hold the key.       *)
let intern_probed = new_definition
 `intern_probed st x <=>
    let p = intern_pos st (intern_hash (tisa_fword st 22) (tisa_fword st 23)) x in
    ~(intern_slot st p = word 0) /\
    (val(word_sub (intern_slot st p) (word 1)) < val(intern_count st)
     ==> ~intern_has st (val(word_sub (intern_slot st p) (word 1)))
                        (tisa_fword st 22) (tisa_fword st 23))`;;

(* The loop invariant over the entry state st. *)
let intern16_inv = new_definition
 `intern16_inv st N j s <=>
    tregs s 0 = tregs st 0 /\ tmem s = tmem st /\
    tregs s 1 = tisa_fword st 22 /\ tregs s 2 = tisa_fword st 23 /\
    tregs s 3 = intern_count st /\
    tregs s 4 = word_sub (intern_slots st) (word 1) /\
    tregs s 5 = intern_hash (tisa_fword st 22) (tisa_fword st 23) /\
    tregs s 6 = intern_slots st /\
    N = val(intern_slots st) /\
    (!x. x < j ==> intern_probed st x)`;;

(* ------------------------------------------------------------------------- *)
(* Probe positions lie below the slot count; words one past a row id.        *)
(* ------------------------------------------------------------------------- *)

let INTERN_POS_LT = prove
 (`!st h x. 0 < val(intern_slots st) ==> val(intern_pos st h x) < val(intern_slots st)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[intern_pos] THEN
  MP_TAC(ISPECL [`word_add h (word x):int64`; `word_sub (intern_slots st) (word 1):int64`]
         (CONJUNCT2 VAL_WORD_AND_LE)) THEN
  MP_TAC(ISPECL [`intern_slots st`; `word 1:int64`] TISA_VAL_SUB_EXACT) THEN
  REWRITE_TAC[VAL_WORD_1] THEN ASM_ARITH_TAC);;

let INTERN_WORD_SUC_NZ = prove
 (`!i. i + 1 < 2 EXP 64 ==> ~(word(i + 1):int64 = word 0)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int64->num`) THEN
  ASM_SIMP_TAC[TISA_VAL_WORD_EXACT; VAL_WORD_0] THEN ARITH_TAC);;

let INTERN_WORD_SUC_PRED = prove
 (`!i. i + 1 < 2 EXP 64 ==> val(word_sub (word(i + 1):int64) (word 1)) = i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word(i + 1):int64) = i + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`word(i + 1):int64`; `word 1:int64`] TISA_VAL_SUB_EXACT) THEN
  ASM_REWRITE_TAC[VAL_WORD_1] THEN ARITH_TAC);;

let INTERN_PROBED_THM = prove
 (`!st x. intern_probed st x <=>
          ~(intern_slot st (intern_pos st (intern_hash (tisa_fword st 22) (tisa_fword st 23)) x) =
            word 0) /\
          (val(word_sub (intern_slot st (intern_pos st (intern_hash (tisa_fword st 22)
                                                       (tisa_fword st 23)) x)) (word 1)) <
           val(intern_count st)
           ==> ~intern_has st
                 (val(word_sub (intern_slot st (intern_pos st (intern_hash (tisa_fword st 22)
                                                              (tisa_fword st 23)) x)) (word 1)))
                 (tisa_fword st 22) (tisa_fword st 23))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[intern_probed] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A state that agrees with a well-formed one on the count, the slot count,  *)
(* the rows region's length, the rows below the count and the slots is      *)
(* well formed.                                                              *)
(* ------------------------------------------------------------------------- *)

let INTERN_OK_TRANSFER = prove
 (`!s t. intern_ok s /\
         intern_count t = intern_count s /\ intern_slots t = intern_slots s /\
         tisa_len t 0 = tisa_len s 0 /\
         (!i. i < 2 * val(intern_count s) ==> intern_word t i = intern_word s i) /\
         (!p. val p < val(intern_slots s) ==> intern_slot t p = intern_slot s p)
         ==> intern_ok t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[intern_ok] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!h x. intern_pos t h x = intern_pos s h x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[intern_pos]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < val(intern_count s)
                    ==> intern_word t (2 * i) = intern_word s (2 * i) /\
                        intern_word t (2 * i + 1) = intern_word s (2 * i + 1)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!h d. d < val(intern_slots s)
                      ==> intern_slot t (intern_pos s h d) = intern_slot s (intern_pos s h d)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC INTERN_POS_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `intern_complete s`)) THEN
    REWRITE_TAC[intern_complete] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `intern_word`)) (concl th) &&
      not (can (find_term ((=) `intern_slot`)) (concl th)) &&
      can (find_term ((=) `2 * i + 1`)) (concl(SPEC `i:num` th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `e:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `e < val(intern_slots s)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `intern_distinct s`)) THEN
    REWRITE_TAC[intern_distinct; intern_has] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Appending the key at the count, through the first empty slot of its probe *)
(* sequence, keeps the interner well formed.                                 *)
(* ------------------------------------------------------------------------- *)

let INTERN_OK_APPEND =
  let rows_x = `!x. x < val(intern_count s)
                    ==> intern_word t (2 * x) = intern_word s (2 * x) /\
                        intern_word t (2 * x + 1) = intern_word s (2 * x + 1)`
  and no_old = `!i. i < val(intern_count s)
                    ==> ~(intern_word s (2 * i) = tisa_fword s 22 /\
                          intern_word s (2 * i + 1) = tisa_fword s 23)` in
  prove
 (`!s t j.
     intern_ok s /\
     val(intern_count s) < val(tisa_len s 0) DIV 16 /\
     j < val(intern_slots s) /\
     (!x. x < j ==> intern_probed s x) /\
     intern_slot s (intern_pos s (intern_hash (tisa_fword s 22) (tisa_fword s 23)) j) = word 0 /\
     intern_slots t = intern_slots s /\ tisa_len t 0 = tisa_len s 0 /\
     val(intern_count t) = val(intern_count s) + 1 /\
     (!i. i < 2 * val(intern_count s) ==> intern_word t i = intern_word s i) /\
     intern_word t (2 * val(intern_count s)) = tisa_fword s 22 /\
     intern_word t (2 * val(intern_count s) + 1) = tisa_fword s 23 /\
     (!p. val p < val(intern_slots s)
          ==> intern_slot t p =
              if p = intern_pos s (intern_hash (tisa_fword s 22) (tisa_fword s 23)) j
              then word(val(intern_count s) + 1) else intern_slot s p)
     ==> intern_ok t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[intern_ok] o
                check (fun th -> concl th = `intern_ok s`)) THEN
  SUBGOAL_THEN `val(intern_count s) + 1 < 2 EXP 64 /\ 0 < val(intern_slots s)`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `tisa_len s 0` VAL_BOUND_64) THEN TISA_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!h x. intern_pos t h x = intern_pos s h x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[intern_pos]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!h d. d < val(intern_slots s)
          ==> intern_slot t (intern_pos s h d) =
              if intern_pos s h d =
                 intern_pos s (intern_hash (tisa_fword s 22) (tisa_fword s 23)) j
              then word(val(intern_count s) + 1) else intern_slot s (intern_pos s h d)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC INTERN_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(word(val(intern_count s) + 1):int64 = word 0)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTERN_WORD_SUC_NZ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* No row below the count holds the key: its probe chain would have      *)
  (* passed the key's probe j, met the empty slot, or been seen by a probe. *)
  SUBGOAL_THEN no_old ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL [TISA_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[intern_complete] o
                check (fun th -> concl th = `intern_complete s`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (ARITH_RULE `d < j \/ d = j \/ j < d`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `d:num` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `intern_probed`)) (concl th))) THEN
      ASM_REWRITE_TAC[INTERN_PROBED_THM] THEN
      ASM_SIMP_TAC[INTERN_WORD_SUC_PRED; intern_has];
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `d:num = j`)) THEN
      SUBGOAL_THEN `word(i + 1):int64 = word 0` MP_TAC THENL
       [ASM_MESON_TAC[]; ASM_SIMP_TAC[INTERN_WORD_SUC_NZ]];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[intern_ok; intern_complete; intern_distinct; intern_has] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [TISA_ARITH_TAC;
    (* every row is found by probing: old rows at their old distance, the  *)
    (* new row at the key's probe j                                          *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < val(intern_count s) \/ i = val(intern_count s)` STRIP_ASSUME_TAC THENL
     [TISA_ARITH_TAC;
      SUBGOAL_THEN `intern_word t (2 * i) = intern_word s (2 * i) /\
                    intern_word t (2 * i + 1) = intern_word s (2 * i + 1)`
       (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN TISA_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL [TISA_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[intern_complete] o
                  check (fun th -> concl th = `intern_complete s`)) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `d:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [COND_CASES_TAC THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `word(i + 1):int64 = word 0` MP_TAC THENL
         [FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
                                     can (find_term ((=) `d:num`)) (lhand(concl th)) &&
                                     not(is_forall(concl th)) &&
                                     type_of(lhand(concl th)) = `:int64`
                                  then SUBST_ALL_TAC th else NO_TAC) THEN
          ASM_MESON_TAC[];
          ASM_SIMP_TAC[INTERN_WORD_SUC_NZ]];
        X_GEN_TAC `e:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `e < val(intern_slots s)` ASSUME_TAC THENL
         [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]];
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `i = val(intern_count s)`)) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `j:num` THEN ASM_SIMP_TAC[] THEN
      X_GEN_TAC `e:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `e < val(intern_slots s)` ASSUME_TAC THENL
       [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:num` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `intern_probed`)) (concl th))) THEN
      ASM_SIMP_TAC[INTERN_PROBED_THM]];
    (* no two rows hold one key *)
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN rows_x ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN TISA_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(a < val(intern_count s) \/ a = val(intern_count s)) /\
                  (b < val(intern_count s) \/ b = val(intern_count s))`
     MP_TAC THENL [CONJ_TAC THEN TISA_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC DISJ_CASES_TAC) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      is_var(lhand(concl th)) && rand(concl th) = `val(intern_count s)`))) THEN
    REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[intern_distinct; intern_has] o
                    check (fun th -> concl th = `intern_distinct s`)) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(MP (SPEC `a:num` (ASSUME rows_x)) (ASSUME `a < val(intern_count s)`)) THEN
      MP_TAC(MP (SPEC `b:num` (ASSUME rows_x)) (ASSUME `b < val(intern_count s)`)) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN (fun th -> REWRITE_TAC[GSYM th]))) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPEC `a:num` (ASSUME rows_x)) THEN MP_TAC(SPEC `a:num` (ASSUME no_old)) THEN
      MP_TAC(ASSUME `intern_word t (2 * a) = intern_word t (2 * val(intern_count s))`) THEN
      MP_TAC(ASSUME `intern_word t (2 * a + 1) = intern_word t (2 * val(intern_count s) + 1)`) THEN
      MP_TAC(ASSUME `intern_word t (2 * val(intern_count s)) = tisa_fword s 22`) THEN
      MP_TAC(ASSUME `intern_word t (2 * val(intern_count s) + 1) = tisa_fword s 23`) THEN
      MP_TAC(ASSUME `a < val(intern_count s)`) THEN MESON_TAC[];
      MP_TAC(SPEC `b:num` (ASSUME rows_x)) THEN MP_TAC(SPEC `b:num` (ASSUME no_old)) THEN
      MP_TAC(ASSUME `intern_word t (2 * val(intern_count s)) = intern_word t (2 * b)`) THEN
      MP_TAC(ASSUME `intern_word t (2 * val(intern_count s) + 1) = intern_word t (2 * b + 1)`) THEN
      MP_TAC(ASSUME `intern_word t (2 * val(intern_count s)) = tisa_fword s 22`) THEN
      MP_TAC(ASSUME `intern_word t (2 * val(intern_count s) + 1) = tisa_fword s 23`) THEN
      MP_TAC(ASSUME `b < val(intern_count s)`) THEN MESON_TAC[]]]);;


(* ------------------------------------------------------------------------- *)
(* The loop body under the invariant: a probe that continues keeps the       *)
(* invariant one probe further; every stop leaves a well-formed interner,    *)
(* and a FIRED stop satisfies intern16_post.                                 *)
(* ------------------------------------------------------------------------- *)

let INTERN16_REGION_FACTS = prove
 (`!st. intern16_regions st
        ==> val(tregs st 0) + 192 <= 2 EXP 64 /\
            val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64 /\
            val(tisa_base st 1) + val(tisa_len st 1) < 2 EXP 64 /\
            val(tisa_base st 2) + val(tisa_len st 2) < 2 EXP 64 /\
            (val(tisa_base st 0) + val(tisa_len st 0) <= val(tregs st 0) \/
             val(tregs st 0) + 192 <= val(tisa_base st 0)) /\
            (val(tisa_base st 1) + val(tisa_len st 1) <= val(tregs st 0) \/
             val(tregs st 0) + 192 <= val(tisa_base st 1)) /\
            (val(tisa_base st 2) + val(tisa_len st 2) <= val(tregs st 0) \/
             val(tregs st 0) + 192 <= val(tisa_base st 2)) /\
            16 <= val(tisa_len st 0) /\ 8 <= val(tisa_len st 1) /\ 8 <= val(tisa_len st 2) /\
            (val(tisa_base st 0) + val(tisa_len st 0) <= val(tisa_base st 1) \/
             val(tisa_base st 1) + val(tisa_len st 1) <= val(tisa_base st 0)) /\
            (val(tisa_base st 0) + val(tisa_len st 0) <= val(tisa_base st 2) \/
             val(tisa_base st 2) + val(tisa_len st 2) <= val(tisa_base st 0)) /\
            (val(tisa_base st 1) + val(tisa_len st 1) <= val(tisa_base st 2) \/
             val(tisa_base st 2) + val(tisa_len st 2) <= val(tisa_base st 1)) /\
            val(intern_count st) <= val(tisa_len st 0) DIV 16`,
  GEN_TAC THEN REWRITE_TAC[intern16_regions] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if length(fst(strip_forall(concl th))) = 2
     then MP_TAC(SPECL [`0`;`1`] th) THEN MP_TAC(SPECL [`0`;`2`] th) THEN
          MP_TAC(SPECL [`1`;`2`] th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN ASM_REWRITE_TAC[]);;

let INTERN_SLOTS_VAL = prove
 (`!st. val(intern_slots st) = val(tisa_len st 1) DIV 8`,
  REWRITE_TAC[intern_slots; VAL_WORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV);;

let INTERN16_PROBED_STEP = prove
 (`!st j. (!x. x < j ==> intern_probed st x) /\ intern_probed st j
          ==> !x. x < j + 1 ==> intern_probed st x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:num = j` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* The body's goal with the invariant unfolded, the region facts and the    *)
(* slot count as arithmetic, and the loop state's view as the entry state's. *)
let INTERN16_BODY_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [intern16_inv] o
                check (fun th -> tisa_has_tm `intern16_inv` th)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = val(intern_slots st)`)) THEN
  MP_TAC(ISPECL [`s0:tisa_state`; `st:tisa_state`] TISA_SAME_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INTERN16_REGION_FACTS) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASSUME_TAC(SPEC `st:tisa_state` INTERN_SLOTS_VAL);;

(* val (word_shl x 1) = 2 * val x for the shifted row ids in the goal and the *)
(* assumptions, where arithmetic shows the id is below 2^63.                  *)
let INTERN16_SHL_TAC : tactic = fun (asl,w) ->
  let shl_tm = `word_shl:int64->num->int64` in
  let is_shl1 t = is_comb t && is_comb(rator t) && rator(rator t) = shl_tm && rand t = `1` in
  let ts = setify (itlist (fun (_,th) acc -> find_terms is_shl1 (concl th) @ acc) asl
                          (find_terms is_shl1 w)) in
  MAP_EVERY (fun t ->
    let x = rand(rator t) in
    TRY(SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,t), mk_binop `( * ):num->num->num` `2` (mk_comb(`val:int64->num`,x))))
          (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
         [MATCH_MP_TAC TISA_VAL_SHL1 THEN TISA_ARITH_TAC; ALL_TAC])) ts (asl,w);;

(* The continuing leaves: the invariant one probe further. *)
let INTERN16_CONT_TAC =
  REWRITE_TAC[intern16_inv] THEN TISA_STATE_NORM_TAC THEN
  MATCH_MP_TAC INTERN16_PROBED_STEP THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INTERN_PROBED_THM; intern_slot; intern_pos; intern_has; intern_word] THEN
  INTERN16_SHL_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * (2 * x + 1) = 8 * (2 * x) + 8`] THEN
  ASM_REWRITE_TAC[];;

(* Unfold the interner's view of a later state (not the entry state). *)
let INTERN16_UNFOLD_LATER_CONV =
  let defs = [`intern_count`, intern_count; `intern_slots`, intern_slots;
              `intern_word`, intern_word; `intern_slot`, intern_slot] in
  fun t -> let h,args = strip_comb t in
    match args with
      s::_ when not(is_var s) && can (assoc h) defs -> REWR_CONV (assoc h defs) t
    | _ -> failwith "INTERN16_UNFOLD_LATER_CONV";;

(* A view equality of a later state: unfold the later state's view, read it *)
(* through the finish and the stores, then compare.                          *)
let INTERN16_VIEW_TAC =
  CONV_TAC(TOP_DEPTH_CONV INTERN16_UNFOLD_LATER_CONV) THEN TISA_STATE_NORM_TAC THEN
  TRY(REWRITE_TAC[intern_count; intern_slots; intern_word; intern_slot] THEN NO_TAC) THEN
  TRY(TISA_ARITH_DECIDE_TAC);;

(* intern_ok of a state that shows the entry state's view. *)
let INTERN16_SAME_OK_TAC =
  MATCH_MP_TAC INTERN_OK_TRANSFER THEN EXISTS_TAC `st:tisa_state` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN INTERN16_VIEW_TAC;;

(* The found leaf: the run wrote only the finish; the id's row is the key. *)
let INTERN16_FOUND_LEAF_TAC =
  TISA_STATE_NORM_TAC THEN INTERN16_SHL_TAC THEN CONJ_TAC THENL
   [INTERN16_SAME_OK_TAC;
    REWRITE_TAC[intern16_post] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV INTERN16_UNFOLD_LATER_CONV) THEN TISA_STATE_NORM_TAC THEN
    REWRITE_TAC[GSYM intern_count] THEN
    REWRITE_TAC[intern_word; ARITH_RULE `8 * (2 * x + 1) = 8 * (2 * x) + 8`] THEN
    ASM_REWRITE_TAC[]];;

(* The append leaf: the new state is well formed by INTERN_OK_APPEND, its   *)
(* view read through the finish and the four stores; the slot written is    *)
(* the key's probe j, and every other slot is unchanged.                    *)
let INTERN16_SLOT_CASES_TAC =
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
                                                   type_of(lhand(concl th)) = `:int64`)) THEN
    INTERN16_VIEW_TAC THEN REWRITE_TAC[TISA_WORD_ADD_VAL];
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM VAL_EQ] o check (fun th ->
      is_neg(concl th) && is_eq(dest_neg(concl th)) && is_var(lhand(dest_neg(concl th))) &&
      type_of(lhand(dest_neg(concl th))) = `:int64`)) THEN
    INTERN16_VIEW_TAC];;

let INTERN16_APPEND_LEAF_TAC =
  TISA_STATE_NORM_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTERN_OK_APPEND THEN MAP_EVERY EXISTS_TAC [`st:tisa_state`; `j:num`] THEN
    ASM_REWRITE_TAC[intern_slot; intern_pos] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
    (fun (asl,w) -> if is_eq w && is_cond(rand w) then INTERN16_SLOT_CASES_TAC (asl,w)
                    else INTERN16_VIEW_TAC (asl,w));
    REWRITE_TAC[intern16_post] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
    INTERN16_VIEW_TAC];;

let INTERN16_LEAF_TAC : tactic = fun (asl,w) ->
  if fst(strip_comb w) = `intern16_inv` then INTERN16_CONT_TAC (asl,w)
  else if can (find_term ((=) `tisa_store`)) w then INTERN16_APPEND_LEAF_TAC (asl,w)
  else if can (find_term ((=) `tisa_finst 1`)) w then INTERN16_FOUND_LEAF_TAC (asl,w)
  else (TISA_STATE_NORM_TAC THEN INTERN16_SAME_OK_TAC) (asl,w);;

let INTERN16_BODY_WP = prove
 (`!st N j s0.
     intern16_regions st /\ intern_ok st /\ j < N /\ intern16_inv st N j s0
     ==> tisa_wp intern16_body (intern16_inv st N (j + 1))
           (\k s. intern_ok s /\ (k = 1 ==> intern16_post st s))
           (tisa_setreg 7 (word j) s0)`,
  INTERN16_BODY_SETUP_TAC THEN REWRITE_TAC[intern16_body] THEN TISA_VCG_TAC THEN
  INTERN16_LEAF_TAC);;

(* ------------------------------------------------------------------------- *)
(* The prologue establishes the loop invariant with no probes made; its one  *)
(* stop (rows over capacity) cannot happen in a well-formed interner.        *)
(* ------------------------------------------------------------------------- *)

let INTERN16_PROLOGUE_WP = prove
 (`!st. intern16_regions st
        ==> tisa_wp intern16_prologue
              (\s. intern16_inv st (val(intern_slots st)) 0 s)
              (\k s. intern_ok s /\ (k = 1 ==> intern16_post st s)) st`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INTERN16_REGION_FACTS) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[intern_count] o
              check (fun th -> concl th = `val(intern_count st) <= val(tisa_len st 0) DIV 16`)) THEN
  REWRITE_TAC[intern16_prologue] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[intern16_inv; intern_count; intern_slots; intern_hash] THEN
  TISA_STATE_NORM_TAC THEN REWRITE_TAC[LT]);;

(* ------------------------------------------------------------------------- *)
(* A stop that wrote only the finish keeps the interner well formed.         *)
(* ------------------------------------------------------------------------- *)

let TISA_FAILST_FINST = prove
 (`!k st. tisa_failst k st = tisa_finst k (word k) st`,
  REWRITE_TAC[tisa_failst; tisa_finst]);;

(* For a state s with the entry state's frame register and memory: the     *)
(* region facts and the view of s as the entry state's.                     *)
let INTERN16_SAME_STATE_SETUP_TAC s =
  FIRST_ASSUM(MP_TAC o MATCH_MP INTERN16_REGION_FACTS o
              check (fun th -> concl th = `intern16_regions st`)) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASSUME_TAC(SPEC `st:tisa_state` INTERN_SLOTS_VAL) THEN
  MP_TAC(ISPECL [s; `st:tisa_state`] TISA_SAME_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC];;

(* ------------------------------------------------------------------------- *)
(* The whole program: from a well-formed interner, every stop leaves a       *)
(* well-formed interner, and a FIRED stop satisfies intern16_post. No run    *)
(* continues past the final RETURN.                                          *)
(* ------------------------------------------------------------------------- *)

let INTERN16_ROOT_WP = prove
 (`!st. tisa_entry_ok intern16 st /\ intern_ok st
        ==> tisa_wp (tisa_root intern16) (\s. F)
              (\k s. intern_ok s /\ (k = 1 ==> intern16_post st s)) st`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `intern16_regions st` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP INTERN16_ENTRY) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[intern_ok]) THEN
    REWRITE_TAC[intern16_regions] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[intern16; tisa_root; TISA_WP_SEQ] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  EXISTS_TAC `\s. intern16_inv st (val(intern_slots st)) 0 s` THEN
  EXISTS_TAC `\k s. intern_ok s /\ (k = 1 ==> intern16_post st s)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC INTERN16_PROLOGUE_WP THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `s:tisa_state` THEN DISCH_TAC THEN
  MATCH_MP_TAC TISA_WP_COUNT_LOOP THEN EXISTS_TAC `intern16_inv st` THEN
  REPEAT CONJ_TAC THENL
   [(* more slots than the loop's cap: UNSUPPORTED, memory unchanged *)
    DISCH_TAC THEN REWRITE_TAC[TISA_FAILST_FINST] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [intern16_inv] o
                  check (fun th -> tisa_has_tm `intern16_inv` th)) THEN
    INTERN16_SAME_STATE_SETUP_TAC `s:tisa_state` THEN
    TISA_STATE_NORM_TAC THEN INTERN16_SAME_OK_TAC;
    (* the loop starts with the invariant the prologue left *)
    DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [intern16_inv] o
                check (fun th -> tisa_has_tm `intern16_inv` th)) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERN16_BODY_WP THEN ASM_REWRITE_TAC[];
    (* every slot probed: UNSUPPORTED, memory unchanged *)
    MAP_EVERY X_GEN_TAC [`N:num`; `s1:tisa_state`] THEN DISCH_TAC THEN
    REWRITE_TAC[TISA_WP_RETURN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [intern16_inv] o
                  check (fun th -> concl th = `intern16_inv st N N s1`)) THEN
    INTERN16_SAME_STATE_SETUP_TAC `s1:tisa_state` THEN
    TISA_STATE_NORM_TAC THEN INTERN16_SAME_OK_TAC]);;

let INTERN16_RUN_COMPLETE = prove
 (`!st k st'. tisa_entry_ok intern16 st /\ intern_ok st /\
              tisa_exec (tisa_root intern16) st = TStop k st'
              ==> intern_ok st' /\ (k = 1 ==> intern16_post st st')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `st:tisa_state` INTERN16_ROOT_WP) THEN
  ASM_REWRITE_TAC[tisa_wp; TISA_RWP_STOP]);;

(* A FIRED run that appended: no row below the old count held the key, so   *)
(* equal keys always get equal ids.                                          *)
let INTERN16_APPEND_ABSENT = prove
 (`!st st'. tisa_entry_ok intern16 st /\ intern_ok st /\
            tisa_exec (tisa_root intern16) st = TStop 1 st' /\
            val(tisa_fword st' 19) = val(intern_count st)
            ==> !i. i < val(intern_count st)
                    ==> ~intern_has st i (tisa_fword st 22) (tisa_fword st 23)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `1`; `st':tisa_state`] INTERN16_RUN_COMPLETE) THEN
  ASM_REWRITE_TAC[intern_ok; intern_distinct; intern16_post] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[intern_has] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `val(intern_count st)`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
  REWRITE_TAC[intern_has] THEN
  SUBGOAL_THEN `intern_word st' (2 * i) = intern_word st (2 * i) /\
                intern_word st' (2 * i + 1) = intern_word st (2 * i + 1)`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `i < val(intern_count st)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `i < val(intern_count st)` THEN
  UNDISCH_TAC `val (intern_count st) < val (intern_count st')` THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The same over tisa_run, the run that the x86 image theorem speaks of.     *)
(* ------------------------------------------------------------------------- *)

let INTERN16_TISA_RUN_COMPLETE = prove
 (`!st k st'. tisa_entry_ok intern16 st /\ intern_ok st /\
              tisa_run intern16 st = TStop k st'
              ==> intern_ok st' /\ (k = 1 ==> intern16_post st st')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `st:tisa_state` INTERN16_ROOT_WP) THEN ASM_REWRITE_TAC[tisa_wp] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> tisa_has_tm `tisa_run` th)) THEN
  ASM_REWRITE_TAC[tisa_run] THEN
  MP_TAC(ISPEC `tisa_exec (tisa_root intern16) st` TISA_RESULT_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC)
     (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC))) THEN
  REWRITE_TAC[tisa_then; TISA_RWP_CONT; TISA_RWP_STOP; TISA_RESULT_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN REWRITE_TAC[]);;

let INTERN16_TISA_RUN_APPEND_ABSENT = prove
 (`!st st'. tisa_entry_ok intern16 st /\ intern_ok st /\
            tisa_run intern16 st = TStop 1 st' /\
            val(tisa_fword st' 19) = val(intern_count st)
            ==> !i. i < val(intern_count st)
                    ==> ~intern_has st i (tisa_fword st 22) (tisa_fword st 23)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC INTERN16_APPEND_ABSENT THEN
  EXISTS_TAC `st':tisa_state` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> tisa_has_tm `tisa_run` th)) THEN
  ASM_REWRITE_TAC[tisa_run] THEN
  MP_TAC(ISPEC `tisa_exec (tisa_root intern16) st` TISA_RESULT_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC)
     (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC))) THEN
  REWRITE_TAC[tisa_then; TISA_FAIL_STOP; TISA_RESULT_INJ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN REWRITE_TAC[]);;
