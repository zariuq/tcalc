(* ========================================================================= *)
(* Joining template theorems into statement theorems.                        *)
(*                                                                           *)
(* tisa_x86_runs mc pc o e epi P Q S C: from any native state at pc + o that *)
(* realizes a t-ISA state with the facts P, the code of statement S ends     *)
(* either at pc + e realizing its continued state, which has the facts Q, or *)
(* at the epilogue with its stopped state's memory and return value; it      *)
(* changes at most C and keeps the image loaded. The facts are the program   *)
(* point's: region bounds, pointer and Boolean registers. A statement whose  *)
(* every path returns has Q = F: it cannot continue.                         *)
(* ========================================================================= *)

needs "tisa/hol/tisa_x86_rel.ml";;

let tisa_x86_postf = define
 `(tisa_x86_postf next epi (Q:tisa_state->bool) (TCont t) s <=>
     read RIP s = word next /\ tisa_x86_rel t s /\ Q t) /\
  (tisa_x86_postf next epi Q (TStop k t) s <=>
     read RIP s = word epi /\ read memory s = tmem t /\ read RAX s = tisa_fword t 19)`;;

let tisa_x86_runs = new_definition
 `tisa_x86_runs (mc:byte list) pc off e epi (P:tisa_state->bool) Q S C <=>
    !t. P t ==>
        ensures x86
         (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + off) /\ tisa_x86_rel t s)
         (\s. bytes_loaded s (word pc) mc /\
              tisa_x86_postf (pc + e) (pc + epi) Q (tisa_exec S t) s)
         C`;;

let tisa_result_CASES = prove_cases_thm tisa_result_INDUCT;;

(* ------------------------------------------------------------------------- *)
(* Sequence.                                                                 *)
(* ------------------------------------------------------------------------- *)

let TISA_SEQ_RUNS = prove
 (`!mc pc oa ob oe epi P Q R a b C.
        C ,, C = C /\
        tisa_x86_runs mc pc oa ob epi P Q a C /\
        tisa_x86_runs mc pc ob oe epi Q R b C
        ==> tisa_x86_runs mc pc oa oe epi P R (TSeq a b) C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_x86_runs] THEN STRIP_TAC THEN
  X_GEN_TAC `t:tisa_state` THEN DISCH_TAC THEN REWRITE_TAC[tisa_exec] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(P:tisa_state->bool) t`) o SPEC `t:tisa_state`) THEN
  STRUCT_CASES_TAC(ISPEC `tisa_exec a t` tisa_result_CASES) THEN REWRITE_TAC[tisa_then] THEN
  DISCH_TAC THENL
   [ASM_CASES_TAC `(Q:tisa_state->bool) a'` THENL
     [MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
      EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ob) /\
                      tisa_x86_rel a' s` THEN
      ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                      tisa_x86_postf (pc + ob) (pc + epi) Q (TCont a') s` THEN
      ASM_REWRITE_TAC[tisa_x86_postf] THEN MESON_TAC[];
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                      tisa_x86_postf (pc + ob) (pc + epi) Q (TCont a') s` THEN
      ASM_REWRITE_TAC[tisa_x86_postf]];
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                    tisa_x86_postf (pc + ob) (pc + epi) Q (TStop a0 a1) s` THEN
    ASM_REWRITE_TAC[tisa_x86_postf]]);;

(* ------------------------------------------------------------------------- *)
(* The two pieces of code IF adds: its test, and the jump over the else.    *)
(* ------------------------------------------------------------------------- *)

(* test c,c; je else: Boolean c chooses the branch. *)
let tisa_x86_test = new_definition
 `tisa_x86_test (mc:byte list) pc off c othen oelse C <=>
    !t. tisa_bool (tregs t c) ==>
        ensures x86
         (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + off) /\ tisa_x86_rel t s)
         (\s. bytes_loaded s (word pc) mc /\ tisa_x86_rel t s /\
              read RIP s = word(pc + (if tregs t c = word 0 then oelse else othen)))
         C`;;

let tisa_x86_jump = new_definition
 `tisa_x86_jump (mc:byte list) pc off e C <=>
    !t. ensures x86
         (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + off) /\ tisa_x86_rel t s)
         (\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + e) /\ tisa_x86_rel t s)
         C`;;

(* A statement whose code continues with a jump. *)
let TISA_RUNS_JUMP = prove
 (`!mc pc off e1 e2 epi P Q S C.
        C ,, C = C /\
        tisa_x86_runs mc pc off e1 epi P Q S C /\
        tisa_x86_jump mc pc e1 e2 C
        ==> tisa_x86_runs mc pc off e2 epi P Q S C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_x86_runs; tisa_x86_jump] THEN STRIP_TAC THEN
  X_GEN_TAC `t:tisa_state` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(P:tisa_state->bool) t`) o SPEC `t:tisa_state`) THEN
  STRUCT_CASES_TAC(ISPEC `tisa_exec S t` tisa_result_CASES) THEN DISCH_TAC THENL
   [ASM_CASES_TAC `(Q:tisa_state->bool) a` THENL
     [MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
      EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + e1) /\
                      tisa_x86_rel a s` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
        EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                        tisa_x86_postf (pc + e1) (pc + epi) Q (TCont a) s` THEN
        ASM_REWRITE_TAC[tisa_x86_postf] THEN MESON_TAC[];
        MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
        EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + e2) /\
                        tisa_x86_rel a s` THEN
        ASM_REWRITE_TAC[tisa_x86_postf] THEN MESON_TAC[]];
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                      tisa_x86_postf (pc + e1) (pc + epi) Q (TCont a) s` THEN
      ASM_REWRITE_TAC[tisa_x86_postf]];
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\
                    tisa_x86_postf (pc + e1) (pc + epi) Q (TStop a0 a1) s` THEN
    ASM_REWRITE_TAC[tisa_x86_postf]]);;

(* IF c a b: test at oi, then-branch at ot, else-branch at ol (an empty else
   is TSkip at oe), both ending at oe; the generator extends the then-branch
   by its jump over the else. *)
let TISA_IF_RUNS = prove
 (`!mc pc oi ot ol oe epi c P Pa Pb Q a b C.
        C ,, C = C /\
        (!t. P t ==> tisa_bool (tregs t c)) /\
        (!t. P t /\ ~(tregs t c = word 0) ==> Pa t) /\
        (!t. P t /\ tregs t c = word 0 ==> Pb t) /\
        tisa_x86_test mc pc oi c ot ol C /\
        tisa_x86_runs mc pc ot oe epi Pa Q a C /\
        tisa_x86_runs mc pc ol oe epi Pb Q b C
        ==> tisa_x86_runs mc pc oi oe epi P Q (TIf c a b) C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_x86_runs; tisa_x86_test] THEN STRIP_TAC THEN
  X_GEN_TAC `t:tisa_state` THEN DISCH_TAC THEN
  SUBGOAL_THEN `tisa_bool (tregs t c)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[tisa_exec] THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ tisa_x86_rel t s /\
                  read RIP s = word(pc + (if tregs t c = word 0 then ol else ot))` THEN
  ASM_SIMP_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ENSURES_PRECONDITION_THM THENL
   [EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ol) /\ tisa_x86_rel t s` THEN
    CONJ_TAC THENL [MESON_TAC[]; ASM_MESON_TAC[]];
    EXISTS_TAC `\s. bytes_loaded s (word pc) mc /\ read RIP s = word(pc + ot) /\ tisa_x86_rel t s` THEN
    CONJ_TAC THENL [MESON_TAC[]; ASM_MESON_TAC[]]]);;

(* The empty statement: no code, and the facts carry over. *)
let TISA_SKIP_RUNS = prove
 (`!mc pc off epi P Q C.
        (!s. C s s) /\ (!t. P t ==> Q t)
        ==> tisa_x86_runs mc pc off off epi P Q TSkip C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tisa_x86_runs; tisa_exec; tisa_x86_postf] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ensures] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ1_TAC THEN ASM_MESON_TAC[]);;
