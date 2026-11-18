(* ========================================================================= *)
(* intern16 that does not fire keeps the table: its count and every word of *)
(* a row below it (INTERN16_TISA_RUN_KEPT). Every stop other than FIRED     *)
(* comes before any store (the capacity check, the loop's cap, every slot    *)
(* probed), so the interner's own VCG, rerun with the stronger post, proves *)
(* it with the same leaf tactics.                                            *)
(*                                                                           *)
(* Loaded after intern16_complete.ml.                                        *)
(* ========================================================================= *)

needs "native/hol/intern16_complete.ml";;

let intern16_kept = new_definition
 `intern16_kept st0 s <=>
    intern_count s = intern_count st0 /\
    (!i. i < 2 * val(intern_count st0) ==> intern_word s i = intern_word st0 i)`;;

let INTERN16_KEPT_TAC =
  REWRITE_TAC[intern16_kept] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN INTERN16_VIEW_TAC;;

let INTERN16_KEPT_LEAF_TAC : tactic = fun (asl,w) ->
  if fst(strip_comb w) = `intern16_inv` then INTERN16_CONT_TAC (asl,w)
  else if can (find_term ((=) `tisa_store`)) w then INTERN16_APPEND_LEAF_TAC (asl,w)
  else if can (find_term ((=) `tisa_finst 1`)) w then INTERN16_FOUND_LEAF_TAC (asl,w)
  else (TISA_STATE_NORM_TAC THEN CONJ_TAC THENL [INTERN16_SAME_OK_TAC; INTERN16_KEPT_TAC]) (asl,w);;

let INTERN16_KEPT_BODY_WP = prove
 (`!st N j s0.
     intern16_regions st /\ intern_ok st /\ j < N /\ intern16_inv st N j s0
     ==> tisa_wp intern16_body (intern16_inv st N (j + 1))
           (\k s. intern_ok s /\ (k = 1 ==> intern16_post st s) /\ (~(k = 1) ==> intern16_kept st s))
           (tisa_setreg 7 (word j) s0)`,
  INTERN16_BODY_SETUP_TAC THEN REWRITE_TAC[intern16_body] THEN TISA_VCG_TAC THEN
  INTERN16_KEPT_LEAF_TAC);;

let INTERN16_KEPT_PROLOGUE_WP = prove
 (`!st. intern16_regions st
        ==> tisa_wp intern16_prologue
              (\s. intern16_inv st (val(intern_slots st)) 0 s)
              (\k s. intern_ok s /\ (k = 1 ==> intern16_post st s) /\ (~(k = 1) ==> intern16_kept st s)) st`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INTERN16_REGION_FACTS) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[intern_count] o
              check (fun th -> concl th = `val(intern_count st) <= val(tisa_len st 0) DIV 16`)) THEN
  REWRITE_TAC[intern16_prologue] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[intern16_inv; intern_count; intern_slots; intern_hash] THEN
  TISA_STATE_NORM_TAC THEN REWRITE_TAC[LT]);;

let INTERN16_KEPT_ROOT_WP = prove
 (`!st. tisa_entry_ok intern16 st /\ intern_ok st
        ==> tisa_wp (tisa_root intern16) (\s. F)
              (\k s. intern_ok s /\ (k = 1 ==> intern16_post st s) /\ (~(k = 1) ==> intern16_kept st s)) st`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `intern16_regions st` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP INTERN16_ENTRY) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[intern_ok]) THEN
    REWRITE_TAC[intern16_regions] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[intern16; tisa_root; TISA_WP_SEQ] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  EXISTS_TAC `\s. intern16_inv st (val(intern_slots st)) 0 s` THEN
  EXISTS_TAC `\k s. intern_ok s /\ (k = 1 ==> intern16_post st s) /\ (~(k = 1) ==> intern16_kept st s)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC INTERN16_KEPT_PROLOGUE_WP THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `s:tisa_state` THEN DISCH_TAC THEN
  MATCH_MP_TAC TISA_WP_COUNT_LOOP THEN EXISTS_TAC `intern16_inv st` THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[TISA_FAILST_FINST] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [intern16_inv] o
                  check (fun th -> tisa_has_tm `intern16_inv` th)) THEN
    INTERN16_SAME_STATE_SETUP_TAC `s:tisa_state` THEN
    TISA_STATE_NORM_TAC THEN CONJ_TAC THENL [INTERN16_SAME_OK_TAC; INTERN16_KEPT_TAC];
    DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [intern16_inv] o
                check (fun th -> tisa_has_tm `intern16_inv` th)) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERN16_KEPT_BODY_WP THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`N:num`; `s1:tisa_state`] THEN DISCH_TAC THEN
    REWRITE_TAC[TISA_WP_RETURN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [intern16_inv] o
                  check (fun th -> concl th = `intern16_inv st N N s1`)) THEN
    INTERN16_SAME_STATE_SETUP_TAC `s1:tisa_state` THEN
    TISA_STATE_NORM_TAC THEN CONJ_TAC THENL [INTERN16_SAME_OK_TAC; INTERN16_KEPT_TAC]]);;

let INTERN16_TISA_RUN_KEPT = prove
 (`!st k st'. tisa_entry_ok intern16 st /\ intern_ok st /\
              tisa_run intern16 st = TStop k st'
              ==> intern_ok st' /\ (k = 1 ==> intern16_post st st') /\ (~(k = 1) ==> intern16_kept st st')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `st:tisa_state` INTERN16_KEPT_ROOT_WP) THEN ASM_REWRITE_TAC[tisa_wp] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> tisa_has_tm `tisa_run` th)) THEN
  ASM_REWRITE_TAC[tisa_run] THEN
  MP_TAC(ISPEC `tisa_exec (tisa_root intern16) st` TISA_RESULT_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC)
     (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC))) THEN
  REWRITE_TAC[tisa_then; TISA_RWP_CONT; TISA_RWP_STOP; TISA_RESULT_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN REWRITE_TAC[]);;

(* Every theorem this file states, for the audits. *)
let intern16_kept_theorems =
 ["INTERN16_KEPT_BODY_WP", INTERN16_KEPT_BODY_WP;
  "INTERN16_KEPT_PROLOGUE_WP", INTERN16_KEPT_PROLOGUE_WP;
  "INTERN16_KEPT_ROOT_WP", INTERN16_KEPT_ROOT_WP;
  "INTERN16_TISA_RUN_KEPT", INTERN16_TISA_RUN_KEPT];;
