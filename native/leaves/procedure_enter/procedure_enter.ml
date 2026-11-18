(* Capacity and one fuel unit for a procedure activation. *)
needs "native/leaves/common/leaf_lib.ml";;
needs "native/hol/tisa_wp_fund.ml";;
needs "native/leaves/procedure_enter/procedure_enter_program.ml";;

let PROCEDURE_ENTER_DECLS = prove
 (`tisa_decls procedure_enter = []`,REWRITE_TAC[PROCEDURE_ENTER_TERM;tisa_decls]);;
let PROCEDURE_ENTER_LEAF_WF = prove
 (`tisa_leaf_wf procedure_enter`,LEAF_WF_TAC PROCEDURE_ENTER_DECLS PROCEDURE_ENTER_TERM);;

let procedure_enter_post = new_definition
 `procedure_enter_post t k u <=>
    tisa_fword u 18 = word k /\
    tisa_fword u 20 = tisa_fword t 20 /\
    (if val(tisa_fword t 22) < val(tisa_fword t 23)
     then if val(word_sub (tisa_fword t 20) (tisa_fword t 21)) < 1
          then k = 4 /\ tisa_fword u 19 = word 4 /\
               tisa_fword u 21 = tisa_fword t 21
          else k = 1 /\ tisa_fword u 19 = word_add (tisa_fword t 22) (word 1) /\
               tisa_fword u 21 = word_add (tisa_fword t 21) (word 1)
     else k = 2 /\ tisa_fword u 19 = word 0 /\
          tisa_fword u 21 = tisa_fword t 21)`;;

let PROCEDURE_ENTER_WP = prove
 (`!t. tisa_entry_ok procedure_enter t
       ==> tisa_wp (tisa_root procedure_enter) (\s. F) (procedure_enter_post t) t`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP LEAF_ENTRY_FRAME) THEN
  REWRITE_TAC[PROCEDURE_ENTER_TERM;tisa_root] THEN
  TISA_FUND_VCG_TAC THEN REWRITE_TAC[procedure_enter_post] THEN
  REWRITE_TAC[TISA_FAILST_FINST;TISA_TREGS_SETFWORD] THEN
  TISA_STATE_NORM_TAC THEN
  ASM_SIMP_TAC[TISA_FWORD_SETFWORD;TISA_TREGS_SETFWORD;
               TISA_TREGS_SETREG;ARITH_EQ] THEN
  TISA_STATE_NORM_TAC THEN LEAF_VAL_NUMERALS_TAC THEN
  ASM_SIMP_TAC[TISA_FWORD_FINST;TISA_TREGS_SETFWORD;TISA_TREGS_SETREG;
               TISA_FWORD_SETFWORD;TISA_FWORD_SETREG;ARITH_EQ;
               ARITH_RULE `18 < 24 /\ 19 < 24 /\ 20 < 24 /\ 21 < 24`]);;

let PROCEDURE_ENTER_RUN = prove
 (`!t k u. tisa_entry_ok procedure_enter t /\ tisa_run procedure_enter t = TStop k u
       ==> procedure_enter_post t k u`,
  MESON_TAC[PROCEDURE_ENTER_WP;LEAF_RUN_BY_WP]);;

let PROCEDURE_ENTER_RECEIPT_VALID = prove
 (`!t. tisa_entry_ok procedure_enter t
       ==> val(tisa_fword t 21) <= val(tisa_fword t 20)`,
  REWRITE_TAC[PROCEDURE_ENTER_TERM;tisa_entry_ok] THEN MESON_TAC[]);;

let PROCEDURE_ENTER_FUEL_ROOM = prove
 (`!budget used:int64. val used <= val budget
       ==> (val(word_sub budget used) < 1 <=> val used = val budget) /\
           (~(val(word_sub budget used) < 1) <=> val used < val budget)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[VAL_WORD_SUB_CASES] THEN
  ASM_ARITH_TAC);;

let PROCEDURE_ENTER_OUTCOMES = prove
 (`!t k u. tisa_entry_ok procedure_enter t /\ tisa_run procedure_enter t = TStop k u
       ==> (k = 1 <=> val(tisa_fword t 22) < val(tisa_fword t 23) /\
                      val(tisa_fword t 21) < val(tisa_fword t 20)) /\
           (k = 2 <=> ~(val(tisa_fword t 22) < val(tisa_fword t 23))) /\
           (k = 4 <=> val(tisa_fword t 22) < val(tisa_fword t 23) /\
                      val(tisa_fword t 21) = val(tisa_fword t 20)) /\
           (k = 1 ==> val(tisa_fword u 19) = val(tisa_fword t 22) + 1 /\
                      val(tisa_fword u 21) = val(tisa_fword t 21) + 1) /\
           (~(k = 1) ==> tisa_fword u 21 = tisa_fword t 21)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PROCEDURE_ENTER_RECEIPT_VALID o
    check (fun th -> fst(strip_comb(concl th)) = `tisa_entry_ok`)) THEN
  MP_TAC(SPECL [`tisa_fword t 20`;`tisa_fword t 21`] PROCEDURE_ENTER_FUEL_ROOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`;`k:num`;`u:tisa_state`] PROCEDURE_ENTER_RUN) THEN
  ASM_REWRITE_TAC[procedure_enter_post] THEN
  ASM_CASES_TAC `val(tisa_fword t 22) < val(tisa_fword t 23)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `val(tisa_fword t 21) = val(tisa_fword t 20)` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC TISA_VAL_OFFSET) THEN
  MP_TAC(ISPEC `tisa_fword t 23` VAL_BOUND_64) THEN
  MP_TAC(ISPEC `tisa_fword t 20` VAL_BOUND_64) THEN ASM_ARITH_TAC);;

let PROCEDURE_ENTER_FRAME = prove
 (`!t k u. tisa_entry_ok procedure_enter t /\ tisa_run procedure_enter t = TStop k u
       ==> tregs u 0 = tregs t 0 /\
           !a. ~(val(tregs t 0) + 144 <= val a /\ val a < val(tregs t 0) + 176)
               ==> tmem u a = tmem t a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`procedure_enter`;`t:tisa_state`;`k:num`;`u:tisa_state`] TISA_RUN_KEEPS) THEN
  ASM_REWRITE_TAC[PROCEDURE_ENTER_LEAF_WF;PROCEDURE_ENTER_DECLS;tisa_keeps;
                  tisa_writable;tisa_rw;LENGTH;CONJUNCT1 LT]);;

let procedure_enter_theorems =
 ["PROCEDURE_ENTER_DECLS",PROCEDURE_ENTER_DECLS;
  "PROCEDURE_ENTER_LEAF_WF",PROCEDURE_ENTER_LEAF_WF;
  "TISA_WP_FUND",TISA_WP_FUND;
  "PROCEDURE_ENTER_WP",PROCEDURE_ENTER_WP;
  "PROCEDURE_ENTER_RUN",PROCEDURE_ENTER_RUN;
  "PROCEDURE_ENTER_RECEIPT_VALID",PROCEDURE_ENTER_RECEIPT_VALID;
  "PROCEDURE_ENTER_FUEL_ROOM",PROCEDURE_ENTER_FUEL_ROOM;
  "PROCEDURE_ENTER_OUTCOMES",PROCEDURE_ENTER_OUTCOMES;
  "PROCEDURE_ENTER_FRAME",PROCEDURE_ENTER_FRAME];;
