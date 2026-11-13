(* ========================================================================= *)
(* Joins the x86 image theorem of intern16 (from the t-ISA generator) with   *)
(* the functional theorem INTERN16_SOUND: the native code's run, when its   *)
(* p1 run returns FIRED, ends in a state satisfying intern16_post, and the  *)
(* x86 memory equals that state's memory outside the saved stack.           *)
(* ========================================================================= *)

loadt "native/hol/intern16.ml";;

let INTERN16_RUN_SOUND = prove
 (`!t u. tisa_entry_ok intern16 t /\ tisa_run intern16 t = TStop 1 u
         ==> intern16_post t u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> tisa_has_tm `tisa_run` th)) THEN
  ASM_REWRITE_TAC[tisa_run] THEN
  MP_TAC(ISPEC `tisa_exec (tisa_root intern16) t` TISA_RESULT_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_TAC `a:tisa_state`)
     (X_CHOOSE_THEN `k:num` (X_CHOOSE_TAC `a:tisa_state`))) THEN
  ASM_REWRITE_TAC[tisa_then; TISA_FAIL_STOP; TISA_RESULT_INJ] THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k = 1`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a:tisa_state = u`)) THEN
    MATCH_MP_TAC INTERN16_SOUND THEN ASM_REWRITE_TAC[]]);;

(* The image theorem for intern16, with its postcondition strengthened by    *)
(* the interning guarantee for a FIRED run.                                  *)
let INTERN16_X86_SOUND =
  let eth = REWRITE_RULE[GSYM INTERN16_TERM] (assoc "intern16" !tisa_entry_thms) in
  let ant,ens = dest_imp(concl eth) in
  let (_,args) = strip_comb ens in
  let q = el 2 args in
  let sv = genvar `:x86state` in
  let extra = `!u. tisa_run intern16 t = TStop 1 u ==> intern16_post t u` in
  let q' = mk_abs(sv, mk_conj(mk_comb(q, sv), extra)) in
  let goal = mk_imp(ant, list_mk_comb(fst(strip_comb ens), [el 0 args; el 1 args; q'; el 3 args])) in
  prove(goal,
    DISCH_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC q THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERN16_RUN_SOUND THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC eth THEN FIRST_ASSUM ACCEPT_TAC]);;

Printf.printf "JOIN INTERN16_RUN_SOUND: %d hyps\n%!" (length(hyp INTERN16_RUN_SOUND));;
Printf.printf "JOIN INTERN16_X86_SOUND: %d hyps\n%!" (length(hyp INTERN16_X86_SOUND));;
print_endline (string_of_thm INTERN16_X86_SOUND);;
