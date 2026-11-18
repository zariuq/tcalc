(* A refused leaf's payload must not overwrite the published policy. *)
needs "native/hol/policy_plan.ml";;

let POLICY_GUARD_REFUSAL_KEEPS_WORD = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput inp cw ns stk i cw' ns' stk'.
     tab_run (trow,tn,twd,tdrop,tapp,tput) inp pl_plan_policy 0 (cw,ns,stk)
             (0,i,(cw',ns',stk'))
     ==> cw' 7 = cw 7`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP TAB_POLICY_RUN) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let POLICY_EARLY_WRITE_CHANGES_FLOOR =
  let early = mk_list([pl_step_tm 20 [] 7 8 [] 7],`:int64 list`) in
  let goal = subst [early,`P:(int64 list)list`]
   `!(trow:num->S->num->num list) tn twd tdrop tapp tput inp cw ns stk.
      cw 7 = 1 /\ cw 8 = 3
      ==> tab_run (trow,tn,twd,tdrop,tapp,tput) inp P 0 (cw,ns,stk)
                  (0,0,(pl_set cw 7 0,ns,stk)) /\
          ~((pl_set cw 7 0) 7 = cw 7)` in
  prove(goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [CONJUNCT2 tab_run] THEN
      MAP_EVERY EXISTS_TAC [`0`;`0`;`ns:S`] THEN
      REWRITE_TAC[tab_leaf;LET_DEF;LET_END_DEF;FST;SND] THEN
      CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[tab_polmax] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV]);;

let policy_plan_control_theorems =
 ["POLICY_GUARD_REFUSAL_KEEPS_WORD",POLICY_GUARD_REFUSAL_KEEPS_WORD;
  "POLICY_EARLY_WRITE_CHANGES_FLOOR",POLICY_EARLY_WRITE_CHANGES_FLOOR];;
leaf_audit policy_plan_control_theorems policy_plan_control_theorems;;
