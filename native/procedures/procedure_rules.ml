(* Useful constructors and inversions of the bounded call semantics. *)
needs "native/procedures/procedure_sem.ml";;

let PROCEDURE_CALL_FIRED_RULE = GEN_ALL
 (REWRITE_RULE[procedure_call_outcome;ARITH_EQ]
   (INST [`1`,`k:num`] (SPEC_ALL (el 13 (CONJUNCTS procedure_RULES)))));;

let PROCEDURE_CALL_DOMAIN_RULE = GEN_ALL
 (REWRITE_RULE[procedure_call_outcome;ARITH_EQ]
   (INST [`0`,`k:num`] (SPEC_ALL (el 13 (CONJUNCTS procedure_RULES)))));;

let PROCEDURE_CHOOSE_EMPTY_PLAN = prove
 (`!call_tag L P b cap depth cls args (s:A) used.
     procedure_choose call_tag L P b cap depth (CONS [] cls) args s used (1,0,s,used)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `procedure_choose call_tag L P b cap depth (CONS [] cls) args (s:A) used
      (1,procedure_frame args 7,s,used)` MP_TAC THENL
   [MATCH_MP_TAC (GEN_ALL(INST
      [`procedure_frame (args:num list)`,`cw1:num->num`]
      (SPEC_ALL(el 8 (CONJUNCTS procedure_RULES))))) THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ARITH_EQ] THEN MATCH_ACCEPT_TAC (CONJUNCT1 procedure_RULES);
    REWRITE_TAC[PROCEDURE_FRAME_RESULT]]);;

let PROCEDURE_CALL_NONZERO = prove
 (`!call_tag L P b cap depth pid args (s:A) used r.
     procedure_call call_tag L P b cap depth pid args s used r ==> ~(FST r = 0)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [PROCEDURE_CALL_CASES] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST;PROCEDURE_CALL_NOT_REFUSED;ARITH_EQ]);;

let procedure_activation = new_definition
 `procedure_activation b cap depth used =
    if b < used then (3,depth,used)
    else if cap <= depth then (2,depth,used)
    else if used = b then (4,depth,used)
    else (1,depth + 1,used + 1)`;;

let PROCEDURE_ACTIVATION_FIRED = prove
 (`!b cap depth used k d1 u1.
     procedure_activation b cap depth used = (k,d1,u1) /\ k = 1
     ==> depth < cap /\ used < b /\ d1 = depth + 1 /\ u1 = used + 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[procedure_activation] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ;ARITH_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let PROCEDURE_ACTIVATION_RESOURCE_KINDS = prove
 (`procedure_activation 0 0 0 0 = (2,0,0) /\
   procedure_activation 0 1 0 0 = (4,0,0) /\
   procedure_activation 1 1 0 0 = (1,1,1)`,
  REWRITE_TAC[procedure_activation] THEN CONV_TAC NUM_REDUCE_CONV);;

let PROCEDURE_CALL_EMPTY_DOMAIN = prove
 (`!call_tag L b cap depth args (s:A) used.
     depth < cap /\ used < b
     ==> procedure_call call_tag L [[]] b cap depth 0 args s used (3,0,s,used + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC PROCEDURE_CALL_DOMAIN_RULE THEN
  ASM_REWRITE_TAC[LENGTH;EL;HD;ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_ACCEPT_TAC (el 6 (CONJUNCTS procedure_RULES)));;

let PROCEDURE_CALL_EMPTY_PLAN = prove
 (`!call_tag L b cap depth args (s:A) used.
     depth < cap /\ used < b
     ==> procedure_call call_tag L [[[]]] b cap depth 0 args s used (1,0,s,used + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC PROCEDURE_CALL_FIRED_RULE THEN
  ASM_REWRITE_TAC[LENGTH;EL;HD;ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_ACCEPT_TAC PROCEDURE_CHOOSE_EMPTY_PLAN);;

let procedure_rules_theorems = procedure_sem_theorems @
 ["PROCEDURE_CALL_FIRED_RULE",PROCEDURE_CALL_FIRED_RULE;
  "PROCEDURE_CALL_DOMAIN_RULE",PROCEDURE_CALL_DOMAIN_RULE;
  "PROCEDURE_CHOOSE_EMPTY_PLAN",PROCEDURE_CHOOSE_EMPTY_PLAN;
  "PROCEDURE_CALL_NONZERO",PROCEDURE_CALL_NONZERO;
  "PROCEDURE_ACTIVATION_FIRED",PROCEDURE_ACTIVATION_FIRED;
  "PROCEDURE_ACTIVATION_RESOURCE_KINDS",PROCEDURE_ACTIVATION_RESOURCE_KINDS;
  "PROCEDURE_CALL_EMPTY_DOMAIN",PROCEDURE_CALL_EMPTY_DOMAIN;
  "PROCEDURE_CALL_EMPTY_PLAN",PROCEDURE_CALL_EMPTY_PLAN];;
