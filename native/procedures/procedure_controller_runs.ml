(* Finite controller traces and their connection to source procedure runs. *)
needs "native/procedures/procedure_controller.ml";;

let procedure_controller_edge = new_definition
 `procedure_controller_edge call_tag fn P b cap
    (q:procedure_controller_phase#procedure_work_frame list#A#num) r <=>
    procedure_controller_step call_tag fn P b cap (FST q) (FST(SND q))
      (FST(SND(SND q))) (SND(SND(SND q))) = SOME r`;;

let procedure_controller_path_RULES,procedure_controller_path_INDUCT,
    procedure_controller_path_CASES = new_inductive_definition
 `(!call_tag fn P b cap (q:procedure_controller_phase#procedure_work_frame list#A#num).
     procedure_controller_path call_tag fn P b cap q q) /\
  (!call_tag fn P b cap q r t.
     procedure_controller_edge call_tag fn P b cap q r /\ procedure_controller_path call_tag fn P b cap r t
     ==> procedure_controller_path call_tag fn P b cap q t)`;;

let PROCEDURE_CONTROLLER_PATH_ONE = prove
 (`!call_tag fn P b cap q r.
    procedure_controller_edge call_tag fn P b cap q (r:procedure_controller_phase#procedure_work_frame list#A#num)
    ==> procedure_controller_path call_tag fn P b cap q r`,
  MESON_TAC[procedure_controller_path_RULES]);;

let PROCEDURE_CONTROLLER_PATH_TRANS = prove
 (`!call_tag fn P b cap q r.
    procedure_controller_path call_tag fn P b cap q (r:procedure_controller_phase#procedure_work_frame list#A#num)
    ==> !t. procedure_controller_path call_tag fn P b cap r t
            ==> procedure_controller_path call_tag fn P b cap q t`,
  MATCH_MP_TAC procedure_controller_path_INDUCT THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[procedure_controller_path_RULES]);;

let procedure_controller_state_meaning = new_definition
 `procedure_controller_state_meaning call_tag fn P b cap
    (q:procedure_controller_phase#procedure_work_frame list#A#num) =
    procedure_controller_meaning call_tag fn P b cap (FST q) (FST(SND q))
      (FST(SND(SND q))) (SND(SND(SND q)))`;;

let PROCEDURE_CONTROLLER_EDGE_MEANING = prove
 (`!call_tag fn P b cap q (r:procedure_controller_phase#procedure_work_frame list#A#num).
    procedure_controller_edge call_tag fn P b cap q r ==>
    procedure_controller_state_meaning call_tag fn P b cap q = procedure_controller_state_meaning call_tag fn P b cap r`,
  REWRITE_TAC[FORALL_PAIR_THM;procedure_controller_edge;
    procedure_controller_state_meaning;FST;SND] THEN
  MESON_TAC[PROCEDURE_CONTROLLER_STEP]);;

let PROCEDURE_CONTROLLER_PATH_MEANING = prove
 (`!call_tag fn P b cap q (r:procedure_controller_phase#procedure_work_frame list#A#num).
    procedure_controller_path call_tag fn P b cap q r ==>
    procedure_controller_state_meaning call_tag fn P b cap q = procedure_controller_state_meaning call_tag fn P b cap r`,
  MATCH_MP_TAC procedure_controller_path_INDUCT THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[PROCEDURE_CONTROLLER_EDGE_MEANING]);;

let PROCEDURE_CONTROLLER_PATH_RESULT = prove
 (`!call_tag fn P b cap pid args (s:A) used k pay s1 used1.
    procedure_controller_path call_tag fn P b cap (ProcedureEnter pid args,[],s,used)
      (ProcedureReturn k pay,[],s1,used1) ==>
    procedure_eval_call cap call_tag fn P b pid args s used = (procedure_call_outcome k,pay,s1,used1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`call_tag:num`;`fn:num->int64 list->(num->num)->A->num->num#num#A#num`;
    `P:(((int64 list)list)list)list`;`b:num`;`cap:num`;
    `(ProcedureEnter pid args,[]:procedure_work_frame list,s:A,used:num)`;
    `(ProcedureReturn k pay,[]:procedure_work_frame list,s1:A,used1:num)`]
   PROCEDURE_CONTROLLER_PATH_MEANING) THEN
  ASM_REWRITE_TAC[procedure_controller_state_meaning;FST;SND;
    PROCEDURE_CONTROLLER_INITIAL;procedure_controller_meaning;procedure_controller_unwind;
    procedure_controller_phase_eval;procedure_eval_boundary;LENGTH;SUB_0]);;

let procedure_controller_exec_done = new_definition
 `procedure_controller_exec_done args clauses (r:num#num#(num->num)#A#num) =
    if FST r = 0 then procedure_controller_choose clauses args
    else ProcedureReturn (FST r) ((FST(SND(SND r))) 7)`;;

let PROCEDURE_CONTROLLER_SOURCE_PREP_TAC =
  REPEAT(GEN_TAC ORELSE DISCH_TAC) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if is_var l && not(aconv l r) then SUBST_ALL_TAC th
    else if is_var r && not(aconv l r) then SUBST_ALL_TAC(GSYM th)
    else failwith "source variable equation")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[procedure_function_leaf;procedure_controller_exec_done;FST;SND;PAIR;ARITH_EQ;LENGTH;ADD1]);;

let PROCEDURE_CONTROLLER_EDGE_TAC =
  ASM_SIMP_TAC[procedure_controller_edge;FST;SND;procedure_controller_step;
    procedure_controller_after;procedure_controller_exec_done;procedure_call_outcome;LET_DEF;LET_END_DEF;
    ARITH_EQ;LT_REFL;ARITH_RULE `(n:num) < call_tag ==> ~(call_tag < n) /\ ~(n = call_tag)`;
    ARITH_RULE `u <= b ==> ~(b < u)`;ARITH_RULE `u < b ==> ~(b < u) /\ ~(u = b)`;
    ARITH_RULE `i < n ==> ~(n <= i)`];;

let PROCEDURE_CONTROLLER_TAKE_STEP_TAC middle =
  MATCH_MP_TAC(CONJUNCT2 procedure_controller_path_RULES) THEN
  EXISTS_TAC middle THEN CONJ_TAC THENL [PROCEDURE_CONTROLLER_EDGE_TAC;ALL_TAC];;

let PROCEDURE_CONTROLLER_PATH_JOIN = prove
 (`!call_tag fn P b cap q r t.
    procedure_controller_path call_tag fn P b cap q (r:procedure_controller_phase#procedure_work_frame list#A#num) /\
    procedure_controller_path call_tag fn P b cap r t ==> procedure_controller_path call_tag fn P b cap q t`,
  MESON_TAC[PROCEDURE_CONTROLLER_PATH_TRANS]);;

let PROCEDURE_CONTROLLER_JOIN_TAC middle =
  MATCH_MP_TAC PROCEDURE_CONTROLLER_PATH_JOIN THEN
  EXISTS_TAC middle THEN CONJ_TAC;;

let PROCEDURE_CONTROLLER_FINISH_TAC =
  MATCH_MP_TAC PROCEDURE_CONTROLLER_PATH_ONE THEN PROCEDURE_CONTROLLER_EDGE_TAC;;

let PROCEDURE_CONTROLLER_CHILD_IH_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && procedure_has "ProcedureEnter" th then
      MP_TAC(REWRITE_RULE[LENGTH;ADD1]
        (SPEC `CONS (ProcedureWorkFrame (CONS st sts) i cw args clauses) stack` th))
    else failwith "source call induction hypothesis") THEN
  DISCH_THEN STRIP_ASSUME_TAC;;

let PROCEDURE_CONTROLLER_SOURCE = prove
 (`!fn.
   (!call_tag L P b cap depth p i cw (s:A) used r.
     procedure_exec call_tag L P b cap depth p i cw s used r ==>
     !stack args clauses. L = procedure_function_leaf fn /\ depth = LENGTH stack + 1 ==>
       procedure_controller_path call_tag fn P b cap
         (ProcedureRun(ProcedureWorkFrame p i cw args clauses),stack,s,used)
         (procedure_controller_exec_done args clauses r,stack,
           FST(SND(SND(SND r))),SND(SND(SND(SND r))))) /\
   (!call_tag L P b cap depth cls args (s:A) used r.
     procedure_choose call_tag L P b cap depth cls args s used r ==>
     !stack. L = procedure_function_leaf fn /\ depth = LENGTH stack + 1 ==>
       procedure_controller_path call_tag fn P b cap
         (procedure_controller_choose cls args,stack,s,used)
         (ProcedureReturn (procedure_call_outcome(FST r)) (FST(SND r)),stack,
           FST(SND(SND r)),SND(SND(SND r)))) /\
   (!call_tag L P b cap depth pid args (s:A) used r.
     procedure_call call_tag L P b cap depth pid args s used r ==>
     !stack. L = procedure_function_leaf fn /\ depth = LENGTH stack ==>
       ~(FST r = 0) /\
       procedure_controller_path call_tag fn P b cap (ProcedureEnter pid args,stack,s,used)
         (ProcedureReturn (FST r) (FST(SND r)),stack,FST(SND(SND r)),SND(SND(SND r))))`,
  GEN_TAC THEN MATCH_MP_TAC procedure_INDUCT THEN REPEAT CONJ_TAC THENL
   [PROCEDURE_CONTROLLER_SOURCE_PREP_TAC THEN
    REWRITE_TAC[procedure_controller_exec_done;FST;SND;ARITH_EQ] THEN
    PROCEDURE_CONTROLLER_FINISH_TAC;
    PROCEDURE_CONTROLLER_SOURCE_PREP_TAC THEN
    PROCEDURE_CONTROLLER_TAKE_STEP_TAC
      `((ProcedureRun(ProcedureWorkFrame sts (i + 1)
         (procedure_set cw (val(EL 17 (st:int64 list))) pay) args clauses),stack,s1:A,used1)):procedure_controller_phase#procedure_work_frame list#A#num` THEN
    ASM_SIMP_TAC[procedure_controller_exec_done;FST;SND;PAIR];
    PROCEDURE_CONTROLLER_SOURCE_PREP_TAC THEN
    PROCEDURE_CONTROLLER_FINISH_TAC;
    PROCEDURE_CONTROLLER_SOURCE_PREP_TAC THEN
    PROCEDURE_CONTROLLER_CHILD_IH_TAC THEN
    PROCEDURE_CONTROLLER_TAKE_STEP_TAC
      `((ProcedureEnter (val(EL 1 st)) (procedure_args st cw),
         CONS(ProcedureWorkFrame (CONS st sts) i cw args clauses) stack,s:A,used)):procedure_controller_phase#procedure_work_frame list#A#num` THEN
    PROCEDURE_CONTROLLER_JOIN_TAC
      `((ProcedureReturn 1 pay,CONS(ProcedureWorkFrame (CONS st sts) i cw args clauses) stack,s1:A,used1)):procedure_controller_phase#procedure_work_frame list#A#num` THENL
     [ASM_REWRITE_TAC[];
      PROCEDURE_CONTROLLER_TAKE_STEP_TAC
        `((ProcedureRun(ProcedureWorkFrame sts (i + 1)
           (procedure_set cw (val(EL 17 (st:int64 list))) pay) args clauses),stack,s1:A,used1)):procedure_controller_phase#procedure_work_frame list#A#num` THEN
      ASM_SIMP_TAC[procedure_controller_exec_done;FST;SND;PAIR]];
    PROCEDURE_CONTROLLER_SOURCE_PREP_TAC THEN
    PROCEDURE_CONTROLLER_CHILD_IH_TAC THEN
    PROCEDURE_CONTROLLER_TAKE_STEP_TAC
      `((ProcedureEnter (val(EL 1 st)) (procedure_args st cw),
         CONS(ProcedureWorkFrame (CONS st sts) i cw args clauses) stack,s:A,used)):procedure_controller_phase#procedure_work_frame list#A#num` THEN
    PROCEDURE_CONTROLLER_JOIN_TAC
      `((ProcedureReturn k pay,CONS(ProcedureWorkFrame (CONS st sts) i cw args clauses) stack,s1:A,used1)):procedure_controller_phase#procedure_work_frame list#A#num` THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[procedure_call_outcome] THEN PROCEDURE_CONTROLLER_FINISH_TAC];
    PROCEDURE_CONTROLLER_SOURCE_PREP_TAC THEN PROCEDURE_CONTROLLER_FINISH_TAC;
    PROCEDURE_CONTROLLER_SOURCE_PREP_TAC THEN
    REWRITE_TAC[procedure_controller_choose;procedure_call_outcome;FST;SND] THEN
    MATCH_ACCEPT_TAC(CONJUNCT1 procedure_controller_path_RULES);
    PROCEDURE_CONTROLLER_SOURCE_PREP_TAC THEN
    REWRITE_TAC[procedure_controller_choose] THEN
    PROCEDURE_CONTROLLER_JOIN_TAC
      `((procedure_controller_choose cs args,stack,s1:A,used1)):procedure_controller_phase#procedure_work_frame list#A#num` THEN
    ASM_SIMP_TAC[procedure_controller_exec_done;FST;SND];
    PROCEDURE_CONTROLLER_SOURCE_PREP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`stack:procedure_work_frame list`;`args:num list`;`cs:((int64 list)list)list`] o
      check (fun th -> is_forall(concl th) && procedure_has "ProcedureRun" th)) THEN
    ASM_SIMP_TAC[procedure_controller_choose;procedure_controller_exec_done;
      procedure_call_outcome;FST;SND];
    PROCEDURE_CONTROLLER_SOURCE_PREP_TAC THEN
    REWRITE_TAC[FST;SND;ARITH_EQ] THEN PROCEDURE_CONTROLLER_FINISH_TAC;
    PROCEDURE_CONTROLLER_SOURCE_PREP_TAC THEN
    REWRITE_TAC[FST;SND;ARITH_EQ] THEN PROCEDURE_CONTROLLER_FINISH_TAC;
    PROCEDURE_CONTROLLER_SOURCE_PREP_TAC THEN
    REWRITE_TAC[FST;SND;ARITH_EQ] THEN PROCEDURE_CONTROLLER_FINISH_TAC;
    PROCEDURE_CONTROLLER_SOURCE_PREP_TAC THEN
    REWRITE_TAC[FST;SND;ARITH_EQ] THEN PROCEDURE_CONTROLLER_FINISH_TAC;
    PROCEDURE_CONTROLLER_SOURCE_PREP_TAC THEN
    REWRITE_TAC[FST;SND;PROCEDURE_CALL_NOT_REFUSED] THEN
    PROCEDURE_CONTROLLER_TAKE_STEP_TAC
      `((procedure_controller_choose (EL pid P) args,stack,s:A,used + 1)):procedure_controller_phase#procedure_work_frame list#A#num` THEN
    ASM_SIMP_TAC[procedure_controller_exec_done;FST;SND;PAIR]]);;

let PROCEDURE_CONTROLLER_EXEC_SOURCE,PROCEDURE_CONTROLLER_CHOOSE_SOURCE,
    PROCEDURE_CONTROLLER_CALL_SOURCE =
  match map (fun th -> GEN_ALL(REWRITE_RULE[]
      (SPECL [`call_tag:num`;`procedure_function_leaf
        (fn:num->int64 list->(num->num)->A->num->num#num#A#num)`] th)))
    (CONJUNCTS(SPEC_ALL PROCEDURE_CONTROLLER_SOURCE)) with
  | [x;y;z] -> x,y,z
  | _ -> failwith "controller source theorem shape";;

let PROCEDURE_CONTROLLER_EVAL_TRACE = prove
 (`!call_tag fn P b cap pid args (s:A) used k pay s1 used1.
    procedure_eval_call cap call_tag fn P b pid args s used = (k,pay,s1,used1) ==>
    ~(k = 0) /\
    procedure_controller_path call_tag fn P b cap (ProcedureEnter pid args,[],s,used)
      (ProcedureReturn k pay,[],s1,used1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `procedure_call call_tag (procedure_function_leaf fn) P b cap 0 pid args (s:A) used (k,pay,s1,used1)`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PROCEDURE_EVAL_CALL_EXACT;SUB_0];ALL_TAC] THEN
  MP_TAC(ISPECL
   [`call_tag:num`;`fn:num->int64 list->(num->num)->A->num->num#num#A#num`;
    `P:(((int64 list)list)list)list`;`b:num`;`cap:num`;`0`;`pid:num`;
    `args:num list`;`s:A`;`used:num`;`(k:num,pay:num,s1:A,used1:num)`]
   PROCEDURE_CONTROLLER_CALL_SOURCE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `[]:procedure_work_frame list`) THEN
  REWRITE_TAC[LENGTH;FST;SND]);;

let PROCEDURE_CONTROLLER_TOTAL = prove
 (`!call_tag fn P b cap pid args (s:A) used.
    ?k pay s1 used1. ~(k = 0) /\
    procedure_controller_path call_tag fn P b cap (ProcedureEnter pid args,[],s,used)
      (ProcedureReturn k pay,[],s1,used1)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC
    `procedure_eval_call cap call_tag (fn:num->int64 list->(num->num)->A->num->num#num#A#num)
      P b pid args s used` PROCEDURE_RESULT_EXHAUSTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `pay:num`
    (X_CHOOSE_THEN `s1:A` (X_CHOOSE_THEN `used1:num` ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`k:num`;`pay:num`;`s1:A`;`used1:num`] THEN
  MATCH_MP_TAC PROCEDURE_CONTROLLER_EVAL_TRACE THEN ASM_REWRITE_TAC[]);;

let PROCEDURE_CONTROLLER_EDGE_DETERMINISTIC = prove
 (`!call_tag fn P b cap q r t:procedure_controller_phase#procedure_work_frame list#A#num.
    procedure_controller_edge call_tag fn P b cap q r /\ procedure_controller_edge call_tag fn P b cap q t ==> r = t`,
  REWRITE_TAC[procedure_controller_edge] THEN MESON_TAC[option_INJ]);;

let PROCEDURE_CONTROLLER_PATH_STUCK = prove
 (`!call_tag fn P b cap q r:procedure_controller_phase#procedure_work_frame list#A#num.
    procedure_controller_path call_tag fn P b cap q r ==> (!t. ~procedure_controller_edge call_tag fn P b cap q t) ==> q = r`,
  MATCH_MP_TAC procedure_controller_path_INDUCT THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let PROCEDURE_CONTROLLER_RETURN_NO_EDGE = prove
 (`!call_tag fn P b cap k pay (s:A) used q.
    ~procedure_controller_edge call_tag fn P b cap (ProcedureReturn k pay,[],s,used) q`,
  REWRITE_TAC[procedure_controller_edge;FST;SND;procedure_controller_step;option_DISTINCT]);;

let PROCEDURE_CONTROLLER_TERMINAL_UNIQUE = prove
 (`!call_tag fn P b cap q r:procedure_controller_phase#procedure_work_frame list#A#num.
    procedure_controller_path call_tag fn P b cap q r ==>
    !out. procedure_controller_path call_tag fn P b cap q out /\
      (!t. ~procedure_controller_edge call_tag fn P b cap r t) /\
      (!t. ~procedure_controller_edge call_tag fn P b cap out t) ==> r = out`,
  MATCH_MP_TAC procedure_controller_path_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[PROCEDURE_CONTROLLER_PATH_STUCK];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    X_GEN_TAC `out:procedure_controller_phase#procedure_work_frame list#A#num` THEN STRIP_TAC THEN
    MP_TAC(ASSUME `procedure_controller_path call_tag fn P b cap
      (q:procedure_controller_phase#procedure_work_frame list#A#num) out`) THEN
    ONCE_REWRITE_TAC[procedure_controller_path_CASES] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `middle:procedure_controller_phase#procedure_work_frame list#A#num` STRIP_ASSUME_TAC)) THENL
     [ASM_MESON_TAC[];
      SUBGOAL_THEN
        `(middle:procedure_controller_phase#procedure_work_frame list#A#num) = r`
        SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[PROCEDURE_CONTROLLER_EDGE_DETERMINISTIC];ASM_MESON_TAC[]]]]);;

let PROCEDURE_CONTROLLER_PHASE_INJECTIVE =
  prove_constructors_injective procedure_controller_phase_RECURSION;;

let PROCEDURE_CONTROLLER_PATH_NONZERO = prove
 (`!call_tag fn P b cap pid args (s:A) used k pay s1 used1.
    procedure_controller_path call_tag fn P b cap (ProcedureEnter pid args,[],s,used)
      (ProcedureReturn k pay,[],s1,used1) ==> ~(k = 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`call_tag:num`;`fn:num->int64 list->(num->num)->A->num->num#num#A#num`;
    `P:(((int64 list)list)list)list`;`b:num`;`cap:num`;`pid:num`;
    `args:num list`;`s:A`;`used:num`] PROCEDURE_CONTROLLER_TOTAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `pay2:num`
    (X_CHOOSE_THEN `s2:A` (X_CHOOSE_THEN `used2:num` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL
   [`call_tag:num`;`fn:num->int64 list->(num->num)->A->num->num#num#A#num`;
    `P:(((int64 list)list)list)list`;`b:num`;`cap:num`;
    `(ProcedureEnter pid args,[]:procedure_work_frame list,s:A,used:num)`;
    `(ProcedureReturn k pay,[]:procedure_work_frame list,s1:A,used1:num)`]
   PROCEDURE_CONTROLLER_TERMINAL_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC
    `(ProcedureReturn k2 pay2,[]:procedure_work_frame list,s2:A,used2:num)`) THEN
  ASM_REWRITE_TAC[PROCEDURE_CONTROLLER_RETURN_NO_EDGE;PAIR_EQ;PROCEDURE_CONTROLLER_PHASE_INJECTIVE] THEN
  ASM_MESON_TAC[]);;

let PROCEDURE_CONTROLLER_EXACT = prove
 (`!call_tag fn P b cap pid args (s:A) used k pay s1 used1.
    procedure_controller_path call_tag fn P b cap (ProcedureEnter pid args,[],s,used)
      (ProcedureReturn k pay,[],s1,used1) <=>
    procedure_eval_call cap call_tag fn P b pid args s used = (k,pay,s1,used1)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL
     [`call_tag:num`;`fn:num->int64 list->(num->num)->A->num->num#num#A#num`;
      `P:(((int64 list)list)list)list`;`b:num`;`cap:num`;`pid:num`;`args:num list`;
      `s:A`;`used:num`;`k:num`;`pay:num`;`s1:A`;`used1:num`]
      PROCEDURE_CONTROLLER_PATH_RESULT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PROCEDURE_CONTROLLER_PATH_NONZERO];ALL_TAC] THEN
    ASM_REWRITE_TAC[procedure_call_outcome];
    MESON_TAC[PROCEDURE_CONTROLLER_EVAL_TRACE]]);;

let procedure_controller_next = new_definition
 `procedure_controller_next call_tag fn P b cap
   (q:procedure_controller_phase#procedure_work_frame list#A#num) =
   procedure_controller_step call_tag fn P b cap (FST q) (FST(SND q))
     (FST(SND(SND q))) (SND(SND(SND q)))`;;

let procedure_controller_stopped = new_definition
 `procedure_controller_stopped call_tag fn P b cap
    (q:procedure_controller_phase#procedure_work_frame list#A#num) <=> procedure_controller_next call_tag fn P b cap q = NONE`;;

let procedure_controller_tick_result = define
 `(procedure_controller_tick_result (q:procedure_controller_phase#procedure_work_frame list#A#num) NONE = q) /\
  (procedure_controller_tick_result q (SOME r) = r)`;;

let procedure_controller_tick = new_definition
 `procedure_controller_tick call_tag fn P b cap
    (q:procedure_controller_phase#procedure_work_frame list#A#num) =
    procedure_controller_tick_result q (procedure_controller_next call_tag fn P b cap q)`;;

let procedure_controller_iter = new_recursive_definition num_RECURSION
 `(procedure_controller_iter 0 call_tag fn P b cap (q:procedure_controller_phase#procedure_work_frame list#A#num) = q) /\
  (procedure_controller_iter (SUC n) call_tag fn P b cap q =
    procedure_controller_iter n call_tag fn P b cap (procedure_controller_tick call_tag fn P b cap q))`;;

let PROCEDURE_CONTROLLER_TICK_EDGE = prove
 (`!call_tag fn P b cap q r:procedure_controller_phase#procedure_work_frame list#A#num.
    procedure_controller_edge call_tag fn P b cap q r ==> procedure_controller_tick call_tag fn P b cap q = r`,
  REWRITE_TAC[procedure_controller_edge;procedure_controller_tick;procedure_controller_next] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[procedure_controller_tick_result]);;

let PROCEDURE_CONTROLLER_ITER_STOPPED = prove
 (`!call_tag n fn P b cap q:procedure_controller_phase#procedure_work_frame list#A#num.
    procedure_controller_stopped call_tag fn P b cap q ==> procedure_controller_iter n call_tag fn P b cap q = q`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[procedure_controller_stopped] THEN
  DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[procedure_controller_stopped]) THEN
  ASM_SIMP_TAC[procedure_controller_iter;procedure_controller_tick;procedure_controller_tick_result]);;

let PROCEDURE_CONTROLLER_PATH_STABILIZES = prove
 (`!call_tag fn P b cap q r:procedure_controller_phase#procedure_work_frame list#A#num.
    procedure_controller_path call_tag fn P b cap q r ==> procedure_controller_stopped call_tag fn P b cap r ==>
    ?n. !m. n <= m ==> procedure_controller_iter m call_tag fn P b cap q = r`,
  MATCH_MP_TAC procedure_controller_path_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `0` THEN
    ASM_SIMP_TAC[PROCEDURE_CONTROLLER_ITER_STOPPED];
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n:num` ASSUME_TAC) THEN
    EXISTS_TAC `SUC n` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(SPEC `m:num` num_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC)) THENL
     [ASM_ARITH_TAC;
      ASM_SIMP_TAC[procedure_controller_iter;PROCEDURE_CONTROLLER_TICK_EDGE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let PROCEDURE_CONTROLLER_TERMINATES = prove
 (`!call_tag fn P b cap pid args (s:A) used.
    ?n k pay s1 used1. ~(k = 0) /\
      !m. n <= m ==>
        procedure_controller_iter m call_tag fn P b cap (ProcedureEnter pid args,[],s,used) =
        (ProcedureReturn k pay,[],s1,used1)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`call_tag:num`;`fn:num->int64 list->(num->num)->A->num->num#num#A#num`;
    `P:(((int64 list)list)list)list`;`b:num`;`cap:num`;`pid:num`;
    `args:num list`;`s:A`;`used:num`] PROCEDURE_CONTROLLER_TOTAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `pay:num`
    (X_CHOOSE_THEN `s1:A` (X_CHOOSE_THEN `used1:num` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL
   [`call_tag:num`;`fn:num->int64 list->(num->num)->A->num->num#num#A#num`;
    `P:(((int64 list)list)list)list`;`b:num`;`cap:num`;
    `(ProcedureEnter pid args,[]:procedure_work_frame list,s:A,used:num)`;
    `(ProcedureReturn k pay,[]:procedure_work_frame list,s1:A,used1:num)`]
    PROCEDURE_CONTROLLER_PATH_STABILIZES) THEN
  ASM_REWRITE_TAC[procedure_controller_stopped;procedure_controller_next;
    procedure_controller_step;FST;SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`n:num`;`k:num`;`pay:num`;`s1:A`;`used1:num`] THEN
  ASM_REWRITE_TAC[]);;

let PROCEDURE_CONTROLLER_ITER_EVAL = prove
 (`!call_tag n fn P b cap q:procedure_controller_phase#procedure_work_frame list#A#num.
    procedure_controller_iter n call_tag fn P b cap q =
    if n = 0 then q else procedure_controller_iter (n - 1) call_tag fn P b cap
      (procedure_controller_tick call_tag fn P b cap q)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[procedure_controller_iter;NOT_SUC;SUC_SUB1]);;

let PROCEDURE_CONTROLLER_CALL_REL = prove
 (`!call_tag fn P b cap pid args (s:A) used k pay s1 used1.
    procedure_controller_path call_tag fn P b cap (ProcedureEnter pid args,[],s,used)
      (ProcedureReturn k pay,[],s1,used1) <=>
    procedure_call call_tag (procedure_function_leaf fn) P b cap 0 pid args s used (k,pay,s1,used1)`,
  REWRITE_TAC[PROCEDURE_CONTROLLER_EXACT;PROCEDURE_EVAL_CALL_EXACT;SUB_0]);;

let PROCEDURE_CONTROLLER_RECEIPTS = prove
 (`!call_tag fn P b cap pid args (s:A) used k pay s1 used1.
    procedure_leaf_receipt_ok (procedure_function_leaf fn) b /\ used <= b /\
    procedure_controller_path call_tag fn P b cap (ProcedureEnter pid args,[],s,used)
      (ProcedureReturn k pay,[],s1,used1) ==> used <= used1 /\ used1 <= b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`call_tag:num`;`procedure_function_leaf(fn:num->int64 list->(num->num)->A->num->num#num#A#num)`;
    `P:(((int64 list)list)list)list`;`b:num`;`cap:num`;`0`;`pid:num`;`args:num list`;
    `s:A`;`used:num`;`(k:num,pay:num,s1:A,used1:num)`]
    (CONJUNCT2(CONJUNCT2 PROCEDURE_RECEIPTS))) THEN
  ASM_REWRITE_TAC[GSYM PROCEDURE_CONTROLLER_CALL_REL;FST;SND]);;

let PROCEDURE_CONTROLLER_WORLD_FRAME = prove
 (`!call_tag R fn P b cap pid args (s:A) used k pay s1 used1.
    (!s. R s s) /\ (!s t u. R s t /\ R t u ==> R s u) /\
    procedure_leaf_frame (procedure_function_leaf fn) R /\
    procedure_controller_path call_tag fn P b cap (ProcedureEnter pid args,[],s,used)
      (ProcedureReturn k pay,[],s1,used1) ==> R s s1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `R:A->A->bool` PROCEDURE_WORLD_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[];ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o ISPECL
   [`call_tag:num`;`procedure_function_leaf(fn:num->int64 list->(num->num)->A->num->num#num#A#num)`;
    `P:(((int64 list)list)list)list`;`b:num`;`cap:num`;`0`;`pid:num`;`args:num list`;
    `s:A`;`used:num`;`(k:num,pay:num,s1:A,used1:num)`]) THEN
  ASM_REWRITE_TAC[GSYM PROCEDURE_CONTROLLER_CALL_REL;FST;SND]);;

let procedure_controller_runs_theorems =
 ["PROCEDURE_CONTROLLER_PATH_ONE",PROCEDURE_CONTROLLER_PATH_ONE;
  "PROCEDURE_CONTROLLER_PATH_TRANS",PROCEDURE_CONTROLLER_PATH_TRANS;
  "PROCEDURE_CONTROLLER_EDGE_MEANING",PROCEDURE_CONTROLLER_EDGE_MEANING;
  "PROCEDURE_CONTROLLER_PATH_MEANING",PROCEDURE_CONTROLLER_PATH_MEANING;
  "PROCEDURE_CONTROLLER_PATH_RESULT",PROCEDURE_CONTROLLER_PATH_RESULT;
  "PROCEDURE_CONTROLLER_SOURCE",PROCEDURE_CONTROLLER_SOURCE;
  "PROCEDURE_CONTROLLER_PATH_JOIN",PROCEDURE_CONTROLLER_PATH_JOIN;
  "PROCEDURE_CONTROLLER_EXEC_SOURCE",PROCEDURE_CONTROLLER_EXEC_SOURCE;
  "PROCEDURE_CONTROLLER_CHOOSE_SOURCE",PROCEDURE_CONTROLLER_CHOOSE_SOURCE;
  "PROCEDURE_CONTROLLER_CALL_SOURCE",PROCEDURE_CONTROLLER_CALL_SOURCE;
  "PROCEDURE_CONTROLLER_EVAL_TRACE",PROCEDURE_CONTROLLER_EVAL_TRACE;
  "PROCEDURE_CONTROLLER_TOTAL",PROCEDURE_CONTROLLER_TOTAL;
  "PROCEDURE_CONTROLLER_EDGE_DETERMINISTIC",PROCEDURE_CONTROLLER_EDGE_DETERMINISTIC;
  "PROCEDURE_CONTROLLER_PATH_STUCK",PROCEDURE_CONTROLLER_PATH_STUCK;
  "PROCEDURE_CONTROLLER_RETURN_NO_EDGE",PROCEDURE_CONTROLLER_RETURN_NO_EDGE;
  "PROCEDURE_CONTROLLER_TERMINAL_UNIQUE",PROCEDURE_CONTROLLER_TERMINAL_UNIQUE;
  "PROCEDURE_CONTROLLER_PHASE_INJECTIVE",PROCEDURE_CONTROLLER_PHASE_INJECTIVE;
  "PROCEDURE_CONTROLLER_PATH_NONZERO",PROCEDURE_CONTROLLER_PATH_NONZERO;
  "PROCEDURE_CONTROLLER_EXACT",PROCEDURE_CONTROLLER_EXACT;
  "PROCEDURE_CONTROLLER_TICK_EDGE",PROCEDURE_CONTROLLER_TICK_EDGE;
  "PROCEDURE_CONTROLLER_ITER_STOPPED",PROCEDURE_CONTROLLER_ITER_STOPPED;
  "PROCEDURE_CONTROLLER_PATH_STABILIZES",PROCEDURE_CONTROLLER_PATH_STABILIZES;
  "PROCEDURE_CONTROLLER_TERMINATES",PROCEDURE_CONTROLLER_TERMINATES;
  "PROCEDURE_CONTROLLER_ITER_EVAL",PROCEDURE_CONTROLLER_ITER_EVAL;
  "PROCEDURE_CONTROLLER_CALL_REL",PROCEDURE_CONTROLLER_CALL_REL;
  "PROCEDURE_CONTROLLER_RECEIPTS",PROCEDURE_CONTROLLER_RECEIPTS;
  "PROCEDURE_CONTROLLER_WORLD_FRAME",PROCEDURE_CONTROLLER_WORLD_FRAME];;
