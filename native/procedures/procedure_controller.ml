(* An explicit activation stack refining the bounded procedure relations. *)
needs "native/procedures/procedure_eval.ml";;

let procedure_work_frame_INDUCT,procedure_work_frame_RECURSION = define_type
 "procedure_work_frame = ProcedureWorkFrame ((int64 list)list) num (num->num) (num list) (((int64 list)list)list)";;

let procedure_controller_phase_INDUCT,procedure_controller_phase_RECURSION = define_type
 "procedure_controller_phase = ProcedureEnter num (num list)
                            | ProcedureRun procedure_work_frame
                            | ProcedureReturn num num";;

let procedure_controller_choose = define
 `(procedure_controller_choose [] args = ProcedureReturn 3 0) /\
  (procedure_controller_choose (CONS clause clauses) args =
    ProcedureRun (ProcedureWorkFrame clause 0 (procedure_frame args) args clauses))`;;

(* A suspended caller keeps the call step until the callee has returned.
   A refusal retries with original arguments, preserving world and receipt. *)
let procedure_controller_after = define
 `(procedure_controller_after (ProcedureWorkFrame [] i cw args clauses) k pay =
    ProcedureReturn 3 (cw 7)) /\
  (procedure_controller_after (ProcedureWorkFrame (CONS st sts) i cw args clauses) k pay =
    let cw1 = procedure_set cw (val(EL 17 st)) pay in
    if k = 1 then ProcedureRun (ProcedureWorkFrame sts (i + 1) cw1 args clauses)
    else if k = 0 then procedure_controller_choose clauses args
    else ProcedureReturn k (cw1 7))`;;

let procedure_controller_step = define
 `(procedure_controller_step call_tag fn P b cap (ProcedureEnter pid args) stack (s:A) used =
    if b < used then SOME(ProcedureReturn 3 3,stack,s,used)
    else if LENGTH P <= pid then SOME(ProcedureReturn 3 3,stack,s,used)
    else if cap <= LENGTH stack then SOME(ProcedureReturn 2 0,stack,s,used)
    else if used = b then SOME(ProcedureReturn 4 4,stack,s,used)
    else SOME(procedure_controller_choose (EL pid P) args,stack,s,used + 1)) /\
  (procedure_controller_step call_tag fn P b cap
      (ProcedureRun (ProcedureWorkFrame [] i cw args clauses)) stack s used =
    SOME(ProcedureReturn 1 (cw 7),stack,s,used)) /\
  (procedure_controller_step call_tag fn P b cap
      (ProcedureRun (ProcedureWorkFrame (CONS st sts) i cw args clauses)) stack s used =
    if call_tag < val(EL 0 st) then SOME(ProcedureReturn 3 (cw 7),stack,s,used)
    else if val(EL 0 st) = call_tag then
      SOME(ProcedureEnter (val(EL 1 st)) (procedure_args st cw),
           CONS (ProcedureWorkFrame (CONS st sts) i cw args clauses) stack,s,used)
    else let r = fn b st cw s used in
      SOME(procedure_controller_after
             (ProcedureWorkFrame (CONS st sts) i cw args clauses) (FST r) (FST(SND r)),
           stack,FST(SND(SND r)),SND(SND(SND r)))) /\
  (procedure_controller_step call_tag fn P b cap (ProcedureReturn k pay) [] s used = NONE) /\
  (procedure_controller_step call_tag fn P b cap (ProcedureReturn k pay) (CONS caller stack) s used =
    SOME(procedure_controller_after caller (procedure_call_outcome k) pay,stack,s,used))`;;

let procedure_controller_finish = new_definition
 `procedure_controller_finish call_tag fn invoke b clauses args (r:num#num#(num->num)#A#num) =
    if FST r = 0 then
      procedure_eval_boundary
        (procedure_eval_choose call_tag fn invoke b clauses args
          (FST(SND(SND(SND r)))) (SND(SND(SND(SND r)))))
    else procedure_eval_boundary
      (FST r,(FST(SND(SND r))) 7,FST(SND(SND(SND r))),SND(SND(SND(SND r))))`;;

let procedure_controller_frame_eval = define
 `procedure_controller_frame_eval call_tag fn invoke b
    (ProcedureWorkFrame plan i cw args clauses) (s:A) used =
    procedure_controller_finish call_tag fn invoke b clauses args
      (procedure_eval_exec call_tag fn invoke b plan i cw s used)`;;

let procedure_controller_phase_eval = define
 `(procedure_controller_phase_eval call_tag fn P b cap depth (ProcedureEnter pid args) (s:A) used =
    procedure_eval_call (cap - depth) call_tag fn P b pid args s used) /\
  (procedure_controller_phase_eval call_tag fn P b cap depth (ProcedureRun activation) s used =
    procedure_controller_frame_eval call_tag fn (procedure_eval_call (cap - (depth + 1)) call_tag fn P b)
      b activation s used) /\
  (procedure_controller_phase_eval call_tag fn P b cap depth (ProcedureReturn k pay) s used =
    procedure_eval_boundary (k,pay,s,used))`;;

let procedure_controller_unwind = define
 `(procedure_controller_unwind call_tag fn P b cap [] (r:num#num#A#num) = r) /\
  (procedure_controller_unwind call_tag fn P b cap (CONS caller stack) r =
    procedure_controller_unwind call_tag fn P b cap stack
      (procedure_controller_phase_eval call_tag fn P b cap (LENGTH stack)
        (procedure_controller_after caller (procedure_call_outcome(FST r)) (FST(SND r)))
        (FST(SND(SND r))) (SND(SND(SND r)))))`;;

let procedure_controller_meaning = new_definition
 `procedure_controller_meaning call_tag fn P b cap phase stack (s:A) used =
    procedure_controller_unwind call_tag fn P b cap stack
      (procedure_controller_phase_eval call_tag fn P b cap (LENGTH stack) phase s used)`;;

let PROCEDURE_CALL_OUTCOME_IDEMPOTENT = prove
 (`!k. procedure_call_outcome(procedure_call_outcome k) = procedure_call_outcome k`,
  GEN_TAC THEN ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[procedure_call_outcome;ARITH_EQ]);;

let PROCEDURE_CONTROLLER_INITIAL = prove
 (`!call_tag fn P b cap pid args (s:A) used.
    procedure_controller_meaning call_tag fn P b cap (ProcedureEnter pid args) [] s used =
    procedure_eval_call cap call_tag fn P b pid args s used`,
  REWRITE_TAC[procedure_controller_meaning;procedure_controller_unwind;
              procedure_controller_phase_eval;LENGTH;SUB_0]);;

let PROCEDURE_CONTROLLER_RETURN = prove
 (`!call_tag fn P b cap k pay caller stack (s:A) used.
    procedure_controller_meaning call_tag fn P b cap (ProcedureReturn k pay) (CONS caller stack) s used =
    procedure_controller_meaning call_tag fn P b cap
      (procedure_controller_after caller (procedure_call_outcome k) pay) stack s used`,
  REWRITE_TAC[procedure_controller_meaning;procedure_controller_unwind;
              procedure_controller_phase_eval;procedure_eval_boundary;FST;SND;
              PROCEDURE_CALL_OUTCOME_IDEMPOTENT]);;

let PROCEDURE_CONTROLLER_CHOOSE = prove
 (`!call_tag fn P b cap depth clauses args (s:A) used.
    procedure_controller_phase_eval call_tag fn P b cap depth (procedure_controller_choose clauses args) s used =
    procedure_eval_boundary
      (procedure_eval_choose call_tag fn (procedure_eval_call (cap - (depth + 1)) call_tag fn P b)
        b clauses args s used)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[procedure_controller_choose;procedure_controller_phase_eval;
      procedure_eval_choose;procedure_eval_boundary;procedure_call_outcome;FST;SND;ARITH_EQ];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[procedure_controller_choose;procedure_controller_phase_eval;
      procedure_controller_frame_eval;procedure_controller_finish;procedure_eval_choose;
      LET_DEF;LET_END_DEF;FST;SND] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

let PROCEDURE_EVAL_CALL_NOT_REFUSED = prove
 (`!call_tag n fn P b pid args (s:A) used.
    ~(FST(procedure_eval_call n call_tag fn P b pid args s used) = 0)`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[procedure_eval_call] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[procedure_eval_boundary;FST;PROCEDURE_CALL_NOT_REFUSED;ARITH_EQ]);;

let PROCEDURE_CONTROLLER_AFTER = prove
 (`!call_tag fn P b cap depth st sts i cw args clauses k pay (s:A) used.
    procedure_controller_phase_eval call_tag fn P b cap depth
      (procedure_controller_after (ProcedureWorkFrame (CONS st sts) i cw args clauses) k pay) s used =
    if k = 1 then
      procedure_controller_frame_eval call_tag fn (procedure_eval_call (cap - (depth + 1)) call_tag fn P b) b
        (ProcedureWorkFrame sts (i + 1) (procedure_set cw (val(EL 17 st)) pay) args clauses) s used
    else procedure_controller_finish call_tag fn (procedure_eval_call (cap - (depth + 1)) call_tag fn P b)
      b clauses args (k,i,procedure_set cw (val(EL 17 st)) pay,s,used)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[procedure_controller_after;LET_DEF;LET_END_DEF] THEN
  ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[procedure_controller_phase_eval] THEN
  ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[PROCEDURE_CONTROLLER_CHOOSE;procedure_controller_phase_eval;
    procedure_controller_finish;FST;SND]);;

let PROCEDURE_CONTROLLER_FRAME_NIL = prove
 (`!call_tag fn P b cap depth i cw args clauses (s:A) used.
    procedure_controller_frame_eval call_tag fn (procedure_eval_call (cap - (depth + 1)) call_tag fn P b) b
      (ProcedureWorkFrame [] i cw args clauses) s used = procedure_eval_boundary(1,cw 7,s,used)`,
  REWRITE_TAC[procedure_controller_frame_eval;procedure_controller_finish;
    procedure_eval_exec;FST;SND;ARITH_EQ]);;

let PROCEDURE_CONTROLLER_FRAME_INVALID = prove
 (`!call_tag fn P b cap depth st sts i cw args clauses (s:A) used.
    call_tag < val(EL 0 st) ==>
    procedure_controller_frame_eval call_tag fn (procedure_eval_call (cap - (depth + 1)) call_tag fn P b) b
      (ProcedureWorkFrame (CONS st sts) i cw args clauses) s used =
    procedure_eval_boundary(3,cw 7,s,used)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[procedure_controller_frame_eval;procedure_eval_exec;
    procedure_controller_finish;FST;SND;ARITH_EQ]);;

let PROCEDURE_CONTROLLER_FRAME_PRIMITIVE = prove
 (`!call_tag fn P b cap depth st sts i cw args clauses (s:A) used k pay s1 used1.
    val(EL 0 st) < call_tag /\ fn b st cw s used = (k,pay,s1,used1) ==>
    procedure_controller_frame_eval call_tag fn (procedure_eval_call (cap - (depth + 1)) call_tag fn P b) b
      (ProcedureWorkFrame (CONS st sts) i cw args clauses) s used =
    procedure_controller_phase_eval call_tag fn P b cap depth
      (procedure_controller_after (ProcedureWorkFrame (CONS st sts) i cw args clauses) k pay) s1 used1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[PROCEDURE_CONTROLLER_AFTER;procedure_controller_frame_eval;procedure_eval_exec] THEN
  ASM_SIMP_TAC[ARITH_RULE `(n:num) < call_tag ==> ~(call_tag < n) /\ ~(n = call_tag)`;
    LET_DEF;LET_END_DEF;FST;SND] THEN
  ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[]);;

let PROCEDURE_CONTROLLER_ENTER = prove
 (`!call_tag fn P b cap depth pid args (s:A) used.
    depth < cap /\ pid < LENGTH P /\ used < b ==>
    procedure_controller_phase_eval call_tag fn P b cap depth (ProcedureEnter pid args) s used =
    procedure_controller_phase_eval call_tag fn P b cap depth
      (procedure_controller_choose (EL pid P) args) s (used + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[procedure_controller_phase_eval;PROCEDURE_EVAL_ENTER;PROCEDURE_CONTROLLER_CHOOSE]);;

let PROCEDURE_CONTROLLER_FRAME_CALL = prove
 (`!call_tag fn P b cap depth st sts i cw args clauses (s:A) used k pay s1 used1.
    val(EL 0 st) = call_tag /\
    procedure_eval_call (cap - (depth + 1)) call_tag fn P b
      (val(EL 1 st)) (procedure_args st cw) s used = (k,pay,s1,used1) ==>
    procedure_controller_frame_eval call_tag fn (procedure_eval_call (cap - (depth + 1)) call_tag fn P b) b
      (ProcedureWorkFrame (CONS st sts) i cw args clauses) s used =
    procedure_controller_phase_eval call_tag fn P b cap depth
      (procedure_controller_after (ProcedureWorkFrame (CONS st sts) i cw args clauses)
        (procedure_call_outcome k) pay) s1 used1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`call_tag:num`;`cap - (depth + 1)`;`fn:num->int64 list->(num->num)->A->num->num#num#A#num`;
      `P:(((int64 list)list)list)list`;`b:num`;`val(EL 1 (st:int64 list))`;
      `procedure_args st cw`;`s:A`;`used:num`] PROCEDURE_EVAL_CALL_NOT_REFUSED) THEN
    ASM_REWRITE_TAC[FST];ALL_TAC] THEN
  ASM_REWRITE_TAC[procedure_call_outcome;PROCEDURE_CONTROLLER_AFTER;
    procedure_controller_frame_eval;procedure_eval_exec;LT_REFL;
    LET_DEF;LET_END_DEF;FST;SND] THEN
  ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[]);;

let PROCEDURE_RESULT_EXHAUSTIVE = prove
 (`!r:num#num#A#num. ?k pay s used. r = (k,pay,s,used)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]);;

let PROCEDURE_CONTROLLER_CALL = prove
 (`!call_tag fn P b cap st sts i cw args clauses stack (s:A) used.
    val(EL 0 st) = call_tag ==>
    procedure_controller_meaning call_tag fn P b cap
      (ProcedureRun (ProcedureWorkFrame (CONS st sts) i cw args clauses)) stack s used =
    procedure_controller_meaning call_tag fn P b cap
      (ProcedureEnter (val(EL 1 st)) (procedure_args st cw))
      (CONS (ProcedureWorkFrame (CONS st sts) i cw args clauses) stack) s used`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC
   `procedure_eval_call (cap - (LENGTH(stack:procedure_work_frame list) + 1)) call_tag
     (fn:num->int64 list->(num->num)->A->num->num#num#A#num) P b
     (val(EL 1 st)) (procedure_args st cw) s used`
   PROCEDURE_RESULT_EXHAUSTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `pay:num`
    (X_CHOOSE_THEN `s1:A` (X_CHOOSE_THEN `used1:num` ASSUME_TAC)))) THEN
  ASM_SIMP_TAC[procedure_controller_meaning;procedure_controller_unwind;
    procedure_controller_phase_eval;LENGTH;ADD1;FST;SND;PROCEDURE_CONTROLLER_FRAME_CALL]);;

let PROCEDURE_CONTROLLER_ENTER_ACTION = prove
 (`!call_tag fn P b cap depth pid args (s:A) used.
    procedure_controller_phase_eval call_tag fn P b cap depth (ProcedureEnter pid args) s used =
    if b < used then procedure_controller_phase_eval call_tag fn P b cap depth (ProcedureReturn 3 3) s used
    else if LENGTH P <= pid then procedure_controller_phase_eval call_tag fn P b cap depth (ProcedureReturn 3 3) s used
    else if cap <= depth then procedure_controller_phase_eval call_tag fn P b cap depth (ProcedureReturn 2 0) s used
    else if used = b then procedure_controller_phase_eval call_tag fn P b cap depth (ProcedureReturn 4 4) s used
    else procedure_controller_phase_eval call_tag fn P b cap depth
      (procedure_controller_choose (EL pid P) args) s (used + 1)`,
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[procedure_controller_phase_eval;PROCEDURE_EVAL_BAD_RECEIPT;
    PROCEDURE_EVAL_BAD_TARGET;PROCEDURE_EVAL_FULL;PROCEDURE_EVAL_EXHAUSTED;
    PROCEDURE_EVAL_ENTER;PROCEDURE_CONTROLLER_CHOOSE;
    procedure_eval_boundary;procedure_call_outcome;FST;SND;ARITH_EQ;
    ARITH_RULE `~(b < u) ==> u <= b`;
    ARITH_RULE `~(n <= p) ==> p < n`;
    ARITH_RULE `c <= d ==> c - d = 0`;
    ARITH_RULE `~(c <= d) ==> d < c /\ 0 < c - d`;
    ARITH_RULE `~(b < u) /\ ~(u = b) ==> u < b`]);;

let PROCEDURE_CONTROLLER_STATE_EQ_TAC =
  REWRITE_TAC[option_INJ;PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN
    (fun th -> if is_var(rhs(concl th)) then SUBST_ALL_TAC(GSYM th) else SUBST_ALL_TAC th));;

let PROCEDURE_CONTROLLER_STEP = prove
 (`!phase call_tag fn P b cap stack (s:A) used phase1 stack1 s1 used1.
    procedure_controller_step call_tag fn P b cap phase stack s used = SOME(phase1,stack1,s1,used1)
    ==> procedure_controller_meaning call_tag fn P b cap phase stack s used =
        procedure_controller_meaning call_tag fn P b cap phase1 stack1 s1 used1`,
  MATCH_MP_TAC procedure_controller_phase_INDUCT THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`pid:num`;`args:num list`] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[procedure_controller_step] THEN REPEAT COND_CASES_TAC THEN
    PROCEDURE_CONTROLLER_STATE_EQ_TAC THEN
    ASM_REWRITE_TAC[procedure_controller_meaning;PROCEDURE_CONTROLLER_ENTER_ACTION];
    MATCH_MP_TAC procedure_work_frame_INDUCT THEN
    MAP_EVERY X_GEN_TAC [`plan:(int64 list)list`;`i:num`;`cw:num->num`;
                        `args:num list`;`clauses:((int64 list)list)list`] THEN
    REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `plan:(int64 list)list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `st:int64 list` (X_CHOOSE_THEN `sts:(int64 list)list` SUBST_ALL_TAC))) THENL
     [REWRITE_TAC[procedure_controller_step] THEN PROCEDURE_CONTROLLER_STATE_EQ_TAC THEN
      REWRITE_TAC[procedure_controller_meaning;procedure_controller_phase_eval;
        PROCEDURE_CONTROLLER_FRAME_NIL];
      ASM_CASES_TAC `call_tag < val(EL 0 (st:int64 list))` THENL
       [ASM_REWRITE_TAC[procedure_controller_step] THEN PROCEDURE_CONTROLLER_STATE_EQ_TAC THEN
        ASM_SIMP_TAC[procedure_controller_meaning;procedure_controller_phase_eval;
          PROCEDURE_CONTROLLER_FRAME_INVALID];ALL_TAC] THEN
      ASM_CASES_TAC `val(EL 0 (st:int64 list)) = call_tag` THENL
       [ASM_REWRITE_TAC[procedure_controller_step] THEN PROCEDURE_CONTROLLER_STATE_EQ_TAC THEN
        MATCH_MP_TAC PROCEDURE_CONTROLLER_CALL THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
      SUBGOAL_THEN `val(EL 0 (st:int64 list)) < call_tag` ASSUME_TAC THENL
       [ASM_ARITH_TAC;ALL_TAC] THEN
      MP_TAC(ISPEC
       `(fn:num->int64 list->(num->num)->A->num->num#num#A#num) b st cw s used`
       PROCEDURE_RESULT_EXHAUSTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `pay:num`
        (X_CHOOSE_THEN `s2:A` (X_CHOOSE_THEN `used2:num` ASSUME_TAC)))) THEN
      ASM_REWRITE_TAC[procedure_controller_step;LET_DEF;LET_END_DEF;FST;SND] THEN
      PROCEDURE_CONTROLLER_STATE_EQ_TAC THEN
      REWRITE_TAC[procedure_controller_meaning;procedure_controller_phase_eval] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC PROCEDURE_CONTROLLER_FRAME_PRIMITIVE THEN
      ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`k:num`;`pay:num`] THEN REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `stack:procedure_work_frame list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `caller:procedure_work_frame`
        (X_CHOOSE_THEN `rest:procedure_work_frame list` SUBST_ALL_TAC))) THENL
     [REWRITE_TAC[procedure_controller_step;option_DISTINCT];
      REWRITE_TAC[procedure_controller_step] THEN PROCEDURE_CONTROLLER_STATE_EQ_TAC THEN
      MATCH_ACCEPT_TAC PROCEDURE_CONTROLLER_RETURN]]);;

let procedure_controller_theorems =
 ["PROCEDURE_CALL_OUTCOME_IDEMPOTENT",PROCEDURE_CALL_OUTCOME_IDEMPOTENT;
  "PROCEDURE_CONTROLLER_INITIAL",PROCEDURE_CONTROLLER_INITIAL;
  "PROCEDURE_CONTROLLER_RETURN",PROCEDURE_CONTROLLER_RETURN;
  "PROCEDURE_CONTROLLER_CHOOSE",PROCEDURE_CONTROLLER_CHOOSE;
  "PROCEDURE_EVAL_CALL_NOT_REFUSED",PROCEDURE_EVAL_CALL_NOT_REFUSED;
  "PROCEDURE_CONTROLLER_AFTER",PROCEDURE_CONTROLLER_AFTER;
  "PROCEDURE_CONTROLLER_FRAME_NIL",PROCEDURE_CONTROLLER_FRAME_NIL;
  "PROCEDURE_CONTROLLER_FRAME_INVALID",PROCEDURE_CONTROLLER_FRAME_INVALID;
  "PROCEDURE_CONTROLLER_FRAME_PRIMITIVE",PROCEDURE_CONTROLLER_FRAME_PRIMITIVE;
  "PROCEDURE_CONTROLLER_ENTER",PROCEDURE_CONTROLLER_ENTER;
  "PROCEDURE_CONTROLLER_FRAME_CALL",PROCEDURE_CONTROLLER_FRAME_CALL;
  "PROCEDURE_RESULT_EXHAUSTIVE",PROCEDURE_RESULT_EXHAUSTIVE;
  "PROCEDURE_CONTROLLER_CALL",PROCEDURE_CONTROLLER_CALL;
  "PROCEDURE_CONTROLLER_ENTER_ACTION",PROCEDURE_CONTROLLER_ENTER_ACTION;
  "PROCEDURE_CONTROLLER_STEP",PROCEDURE_CONTROLLER_STEP];;
