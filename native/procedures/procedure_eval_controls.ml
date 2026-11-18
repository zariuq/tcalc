(* Recursive calls, exact receipts and retained effects on failed clauses. *)
needs "native/procedures/procedure_eval.ml";;
needs "native/procedures/procedure_controls.ml";;

let procedure_countdown_step = new_definition
 `procedure_countdown_step op dst =
   [word op;word 0;word 0;word 0;word 0;word 0;word 0;word 0;word 0;
    word 0;word 8;word 9;word 10;word 11;word 12;word 13;word 14;word dst]:int64 list`;;

let procedure_countdown_leaf = new_definition
 `procedure_countdown_leaf (b:num) (st:int64 list) (cw:num->num) (s:num) (used:num) =
   if used < b then
     if val(EL 0 st) = 0 then ((if cw 8 = 0 then 1 else 0),0,s,used + 1)
     else if val(EL 0 st) = 1 then (1,cw 8 - 1,s,used + 1)
     else if val(EL 0 st) = 2 then (1,cw 7 + 1,s,used + 1)
     else (3,3,s,used)
   else (4,4,s,used)`;;

let procedure_countdown_program = new_definition
 `procedure_countdown_program =
   [[[procedure_countdown_step 0 7];
     [procedure_countdown_step 1 8;procedure_countdown_step 32 7;
      procedure_countdown_step 2 7]]]`;;

let procedure_countdown_unrolls =
  CONJUNCT1 procedure_eval_call ::
  map (fun n -> CONV_RULE NUM_REDUCE_CONV
       (INST [mk_small_numeral n,`n:num`] (CONJUNCT2 procedure_eval_call)))
      [0;1;2;3];;

let procedure_countdown_eval_conv =
  let cs = Compute.bool_compset() in
  Compute.set_skip cs `COND:bool->A->A->A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_conv (`EL:num->A list->A`,2,EL_CONV) cs;
  Compute.add_conv (`val:N word->num`,1,WORD_RED_CONV) cs;
  Compute.add_thms
   (procedure_countdown_unrolls @
    [procedure_countdown_program;procedure_countdown_step;procedure_countdown_leaf;
     procedure_eval_exec;procedure_eval_choose;procedure_eval_boundary;
     procedure_call_outcome;procedure_args;procedure_frame;procedure_set;
     LENGTH;FST;SND;LET_END_DEF]) cs;
  Compute.CBV_CONV cs;;

let PROCEDURE_COUNTDOWN_EVAL_TAC =
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV procedure_countdown_eval_conv) THEN REFL_TAC;;

let PROCEDURE_COUNTDOWN_RETURNS = prove
 (`!s. procedure_eval_call 4 32 procedure_countdown_leaf procedure_countdown_program 14 0
       [3;0;0;0;0;0;0] s 0 = (1,3,s,14)`,
  PROCEDURE_COUNTDOWN_EVAL_TAC);;

let PROCEDURE_COUNTDOWN_STACK_BOUNDARY = prove
 (`!s. procedure_eval_call 3 32 procedure_countdown_leaf procedure_countdown_program 14 0
       [3;0;0;0;0;0;0] s 0 = (2,0,s,9)`,
  PROCEDURE_COUNTDOWN_EVAL_TAC);;

let PROCEDURE_COUNTDOWN_FUEL_BOUNDARY = prove
 (`!s. procedure_eval_call 4 32 procedure_countdown_leaf procedure_countdown_program 13 0
       [3;0;0;0;0;0;0] s 0 = (4,4,s,13)`,
  PROCEDURE_COUNTDOWN_EVAL_TAC);;

let PROCEDURE_COUNTDOWN_ENTRY_BOUNDARIES = prove
 (`!s.
    procedure_eval_call 0 32 procedure_countdown_leaf procedure_countdown_program 0 0
      [3;0;0;0;0;0;0] s 0 = (2,0,s,0) /\
    procedure_eval_call 1 32 procedure_countdown_leaf procedure_countdown_program 0 0
      [3;0;0;0;0;0;0] s 0 = (4,4,s,0) /\
    procedure_eval_call 0 32 procedure_countdown_leaf procedure_countdown_program 0 1
      [3;0;0;0;0;0;0] s 0 = (3,3,s,0) /\
    procedure_eval_call 0 32 procedure_countdown_leaf procedure_countdown_program 0 0
      [3;0;0;0;0;0;0] s 1 = (3,3,s,1)`,
  GEN_TAC THEN REPEAT CONJ_TAC THEN PROCEDURE_COUNTDOWN_EVAL_TAC);;

let procedure_prepare_refuse_fn = new_definition
 `procedure_prepare_refuse_fn b (st:int64 list) (cw:num->num) (n:num) used =
    if used + 2 <= b then (0,0,n + 1,used + 2) else (4,4,n,used)`;;

let PROCEDURE_PREPARE_FUNCTION = prove
 (`procedure_prepare_refuse = procedure_function_leaf procedure_prepare_refuse_fn`,
  REWRITE_TAC[FUN_EQ_THM;procedure_prepare_refuse;procedure_function_leaf;
              procedure_prepare_refuse_fn] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let PROCEDURE_EVAL_REFUSAL_PREFIX_KEPT =
  REWRITE_RULE[PROCEDURE_PREPARE_FUNCTION;PROCEDURE_EVAL_CALL_EXACT;SUB_0]
    PROCEDURE_REFUSAL_PREFIX_KEPT;;

let procedure_eval_controls_theorems =
 ["PROCEDURE_COUNTDOWN_RETURNS",PROCEDURE_COUNTDOWN_RETURNS;
  "PROCEDURE_COUNTDOWN_STACK_BOUNDARY",PROCEDURE_COUNTDOWN_STACK_BOUNDARY;
  "PROCEDURE_COUNTDOWN_FUEL_BOUNDARY",PROCEDURE_COUNTDOWN_FUEL_BOUNDARY;
  "PROCEDURE_COUNTDOWN_ENTRY_BOUNDARIES",PROCEDURE_COUNTDOWN_ENTRY_BOUNDARIES;
  "PROCEDURE_PREPARE_FUNCTION",PROCEDURE_PREPARE_FUNCTION;
  "PROCEDURE_EVAL_REFUSAL_PREFIX_KEPT",PROCEDURE_EVAL_REFUSAL_PREFIX_KEPT];;
