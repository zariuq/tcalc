(* Concrete controller iterations with recursion, retries and resource exits. *)
needs "native/procedures/procedure_controller_runs.ml";;
needs "native/procedures/procedure_eval_controls.ml";;

let procedure_controller_retry_program = new_definition
 `procedure_controller_retry_program =
   [[[procedure_countdown_step 1 8;procedure_countdown_step 0 7];
     [procedure_countdown_step 1 7]]]`;;

let procedure_controller_controls_conv =
  let cs = Compute.bool_compset() in
  Compute.set_skip cs `COND:bool->A->A->A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_conv (`EL:num->A list->A`,2,EL_CONV) cs;
  Compute.add_conv (`val:N word->num`,1,WORD_RED_CONV) cs;
  Compute.add_thms
   [PROCEDURE_CONTROLLER_ITER_EVAL;procedure_controller_tick;
    procedure_controller_tick_result;procedure_controller_next;
    procedure_controller_step;procedure_controller_after;procedure_controller_choose;
    procedure_controller_retry_program;procedure_countdown_program;
    procedure_countdown_step;procedure_countdown_leaf;
    procedure_prepare_refuse_fn;procedure_guard_step;
    procedure_call_outcome;procedure_args;procedure_frame;procedure_set;
    LENGTH;FST;SND;LET_END_DEF] cs;
  Compute.CBV_CONV cs;;

let PROCEDURE_CONTROLLER_CONTROLS_TAC =
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV procedure_controller_controls_conv) THEN REFL_TAC;;

let PROCEDURE_CONTROLLER_RECURSIVE_RETURN = prove
 (`!s. procedure_controller_iter 32 32 procedure_countdown_leaf procedure_countdown_program 14 4
    (ProcedureEnter 0 [3;0;0;0;0;0;0],[],s,0) = (ProcedureReturn 1 3,[],s,14)`,
  PROCEDURE_CONTROLLER_CONTROLS_TAC);;

let PROCEDURE_CONTROLLER_STACK_CONTROL = prove
 (`!s. procedure_controller_iter 32 32 procedure_countdown_leaf procedure_countdown_program 14 3
    (ProcedureEnter 0 [3;0;0;0;0;0;0],[],s,0) = (ProcedureReturn 2 0,[],s,9)`,
  PROCEDURE_CONTROLLER_CONTROLS_TAC);;

let PROCEDURE_CONTROLLER_FUEL_CONTROL = prove
 (`!s. procedure_controller_iter 32 32 procedure_countdown_leaf procedure_countdown_program 13 4
    (ProcedureEnter 0 [3;0;0;0;0;0;0],[],s,0) = (ProcedureReturn 4 4,[],s,13)`,
  PROCEDURE_CONTROLLER_CONTROLS_TAC);;

let PROCEDURE_CONTROLLER_ARGUMENT_RETRY = prove
 (`!s. procedure_controller_iter 8 32 procedure_countdown_leaf procedure_controller_retry_program 4 1
    (ProcedureEnter 0 [2;0;0;0;0;0;0],[],s,0) = (ProcedureReturn 1 1,[],s,4)`,
  PROCEDURE_CONTROLLER_CONTROLS_TAC);;

let PROCEDURE_CONTROLLER_PREFIX_KEPT = prove
 (`!n. procedure_controller_iter 8 32 procedure_prepare_refuse_fn [[[procedure_guard_step];[]]] 3 1
    (ProcedureEnter 0 [4;0;0;0;0;0;0],[],n,0) = (ProcedureReturn 1 0,[],n + 1,3)`,
  PROCEDURE_CONTROLLER_CONTROLS_TAC);;

let PROCEDURE_CONTROLLER_ENTRY_CONTROLS = prove
 (`!s.
    procedure_controller_iter 2 32 procedure_countdown_leaf procedure_countdown_program 0 0
      (ProcedureEnter 0 [3;0;0;0;0;0;0],[],s,0) = (ProcedureReturn 2 0,[],s,0) /\
    procedure_controller_iter 2 32 procedure_countdown_leaf procedure_countdown_program 0 1
      (ProcedureEnter 0 [3;0;0;0;0;0;0],[],s,0) = (ProcedureReturn 4 4,[],s,0) /\
    procedure_controller_iter 2 32 procedure_countdown_leaf procedure_countdown_program 0 0
      (ProcedureEnter 1 [3;0;0;0;0;0;0],[],s,0) = (ProcedureReturn 3 3,[],s,0) /\
    procedure_controller_iter 2 32 procedure_countdown_leaf procedure_countdown_program 0 0
      (ProcedureEnter 0 [3;0;0;0;0;0;0],[],s,1) = (ProcedureReturn 3 3,[],s,1)`,
  GEN_TAC THEN REPEAT CONJ_TAC THEN PROCEDURE_CONTROLLER_CONTROLS_TAC);;

let procedure_controller_controls_theorems =
 ["PROCEDURE_CONTROLLER_RECURSIVE_RETURN",PROCEDURE_CONTROLLER_RECURSIVE_RETURN;
  "PROCEDURE_CONTROLLER_STACK_CONTROL",PROCEDURE_CONTROLLER_STACK_CONTROL;
  "PROCEDURE_CONTROLLER_FUEL_CONTROL",PROCEDURE_CONTROLLER_FUEL_CONTROL;
  "PROCEDURE_CONTROLLER_ARGUMENT_RETRY",PROCEDURE_CONTROLLER_ARGUMENT_RETRY;
  "PROCEDURE_CONTROLLER_PREFIX_KEPT",PROCEDURE_CONTROLLER_PREFIX_KEPT;
  "PROCEDURE_CONTROLLER_ENTRY_CONTROLS",PROCEDURE_CONTROLLER_ENTRY_CONTROLS];;
