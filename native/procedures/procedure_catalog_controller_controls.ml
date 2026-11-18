(* Calls beyond ordinal 32, with named primitives and the same receipts. *)
needs "native/procedures/procedure_catalog_controller.ml";;

let procedure_countdown_tagged_program = new_definition
 `procedure_countdown_tagged_program call_tag =
   [[[procedure_countdown_step 0 7];
     [procedure_countdown_step 1 8;procedure_countdown_step call_tag 7;
      procedure_countdown_step 2 7]]]`;;

let procedure_countdown_operations = define
 `(procedure_countdown_operations (KernelOperation k) b fields cw (s:num) used =
    procedure_countdown_leaf b (CONS (word k) fields) cw s used) /\
  (procedure_countdown_operations (ReaderOperation k) b fields cw s used = (3,3,s,used)) /\
  (procedure_countdown_operations ProcedureCallMarker b fields cw s used = (3,3,s,used))`;;

let PROCEDURE_COUNTDOWN_PROFILE32_DATA = prove
 (`procedure_countdown_tagged_program 32 = procedure_countdown_program`,
  REWRITE_TAC[procedure_countdown_tagged_program;procedure_countdown_program]);;

let procedure_catalog_controls_conv =
  let cs = Compute.bool_compset() in
  Compute.set_skip cs `COND:bool->A->A->A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_conv (`EL:num->A list->A`,2,EL_CONV) cs;
  Compute.add_conv (`val:N word->num`,1,WORD_RED_CONV) cs;
  Compute.add_thms
   (procedure_countdown_unrolls @ [procedure_eval_exec;procedure_eval_choose;procedure_eval_boundary;
    PROCEDURE_CONTROLLER_ITER_EVAL;procedure_controller_tick;
    procedure_controller_tick_result;procedure_controller_next;
    procedure_controller_step;procedure_controller_after;procedure_controller_choose;
    procedure_catalog_run;procedure_catalog_call_tag;procedure_catalog_primitive;
    procedure_catalog_forty;procedure_countdown_tagged_program;procedure_countdown_operations;
    procedure_countdown_program;procedure_countdown_step;procedure_countdown_leaf;
    procedure_call_outcome;procedure_args;procedure_frame;procedure_set;
    LENGTH;TL;FST;SND;LET_END_DEF]) cs;
  Compute.add_thms
   [REWRITE_RULE[procedure_catalog_forty] (CONJUNCT1 PROCEDURE_CATALOG_FORTY_INHABITED)] cs;
  Compute.CBV_CONV cs;;

let PROCEDURE_CATALOG_CONTROL_TAC =
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV procedure_catalog_controls_conv) THEN REFL_TAC;;

let PROCEDURE_CATALOG_FORTY_RECURSION = prove
 (`!s. procedure_catalog_run 4 procedure_catalog_forty procedure_countdown_operations
    (procedure_countdown_tagged_program 40) 14 0 [3;0;0;0;0;0;0] s 0 = (1,3,s,14)`,
  PROCEDURE_CATALOG_CONTROL_TAC);;

let PROCEDURE_CATALOG_FORTY_STACK = prove
 (`!s. procedure_catalog_run 3 procedure_catalog_forty procedure_countdown_operations
    (procedure_countdown_tagged_program 40) 14 0 [3;0;0;0;0;0;0] s 0 = (2,0,s,9)`,
  PROCEDURE_CATALOG_CONTROL_TAC);;

let PROCEDURE_CATALOG_FORTY_FUEL = prove
 (`!s. procedure_catalog_run 4 procedure_catalog_forty procedure_countdown_operations
    (procedure_countdown_tagged_program 40) 13 0 [3;0;0;0;0;0;0] s 0 = (4,4,s,13)`,
  PROCEDURE_CATALOG_CONTROL_TAC);;

let PROCEDURE_CATALOG_OLD_TAG_IS_PRIMITIVE = prove
 (`!s. procedure_catalog_run 4 procedure_catalog_forty procedure_countdown_operations
    procedure_countdown_program 14 0 [3;0;0;0;0;0;0] s 0 = (3,3,s,3)`,
  PROCEDURE_CATALOG_CONTROL_TAC);;

let PROCEDURE_CATALOG_FORTY_CONTROLLER = prove
 (`!s. procedure_controller_iter 32 (procedure_catalog_call_tag procedure_catalog_forty)
    (procedure_catalog_primitive procedure_catalog_forty procedure_countdown_operations)
    (procedure_countdown_tagged_program 40) 14 4
    (ProcedureEnter 0 [3;0;0;0;0;0;0],[],s,0) = (ProcedureReturn 1 3,[],s,14)`,
  PROCEDURE_CATALOG_CONTROL_TAC);;

let procedure_catalog_controller_controls_theorems =
 ["PROCEDURE_COUNTDOWN_PROFILE32_DATA",PROCEDURE_COUNTDOWN_PROFILE32_DATA;
  "PROCEDURE_CATALOG_FORTY_RECURSION",PROCEDURE_CATALOG_FORTY_RECURSION;
  "PROCEDURE_CATALOG_FORTY_STACK",PROCEDURE_CATALOG_FORTY_STACK;
  "PROCEDURE_CATALOG_FORTY_FUEL",PROCEDURE_CATALOG_FORTY_FUEL;
  "PROCEDURE_CATALOG_OLD_TAG_IS_PRIMITIVE",PROCEDURE_CATALOG_OLD_TAG_IS_PRIMITIVE;
  "PROCEDURE_CATALOG_FORTY_CONTROLLER",PROCEDURE_CATALOG_FORTY_CONTROLLER];;
