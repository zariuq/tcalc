(* The exported sub1 program inhabits the typed profile, but not U64-only. *)
needs "native/driver/native_component_typed_p1.ml";;
needs "native/driver/mm_sub1_component_program.ml";;

let MM_SUB1_COMPONENT_POINTER_INPUTS = prove
 (`tisa_inits mm_sub1_component_program =
    [(1,TyPtr,0);(2,TyPtr,1);(3,TyPtr,2);(4,TyPtr,3);(5,TyPtr,4)]`,
  REWRITE_TAC[MM_SUB1_COMPONENT_TERM;tisa_inits]);;

let MM_SUB1_COMPONENT_WF = prove
 (`component_p1_wf mm_sub1_component_program`,
  REWRITE_TAC[component_p1_wf;MM_SUB1_COMPONENT_TERM;tisa_decls;tisa_root;
    tisa_stmt_ok;tisa_instr_ok;tisa_rw;tisa_readable;LENGTH;EL;HD;TL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[FST;SND] THEN CONV_TAC NUM_REDUCE_CONV);;

let MM_SUB1_COMPONENT_TYPED_OK = prove
 (`component_typed_ok (component_of_p1 mm_sub1_component_program)`,
  MATCH_MP_TAC COMPONENT_P1_TYPED_OK THEN MATCH_ACCEPT_TAC MM_SUB1_COMPONENT_WF);;

let MM_SUB1_COMPONENT_NOT_U64_PROFILE = prove
 (`~component_ok (component_of_p1 mm_sub1_component_program)`,
  REWRITE_TAC[COMPONENT_U64_PROFILE;COMPONENT_P1_FIELDS;MM_SUB1_COMPONENT_POINTER_INPUTS;
    ALL;distinctness "tisa_ty"]);;

let native_component_typed_client_theorems = native_component_typed_p1_theorems @
 ["MM_SUB1_COMPONENT_POINTER_INPUTS",MM_SUB1_COMPONENT_POINTER_INPUTS;
  "MM_SUB1_COMPONENT_WF",MM_SUB1_COMPONENT_WF;
  "MM_SUB1_COMPONENT_TYPED_OK",MM_SUB1_COMPONENT_TYPED_OK;
  "MM_SUB1_COMPONENT_NOT_U64_PROFILE",MM_SUB1_COMPONENT_NOT_U64_PROFILE];;
