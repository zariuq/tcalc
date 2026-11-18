(* ABI data checked against the independent runtime and machine contracts. *)
needs "native/abi/native_abi_decl_load.ml";;
needs "native/driver/component_driver.ml";;
needs "native/driver/native_component_stack.ml";;
needs "native/procedures/procedure_rules.ml";;

let NATIVE_ABI_WORD_BITS = prove
 (`dimindex(:64) = 8 * native_abi_WordBytes`,
  REWRITE_TAC (DIMINDEX_64::native_abi_definitions) THEN CONV_TAC NUM_REDUCE_CONV);;

let NATIVE_ABI_COMPONENT_ENTRY = prove
 (`!c t. component_entry c t <=>
    val(tisa_frame t) + native_abi_FrameBytes <= 2 EXP 64 /\
    val(tisa_fword t native_abi_RuntimeFrame_fuel_used) <=
      val(tisa_fword t native_abi_RuntimeFrame_fuel_budget) /\
    tisa_decls_ok t 0 (component_decls c) /\ tisa_init_ok t (component_inits c)`,
  REWRITE_TAC (component_entry::native_abi_definitions));;

let NATIVE_ABI_DRIVER_SIZE = prove
 (`LENGTH drv_mc = native_abi_DriverCodeBytes`,
  REWRITE_TAC (COMPUTE_LENGTH_RULE drv_mc::native_abi_definitions));;

let NATIVE_ABI_COMPONENT_STATUS = prove
 (`!c t k u. component_ok c /\ component_entry c t /\ component_run c t = TStop k u
     ==> tisa_fword u native_abi_RuntimeFrame_status = word k`,
  REWRITE_TAC native_abi_definitions THEN MATCH_ACCEPT_TAC COMPONENT_RUN_STATUS);;

let NATIVE_ABI_STACK_PROFILE = prove
 (`!c mc pc. component_stack_image native_abi_LeafStackSaveBytes c mc pc <=> component_image c mc pc`,
  REWRITE_TAC native_abi_definitions THEN MATCH_ACCEPT_TAC COMPONENT_STACK_BASE_IMAGE);;

let NATIVE_ABI_DRIVER_WORDS = prove
 (`!m d plan ns ctl bind leaves budget used stepl bw nbw lpc nl.
    drv_holds m d plan ns ctl bind leaves budget used stepl bw nbw lpc nl
    ==> drv_word m (word_add d (word(native_abi_WordBytes * native_abi_DriveDescriptor_budget))) = budget /\
        drv_word m (word_add d (word(native_abi_WordBytes * native_abi_DriveDescriptor_used))) = used /\
        drv_word m (word_add d (word(native_abi_WordBytes * native_abi_DriveDescriptor_ctl))) = ctl /\
        drv_word m (word_add d (word(native_abi_WordBytes * native_abi_DriveDescriptor_bind))) = bind /\
        drv_word m (word_add d (word(native_abi_WordBytes * native_abi_DriveDescriptor_leaves))) = leaves`,
  REWRITE_TAC (drv_holds::native_abi_definitions) THEN
  CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

let NATIVE_ABI_STEP_FIELDS = prove
 (`!progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw st.
    component_step_ok progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw st
    ==> LENGTH st = native_abi_StepWords /\
        val(EL native_abi_DriveStep_leaf st) < nl /\
        val(EL native_abi_DriveStep_dst st) < nctl`,
  REWRITE_TAC (component_step_ok::native_abi_definitions) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `17` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `10`)) (concl th) && can (find_term ((=) `nctl:num`)) (concl th))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let NATIVE_ABI_PROCEDURE_RESULT = prove
 (`!args. procedure_frame args native_abi_ProcedureControls_result = 0`,
  REWRITE_TAC native_abi_definitions THEN MATCH_ACCEPT_TAC PROCEDURE_FRAME_RESULT);;

let native_abi_contract_theorems =
 ["NATIVE_ABI_WORD_BITS",NATIVE_ABI_WORD_BITS;
  "NATIVE_ABI_COMPONENT_ENTRY",NATIVE_ABI_COMPONENT_ENTRY;
  "NATIVE_ABI_DRIVER_SIZE",NATIVE_ABI_DRIVER_SIZE;
  "NATIVE_ABI_COMPONENT_STATUS",NATIVE_ABI_COMPONENT_STATUS;
  "NATIVE_ABI_STACK_PROFILE",NATIVE_ABI_STACK_PROFILE;
  "NATIVE_ABI_DRIVER_WORDS",NATIVE_ABI_DRIVER_WORDS;
  "NATIVE_ABI_STEP_FIELDS",NATIVE_ABI_STEP_FIELDS;
  "NATIVE_ABI_PROCEDURE_RESULT",NATIVE_ABI_PROCEDURE_RESULT];;
