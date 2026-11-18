(* Module control-word roles are checked against the existing HOLR plans. *)
needs "native/abi/native_abi_core_basis.ml";;

let NATIVE_ABI_CORE_READER = prove
 (`EL native_abi_DriveStep_dst (HD pl_plan_dd) = word native_abi_CoreControls_reader_state /\
   EL native_abi_DriveStep_dst (HD(TL pl_plan_dd)) = word native_abi_CoreControls_opcode /\
   EL native_abi_DriveStep_arg0 (HD pl_prefix_op0) = word native_abi_CoreControls_header /\
   EL native_abi_DriveStep_arg0 (HD pl_inc_cnt) = word native_abi_CoreControls_count /\
   EL native_abi_DriveStep_dst (HD pl_inc_cnt) = word native_abi_CoreControls_count`,
  REWRITE_TAC (pl_plan_dd::pl_prefix_op0::pl_inc_cnt::native_abi_definitions) THEN
  REWRITE_TAC[HD;TL] THEN CONV_TAC STEP_EL_CONV2);;

let NATIVE_ABI_CORE_END = prove
 (`EL native_abi_DriveStep_dst (HD(TL pl_end_d)) = word native_abi_CoreControls_end /\
   EL native_abi_DriveStep_arg0 (HD pl_end_a) = word native_abi_CoreControls_header /\
   EL native_abi_DriveStep_hot_1 (HD(TL pl_end_a)) = word native_abi_CoreControls_fnv`,
  REWRITE_TAC (pl_end_a::pl_end_d::native_abi_definitions) THEN
  REWRITE_TAC[HD;TL] THEN CONV_TAC STEP_EL_CONV2);;

let NATIVE_ABI_CORE_HEADER = prove
 (`EL native_abi_DriveStep_dst (HD pl_hdr_g) = word native_abi_CoreControls_header /\
   EL native_abi_DriveStep_arg0 (HD(TL pl_hdr_p)) = word native_abi_CoreControls_policy /\
   EL native_abi_DriveStep_dst (HD pl_hdr_commit) = word native_abi_CoreControls_policy`,
  REWRITE_TAC (pl_hdr_g::pl_hdr_p::pl_hdr_commit::native_abi_definitions) THEN
  REWRITE_TAC[HD;TL] THEN CONV_TAC STEP_EL_CONV2);;

let NATIVE_ABI_CORE_POLICY = prove
 (`EL native_abi_DriveStep_arg0 (HD pl_plan_policy) = word native_abi_CoreControls_policy /\
   EL native_abi_DriveStep_dst (HD(TL pl_plan_policy)) = word native_abi_CoreControls_policy`,
  REWRITE_TAC (pl_plan_policy::native_abi_definitions) THEN
  REWRITE_TAC[HD;TL] THEN CONV_TAC STEP_EL_CONV2);;

let NATIVE_ABI_ARGUMENTS = prove
 (`!st cw. procedure_args st cw =
    [cw(val(EL native_abi_DriveStep_arg0 st));cw(val(EL native_abi_DriveStep_arg1 st));
     cw(val(EL native_abi_DriveStep_hot_1 st));cw(val(EL native_abi_DriveStep_hot_2 st));
     cw(val(EL native_abi_DriveStep_hot_3 st));cw(val(EL native_abi_DriveStep_hot_4 st));
     cw(val(EL native_abi_DriveStep_hot_5 st))] /\
    LENGTH(procedure_args st cw) = native_abi_CallArgumentCount`,
  REWRITE_TAC (procedure_args::LENGTH::native_abi_definitions) THEN CONV_TAC NUM_REDUCE_CONV);;

let native_abi_core_theorems = native_abi_contract_theorems @
 ["NATIVE_ABI_CORE_READER",NATIVE_ABI_CORE_READER;
  "NATIVE_ABI_CORE_END",NATIVE_ABI_CORE_END;
  "NATIVE_ABI_CORE_HEADER",NATIVE_ABI_CORE_HEADER;
  "NATIVE_ABI_CORE_POLICY",NATIVE_ABI_CORE_POLICY;
  "NATIVE_ABI_ARGUMENTS",NATIVE_ABI_ARGUMENTS];;
