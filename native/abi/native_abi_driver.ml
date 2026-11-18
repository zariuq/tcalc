(* Generated driver coordinates checked against its independent semantics. *)
needs "native/abi/native_abi_contract.ml";;

let NATIVE_ABI_DRIVER_STACK = prove
 (`!cfr a. drv_stack cfr a <=>
    val cfr <= val a + native_abi_LeafStackSaveBytes + native_abi_WordBytes /\
    val a < val cfr + native_abi_DriverFrameDistance`,
  REWRITE_TAC (drv_stack::native_abi_definitions) THEN ARITH_TAC);;

let NATIVE_ABI_DRIVER_WORK = prove
 (`native_abi_DriverWorkBytes = native_abi_LeafStackSaveBytes +
      native_abi_DriverFrameDistance + 2 * native_abi_WordBytes /\
   native_abi_StepBytes = native_abi_StepWords * native_abi_WordBytes /\
   native_abi_CallRequestBytes = native_abi_CallRequestWords * native_abi_WordBytes /\
   native_abi_CallRequestWords = native_abi_CallArgumentCount + 1`,
  REWRITE_TAC native_abi_definitions THEN CONV_TAC NUM_REDUCE_CONV);;

let NATIVE_ABI_DRIVER_DESCRIPTOR = prove
 (`!m d plan ns ctl bind leaves budget used stepl bw nbw lpc nl.
    drv_holds m d plan ns ctl bind leaves budget used stepl bw nbw lpc nl <=>
    LENGTH stepl = ns /\
    drv_word m (word_add d (word(native_abi_WordBytes * native_abi_DriveDescriptor_plan))) = plan /\
    drv_word m (word_add d (word(native_abi_WordBytes * native_abi_DriveDescriptor_plan_end))) =
      word_add plan (word(native_abi_StepBytes * ns)) /\
    drv_word m (word_add d (word(native_abi_WordBytes * native_abi_DriveDescriptor_ctl))) = ctl /\
    drv_word m (word_add d (word(native_abi_WordBytes * native_abi_DriveDescriptor_bind))) = bind /\
    drv_word m (word_add d (word(native_abi_WordBytes * native_abi_DriveDescriptor_leaves))) = leaves /\
    drv_word m (word_add d (word(native_abi_WordBytes * native_abi_DriveDescriptor_budget))) = budget /\
    drv_word m (word_add d (word(native_abi_WordBytes * native_abi_DriveDescriptor_used))) = used /\
    (!i f. i < ns /\ f < native_abi_StepWords
      ==> drv_word m (word_add plan (word(native_abi_StepBytes * i + native_abi_WordBytes * f))) = EL f (EL i stepl)) /\
    (!k. k < nbw ==> drv_word m (word_add bind (word(native_abi_WordBytes * k))) = bw k) /\
    (!j. j < nl ==> drv_word m (word_add leaves (word(native_abi_WordBytes * j))) = word(lpc j))`,
  REWRITE_TAC (drv_holds::native_abi_definitions) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0]);;

let NATIVE_ABI_DRIVER_FINAL = prove
 (`!d plan res. drv_final d plan res =
    write (bytes64 (word_add d (word(native_abi_WordBytes * native_abi_DriveDescriptor_at))))
      (word_add plan (word(native_abi_StepBytes * FST(SND res))))
      (write (bytes64 (word_add d (word(native_abi_WordBytes * native_abi_DriveDescriptor_used))))
        (SND(SND(SND res))) (FST(SND(SND res))))`,
  REWRITE_TAC (drv_final::native_abi_definitions) THEN CONV_TAC NUM_REDUCE_CONV);;

let NATIVE_ABI_DRIVER_CHILD = prove
 (`!bw ctl budget used st m j. drv_fw bw ctl budget used st m j =
    if j < 2 * native_abi_MaxRegions then bw (val(EL (1 + j DIV 2) st) + j MOD 2)
    else if j <= native_abi_RuntimeFrame_ret_val then word 0
    else if j = native_abi_RuntimeFrame_fuel_budget then budget
    else if j = native_abi_RuntimeFrame_fuel_used then used
    else drv_cw ctl m (EL (j - (native_abi_RuntimeFrame_arg0 - native_abi_DriveStep_arg0)) st)`,
  REWRITE_TAC (drv_fw::native_abi_definitions) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `j <= 19 <=> j < 20`]);;

let NATIVE_ABI_DRIVER_REGION_FIELDS = prove
 (`!r. r < native_abi_MaxRegions
     ==> EL r [native_abi_DriveStep_region_0;native_abi_DriveStep_region_1;
               native_abi_DriveStep_region_2;native_abi_DriveStep_region_3;
               native_abi_DriveStep_region_4;native_abi_DriveStep_region_5;
               native_abi_DriveStep_region_6;native_abi_DriveStep_region_7;
               native_abi_DriveStep_region_8] = 1 + r`,
  REWRITE_TAC native_abi_definitions THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let native_abi_driver_theorems = native_abi_contract_theorems @
 ["NATIVE_ABI_DRIVER_STACK",NATIVE_ABI_DRIVER_STACK;
  "NATIVE_ABI_DRIVER_WORK",NATIVE_ABI_DRIVER_WORK;
  "NATIVE_ABI_DRIVER_DESCRIPTOR",NATIVE_ABI_DRIVER_DESCRIPTOR;
  "NATIVE_ABI_DRIVER_FINAL",NATIVE_ABI_DRIVER_FINAL;
  "NATIVE_ABI_DRIVER_CHILD",NATIVE_ABI_DRIVER_CHILD;
  "NATIVE_ABI_DRIVER_REGION_FIELDS",NATIVE_ABI_DRIVER_REGION_FIELDS];;
