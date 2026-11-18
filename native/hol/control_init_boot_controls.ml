(* Physical control-word observations needed by BOOT_START. *)
needs "native/hol/kernel_boot_load.ml";;
needs "native/hol/control_init_values.ml";;
needs "native/hol/zero_init.ml";;

let ZERO_INIT_CONTROL_ZERO = prove
 (`!ctl slot u. drv_word (drv_after ctl (zinit_step slot) u) ctl = tisa_fword u 19`,
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_after;zinit_step] THEN
  CONV_TAC STEP_EL_CONV2 THEN REWRITE_TAC[WORD_ADD_0;DRV_WORD_WRITE_SAME]);;

let CONTROL_INIT_FIXED_VALUES = prove
 (`!policy:int64.
     control_init_value policy 7 = policy /\
     control_init_value policy 17 = word 0 /\ control_init_value policy 19 = word 0 /\
     control_init_value policy 20 = word 0 /\ control_init_value policy 22 = fnv_offset`,
  REWRITE_TAC[control_init_value;fnv_offset] THEN CONV_TAC NUM_REDUCE_CONV);;

let CONTROL_INIT_BOOT_CONTROLS =
  REWRITE_RULE[GSYM pl_cwords;CONTROL_INIT_FIXED_VALUES] CONTROL_INIT_CONTROL_VALUES;;

let control_init_boot_control_theorems =
 ["CONTROL_INIT_FIXED_VALUES",CONTROL_INIT_FIXED_VALUES;
  "CONTROL_INIT_BOOT_CONTROLS",CONTROL_INIT_BOOT_CONTROLS];;
leaf_audit control_init_boot_control_theorems control_init_boot_control_theorems;;
