(* Bootstrap relation with minimal count/header initialization views. *)
needs "native/hol/boot_init_rel.ml";;
needs "native/hol/zero_init_boot_minimal_ready.ml";;

let BOOT_ZERO_FROM_MINIMAL_INIT = prove
 (`!bw d plan used status m.
     zinit_abi_post (zinit_boot_view bw) zinit_boot_slots d plan used status m /\
     status = word 1
     ==> hol_boot_zero bw m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ZINIT_BOOT_VIEW_ZERO THEN
  MP_TAC(SPECL [`zinit_boot_view (bw:num->int64)`;`zinit_boot_slots`;`d:int64`;
                `plan:int64`;`used:int64`;`status:int64`;`m:int64->byte`] ZINIT_ABI_EXACT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let BOOT_FRESH_TAB_MINIMAL =
 boot_from_receipt `zinit_boot_view` BOOT_ZERO_FROM_MINIMAL_INIT BOOT_FRESH_TAB;;
let BOOT_START_MINIMAL =
 boot_from_receipt `zinit_boot_view` BOOT_ZERO_FROM_MINIMAL_INIT BOOT_START;;

let boot_minimal_rel_theorems =
 ["BOOT_ZERO_FROM_MINIMAL_INIT",BOOT_ZERO_FROM_MINIMAL_INIT;
  "BOOT_FRESH_TAB_MINIMAL",BOOT_FRESH_TAB_MINIMAL;
  "BOOT_START_MINIMAL",BOOT_START_MINIMAL];;
leaf_audit boot_minimal_rel_theorems boot_minimal_rel_theorems;;
