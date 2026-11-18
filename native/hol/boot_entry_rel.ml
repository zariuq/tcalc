(* Bootstrap from native clearing of counts, marks, hash arrays and flags. *)
needs "native/hol/boot_minimal_rel.ml";;
needs "native/hol/zero_init_entry.ml";;

let BOOT_ZERO_FROM_ENTRY_INIT = prove
 (`!bw d plan used status m.
     zinit_abi_post (zinit_entry_view bw) zinit_entry_slots d plan used status m /\
     status = word 1
     ==> hol_boot_zero bw m /\ zinit_zero bw zinit_entry_extra m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ZINIT_ENTRY_ZERO THEN
  MP_TAC(SPECL [`zinit_entry_view (bw:num->int64)`;`zinit_entry_slots`;`d:int64`;
                `plan:int64`;`used:int64`;`status:int64`;`m:int64->byte`] ZINIT_ABI_EXACT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let BOOT_ZERO_ENTRY = prove
 (`!bw d plan used status m.
     zinit_abi_post (zinit_entry_view bw) zinit_entry_slots d plan used status m /\
     status = word 1
     ==> hol_boot_zero bw m`,
  MESON_TAC[BOOT_ZERO_FROM_ENTRY_INIT]);;

let BOOT_FRESH_TAB_ENTRY =
 boot_from_receipt_on `zinit_entry_slots` `zinit_entry_view` BOOT_ZERO_ENTRY BOOT_FRESH_TAB;;
let BOOT_START_ENTRY =
 boot_from_receipt_on `zinit_entry_slots` `zinit_entry_view` BOOT_ZERO_ENTRY BOOT_START;;

let boot_entry_rel_theorems = zero_init_entry_theorems @
 ["BOOT_ZERO_FROM_ENTRY_INIT",BOOT_ZERO_FROM_ENTRY_INIT;
  "BOOT_ZERO_ENTRY",BOOT_ZERO_ENTRY;
  "BOOT_FRESH_TAB_ENTRY",BOOT_FRESH_TAB_ENTRY;
  "BOOT_START_ENTRY",BOOT_START_ENTRY];;
leaf_audit boot_entry_rel_theorems boot_entry_rel_theorems;;
