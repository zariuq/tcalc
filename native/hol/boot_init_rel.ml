(* Bootstrap contracts from the clearing ABI's actual-memory receipt.
   Layout, control initialization and the boot plan's own premises remain
   explicit; the caller no longer has to supply a prior-zero assumption. *)
needs "native/hol/kernel_boot_load.ml";;
needs "native/hol/zero_init_boot_receipt.ml";;

let BOOT_FRESH_TAB_INITIALIZED = boot_from_init BOOT_FRESH_TAB;;
let BOOT_START_INITIALIZED = boot_from_init BOOT_START;;

let boot_init_rel_theorems =
 ["BOOT_ZERO_FROM_INIT",BOOT_ZERO_FROM_INIT;
  "BOOT_FRESH_TAB_INITIALIZED",BOOT_FRESH_TAB_INITIALIZED;
  "BOOT_START_INITIALIZED",BOOT_START_INITIALIZED];;
leaf_audit boot_init_rel_theorems boot_init_rel_theorems;;
