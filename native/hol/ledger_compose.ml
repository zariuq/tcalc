(* ========================================================================= *)
(* LEDGER.txt, part 3: the premise ledger of the one-session composition    *)
(* (holr_compose.ml), in the session that also has parts 1 and 2's          *)
(* theorems. Load after ledger_holr.ml and ledger_drv.ml.                    *)
(* ========================================================================= *)

ledger_put_part (tcalc_path "native/hol/LEDGER.txt") 3
  "one session on s2n-bignum's base: the x86 files, holr_leaf_link.ml, the Model world (model_world_load.ml), holr_compose.ml."
  [ledger_lines [] (ledger_obls_drv @ ledger_obls)
     ("INTERN16_FIRED_NAT_NEW_ROWS", INTERN16_FIRED_NAT_NEW_ROWS)];;
