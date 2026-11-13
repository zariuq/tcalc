(* ========================================================================= *)
(* LEDGER.txt, part 2 (a session on s2n-bignum's base with the driver       *)
(* loaded): the premise ledgers of the driver's and the reader loop's top   *)
(* theorems, and of the leaf link's. Replaces part 2 (ledger.ml).           *)
(* ========================================================================= *)

loadt "native/hol/ledger.ml";;
needs "native/hol/holr_leaf_link.ml";;

let ledger_cands_drv = [];;

let ledger_obls_drv =
  [`\nl progs lmc lpc. !j. j < nl ==> tisa_leaf_wf (progs j) /\ tisa_leaf_spec (progs j) (lmc j) (lpc j)`,
     false, "LEAVES (the leaf table: INTERN16_LEAF_WF/SPEC, FNV_LEAF_WF/SPEC, LEB128_LEAF_WF/SPEC, NAME_LEAF_WF/SPEC for the shipped leaves)";
   `\pc stackpointer d plan ns ctl nctl bind nbw leaves nl lpc lmc.
      drv_layout pc stackpointer d plan ns ctl nctl bind nbw leaves nl lpc lmc`, false,
     "HOST_LAYOUT (the host lays out the driver's regions)";
   `\progs pc stackpointer d plan ns nctl bind nbw leaves nl lpc lmc bw stepl.
      ALL (drv_step_ok progs pc stackpointer d plan ns nctl bind nbw leaves nl lpc lmc bw) stepl`, true,
     "PLAN_STEPS_OK (every step of a per-record plan is well formed: the per-record plans)";
   `\m0 d plan ns ctl bind leaves budget used0 stepl bw nbw lpc nl.
      drv_holds m0 d plan ns ctl bind leaves budget used0 stepl bw nbw lpc nl`, false,
     "HOST_MEMORY (memory holds the plan, the control block and the bindings)";
   `\m0 p mc. drv_code m0 p mc`, false, "LOADER_CODE (the code bytes are in memory)";
   `\nl m0 lpc lmc. !j. j < nl ==> drv_code m0 (lpc j) (lmc j)`, false,
     "LOADER_CODE (each leaf's code bytes)";
   `\progs pcr pcd E r ht nh ds pl m0 opa enda ctl bind nbw leaves nl lpc lmc bw.
      rec_layout progs pcr pcd E r ht nh ds pl m0 opa enda ctl bind nbw leaves nl lpc lmc bw`, false,
     "HOST_LAYOUT (the host lays out the reader loop's regions)";
   `\progs pcd E ctl nctl bind nbw leaves nl lpc lmc bw pl m0 ds.
      ALL (rec_plan_ok progs pcd E ctl nctl bind nbw leaves nl lpc lmc bw pl m0) ds`, true,
     "PLAN_STEPS_OK (every record's plan is well formed: the per-record plans)";
   `\dd ds. MEM (dd:int64) ds`, false, "HOST_MEMORY (the reader's descriptor is one of the plans)";
   `\nh m0 ht ds. !k. k < val nh
        ==> drv_word m0 (word_add ht (word(8 * k))) = word 0 \/
            MEM (drv_word m0 (word_add ht (word(8 * k)))) ds`, false,
     "HOST_MEMORY (the dispatch table holds plans or zeros)";
   `\m0 r pcd dd ht nh opa enda budget used0. rec_desc m0 r pcd dd ht nh opa enda budget used0`, false,
     "HOST_MEMORY (the reader's descriptor)";
   `\st. intern_ok st`, false,
     "INTERN_OK (an empty table is well formed and every run keeps it: INTERN16_RUN_COMPLETE)";
   `\st rows. intern_rows st rows`, true,
     "HANDLER_TABLE_REPRESENTATION (the interner's rows region holds the native table, as packed keys)";
   `\st key. tisa_fword st 22 = key_word0 key`, true,
     "HANDLER_TABLE_REPRESENTATION (the handler passes the row's packed key)";
   `\st key. tisa_fword st 23 = key_word1 key`, true,
     "HANDLER_TABLE_REPRESENTATION (the handler passes the row's packed key)";
   `\st bss. name_rows st bss`, true,
     "HANDLER_TABLE_REPRESENTATION (the name interner's rows hold the native names' bytes)";
   `\st. name_ok st`, false,
     "NAME_OK (an empty name table is well formed and every run keeps it: NAME_RUN_COMPLETE)";
   `\st. name_hash_ok st`, false, "NAME_HASH (the caller passes the name's FNV-1a 64)";
   `\p st. tisa_entry_ok p st`, false, "ENTRY (the driver enters the leaf with a validated frame)";
   `\p st st'. tisa_exec (tisa_root p) st = TStop 1 st'`, false, "FIRED (the leaf's run fired)";
   `\p st st'. tisa_run p st = TStop 1 st'`, false, "FIRED (the leaf's run fired)";
   `\st st'. val(tisa_fword st' 19) = val(intern_count st)`, false, "APPENDED (the run appended a row)";
   `\st st'. val(tisa_fword st' 19) = val(name_count st)`, false, "APPENDED (the run appended a name)"];;

ledger_put_part (tcalc_path "native/hol/LEDGER.txt") 2
  "session on s2n-bignum's base (the driver's evidence run: t-ISA, leaves, driver.ml, records.ml, drive_*.ml), with holr_leaf_link.ml."
  (map (ledger_lines ledger_cands_drv ledger_obls_drv)
      ["DRV_CORRECT", DRV_CORRECT; "REC_CORRECT", REC_CORRECT;
       "INTERN16_KEYS_DISTINCT", INTERN16_KEYS_DISTINCT;
       "INTERN16_APPENDED_KEY_ABSENT", INTERN16_APPENDED_KEY_ABSENT;
       "NAME_KEYS_DISTINCT", NAME_KEYS_DISTINCT; "NAME_APPENDED_ABSENT", NAME_APPENDED_ABSENT]);;
