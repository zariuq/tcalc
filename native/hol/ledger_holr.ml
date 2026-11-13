(* ========================================================================= *)
(* LEDGER.txt, part 1 (HolInHol session): the premise ledgers of the        *)
(* meaning's and the native layer's top theorems. Load after holr_keys.ml  *)
(* and ledger.ml. Part 2 (ledger_drv.ml) is the driver's, written in a      *)
(* session on s2n-bignum's base; part 3 (ledger_compose.ml) the one-session *)
(* composition's.                                                            *)
(* ========================================================================= *)

let ledger_cands =
  ["NAT_BOOT_TYS_OK", NAT_BOOT_TYS_OK; "NAT_BOOT_CANON", NAT_BOOT_CANON;
   "NAT_ACCEPTS_SPEC", NAT_ACCEPTS_SPEC; "NAT_KEYS_NEW_ROWS", NAT_KEYS_NEW_ROWS;
   "NAT_NEW_NAMES_OF_BYTES", NAT_NEW_NAMES_OF_BYTES];;

let ledger_obls =
  [`\bytes pol recs. bytes = holr_stream pol 0 recs`, false,
     "READER_DECODES (the reader reports the records the bytes encode)";
   `\pol. pol <= 2`, false, "READER_HEADER (the header's policy, checked by the reader)";
   `\recs s0 s. tc_path nat_step recs s0 s`, true,
     "NATIVE_RUN (the x86 checker steps nat_step on every record: the per-record plans)";
   `\nms tys dbs ths es spec. ALL2 (\h sp. nat_matches nms tys dbs (EL h ths) sp) es spec`, true,
     "NATIVE_SPEC_MATCH (the checker matches each EMIT row with the expected sequent)";
   `\ctx spec. ALL (holr_spec_ok ctx) spec`, true,
     "NATIVE_SPEC_WELLFORMED (the checker checks the expected sequents in the final theory)";
   `\decls spec ctx. holr_spec_pinned decls spec ctx`, true,
     "NATIVE_SPEC_NAMES (the checker checks the specification's names)";
   `\decls axs ctx. holr_axioms_allowed decls axs ctx`, true,
     "NATIVE_SPEC_AXIOMS (the checker checks the stream's axioms against the list)";
   `\nms. NAMES_INJ nms`, false, "NAT_CANON (names injective: nat_canon, kept by NAT_STEP_CANON)";
   `\tys dbs. nat_keys tys dbs`, true,
     "HANDLER_CANONICAL_KEYS (the handlers intern canonical keys: ignored fields zero, children first)";
   `\l. keys_distinct (l:(num#num#num)list)`, false,
     "INTERN16_KEYS_DISTINCT (holr_leaf_link.ml: intern_ok and HANDLER_TABLE_REPRESENTATION)";
   `\dbs md nms tys dbs'.
      !k. k < LENGTH dbs + LENGTH md /\ LENGTH dbs <= k
          ==> (?t. fddb nms tys dbs' k t) \/ (?l. fddbs nms tys dbs' k l)`, true,
     "HANDLER_DB_DECODES (every de Bruijn row a handler appends decodes)";
   `\key. ALL (\b. b < 256) key`, false, "NAME_BYTES_LT (holr_leaf_link.ml)";
   `\bss. ALL (ALL (\b. b < 256)) bss`, false, "NAME_BYTES_LT (holr_leaf_link.ml)";
   `\bss key. !j. j < LENGTH bss ==> ~(EL j bss = key)`, false,
     "NAME_APPENDED_ABSENT (holr_leaf_link.ml, from NAME_APPEND_ABSENT)"];;

ledger_put_part (tcalc_path "native/hol/LEDGER.txt") 1
  "HolInHol session (holfibre_all.ml, holr_native.ml, holr_instance.ml, holr_keys.ml)."
  (map (ledger_lines ledger_cands ledger_obls)
       ["NAT_ACCEPTS_SOUND", NAT_ACCEPTS_SOUND; "NAT_ACCEPTS_SPEC", NAT_ACCEPTS_SPEC;
        "HOLR_ACCEPTS_SPEC", HOLR_ACCEPTS_SPEC; "NAT_KEYS_NEW_ROWS", NAT_KEYS_NEW_ROWS;
        "NAT_NEW_NAMES_OF_BYTES", NAT_NEW_NAMES_OF_BYTES]);;
