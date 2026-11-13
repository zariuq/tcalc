(* ========================================================================= *)
(* One session, one theorem: the interning leaf's theorems (t-ISA, proved   *)
(* on s2n-bignum's base, holr_leaf_link.ml) discharge the native step's     *)
(* freshness premise (holr_native.ml, holr_keys.ml). Loaded in a session on *)
(* s2n-bignum's base after the x86 files, holr_leaf_link.ml and             *)
(* model_world_load.ml.                                                      *)
(*                                                                           *)
(* When the interner fires on a type row's packed key, appending it, and    *)
(* the interners' tables hold the native type and term rows, the row is new *)
(* (nat_new_rows), given canonical keys and injective names. The table      *)
(* representation (intern_rows) and canonical keys (nat_keys) are the       *)
(* handler obligations the premise ledger lists as open.                    *)
(* ========================================================================= *)

let INTERN16_FIRED_NAT_NEW_ROWS = prove
 (`!st st' sd key tys dbs nms.
      tisa_entry_ok intern16 st /\ intern_ok st /\
      tisa_exec (tisa_root intern16) st = TStop 1 st' /\
      val(tisa_fword st' 19) = val(intern_count st) /\
      intern_rows st tys /\
      tisa_fword st 22 = key_word0 key /\ tisa_fword st 23 = key_word1 key /\
      intern_ok sd /\ intern_rows sd dbs /\
      NAMES_INJ nms /\ nat_keys (APPEND tys [key]) dbs
      ==> nat_new_rows nms tys dbs [key] []`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC NAT_KEYS_NEW_ROWS THEN
  ASM_REWRITE_TAC[APPEND_NIL; LENGTH; ADD_CLAUSES] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC KEYS_DISTINCT_SNOC THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTERN16_KEYS_DISTINCT THEN ASM_MESON_TAC[];
      MATCH_MP_TAC INTERN16_APPENDED_KEY_ABSENT THEN ASM_MESON_TAC[]];
    MATCH_MP_TAC INTERN16_KEYS_DISTINCT THEN ASM_MESON_TAC[];
    GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE `!k n. k < n /\ n <= k ==> F`)) THEN
    REWRITE_TAC[]]);;
