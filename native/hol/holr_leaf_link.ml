(* ========================================================================= *)
(* What the interning leaves give for a table, in a t-ISA session.          *)
(*                                                                           *)
(* intern16 keeps a table of 16-byte keys; a type or de Bruijn row          *)
(* (tag,a,b) is stored as the key words k0 = tag + 8a, k1 = b (tag | a << 3, *)
(* NATIVE-CHECKER.txt section 3). intern_rows st rows: the interner's rows  *)
(* below the count are the keys of rows, in order. intern_name keeps a      *)
(* table of byte strings; name_rows st bss: its rows below the count hold   *)
(* the byte strings bss, in order.                                           *)
(*                                                                           *)
(* INTERN16_KEYS_DISTINCT: a well-formed interner (intern_ok, kept by every *)
(* run: INTERN16_RUN_COMPLETE) holds no key twice, so the table has         *)
(* distinct keys. INTERN16_APPENDED_KEY_ABSENT: a run that appended found   *)
(* no earlier row holding the key (INTERN16_APPEND_ABSENT), so the appended *)
(* row's key is absent from the table before it. NAME_KEYS_DISTINCT and     *)
(* NAME_APPENDED_ABSENT state the same for names (name_ok, NAME_APPEND_ABSENT),*)
(* and NAME_BYTES_LT that names are bytes.                                   *)
(*                                                                           *)
(* These conclusions are the premises of holr_keys.ml's NAT_KEYS_NEW_ROWS,  *)
(* KEYS_DISTINCT_SNOC and NAT_NEW_NAMES_OF_BYTES, stated over lists of      *)
(* numbers only. The two files meet there: the t-ISA leaves are built on    *)
(* s2n-bignum's x86 base, where HolInHol's kernel (which the native steps   *)
(* use) does not load (holfibre_rows.ml). keys_distinct is defined here     *)
(* with the same text as in holr_keys.ml.                                    *)
(*                                                                           *)
(* Loaded in a session started in s2n-bignum's directory.                    *)
(* ========================================================================= *)

needs "native/hol/intern16_complete.ml";;
needs "native/hol/intern_name.ml";;

let keys_distinct = new_definition
 `keys_distinct (l:A list) <=>
    !i j. i < LENGTH l /\ j < LENGTH l /\ EL i l = EL j l ==> i = j`;;

let key_word0 = new_definition
 `key_word0 ((tag,a,b):num#num#num) = (word (tag + 8 * a):int64)`;;

let key_word1 = new_definition
 `key_word1 ((tag,a,b):num#num#num) = (word b:int64)`;;

let intern_rows = new_definition
 `intern_rows st (rows:(num#num#num)list) <=>
    val(intern_count st) = LENGTH rows /\
    !i. i < LENGTH rows ==> intern_has st i (key_word0 (EL i rows)) (key_word1 (EL i rows))`;;

let INTERN16_KEYS_DISTINCT = prove
 (`!st rows. intern_ok st /\ intern_rows st rows ==> keys_distinct rows`,
  REWRITE_TAC[intern_ok; intern_distinct; intern_rows; keys_distinct] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term ((=) `intern_word`)) (concl th) && not (can (find_term ((=) `intern_slot`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `i:num` th) THEN MP_TAC(SPEC `j:num` th)) THEN
  ASM_REWRITE_TAC[intern_has] THEN MESON_TAC[]);;

let INTERN16_APPENDED_KEY_ABSENT = prove
 (`!st st' rows key.
      tisa_entry_ok intern16 st /\ intern_ok st /\
      tisa_exec (tisa_root intern16) st = TStop 1 st' /\
      val(tisa_fword st' 19) = val(intern_count st) /\
      intern_rows st rows /\
      tisa_fword st 22 = key_word0 key /\ tisa_fword st 23 = key_word1 key
      ==> !j. j < LENGTH rows ==> ~(EL j rows = key)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `st':tisa_state`] INTERN16_APPEND_ABSENT) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `intern_rows st (rows:(num#num#num)list)` THEN REWRITE_TAC[intern_rows] THEN
  MESON_TAC[]);;

let name_rows = new_definition
 `name_rows st (bss:(num list)list) <=>
    val(name_count st) = LENGTH bss /\
    !i. i < LENGTH bss ==> name_row_bytes st i = EL i bss`;;

let NAME_KEYS_DISTINCT = prove
 (`!st bss. name_ok st /\ name_rows st bss ==> keys_distinct bss`,
  REWRITE_TAC[name_ok; name_distinct; name_rows; keys_distinct] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term ((=) `name_row_bytes`)) (concl th) &&
    not (can (find_term ((=) `name_slot`)) (concl th)) &&
    not (can (find_term ((=) `name_word`)) (concl th)))) THEN
  ASM_MESON_TAC[]);;

let NAME_APPENDED_ABSENT = prove
 (`!st st' bss.
      tisa_entry_ok intern_name st /\ name_ok st /\ name_hash_ok st /\
      tisa_run intern_name st = TStop 1 st' /\
      val(tisa_fword st' 19) = val(name_count st) /\ name_rows st bss
      ==> !j. j < LENGTH bss ==> ~(EL j bss = name_key st)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `st':tisa_state`] NAME_APPEND_ABSENT) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `name_rows st (bss:(num list)list)` THEN REWRITE_TAC[name_rows] THEN
  MESON_TAC[]);;

let ALL_LIST_OF_SEQ_BYTES = prove
 (`!f n. (!k. f k < 256) ==> ALL (\b. b < 256) (list_of_seq f n)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[list_of_seq; ALL; ALL_APPEND]);;

let ALL_OF_EL = prove
 (`!P (l:A list). (!i. i < LENGTH l ==> P (EL i l)) ==> ALL P l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; LENGTH] THEN DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[EL; HD; LT_0];
    FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC i`) THEN ASM_REWRITE_TAC[EL; TL; LT_SUC]]);;

let NAME_BYTES_LT = prove
 (`!st bss. name_rows st bss
            ==> ALL (ALL (\b. b < 256)) bss /\ ALL (\b. b < 256) (name_key st)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[name_rows] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALL_OF_EL THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o C MATCH_MP (ASSUME `n < LENGTH (bss:(num list)list)`)) THEN
    REWRITE_TAC[name_row_bytes];
    REWRITE_TAC[name_key; region_range]] THEN
  MATCH_MP_TAC ALL_LIST_OF_SEQ_BYTES THEN REWRITE_TAC[REGION_BYTE_LT]);;
