(* ========================================================================= *)
(* Canonical keys: from the interners' theorems to the native steps'         *)
(* freshness premises (nat_new_rows, nat_new_names).                         *)
(*                                                                           *)
(* Interning stores a type or de Bruijn row as its key (tag,a,b), keeps no  *)
(* two rows holding one key, and appends a key only when no row holds it    *)
(* (intern_ok, INTERN16_APPEND_ABSENT); a name row holds the name's bytes   *)
(* (name_ok, NAME_APPEND_ABSENT). holr_leaf_link.ml states what those       *)
(* theorems give for a table of keys, in a t-ISA session; this file takes   *)
(* those statements as premises.                                             *)
(*                                                                           *)
(* Keys are canonical when the fields a decoding ignores are zero (a type   *)
(* variable's second field, an empty list's two fields, a bound variable's *)
(* second field) and a row's row children are earlier rows: nat_keys, an    *)
(* invariant of the two tables; appending rows with canonical keys keeps it *)
(* (NAT_KEYS_APPEND). Under canonical keys and canonical names, a table in  *)
(* which no two rows hold one key decodes injectively (NAT_KEYS_INJ_TY,     *)
(* NAT_KEYS_INJ_DB), so two rows hold one key exactly when they decode to   *)
(* one object (NAT_KEYS_EQ_TY, NAT_KEYS_EQ_DB). An appended key that was    *)
(* absent keeps the table's keys distinct (KEYS_DISTINCT_SNOC). Hence       *)
(* NAT_KEYS_NEW_ROWS: when the tables after a step have canonical, distinct *)
(* keys, the step's appended rows are new (with the appended de Bruijn     *)
(* rows' decodings, which the handlers give); NAT_NEW_NAMES_OF_BYTES: a     *)
(* name whose bytes no earlier name row holds is new.                       *)
(*                                                                           *)
(* Loaded after holr_native.ml.                                             *)
(* ========================================================================= *)

let ty_key_ok = new_definition
 `ty_key_ok i ((tag,a,b):num#num#num) <=>
    tag = 0 /\ b = 0 \/ tag = 1 /\ b < i \/ tag = 2 /\ a = 0 /\ b = 0 \/
    tag = 3 /\ a < i /\ b < i`;;

let db_key_ok = new_definition
 `db_key_ok i ((tag,a,b):num#num#num) <=>
    tag = 0 \/ tag = 1 /\ b = 0 \/ tag = 2 \/ tag = 3 /\ a < i /\ b < i \/
    tag = 4 /\ b < i \/ tag = 5 /\ a = 0 /\ b = 0 \/ tag = 6 /\ a < i /\ b < i`;;

let nat_keys = new_definition
 `nat_keys (tys:(num#num#num)list) (dbs:(num#num#num)list) <=>
    (!i. i < LENGTH tys ==> ty_key_ok i (EL i tys)) /\
    (!i. i < LENGTH dbs ==> db_key_ok i (EL i dbs))`;;

(* No two rows of a table hold one key. *)
let keys_distinct = new_definition
 `keys_distinct (l:A list) <=>
    !i j. i < LENGTH l /\ j < LENGTH l /\ EL i l = EL j l ==> i = j`;;

let NAT_KEYS_APPEND = prove
 (`!tys dbs mt md.
      nat_keys tys dbs /\
      (!d. d < LENGTH mt ==> ty_key_ok (LENGTH tys + d) (EL d mt)) /\
      (!d. d < LENGTH md ==> db_key_ok (LENGTH dbs + d) (EL d md))
      ==> nat_keys (APPEND tys mt) (APPEND dbs md)`,
  REWRITE_TAC[nat_keys; LENGTH_APPEND; EL_APPEND] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i - LENGTH (tys:(num#num#num)list)` o check (fun th ->
      can (find_term ((=) `mt:(num#num#num)list`)) (concl th)));
    FIRST_X_ASSUM(MP_TAC o SPEC `i - LENGTH (dbs:(num#num#num)list)` o check (fun th ->
      can (find_term ((=) `md:(num#num#num)list`)) (concl th)))] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(i < n) ==> n + (i - n) = i`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let KEYS_DISTINCT_SNOC = prove
 (`!(l:A list) x. keys_distinct l /\ (!j. j < LENGTH l ==> ~(EL j l = x))
                  ==> keys_distinct (APPEND l [x])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[keys_distinct; LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `APPEND (l:A list) [x]`)) (concl th)))) THEN
  ASM_CASES_TAC `i < LENGTH (l:A list)` THEN ASM_CASES_TAC `j < LENGTH (l:A list)` THEN
  ASM_SIMP_TAC[EL_APPEND] THENL
   [ASM_MESON_TAC[];
    SUBGOAL_THEN `j = LENGTH (l:A list)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUB_REFL; EL; HD] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `i = LENGTH (l:A list)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUB_REFL; EL; HD] THEN ASM_MESON_TAC[];
    DISCH_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* One key, one object.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Rows holding one key decode alike. *)
let NAT_KEY_SAME_DECODE_TY = prove
 (`!nms tys i j. i < LENGTH tys /\ j < LENGTH tys /\ EL i tys = EL j tys
                 ==> (!t. fdty nms tys i t <=> fdty nms tys j t) /\
                     (!l. fdtys nms tys i l <=> fdtys nms tys j l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[fdty_CASES] THEN ASM_REWRITE_TAC[]);;

let NAT_KEY_SAME_DECODE_DB = prove
 (`!nms tys dbs i j. i < LENGTH dbs /\ j < LENGTH dbs /\ EL i dbs = EL j dbs
                     ==> (!t. fddb nms tys dbs i t <=> fddb nms tys dbs j t) /\
                         (!l. fddbs nms tys dbs i l <=> fddbs nms tys dbs j l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[fddb_CASES] THEN ASM_REWRITE_TAC[]);;

let NAMES_INJ = new_definition
 `NAMES_INJ (nms:string list) <=>
    !x y. x < LENGTH nms /\ y < LENGTH nms /\ EL x nms = EL y nms ==> x = y`;;

(* Canonical, distinct keys and canonical names: one object, one row. *)
let NAT_KEYS_INJ_TY = prove
 (`!nms tys.
      NAMES_INJ nms /\ (!i. i < LENGTH tys ==> ty_key_ok i (EL i tys)) /\
      keys_distinct tys
      ==> (!i t. fdty nms tys i t ==> !j. fdty nms tys j t ==> i = j) /\
          (!i l. fdtys nms tys i l ==> !j. fdtys nms tys j l ==> i = j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NAMES_INJ; keys_distinct] THEN STRIP_TAC THEN
  MATCH_MP_TAC fdty_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[fdty_CASES] THEN
  REWRITE_TAC[holtype_INJ; holtype_DISTINCT; NOT_CONS_NIL; CONS_11] THEN STRIP_TAC THEN
  (SUBGOAL_THEN `ty_key_ok i (EL i (tys:(num#num#num)list)) /\ ty_key_ok j (EL j tys)` MP_TAC
   THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[ty_key_ok; PAIR_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term ((=) `tys:(num#num#num)list`)) (concl th) &&
    not (can (find_term ((=) `ty_key_ok`)) (concl th)))) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]);;

let NAT_KEYS_INJ_DB = prove
 (`!nms tys dbs.
      NAMES_INJ nms /\
      (!i t. fdty nms tys i t ==> !j. fdty nms tys j t ==> i = j) /\
      (!i. i < LENGTH dbs ==> db_key_ok i (EL i dbs)) /\ keys_distinct dbs
      ==> (!i t. fddb nms tys dbs i t ==> !j. fddb nms tys dbs j t ==> i = j) /\
          (!i l. fddbs nms tys dbs i l ==> !j. fddbs nms tys dbs j l ==> i = j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NAMES_INJ; keys_distinct] THEN STRIP_TAC THEN
  MATCH_MP_TAC fddb_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[fddb_CASES] THEN
  REWRITE_TAC[hdbterm_INJ; hdbterm_DISTINCT; NOT_CONS_NIL; CONS_11] THEN STRIP_TAC THEN
  (SUBGOAL_THEN `db_key_ok i (EL i (dbs:(num#num#num)list)) /\ db_key_ok j (EL j dbs)` MP_TAC
   THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[db_key_ok; PAIR_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term ((=) `dbs:(num#num#num)list`)) (concl th) &&
    not (can (find_term ((=) `db_key_ok`)) (concl th)))) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]);;

(* Under canonical, distinct keys, two rows hold one key exactly when they   *)
(* decode to one object.                                                     *)
let NAT_KEYS_EQ_TY = prove
 (`!nms tys i j t u.
      NAMES_INJ nms /\ (!i. i < LENGTH tys ==> ty_key_ok i (EL i tys)) /\
      keys_distinct tys /\ fdty nms tys i t /\ fdty nms tys j u
      ==> (EL i tys = EL j tys <=> t = u)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `fdty nms tys j t` MP_TAC THENL
     [ASM_MESON_TAC[NAT_KEY_SAME_DECODE_TY; FDTY_BOUND]; ALL_TAC] THEN
    ASM_MESON_TAC[FDTY_FUNCTIONAL];
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`] NAT_KEYS_INJ_TY) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let NAT_KEYS_EQ_DB = prove
 (`!nms tys dbs i j t u.
      NAMES_INJ nms /\ (!i t. fdty nms tys i t ==> !j. fdty nms tys j t ==> i = j) /\
      (!i. i < LENGTH dbs ==> db_key_ok i (EL i dbs)) /\ keys_distinct dbs /\
      fddb nms tys dbs i t /\ fddb nms tys dbs j u
      ==> (EL i dbs = EL j dbs <=> t = u)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `fddb nms tys dbs j t` MP_TAC THENL
     [ASM_MESON_TAC[NAT_KEY_SAME_DECODE_DB; FDDB_BOUND]; ALL_TAC] THEN
    ASM_MESON_TAC[FDDB_FUNCTIONAL];
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`]
                 NAT_KEYS_INJ_DB) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The freshness premises.                                                   *)
(* ------------------------------------------------------------------------- *)

(* When the tables after a step have canonical keys and no two rows hold one *)
(* key (the interners' invariant, or the old tables' and each appended key's *)
(* absence, KEYS_DISTINCT_SNOC), and the appended de Bruijn rows decode,     *)
(* the step's appended rows are new.                                          *)
let NAT_KEYS_NEW_ROWS = prove
 (`!nms tys dbs mt md.
      NAMES_INJ nms /\ nat_keys (APPEND tys mt) (APPEND dbs md) /\
      keys_distinct (APPEND tys mt) /\ keys_distinct (APPEND dbs md) /\
      (!k. k < LENGTH dbs + LENGTH md /\ LENGTH dbs <= k
           ==> (?t. fddb nms (APPEND tys mt) (APPEND dbs md) k t) \/
               (?l. fddbs nms (APPEND tys mt) (APPEND dbs md) k l))
      ==> nat_new_rows nms tys dbs mt md`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nat_keys] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`nms:string list`; `APPEND tys mt:(num#num#num)list`] NAT_KEYS_INJ_TY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`nms:string list`; `APPEND tys mt:(num#num#num)list`;
                `APPEND dbs md:(num#num#num)list`] NAT_KEYS_INJ_DB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[nat_new_rows; fdty_same; fddb_same] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `j:num = k` (fun th -> ASM_MESON_TAC[th; LT_REFL]) THEN ASM_MESON_TAC[]);;

(* A name is the image of its bytes, and images of bytes are one-to-one.    *)
let CHAR_INJ = injectivity "char";;

let BITS8 = prove
 (`!n. n < 256
       ==> n = (if ODD (n DIV 128) then 128 else 0) + (if ODD (n DIV 64) then 64 else 0) +
               (if ODD (n DIV 32) then 32 else 0) + (if ODD (n DIV 16) then 16 else 0) +
               (if ODD (n DIV 8) then 8 else 0) + (if ODD (n DIV 4) then 4 else 0) +
               (if ODD (n DIV 2) then 2 else 0) + (if ODD n then 1 else 0)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let HCHAR_OF_INJ = prove
 (`!a b. a < 256 /\ b < 256 /\ hchar_of a = hchar_of b ==> a = b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hchar_of; CHAR_INJ] THEN STRIP_TAC THEN
  MP_TAC(SPEC `a:num` BITS8) THEN MP_TAC(SPEC `b:num` BITS8) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let HOLR_NAME_INJ = prove
 (`!l l'. ALL (\b. b < 256) l /\ ALL (\b. b < 256) l' /\ holr_name l = holr_name l'
          ==> l = l'`,
  REWRITE_TAC[holr_name] THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALL; NOT_CONS_NIL; CONS_11] THEN ASM_MESON_TAC[HCHAR_OF_INJ]);;

(* A name whose bytes no earlier name row holds is new. *)
let NAT_NEW_NAMES_OF_BYTES = prove
 (`!bss key. ALL (\b. b < 256) key /\ ALL (ALL (\b. b < 256)) bss /\
             (!j. j < LENGTH bss ==> ~(EL j bss = key))
             ==> nat_new_names (MAP holr_name bss) [holr_name key]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nat_new_names; LENGTH_MAP; LENGTH; ADD_CLAUSES] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`k:num`; `j:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `k = LENGTH (bss:(num list)list)` SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_APPEND; LENGTH_MAP; LT_REFL; SUB_REFL; EL; HD; EL_MAP] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `EL j (bss:(num list)list) = key` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC HOLR_NAME_INJ THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL (ALL (\b. b < 256)) (bss:(num list)list)` THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[MEM_EL]);;

(* The interners' invariant makes a table canonical: names whose bytes are   *)
(* distinct, and tables with canonical, distinct keys whose de Bruijn rows   *)
(* decode.                                                                    *)
let NAT_KEYS_CANON = prove
 (`!bss tys dbs.
      ALL (ALL (\b. b < 256)) bss /\ keys_distinct bss /\ nat_keys tys dbs /\
      keys_distinct tys /\ keys_distinct dbs /\
      (!i. i < LENGTH dbs ==> (?t. fddb (MAP holr_name bss) tys dbs i t) \/
                              (?l. fddbs (MAP holr_name bss) tys dbs i l))
      ==> nat_canon (MAP holr_name bss) tys dbs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nat_keys] THEN STRIP_TAC THEN
  SUBGOAL_THEN `NAMES_INJ (MAP holr_name bss)` ASSUME_TAC THENL
   [REWRITE_TAC[NAMES_INJ; LENGTH_MAP] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `keys_distinct (bss:(num list)list)` THEN
    REWRITE_TAC[keys_distinct] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOLR_NAME_INJ THEN
    UNDISCH_TAC `EL x (MAP holr_name bss) = EL y (MAP holr_name bss)` THEN
    ASM_SIMP_TAC[EL_MAP] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL (ALL (\b. b < 256)) (bss:(num list)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[MEM_EL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`MAP holr_name bss`; `tys:(num#num#num)list`] NAT_KEYS_INJ_TY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`MAP holr_name bss`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`]
               NAT_KEYS_INJ_DB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NAMES_INJ]) THEN
  REWRITE_TAC[nat_canon; fdty_same; fddb_same] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[]);;
