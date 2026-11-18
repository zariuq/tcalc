(* Counted streams of canonical unsigned LEB128 identifiers. *)

needs "native/hol/holr_leb.ml";;

let rd_id_payload = new_definition
 `rd_id_payload n (bs:num list) ids rest <=>
    LENGTH ids = n /\ ALL (\x. x < 2 EXP 62) ids /\
    bs = APPEND (ITLIST APPEND (MAP leb_enc ids) []) rest`;;

let RD_ID_PAYLOAD_NIL = prove
 (`!bs ids rest. rd_id_payload 0 bs ids rest <=> ids = [] /\ bs = rest`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_id_payload; LENGTH_EQ_NIL] THEN
  ASM_CASES_TAC `ids:num list = []` THEN ASM_REWRITE_TAC[ALL; MAP; ITLIST; APPEND]);;

let RD_ID_PAYLOAD_CONS = prove
 (`!n bs v ids rest.
      rd_id_payload (SUC n) bs (CONS v ids) rest <=>
      v < 2 EXP 62 /\
      ?next. bs = APPEND (leb_enc v) next /\ rd_id_payload n next ids rest`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_id_payload; LENGTH; ALL; MAP; ITLIST;
    SUC_INJ; GSYM APPEND_ASSOC] THEN MESON_TAC[]);;

let RD_ID_PAYLOAD_CANCEL = prove
 (`!(pre:num list) x y. APPEND pre x = APPEND pre y <=> x = y`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; CONS_11]);;

let RD_ID_PAYLOAD_PEEL = prove
 (`!n bs ids rest v next.
      rd_id_payload (SUC n) bs ids rest /\
      leb_fires bs v /\ bs = APPEND (leb_enc v) next
      ==> ?tail. ids = CONS v tail /\ rd_id_payload n next tail rest`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ids:num list` list_CASES) THENL
   [REWRITE_TAC[rd_id_payload; LENGTH; NOT_SUC];
    REWRITE_TAC[RD_ID_PAYLOAD_CONS; CONS_11] THEN STRIP_TAC THEN
    SUBGOAL_THEN `leb_fires (bs:num list) h` ASSUME_TAC THENL
     [REWRITE_TAC[leb_fires] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `h:num = v` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[LEB_FIRES_UNIQUE];
        ASM_MESON_TAC[RD_ID_PAYLOAD_CANCEL]]]]);;

let RD_ID_PAYLOAD_STEP = prove
 (`!n bs v next.
      leb_fires bs v /\ bs = APPEND (leb_enc v) next
      ==> ((?ids rest. rd_id_payload (SUC n) bs ids rest) <=>
           (?ids rest. rd_id_payload n next ids rest))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `ids:num list` (X_CHOOSE_TAC `rest:num list`)) THEN
    MP_TAC(SPECL [`n:num`; `bs:num list`; `ids:num list`; `rest:num list`;
                   `v:num`; `next:num list`] RD_ID_PAYLOAD_PEEL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `tail:num list` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`tail:num list`; `rest:num list`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `tail:num list` (X_CHOOSE_TAC `rest:num list`)) THEN
    MAP_EVERY EXISTS_TAC [`CONS v tail:num list`; `rest:num list`] THEN
    REWRITE_TAC[RD_ID_PAYLOAD_CONS] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[leb_fires]; EXISTS_TAC `next:num list` THEN ASM_REWRITE_TAC[]]]);;

let RD_ID_PAYLOAD_LENGTH = prove
 (`!n bs ids rest. rd_id_payload n bs ids rest ==> n + LENGTH rest <= LENGTH bs`,
  REWRITE_TAC[rd_id_payload] THEN
  SUBGOAL_THEN
   `!ids. LENGTH ids <= LENGTH(ITLIST APPEND (MAP leb_enc ids) [])`
   MP_TAC THENL
   [LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; MAP; ITLIST; LENGTH_APPEND] THEN
    MP_TAC(SPEC `h:num` LEB_ENC_LENGTH_POS) THEN ASM_ARITH_TAC;
    DISCH_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH_APPEND] THEN
    FIRST_ASSUM(MP_TAC o SPEC `ids:num list`) THEN ASM_ARITH_TAC]);;

let RD_ID_PAYLOAD_MALFORMED = prove
 (`!n bs. (!v. ~leb_fires bs v) ==> ~(?ids rest. rd_id_payload (SUC n) bs ids rest)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  X_GEN_TAC `ids:num list` THEN STRUCT_CASES_TAC(ISPEC `ids:num list` list_CASES) THENL
   [REWRITE_TAC[rd_id_payload; LENGTH; NOT_SUC];
    REWRITE_TAC[RD_ID_PAYLOAD_CONS] THEN ASM_MESON_TAC[leb_fires]]);;

let RD_ID_PAYLOAD_AFTER_COUNT = prove
 (`!bs n next ids rest.
     leb_fires bs n /\ bs = APPEND (leb_enc n) next
     ==> (rd_id_payload n next ids rest <=>
          LENGTH ids < 2 EXP 62 /\ ALL (\v. v < 2 EXP 62) ids /\
          bs = APPEND (leb_enc(LENGTH ids))
                      (APPEND (ITLIST APPEND (MAP leb_enc ids) []) rest))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n < 2 EXP 62` ASSUME_TAC THENL
   [ASM_MESON_TAC[leb_fires]; ALL_TAC] THEN
  EQ_TAC THENL
   [REWRITE_TAC[rd_id_payload] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN SUBGOAL_THEN `leb_fires bs (LENGTH(ids:num list))` ASSUME_TAC THENL
     [REWRITE_TAC[leb_fires] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `LENGTH(ids:num list) = n` ASSUME_TAC THENL
       [ASM_MESON_TAC[LEB_FIRES_UNIQUE];
        REWRITE_TAC[rd_id_payload] THEN ASM_MESON_TAC[RD_ID_PAYLOAD_CANCEL]]]]);;

(* The two counted loops can visit the whole 62-bit count range. *)
let RD_ID_CHUNK_COUNT = prove
 (`!n. n < 2 EXP 62 ==> n DIV 2147483648 + 1 <= 2147483648`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `2147483648`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let RD_ID_CHUNK_START = prove
 (`!n chunk. chunk < n DIV 2147483648 + 1 ==> 2147483648 * chunk <= n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `2147483648`] DIVISION) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o C MATCH_MP (ARITH_RULE `~(2147483648 = 0)`)) THEN
  ASM_ARITH_TAC);;

let RD_ID_CHUNK_PREFIX = prove
 (`!n chunk.
     2147483648 * chunk <= n
     ==> 2147483648 * chunk + MIN 2147483648 (n - 2147483648 * chunk) =
         MIN n (2147483648 * (chunk + 1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MIN] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RD_ID_STACK_FITS = prove
 (`!n byte_count. n <= byte_count DIV 8 <=> 8 * n <= byte_count`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`byte_count:num`; `8`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let RD_ID_FLAT_APPEND = prove
 (`!xs ys. ITLIST APPEND (MAP leb_enc (APPEND xs ys)) [] =
          APPEND (ITLIST APPEND (MAP leb_enc xs) [])
                 (ITLIST APPEND (MAP leb_enc ys) [])`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; MAP; ITLIST; APPEND_ASSOC]);;

let RD_ID_PAYLOAD_PUSH = prove
 (`!n bs ids v rest.
     rd_id_payload n bs ids (APPEND (leb_enc v) rest) /\ v < 2 EXP 62
     ==> rd_id_payload (n + 1) bs (APPEND ids [v]) rest`,
  REWRITE_TAC[rd_id_payload; RD_ID_FLAT_APPEND; LENGTH_APPEND; ALL_APPEND;
    LENGTH; ALL; MAP; ITLIST; APPEND_NIL; GSYM APPEND_ASSOC; ARITH_RULE `SUC 0 = 1`] THEN
  SIMP_TAC[]);;
