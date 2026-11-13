(* ========================================================================= *)
(* Minimal unsigned LEB128 (leb_enc, holr_spec.ml) as a prefix code.        *)
(*                                                                           *)
(* leb_dec reads a byte string as base-128 digits, least significant first; *)
(* it inverts leb_enc. Over a byte string bs, a value v < 2^62 fires when   *)
(* bs begins with leb_enc v (leb_fires), and bs is short when it is a       *)
(* proper prefix of such an encoding (leb_short): a streaming reader needs  *)
(* more input exactly then. No byte string is both, and at most one value   *)
(* fires. A reader that scans bytes c 0, c 1, ... sees the encoding's shape *)
(* byte by byte: the bytes before the first one without its high bit are    *)
(* continuations, and that byte ends the encoding. The LEB_SEQ_* theorems   *)
(* give the verdict at each of a scan's stops.                              *)
(* ========================================================================= *)

needs "native/hol/holr_bytes.ml";;

let leb_dec = define
 `(leb_dec [] = 0) /\
  (leb_dec (CONS b l) = b MOD 128 + 128 * leb_dec l)`;;

let leb_fires = new_definition
 `leb_fires bs v <=> v < 2 EXP 62 /\ ?rest. bs = APPEND (leb_enc v) rest`;;

let leb_short = new_definition
 `leb_short bs <=> ?v rest. v < 2 EXP 62 /\ leb_enc v = APPEND bs rest /\ ~(rest = [])`;;

(* ------------------------------------------------------------------------- *)
(* Decoding inverts encoding.                                                *)
(* ------------------------------------------------------------------------- *)

let LEB_DIGIT_SPLIT = prove
 (`!v. ~(v < 128) ==> v DIV 128 < v /\ 0 < v DIV 128 /\
                      (v MOD 128 + 128) MOD 128 = v MOD 128 /\
                      v MOD 128 + 128 * (v DIV 128) = v /\
                      128 <= v MOD 128 + 128 /\ v MOD 128 + 128 < 256`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPECL [`v:num`; `128`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `x + 128 = 1 * 128 + x`] THEN
  REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_REFL] THEN ASM_ARITH_TAC);;

let LEB_DEC_ENC = prove
 (`!v. leb_dec (leb_enc v) = v`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `v:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[leb_enc_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[leb_dec; MOD_LT; MULT_CLAUSES; ADD_CLAUSES] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LEB_DIGIT_SPLIT) THEN
  ASM_SIMP_TAC[]);;

let LEB_ENC_INJ = prove
 (`!v w. leb_enc v = leb_enc w <=> v = w`,
  MESON_TAC[LEB_DEC_ENC]);;

(* ------------------------------------------------------------------------- *)
(* The shape of an encoding: every byte is below 256; a byte has its high    *)
(* bit exactly when it is not the last; the last is not 0 after a            *)
(* continuation; a value below 128^(k+1) takes at most k + 1 bytes.          *)
(* ------------------------------------------------------------------------- *)

let LEB_ENC_LENGTH_POS = prove
 (`!v. 0 < LENGTH (leb_enc v)`,
  REWRITE_TAC[LT_NZ; LENGTH_EQ_NIL; LEB_ENC_NONEMPTY]);;

let LEB_ENC_LENGTH_1 = prove
 (`!v. LENGTH (leb_enc v) = 1 <=> v < 128`,
  GEN_TAC THEN ONCE_REWRITE_TAC[leb_enc_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LENGTH; ONE; SUC_INJ; LENGTH_EQ_NIL; LEB_ENC_NONEMPTY]);;

let LEB_ENC_LENGTH_LE = prove
 (`!k v. v < 128 EXP (SUC k) ==> LENGTH (leb_enc v) <= SUC k`,
  INDUCT_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[leb_enc_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN TRY ARITH_TAC THENL
   [REWRITE_TAC[EXP_1] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN REWRITE_TAC[LE_SUC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `v < 128 EXP SUC (SUC k)` THEN REWRITE_TAC[EXP] THEN ARITH_TAC]);;

let LEB_ENC_LENGTH_62 = prove
 (`!v. v < 2 EXP 62 ==> LENGTH (leb_enc v) <= 9`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`8`; `v:num`] LEB_ENC_LENGTH_LE) THEN
  ANTS_TAC THENL [UNDISCH_TAC `v < 2 EXP 62` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
                  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]]);;

let LEB_ENC_BYTES = prove
 (`!v j. j < LENGTH (leb_enc v)
         ==> EL j (leb_enc v) < 256 /\
             (128 <= EL j (leb_enc v) <=> j + 1 < LENGTH (leb_enc v)) /\
             (j + 1 = LENGTH (leb_enc v) /\ ~(j = 0) ==> ~(EL j (leb_enc v) = 0))`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `v:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[leb_enc_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[LENGTH; ARITH_RULE `j < SUC 0 <=> j = 0`] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EL; HD] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LEB_DIGIT_SPLIT) THEN
  MP_TAC(SPEC `v DIV 128` LEB_ENC_LENGTH_POS) THEN DISCH_TAC THEN
  X_GEN_TAC `j:num` THEN STRUCT_CASES_TAC(SPEC `j:num` num_CASES) THEN
  REWRITE_TAC[LENGTH; EL; HD; TL] THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LT_SUC; ARITH_RULE `SUC j + 1 < SUC n <=> j + 1 < n`;
              ARITH_RULE `SUC j + 1 = SUC n <=> j + 1 = n`; NOT_SUC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v DIV 128` o check (fun th -> is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 0` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `v DIV 128 < 128` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LEB_ENC_LENGTH_1] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[leb_enc_def] THEN ASM_REWRITE_TAC[EL; HD] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Byte strings as sequences, and the value of their digits.                 *)
(* ------------------------------------------------------------------------- *)

let LIST_OF_SEQ_CONS = prove
 (`!(c:num->A) n. list_of_seq c (SUC n) = CONS (c 0) (list_of_seq (\j. c (SUC j)) n)`,
  GEN_TAC THEN INDUCT_TAC THEN ONCE_REWRITE_TAC[list_of_seq] THEN
  ASM_REWRITE_TAC[list_of_seq; APPEND]);;

let LIST_OF_SEQ_ADD = prove
 (`!(c:num->A) m n. list_of_seq c (m + n) =
                    APPEND (list_of_seq c m) (list_of_seq (\j. c (m + j)) n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_of_seq; ADD_CLAUSES; APPEND_NIL; APPEND_ASSOC]);;

let LIST_OF_SEQ_PREFIX = prove
 (`!(c:num->A) n l.
     (?rest. list_of_seq c n = APPEND l rest) <=>
     LENGTH l <= n /\ !j. j < LENGTH l ==> c j = EL j l`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `rest:A list`) THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:A list->num`) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_APPEND] THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `EL j:A list->A`) THEN
    ASM_SIMP_TAC[EL_APPEND; EL_LIST_OF_SEQ; ARITH_RULE `j < l ==> j < l + r:num`];
    STRIP_TAC THEN
    EXISTS_TAC `list_of_seq (\j. (c:num->A) (LENGTH (l:A list) + j)) (n - LENGTH l)` THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [MATCH_MP (ARITH_RULE `m <= n ==> n = m + (n - m)`) th]) THEN
    REWRITE_TAC[LIST_OF_SEQ_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ]]);;

let LEB_DEC_APPEND = prove
 (`!l1 l2. leb_dec (APPEND l1 l2) = leb_dec l1 + 128 EXP (LENGTH l1) * leb_dec l2`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; leb_dec; LENGTH; EXP] THEN
  ARITH_TAC);;

let LEB_DEC_SEQ_SUC = prove
 (`!c i. leb_dec (list_of_seq c (SUC i)) =
         leb_dec (list_of_seq c i) + (c i MOD 128) * 128 EXP i`,
  REWRITE_TAC[list_of_seq; LEB_DEC_APPEND; LENGTH_LIST_OF_SEQ; leb_dec] THEN ARITH_TAC);;

let LEB_DEC_LT = prove
 (`!l. leb_dec l < 128 EXP (LENGTH l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[leb_dec; LENGTH; EXP] THENL
   [ARITH_TAC;
    POP_ASSUM MP_TAC THEN MP_TAC(SPECL [`h:num`; `128`] DIVISION) THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A scan: bytes c 0 .. c (i-1) with their high bits and c i without (and    *)
(* not 0 after a continuation) are the encoding of their value.              *)
(* ------------------------------------------------------------------------- *)

let LEB_ENC_SEQ = prove
 (`!i c. (!j. j < i ==> 128 <= c j /\ c j < 256) /\ c i < 128 /\
         (~(i = 0) ==> ~(c i = 0))
         ==> leb_enc (leb_dec (list_of_seq c (SUC i))) = list_of_seq c (SUC i)`,
  INDUCT_TAC THEN GEN_TAC THEN STRIP_TAC THENL
   [REWRITE_TAC[list_of_seq; APPEND; leb_dec] THEN
    ASM_SIMP_TAC[MOD_LT; MULT_CLAUSES; ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC[leb_enc_def] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[LIST_OF_SEQ_CONS] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\j. (c:num->num) (SUC j)`) THEN BETA_TAC THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[NOT_SUC]];
    ALL_TAC] THEN
  ABBREV_TAC `l = list_of_seq (\j. (c:num->num) (SUC j)) (SUC i)` THEN
  DISCH_TAC THEN REWRITE_TAC[leb_dec] THEN
  SUBGOAL_THEN `128 <= c 0 /\ c 0 < 256` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(leb_dec l = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `leb_enc (leb_dec l) = l` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[leb_enc_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
    EXPAND_TAC "l" THEN REWRITE_TAC[LIST_OF_SEQ_CONS; CONS_11] THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[LIST_OF_SEQ_EQ_NIL] THEN
    ASM_MESON_TAC[NOT_SUC];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[leb_enc_def] THEN
  SUBGOAL_THEN `~(c 0 MOD 128 + 128 * leb_dec l < 128)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(leb_dec l = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[CONS_11] THEN
  SUBGOAL_THEN `c 0 MOD 128 = c 0 - 128` ASSUME_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `x + 128 * y = y * 128 + x`] THEN
  SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ] THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN SIMP_TAC[DIV_LT; MOD_LT_EQ; ARITH_EQ; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* An encoding that is a prefix of a scan ends at the scan's first byte      *)
(* without its high bit.                                                     *)
let LEB_PREFIX_SCAN = prove
 (`!v (c:num->num) i.
     (!j. j < LENGTH (leb_enc v) ==> c j = EL j (leb_enc v)) /\
     (!j. j < i ==> 128 <= c j)
     ==> i < LENGTH (leb_enc v) /\ (c i < 128 ==> LENGTH (leb_enc v) = SUC i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `v:num` LEB_ENC_LENGTH_POS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < LENGTH (leb_enc v)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`v:num`; `LENGTH (leb_enc v) - 1`] LEB_ENC_BYTES) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `128 <= EL (LENGTH (leb_enc v) - 1) (leb_enc v)` MP_TAC THENL
     [SUBGOAL_THEN `EL (LENGTH (leb_enc v) - 1) (leb_enc v) = c (LENGTH (leb_enc v) - 1)`
       SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `EL i (leb_enc v) = c i` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`v:num`; `i:num`] LEB_ENC_BYTES) THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Firing and shortness over a sequence of n bytes.                         *)
(* ------------------------------------------------------------------------- *)

let LEB_FIRES_SEQ = prove
 (`!c n v. leb_fires (list_of_seq c n) v <=>
           v < 2 EXP 62 /\ LENGTH (leb_enc v) <= n /\
           !j. j < LENGTH (leb_enc v) ==> c j = EL j (leb_enc v)`,
  REWRITE_TAC[leb_fires; GSYM LIST_OF_SEQ_PREFIX]);;

let LEB_SHORT_SEQ = prove
 (`!c n. leb_short (list_of_seq c n) ==> n <= 8 /\ !j. j < n ==> 128 <= c j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[leb_short; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v:num`; `rest:num list`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:num list->num`) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_LIST_OF_SEQ] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `~(rest:num list = [])`)) THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(SPEC `v:num` LEB_ENC_LENGTH_62) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`v:num`; `j:num`] LEB_ENC_BYTES) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `EL j (leb_enc v) = c j` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[EL_APPEND; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ];
    ASM_ARITH_TAC]);;

let LEB_SEQ_NOT_FIRES = prove
 (`!c n v. leb_fires (list_of_seq c n) v
           ==> !i. (!j. j < i ==> 128 <= c j)
                   ==> i < LENGTH (leb_enc v) /\
                       (c i < 128 ==> list_of_seq c (SUC i) = leb_enc v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LEB_FIRES_SEQ] THEN STRIP_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`v:num`; `c:num->num`; `i:num`] LEB_PREFIX_SCAN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH (leb_enc v) = SUC i` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[EL_LIST_OF_SEQ] THEN ASM_MESON_TAC[]);;

(* The verdict at each stop of a scan of the n bytes available.              *)

(* Byte i ends the scan, is not 0 after a continuation, and the value is     *)
(* below 2^62: the bytes begin with the value's encoding.                    *)
let LEB_SEQ_FIRES = prove
 (`!c n i. i < n /\ (!j. j < i ==> 128 <= c j /\ c j < 256) /\ c i < 128 /\
           (~(i = 0) ==> ~(c i = 0)) /\ leb_dec (list_of_seq c (SUC i)) < 2 EXP 62
           ==> leb_fires (list_of_seq c n) (leb_dec (list_of_seq c (SUC i))) /\
               LENGTH (leb_enc (leb_dec (list_of_seq c (SUC i)))) = SUC i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LEB_FIRES_SEQ] THEN
  MP_TAC(SPECL [`i:num`; `c:num->num`] LEB_ENC_SEQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[EL_LIST_OF_SEQ]]);;

(* All n <= 8 bytes have their high bit: the input ends first.               *)
let LEB_SEQ_SHORT = prove
 (`!c n. n <= 8 /\ (!j. j < n ==> 128 <= c j /\ c j < 256)
         ==> leb_short (list_of_seq c n) /\ !v. ~leb_fires (list_of_seq c n) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `v:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP LEB_SEQ_NOT_FIRES) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `leb_fires (list_of_seq c n) v` THEN
    REWRITE_TAC[LEB_FIRES_SEQ] THEN ARITH_TAC] THEN
  ABBREV_TAC `d = \j. if j < n then (c:num->num) j else 1` THEN
  SUBGOAL_THEN `list_of_seq (d:num->num) n = list_of_seq (c:num->num) n` ASSUME_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN SIMP_TAC[EL_LIST_OF_SEQ] THEN
    EXPAND_TAC "d" THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `d:num->num`] LEB_ENC_SEQ) THEN ANTS_TAC THENL
   [EXPAND_TAC "d" THEN ASM_SIMP_TAC[LT_REFL] THEN ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `(d:num->num) n = 1` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[LT_REFL]; ALL_TAC] THEN
  REWRITE_TAC[leb_short] THEN
  MAP_EVERY EXISTS_TAC [`leb_dec (list_of_seq d (SUC n))`; `[1]`] THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[LEB_DEC_SEQ_SUC] THEN
    MP_TAC(ISPEC `list_of_seq (d:num->num) n` LEB_DEC_LT) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
    MP_TAC(SPECL [`128`; `n:num`; `8`] LE_EXP) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ASM_REWRITE_TAC[list_of_seq]]);;

(* Byte i is 0 after a continuation: malformed.                              *)
let LEB_SEQ_NONMINIMAL = prove
 (`!c n i. i < n /\ ~(i = 0) /\ c i = 0 /\ (!j. j < i ==> 128 <= c j)
           ==> (!v. ~leb_fires (list_of_seq c n) v) /\ ~leb_short (list_of_seq c n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `v:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP LEB_SEQ_NOT_FIRES) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 128`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:num list->num`) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `EL i (leb_enc v) = 0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `leb_enc v`
                               then REWRITE_TAC[GSYM th] else NO_TAC) THEN
      ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `i < SUC i`];
      ALL_TAC] THEN
    MP_TAC(SPECL [`v:num`; `i:num`] LEB_ENC_BYTES) THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP LEB_SHORT_SEQ) THEN
    DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* Byte i ends the scan and the value is 2^62 or more: malformed.            *)
let LEB_SEQ_TOO_BIG = prove
 (`!c n i. i < n /\ (!j. j < i ==> 128 <= c j) /\ c i < 128 /\
           2 EXP 62 <= leb_dec (list_of_seq c (SUC i))
           ==> (!v. ~leb_fires (list_of_seq c n) v) /\ ~leb_short (list_of_seq c n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `v:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP LEB_SEQ_NOT_FIRES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `2 EXP 62 <= leb_dec (list_of_seq c (SUC i))` THEN
    ASM_REWRITE_TAC[LEB_DEC_ENC] THEN
    UNDISCH_TAC `leb_fires (list_of_seq c n) v` THEN REWRITE_TAC[leb_fires] THEN ARITH_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP LEB_SHORT_SEQ) THEN
    DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

(* Nine bytes with their high bits: malformed.                               *)
let LEB_SEQ_NINE = prove
 (`!c n. 9 <= n /\ (!j. j < 9 ==> 128 <= c j)
         ==> (!v. ~leb_fires (list_of_seq c n) v) /\ ~leb_short (list_of_seq c n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `v:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `9` o MATCH_MP LEB_SEQ_NOT_FIRES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `leb_fires (list_of_seq c n) v` THEN REWRITE_TAC[leb_fires] THEN
    STRIP_TAC THEN MP_TAC(SPEC `v:num` LEB_ENC_LENGTH_62) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP LEB_SHORT_SEQ) THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* At most one value fires, and a byte string that fires is not short.      *)
(* ------------------------------------------------------------------------- *)

let LEB_FIRES_LAST = prove
 (`!c n v. leb_fires (list_of_seq c n) v
           ==> (!j. j + 1 < LENGTH (leb_enc v) ==> 128 <= c j) /\
               c (LENGTH (leb_enc v) - 1) < 128 /\ LENGTH (leb_enc v) - 1 < n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LEB_FIRES_SEQ] THEN STRIP_TAC THEN
  MP_TAC(SPEC `v:num` LEB_ENC_LENGTH_POS) THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`v:num`; `j:num`] LEB_ENC_BYTES) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
    MP_TAC(SPECL [`v:num`; `LENGTH (leb_enc v) - 1`] LEB_ENC_BYTES) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (leb_enc v) - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let LEB_FIRES_UNIQUE = prove
 (`!bs v w. leb_fires bs v /\ leb_fires bs w ==> v = w`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ABBREV_TAC `c = \i. EL i (bs:num list)` THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP LEB_FIRES_LAST
    (ASSUME `leb_fires (list_of_seq c (LENGTH (bs:num list))) v`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!j. j < LENGTH (leb_enc v) - 1 ==> 128 <= c j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `LENGTH (leb_enc v) - 1` (MATCH_MP LEB_SEQ_NOT_FIRES
    (ASSUME `leb_fires (list_of_seq c (LENGTH (bs:num list))) v`))) THEN
  MP_TAC(SPEC `LENGTH (leb_enc v) - 1` (MATCH_MP LEB_SEQ_NOT_FIRES
    (ASSUME `leb_fires (list_of_seq c (LENGTH (bs:num list))) w`))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM LEB_ENC_INJ] THEN ASM_MESON_TAC[]);;

let LEB_FIRES_NOT_SHORT = prove
 (`!bs v. leb_fires bs v ==> ~leb_short bs`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ABBREV_TAC `c = \i. EL i (bs:num list)` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LEB_FIRES_LAST) THEN
  DISCH_THEN(MP_TAC o SPEC `LENGTH (leb_enc v) - 1` o CONJUNCT2 o MATCH_MP LEB_SHORT_SEQ) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
