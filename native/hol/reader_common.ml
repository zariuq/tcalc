(* ========================================================================= *)
(* The HOLR reader's view of a t-ISA p1 state: the bytes of a region as     *)
(* numbers, as a list, and from an offset on. Shared by the reader's        *)
(* routines (reader_leb128.ml, reader_fnv.ml).                               *)
(* ========================================================================= *)

needs "native/hol/tisa_wp.ml";;

(* Byte i of region r, its whole contents, and its bytes from an offset on   *)
(* (none when the offset lies past the end).                                 *)
let region_byte = new_definition
 `region_byte st r i = val(tisa_read st (word_add (tisa_base st r) (word i)) 1)`;;

let region_bytes = new_definition
 `region_bytes st r = list_of_seq (region_byte st r) (val(tisa_len st r))`;;

let region_from = new_definition
 `region_from st r off = list_of_seq (\j. region_byte st r (off + j)) (val(tisa_len st r) - off)`;;

(* The n bytes of region r from an offset. *)
let region_range = new_definition
 `region_range st r off n = list_of_seq (\j. region_byte st r (off + j)) n`;;

let REGION_BYTE_LT = prove
 (`!st r i. region_byte st r i < 256`,
  REPEAT GEN_TAC THEN REWRITE_TAC[region_byte; tisa_read; VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `read (bytes (word_add (tisa_base st r) (word i),1)) (tmem st)` THEN
  REWRITE_TAC[MOD_LE] THEN
  MP_TAC(ISPECL [`word_add (tisa_base st r) (word i):int64`; `1`; `tmem st`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let READ_REGION_BYTE = prove
 (`!st r i. tisa_read st (word_add (tisa_base st r) (word i)) 1 = word (region_byte st r i)`,
  REWRITE_TAC[region_byte; WORD_VAL]);;

let VAL_WORD_REGION_BYTE = prove
 (`!st r i. val(word (region_byte st r i):int64) = region_byte st r i`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN
  MP_TAC(SPECL [`st:tisa_state`; `r:num`; `i:num`] REGION_BYTE_LT) THEN ARITH_TAC);;

(* A region whose contents are pre followed by suf has suf from the offset   *)
(* LENGTH pre on.                                                            *)
let REGION_FROM_SPLIT = prove
 (`!st r off pre suf. region_bytes st r = APPEND pre suf /\ LENGTH pre = off
                      ==> region_from st r off = suf`,
  REPEAT GEN_TAC THEN REWRITE_TAC[region_bytes; region_from] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:num list->num`) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_APPEND] THEN DISCH_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `j < val(tisa_len st r) - off` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `EL (off + j):num list->num` o
    check (fun th -> is_eq(concl th) && is_comb(lhand(concl th)) &&
                     can (find_term ((=) `list_of_seq:(num->num)->num->num list`)) (lhand(concl th)))) THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `j < l - off ==> off + j < l`; EL_APPEND] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(off + j < off)`; ADD_SUB2]);;
