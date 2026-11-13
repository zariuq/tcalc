(* ========================================================================= *)
(* The HOLR reader's minimal unsigned LEB128 decoder, as the standalone      *)
(* t-ISA p1 program leb128 (tcalc/native/reader/leb128.metta; its text is    *)
(* tcalc/native/reader/leb128_prog.txt, its image record leb128.hol).        *)
(*                                                                           *)
(* Regions: 0 input (RO), 1 out (RW, at least 16 bytes); arg0 the offset.   *)
(* The bytes from the offset to the input's end are leb128_bytes st.        *)
(*                                                                           *)
(* LEB128_RUN: every run from a state entry validation accepts ends in one  *)
(* of three ways, each characterized by the format's own encoding leb_enc   *)
(* (holr_leb.ml):                                                           *)
(*   FIRED with ret_val v and out = (v, LENGTH (leb_enc v)), where the      *)
(*     bytes begin with leb_enc v and v < 2^62 (leb_fires);                 *)
(*   REFUSED with ret_val 2, the bytes being a proper prefix of such an     *)
(*     encoding: the input ends first (leb_short);                          *)
(*   REFUSED with ret_val 1 otherwise: a malformed integer.                 *)
(* LEB128_SOUND and LEB128_COMPLETE are its two directions for FIRED;       *)
(* LEB128_SHORT and LEB128_MALFORMED its two refusals. These are CeTTa's    *)
(* reader's verdicts (hol_stream.c, cur_uv): its "need input" is leb_short, *)
(* its integer error the rest.                                               *)
(*                                                                           *)
(* The loop body is proved with the weakest-precondition generator of       *)
(* tisa_wp.ml and the invariant leb128_inv; the verdict at each of its      *)
(* stops is a LEB_SEQ_* theorem of holr_leb.ml, independent of t-ISA.        *)
(* ========================================================================= *)

needs "native/hol/reader_common.ml";;
needs "native/hol/holr_leb.ml";;

(* ------------------------------------------------------------------------- *)
(* The program, as its text leb128_prog.txt; LEB128_TERM is that text.      *)
(* ------------------------------------------------------------------------- *)

let leb128_prologue = new_definition
 `leb128_prologue = (TSeq (TInstr (TLoadFrame TyU64 1 22)) (TSeq (TInstr (TLoadFrame TyU64 2 1)) (TSeq (TInstr (TCmp CondUlt TyU64 9 2 (OpReg 1))) (TSeq (TIf 9 (TSeq (TInstr (TImm TyU64 10 (word 2))) (TReturn 0 10)) TSkip) (TSeq (TInstr (TBin BinSub TyU64 2 2 1)) (TSeq (TInstr (TLoadFrame TyPtr 3 0)) (TSeq (TInstr (TAddr 0 3 3 (SOME 1) 0 (&0:int))) (TSeq (TInstr (TImm TyU64 4 (word 0))) (TSeq (TInstr (TImm TyU64 5 (word 1))) (TInstr (TImm TyU64 7 (word 9))))))))))))`;;

let leb128_body = new_definition
 `leb128_body = (TSeq (TInstr (TMov TyU64 1 6)) (TSeq (TInstr (TCmp CondUle TyU64 9 2 (OpReg 1))) (TSeq (TIf 9 (TSeq (TInstr (TImm TyU64 10 (word 2))) (TReturn 0 10)) TSkip) (TSeq (TInstr (TAddr 0 11 3 (SOME 6) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 1 0 8 11 (&0:int))) (TSeq (TInstr (TCmp CondUlt TyU64 9 8 (OpImm (word 128)))) (TIf 9 (TSeq (TInstr (TCmp CondNe TyU64 9 1 (OpImm (word 0)))) (TSeq (TInstr (TCmp CondEq TyU64 10 8 (OpImm (word 0)))) (TSeq (TInstr (TBin BinAnd TyBool 9 9 10)) (TSeq (TIf 9 (TSeq (TInstr (TImm TyU64 10 (word 1))) (TReturn 0 10)) TSkip) (TSeq (TInstr (TBin BinMulLo TyU64 8 8 5)) (TSeq (TInstr (TBin BinAdd TyU64 4 4 8)) (TSeq (TInstr (TImm TyU64 10 (word 4611686018427387904))) (TSeq (TInstr (TCmp CondUle TyU64 9 10 (OpReg 4))) (TSeq (TIf 9 (TSeq (TInstr (TImm TyU64 10 (word 1))) (TReturn 0 10)) TSkip) (TSeq (TInstr (TLoadFrame TyPtr 11 2)) (TSeq (TInstr (TStore 8 1 11 (&0:int) 4)) (TSeq (TInstr (TImm TyU64 10 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 10 1 10)) (TSeq (TInstr (TStore 8 1 11 (&8:int) 10)) (TReturn 1 4))))))))))))))) (TSeq (TInstr (TImm TyU64 10 (word 128))) (TSeq (TInstr (TBin BinSub TyU64 8 8 10)) (TSeq (TInstr (TBin BinMulLo TyU64 8 8 5)) (TSeq (TInstr (TBin BinAdd TyU64 4 4 8)) (TInstr (TShift ShiftLeft TyU64 5 5 7)))))))))))))`;;

let leb128 = new_definition
 `leb128 = TProg [(1,0,1); (2,16,8)] [] (TSeq leb128_prologue (TSeq (TCountLoop 6 7 9 leb128_body) (TSeq (TInstr (TImm TyU64 10 (word 1))) (TReturn 0 10))))`;;

let LEB128_TERM = prove
 (`leb128 = (TProg [(1,0,1); (2,16,8)] [] (TSeq (TSeq (TInstr (TLoadFrame TyU64 1 22)) (TSeq (TInstr (TLoadFrame TyU64 2 1)) (TSeq (TInstr (TCmp CondUlt TyU64 9 2 (OpReg 1))) (TSeq (TIf 9 (TSeq (TInstr (TImm TyU64 10 (word 2))) (TReturn 0 10)) TSkip) (TSeq (TInstr (TBin BinSub TyU64 2 2 1)) (TSeq (TInstr (TLoadFrame TyPtr 3 0)) (TSeq (TInstr (TAddr 0 3 3 (SOME 1) 0 (&0:int))) (TSeq (TInstr (TImm TyU64 4 (word 0))) (TSeq (TInstr (TImm TyU64 5 (word 1))) (TInstr (TImm TyU64 7 (word 9)))))))))))) (TSeq (TCountLoop 6 7 9 (TSeq (TInstr (TMov TyU64 1 6)) (TSeq (TInstr (TCmp CondUle TyU64 9 2 (OpReg 1))) (TSeq (TIf 9 (TSeq (TInstr (TImm TyU64 10 (word 2))) (TReturn 0 10)) TSkip) (TSeq (TInstr (TAddr 0 11 3 (SOME 6) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 1 0 8 11 (&0:int))) (TSeq (TInstr (TCmp CondUlt TyU64 9 8 (OpImm (word 128)))) (TIf 9 (TSeq (TInstr (TCmp CondNe TyU64 9 1 (OpImm (word 0)))) (TSeq (TInstr (TCmp CondEq TyU64 10 8 (OpImm (word 0)))) (TSeq (TInstr (TBin BinAnd TyBool 9 9 10)) (TSeq (TIf 9 (TSeq (TInstr (TImm TyU64 10 (word 1))) (TReturn 0 10)) TSkip) (TSeq (TInstr (TBin BinMulLo TyU64 8 8 5)) (TSeq (TInstr (TBin BinAdd TyU64 4 4 8)) (TSeq (TInstr (TImm TyU64 10 (word 4611686018427387904))) (TSeq (TInstr (TCmp CondUle TyU64 9 10 (OpReg 4))) (TSeq (TIf 9 (TSeq (TInstr (TImm TyU64 10 (word 1))) (TReturn 0 10)) TSkip) (TSeq (TInstr (TLoadFrame TyPtr 11 2)) (TSeq (TInstr (TStore 8 1 11 (&0:int) 4)) (TSeq (TInstr (TImm TyU64 10 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 10 1 10)) (TSeq (TInstr (TStore 8 1 11 (&8:int) 10)) (TReturn 1 4))))))))))))))) (TSeq (TInstr (TImm TyU64 10 (word 128))) (TSeq (TInstr (TBin BinSub TyU64 8 8 10)) (TSeq (TInstr (TBin BinMulLo TyU64 8 8 5)) (TSeq (TInstr (TBin BinAdd TyU64 4 4 8)) (TInstr (TShift ShiftLeft TyU64 5 5 7)))))))))))))) (TSeq (TInstr (TImm TyU64 10 (word 1))) (TReturn 0 10)))))`,
  REWRITE_TAC[leb128; leb128_prologue; leb128_body]);;

(* ------------------------------------------------------------------------- *)
(* What a run means: the bytes from the offset, the out words, the verdict. *)
(* ------------------------------------------------------------------------- *)

let leb128_bytes = new_definition
 `leb128_bytes st = region_from st 0 (val(tisa_fword st 22))`;;

let leb128_out = new_definition
 `leb128_out st k = tisa_read st (word_add (tisa_base st 1) (word (8 * k))) 8`;;

(* The memory a run leaves: the entry memory with the out words (a FIRED   *)
(* run) and the status and return words written, and nothing else.          *)
let leb128_post = new_definition
 `leb128_post st k s <=>
    (k = 1 /\ ?v. leb_fires (leb128_bytes st) v /\ tisa_fword s 19 = word v /\
                  leb128_out s 0 = word v /\ leb128_out s 1 = word (LENGTH (leb_enc v)) /\
                  tmem s = tmem (tisa_finst 1 (word v)
                                  (tisa_store (word_add (tisa_base st 1) (word 8)) 8
                                              (word (LENGTH (leb_enc v)))
                                  (tisa_store (tisa_base st 1) 8 (word v) st)))) \/
    (k = 0 /\ tisa_fword s 19 = word 2 /\ leb_short (leb128_bytes st) /\
              tmem s = tmem (tisa_finst 0 (word 2) st)) \/
    (k = 0 /\ tisa_fword s 19 = word 1 /\ (!v. ~leb_fires (leb128_bytes st) v) /\
              ~leb_short (leb128_bytes st) /\ tmem s = tmem (tisa_finst 0 (word 1) st))`;;

(* The loop invariant before byte i, over the entry state st: the registers *)
(* of the prologue (avail = len - off, at = the integer's first byte), the  *)
(* value of the bytes before i, the scale 128^i, and those bytes exist and  *)
(* have their high bits.                                                     *)
let leb128_inv = new_definition
 `leb128_inv st N i s <=>
    tregs s 0 = tregs st 0 /\ tmem s = tmem st /\ N = 9 /\
    val(tisa_fword st 22) <= val(tisa_len st 0) /\
    tregs s 2 = word_sub (tisa_len st 0) (tisa_fword st 22) /\
    tregs s 3 = word_add (tisa_base st 0) (word (1 * val (tisa_fword st 22))) /\
    tregs s 4 = word (leb_dec (list_of_seq (\j. region_byte st 0 (val(tisa_fword st 22) + j)) i)) /\
    tregs s 5 = word (128 EXP i) /\
    i <= val(tisa_len st 0) - val(tisa_fword st 22) /\
    (!j. j < i ==> 128 <= region_byte st 0 (val(tisa_fword st 22) + j))`;;

(* ------------------------------------------------------------------------- *)
(* Entry validation: the regions' bounds and separations.                    *)
(* ------------------------------------------------------------------------- *)

let LEB128_ENTRY = prove
 (`!st. tisa_entry_ok leb128 st
        ==> val(tregs st 0) + 192 <= 2 EXP 64 /\
            val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64 /\
            (val(tisa_len st 0) = 0 \/
             val(tisa_base st 0) + val(tisa_len st 0) <= val(tregs st 0) + 144 \/
             val(tregs st 0) + 192 <= val(tisa_base st 0)) /\
            16 <= val(tisa_len st 1) /\
            val(tisa_base st 1) + val(tisa_len st 1) < 2 EXP 64 /\
            (val(tisa_base st 1) + val(tisa_len st 1) <= val(tregs st 0) \/
             val(tregs st 0) + 192 <= val(tisa_base st 1)) /\
            (val(tisa_len st 0) = 0 \/
             val(tisa_base st 0) + val(tisa_len st 0) <= val(tisa_base st 1) \/
             val(tisa_base st 1) + val(tisa_len st 1) <= val(tisa_base st 0))`,
  GEN_TAC THEN
  REWRITE_TAC[leb128; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok;
              tisa_region_ok; tisa_pair_ok; tisa_frame; tisa_base; tisa_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(val(tisa_fword st 3) = 0)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `val(tisa_fword st 1) = 0` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* One byte's step on the value and the scale.                               *)
(* ------------------------------------------------------------------------- *)

let LEB_STEP_VAL = prove
 (`!A b j. A < 128 EXP j /\ b < 128 /\ j < 9
           ==> val(word_add (word A) (word_mul (word b) (word (128 EXP j))):int64) =
               A + b * 128 EXP j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_MUL; GSYM WORD_ADD] THEN
  MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN
  SUBGOAL_THEN `128 EXP j <= 128 EXP 8` MP_TAC THENL
   [REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `b * 128 EXP j <= 127 * 128 EXP j` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let LEB_STEP_WORD = prove
 (`!A b S. 128 <= b
           ==> word_add (word A) (word_mul (word_sub (word b) (word 128)) (word S)):int64 =
               word (A + (b - 128) * S)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_SUB2; GSYM WORD_MUL; GSYM WORD_ADD]);;

(* A final byte: the value the comparison with 2^62 sees, and the word. *)
let LEB_STEP_DEC = prove
 (`!c j. c j < 128 /\ j < 9
         ==> val(word_add (word (leb_dec (list_of_seq c j)))
                          (word_mul (word (c j)) (word (128 EXP j))):int64) =
             leb_dec (list_of_seq c (SUC j))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LEB_STEP_VAL o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `list_of_seq (c:num->num) j` LEB_DEC_LT) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[LEB_DEC_SEQ_SUC; MOD_LT]]);;

let LEB_STEP_FINAL = prove
 (`!c j. c j < 128
         ==> word_add (word (leb_dec (list_of_seq c j)))
                      (word_mul (word (c j)) (word (128 EXP j))):int64 =
             word (leb_dec (list_of_seq c (SUC j)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM WORD_ADD; GSYM WORD_MUL; LEB_DEC_SEQ_SUC; MOD_LT]);;

(* A continuation byte. *)
let LEB_STEP_CONT = prove
 (`!c j. 128 <= c j /\ c j < 256
         ==> word_add (word (leb_dec (list_of_seq c j)))
                      (word_mul (word_sub (word (c j)) (word 128)) (word (128 EXP j))):int64 =
             word (leb_dec (list_of_seq c (SUC j)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LEB_STEP_WORD; LEB_DEC_SEQ_SUC] THEN
  SUBGOAL_THEN `(c:num->num) j MOD 128 = c j - 128` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC);;

let LEB_SCALE_STEP = prove
 (`!j. word_shl (word (128 EXP j):int64) 7 = word (128 EXP (SUC j))`,
  REWRITE_TAC[WORD_SHL_WORD; EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The loop body: each stop's verdict, or the invariant one byte further.    *)
(* ------------------------------------------------------------------------- *)

(* The bytes from the offset, as the sequence the LEB_SEQ_* theorems scan. *)
let LEB128_C = `\j. region_byte st 0 (val (tisa_fword st 22) + j)`;;

(* The invariant unfolded, the entry facts, the loop state's view as the     *)
(* entry state's, and the values of the index and of avail.                  *)
let LEB128_BODY_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [leb128_inv] o
                check (fun th -> tisa_has_tm `leb128_inv` th)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = 9`)) THEN
  MP_TAC(ISPECL [`s0:tisa_state`; `st:tisa_state`] TISA_SAME_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LEB128_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN TISA_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (tisa_len st 0) (tisa_fword st 22)) =
                val(tisa_len st 0) - val(tisa_fword st 22)` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_SUB_EXACT THEN ASM_REWRITE_TAC[]; ALL_TAC];;

(* A leaf in the reader's terms: comparisons with word 0 as values, the     *)
(* byte read as region_byte, constant words as numbers.                      *)
let LEB128_LEAF_PREP_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM VAL_EQ_0]) THEN
  FIRST_X_ASSUM(fun th -> if concl th = `val(word j:int64) = j` then
     RULE_ASSUM_TAC(REWRITE_RULE[th; MULT_CLAUSES]) THEN REWRITE_TAC[th; MULT_CLAUSES] THEN
     ASSUME_TAC th else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_REGION_BYTE; VAL_WORD_REGION_BYTE]) THEN
  REWRITE_TAC[READ_REGION_BYTE; VAL_WORD_REGION_BYTE; TISA_TREGS_SETREG; TISA_TREGS_STORE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_sub (tisa_len st 0) (tisa_fword st 22)) =
                val(tisa_len st 0) - val(tisa_fword st 22)`]) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV);;

let LEB128_BYTES_TAC = REWRITE_TAC[leb128_bytes; region_from];;

(* The memory a stop leaves, against the entry state's: unfold the finish   *)
(* and the stores; registers other than the frame's do not matter.           *)
let LEB128_MEM_TAC =
  REWRITE_TAC[tisa_finst; tisa_setfword; tisa_store; tmem; tregs; tisa_frame;
              TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

(* Apply a LEB_SEQ_* verdict theorem to the bytes from the offset. *)
let LEB128_SEQ_TAC th extra =
  LEB128_BYTES_TAC THEN
  MP_TAC(ISPECL ([LEB128_C; `val (tisa_len st 0) - val (tisa_fword st 22)`] @ extra) th) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REGION_BYTE_LT] THEN REPEAT CONJ_TAC THEN
    TRY(REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) THEN
    TRY ASM_ARITH_TAC;
    SIMP_TAC[]];;

(* The value of the bytes up to byte j, when byte j is final. *)
let LEB128_DEC_TAC =
  let th = BETA_RULE(ISPECL [LEB128_C; `j:num`] LEB_STEP_DEC) in
  MP_TAC th THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME (snd(dest_imp(concl th)))]);;

let LEB128_FINAL_TAC =
  MP_TAC(BETA_RULE(ISPECL [LEB128_C; `j:num`] LEB_STEP_FINAL)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  REWRITE_TAC[GSYM WORD_ADD];;

(* No byte left: the input ends first. *)
let LEB128_SHORT_LEAF_TAC =
  REWRITE_TAC[leb128_post; ARITH_EQ] THEN DISJ1_TAC THEN
  REPEAT CONJ_TAC THENL
   [TISA_STATE_NORM_TAC; LEB128_SEQ_TAC LEB_SEQ_SHORT []; LEB128_MEM_TAC];;

(* A malformed integer, by the verdict theorem th. *)
let LEB128_BAD_LEAF_TAC th extra =
  REWRITE_TAC[leb128_post; ARITH_EQ] THEN DISJ2_TAC THEN
  REPEAT CONJ_TAC THENL
   [TISA_STATE_NORM_TAC; LEB128_SEQ_TAC th extra; LEB128_SEQ_TAC th extra; LEB128_MEM_TAC];;

(* The integer ends at byte j: the value and its length in out, FIRED. *)
let LEB128_FIRED_LEAF_TAC =
  LEB128_DEC_TAC THEN LEB128_FINAL_TAC THEN
  REWRITE_TAC[leb128_post; ARITH_EQ] THEN
  EXISTS_TAC `leb_dec (list_of_seq (\j. region_byte st 0 (val (tisa_fword st 22) + j)) (SUC j))` THEN
  MP_TAC(BETA_RULE(ISPECL [LEB128_C; `val (tisa_len st 0) - val (tisa_fword st 22)`; `j:num`]
                          LEB_SEQ_FIRES)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REGION_BYTE_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[];
    STRIP_TAC] THEN
  REWRITE_TAC[GSYM ADD1] THEN ASM_REWRITE_TAC[leb128_bytes; region_from] THEN
  REPEAT CONJ_TAC THENL
   [TISA_STATE_NORM_TAC;
    REWRITE_TAC[leb128_out] THEN TISA_STATE_NORM_TAC;
    REWRITE_TAC[leb128_out] THEN TISA_STATE_NORM_TAC THEN
    REWRITE_TAC[GSYM ADD1] THEN ASM_REWRITE_TAC[];
    LEB128_MEM_TAC THEN REWRITE_TAC[GSYM ADD1] THEN ASM_REWRITE_TAC[]];;

(* A continuation byte: the invariant one byte further. *)
let LEB128_CONT_LEAF_TAC =
  REWRITE_TAC[leb128_inv; TISA_TREGS_SETREG; TISA_TMEM_SETREG; MULT_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM ADD1; LEB_SCALE_STEP] THEN
  MP_TAC(BETA_RULE(ISPECL [LEB128_C; `j:num`] LEB_STEP_CONT)) THEN
  ANTS_TAC THENL [REWRITE_TAC[REGION_BYTE_LT] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_ARITH_TAC;
    X_GEN_TAC `k:num` THEN REWRITE_TAC[ARITH_RULE `k < SUC j <=> k < j \/ k = j`] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM SUBST1_TAC THEN ASM_ARITH_TAC]];;

let LEB128_LEAF_TAC : tactic = fun (asl,w) ->
  let h,args = strip_comb w in
  if h = `leb128_inv` then LEB128_CONT_LEAF_TAC (asl,w)
  else if el 1 args = `1` then LEB128_FIRED_LEAF_TAC (asl,w)
  else if el 1 (snd(strip_comb(el 2 args))) = `word 2:int64` then LEB128_SHORT_LEAF_TAC (asl,w)
  else ((LEB128_BAD_LEAF_TAC LEB_SEQ_NONMINIMAL [`j:num`] THEN NO_TAC) ORELSE
        (LEB128_DEC_TAC THEN LEB128_BAD_LEAF_TAC LEB_SEQ_TOO_BIG [`j:num`])) (asl,w);;

let LEB128_BODY_WP = prove
 (`!st N j s0. tisa_entry_ok leb128 st /\ j < N /\ leb128_inv st N j s0
       ==> tisa_wp leb128_body (leb128_inv st N (j + 1)) (leb128_post st)
                   (tisa_setreg 6 (word j) s0)`,
  LEB128_BODY_SETUP_TAC THEN REWRITE_TAC[leb128_body] THEN TISA_VCG_TAC THEN
  LEB128_LEAF_PREP_TAC THEN LEB128_LEAF_TAC);;

(* ------------------------------------------------------------------------- *)
(* The prologue: an offset past the end is the end of the input; otherwise  *)
(* the invariant before byte 0.                                              *)
(* ------------------------------------------------------------------------- *)

let LEB128_PROLOGUE_WP = prove
 (`!st. tisa_entry_ok leb128 st
        ==> tisa_wp leb128_prologue (\s. tregs s 7 = word 9 /\ leb128_inv st 9 0 s)
                    (leb128_post st) st`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LEB128_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[leb128_prologue] THEN TISA_VCG_TAC THENL
   [REWRITE_TAC[TISA_TREGS_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[leb128_post; ARITH_EQ] THEN DISJ1_TAC THEN
    REPEAT CONJ_TAC THENL [TISA_STATE_NORM_TAC; ALL_TAC; LEB128_MEM_TAC] THEN
    LEB128_BYTES_TAC THEN
    SUBGOAL_THEN `val (tisa_len st 0) - val (tisa_fword st 22) = 0` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [LEB128_C; `0`] LEB_SEQ_SHORT) THEN
    REWRITE_TAC[LT] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    REWRITE_TAC[leb128_inv; TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[list_of_seq; leb_dec; EXP; LT; LE_0] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The whole program, and its runs.                                          *)
(* ------------------------------------------------------------------------- *)

let LEB128_ROOT_WP = prove
 (`!st. tisa_entry_ok leb128 st
        ==> tisa_wp (tisa_root leb128) (\s. F) (leb128_post st) st`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[leb128; tisa_root; TISA_WP_SEQ] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  EXISTS_TAC `\s. tregs s 7 = word 9 /\ leb128_inv st 9 0 s` THEN
  EXISTS_TAC `leb128_post st` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC LEB128_PROLOGUE_WP THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `s:tisa_state` THEN STRIP_TAC THEN
  MATCH_MP_TAC TISA_WP_COUNT_LOOP THEN EXISTS_TAC `leb128_inv st` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LEB128_BODY_WP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* nine bytes with their high bits *)
  MAP_EVERY X_GEN_TAC [`N:num`; `s1:tisa_state`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [leb128_inv]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = 9`)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LEB128_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  TISA_VCG_TAC THEN REWRITE_TAC[TISA_TREGS_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[leb128_post; ARITH_EQ] THEN DISJ2_TAC THEN
  REPEAT CONJ_TAC THENL
   [TISA_STATE_NORM_TAC;
    LEB128_BYTES_TAC THEN MP_TAC(ISPECL [LEB128_C; `val (tisa_len st 0) - val (tisa_fword st 22)`]
      LEB_SEQ_NINE) THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    LEB128_BYTES_TAC THEN MP_TAC(ISPECL [LEB128_C; `val (tisa_len st 0) - val (tisa_fword st 22)`]
      LEB_SEQ_NINE) THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    LEB128_MEM_TAC]);;

let LEB128_RUN = prove
 (`!st k st'. tisa_entry_ok leb128 st /\ tisa_run leb128 st = TStop k st'
              ==> leb128_post st k st'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `st:tisa_state` LEB128_ROOT_WP) THEN ASM_REWRITE_TAC[tisa_wp] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> tisa_has_tm `tisa_run` th)) THEN
  ASM_REWRITE_TAC[tisa_run] THEN
  MP_TAC(ISPEC `tisa_exec (tisa_root leb128) st` TISA_RESULT_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC)
     (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC))) THEN
  REWRITE_TAC[tisa_then; TISA_RWP_CONT; TISA_RWP_STOP; TISA_RESULT_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN REWRITE_TAC[]);;

(* Soundness: a FIRED run's value is the value whose encoding the bytes      *)
(* begin with, below 2^62; out holds it and its length.                      *)
let LEB128_SOUND = prove
 (`!st st'. tisa_entry_ok leb128 st /\ tisa_run leb128 st = TStop 1 st'
            ==> ?v. leb_fires (leb128_bytes st) v /\ tisa_fword st' 19 = word v /\
                    leb128_out st' 0 = word v /\
                    leb128_out st' 1 = word (LENGTH (leb_enc v)) /\
                    tmem st' = tmem (tisa_finst 1 (word v)
                                      (tisa_store (word_add (tisa_base st 1) (word 8)) 8
                                                  (word (LENGTH (leb_enc v)))
                                      (tisa_store (tisa_base st 1) 8 (word v) st)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `1`; `st':tisa_state`] LEB128_RUN) THEN
  ASM_REWRITE_TAC[leb128_post; ARITH_EQ]);;

(* Completeness: when the bytes begin with leb_enc v, v < 2^62, every run    *)
(* fires with v and its length.                                              *)
let LEB128_COMPLETE = prove
 (`!st v k st'. tisa_entry_ok leb128 st /\ leb_fires (leb128_bytes st) v /\
                tisa_run leb128 st = TStop k st'
                ==> k = 1 /\ tisa_fword st' 19 = word v /\
                    leb128_out st' 0 = word v /\
                    leb128_out st' 1 = word (LENGTH (leb_enc v)) /\
                    tmem st' = tmem (tisa_finst 1 (word v)
                                      (tisa_store (word_add (tisa_base st 1) (word 8)) 8
                                                  (word (LENGTH (leb_enc v)))
                                      (tisa_store (tisa_base st 1) 8 (word v) st)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `k:num`; `st':tisa_state`] LEB128_RUN) THEN
  ASM_REWRITE_TAC[leb128_post] THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`leb128_bytes st`; `v:num`; `v':num`] LEB_FIRES_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[LEB_FIRES_NOT_SHORT];
    ASM_MESON_TAC[]]);;

(* The two refusals: the input ends first exactly when the bytes are a      *)
(* proper prefix of an encoding; malformed exactly when neither fires nor   *)
(* short.                                                                    *)
let LEB128_SHORT = prove
 (`!st k st'. tisa_entry_ok leb128 st /\ tisa_run leb128 st = TStop k st'
              ==> (leb_short (leb128_bytes st) <=> k = 0 /\ tisa_fword st' 19 = word 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `k:num`; `st':tisa_state`] LEB128_RUN) THEN
  ASM_REWRITE_TAC[leb128_post] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THENL
   [ASM_MESON_TAC[LEB_FIRES_NOT_SHORT];
    CONV_TAC WORD_REDUCE_CONV]);;

let LEB128_MALFORMED = prove
 (`!st k st'. tisa_entry_ok leb128 st /\ tisa_run leb128 st = TStop k st'
              ==> ((!v. ~leb_fires (leb128_bytes st) v) /\ ~leb_short (leb128_bytes st) <=>
                   k = 0 /\ tisa_fword st' 19 = word 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `k:num`; `st':tisa_state`] LEB128_RUN) THEN
  ASM_REWRITE_TAC[leb128_post] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THENL
   [ASM_MESON_TAC[];
    CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[]]);;
