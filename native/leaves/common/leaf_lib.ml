(* ========================================================================= *)
(* What the plan leaves' proofs share (tcalc/native/leaves).                 *)
(*                                                                           *)
(* LEAF_RUN_BY_WP: a run of a program ends as R says when the program's     *)
(* root, from the entry state, never continues and stops only as R says    *)
(* (tisa_wp (tisa_root prog) (\s. F) R t): a run is the root's execution,  *)
(* and a root that continued would end in the fall-through failure.         *)
(*                                                                           *)
(* LEAF_ENTRY_FRAME: every entry state's frame lies below 2^64 - 192.       *)
(*                                                                           *)
(* The image side, as tcalc/native/driver/drive_reader.ml does it for the   *)
(* reader's leaves: tisa_leaf_wf of a program by computation over its text  *)
(* (LEAF_WF_TAC), and the uniform image theorem tisa_leaf_spec from the     *)
(* generator's image theorem (LEAF_SPEC_TAC).                               *)
(* ========================================================================= *)

needs "native/driver/driver_leaf.ml";;
needs "native/hol/tisa_wp.ml";;

let LEAF_ENTRY_FRAME = prove
 (`!prog t. tisa_entry_ok prog t ==> val(tregs t 0) + 192 <= 2 EXP 64`,
  GEN_TAC THEN ONCE_REWRITE_TAC[TISA_PROG_CASES] THEN
  REWRITE_TAC[tisa_entry_ok; tisa_frame] THEN MESON_TAC[]);;

let LEAF_RUN_BY_WP = prove
 (`!prog t (R:num->tisa_state->bool).
     tisa_entry_ok prog t /\ tisa_wp (tisa_root prog) (\s. F) R t
     ==> !k u. tisa_run prog t = TStop k u ==> R k u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[tisa_run] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[tisa_wp]) THEN
  MP_TAC(ISPEC `tisa_exec (tisa_root prog) t` TISA_RESULT_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC)
     (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC))) THEN
  REWRITE_TAC[tisa_then; TISA_RWP_CONT; TISA_RWP_STOP; TISA_RESULT_INJ] THEN
  MESON_TAC[]);;

(* val (word n) for a numeral n, in the goal and the assumptions: the       *)
(* generator leaves an immediate operand's comparison in that form.          *)
let LEAF_VAL_NUMERAL_CONV = REWRITE_CONV[VAL_WORD; DIMINDEX_64] THENC NUM_REDUCE_CONV;;

let leaf_val_numeral t =
  match t with Comb(Const("val",_),Comb(Const("word",_),n)) -> is_numeral n | _ -> false;;

let LEAF_VAL_NUMERALS_CONV =
  DEPTH_CONV(fun t -> if leaf_val_numeral t then LEAF_VAL_NUMERAL_CONV t else failwith "");;

let LEAF_VAL_NUMERALS_TAC =
  RULE_ASSUM_TAC(CONV_RULE LEAF_VAL_NUMERALS_CONV) THEN CONV_TAC LEAF_VAL_NUMERALS_CONV;;

(* The generator with focused arithmetic (tisa_wp.ml, tisa_arith_focus), *)
(* the flag restored however the tactic ends.                               *)
let LEAF_FOCUS_TAC (tac:tactic) : tactic = fun g ->
  let old = !tisa_arith_focus in
  tisa_arith_focus := true;
  try let r = tac g in tisa_arith_focus := old; r
  with e -> tisa_arith_focus := old; raise e;;

(* An increment as one word. *)
let LEAF_WORD_ADD_1 = prove
 (`!c:int64. word_add c (word 1) = word(val c + 1)`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM WORD_VAL] THEN
  REWRITE_TAC[WORD_ADD]);;

(* A length check by a shift: 8 c exceeds l exactly when l DIV 8 < c. *)
let LEAF_DIV8_LT = prove
 (`!c l. l DIV 8 < c <=> ~(8 * c <= l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN AP_TERM_TAC THEN
  SIMP_TAC[LE_RDIV_EQ; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Word arithmetic for tables of rows of s words (row_word, put_word).        *)
(*                                                                           *)
(* LEAF_PRODUCT_WITHIN: the product test of leaves.metta (product-within)    *)
(* decides x y <= lim exactly, for x, y <= lim < 2^61, from the 32-bit      *)
(* halves; every product and sum it forms is exact. LEAF_PRODUCT_GUARD is    *)
(* the same in the specifications' form (8 s c <= l, given i < c and w < s, *)
(* so that s and c are at least 1). LEAF_ROW_INDEX: word s i + w of a table *)
(* of c rows lies inside it.                                                *)
(* ------------------------------------------------------------------------- *)

let LEAF_VAL_MUL_EXACT = prove
 (`!x y:int64. val x * val y < 2 EXP 64 ==> val(word_mul x y) = val x * val y`,
  SIMP_TAC[VAL_WORD_MUL; DIMINDEX_64; MOD_LT]);;

let LEAF_VAL_SHL_EXACT = prove
 (`!(x:int64) n. val x * 2 EXP n < 2 EXP 64 ==> val(word_shl x n) = val x * 2 EXP n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SHL; DIMINDEX_64] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MULT_SYM] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;

let LEAF_HALVES = prove
 (`!x:int64. val(word_ushr x 32) = val x DIV 2 EXP 32 /\
             val(word_and x (word 4294967295)) = val x MOD 2 EXP 32 /\
             (word_ushr x 32 = word 0 <=> val x < 2 EXP 32) /\
             val x = 2 EXP 32 * (val x DIV 2 EXP 32) + val x MOD 2 EXP 32 /\
             val x MOD 2 EXP 32 < 2 EXP 32`,
  GEN_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (ISPECL [`x:int64`; `32`] VAL_WORD_AND_MASK_WORD)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD_USHR; GSYM VAL_EQ_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[DIV_EQ_0; ARITH_EQ; MOD_LT_EQ] THEN
  MP_TAC(SPECL [`val(x:int64)`; `4294967296`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let LEAF_PRODUCT_WITHIN = prove
 (`!s c:int64 lim.
     lim < 2 EXP 61 /\ val s <= lim /\ val c <= lim
     ==> (val s * val c <= lim <=>
          ~(~(word_ushr s 32 = word 0) /\ ~(word_ushr c 32 = word 0)) /\
          val(word_add (word_mul (word_ushr s 32) (word_and c (word 4294967295)))
                       (word_mul (word_ushr c 32) (word_and s (word 4294967295)))) < 536870912 /\
          ~(lim < val(word_mul (word_and s (word 4294967295)) (word_and c (word 4294967295)))) /\
          ~(lim < val(word_add
                       (word_shl (word_add (word_mul (word_ushr s 32) (word_and c (word 4294967295)))
                                           (word_mul (word_ushr c 32) (word_and s (word 4294967295)))) 32)
                       (word_mul (word_and s (word 4294967295)) (word_and c (word 4294967295))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s:int64` LEAF_HALVES) THEN MP_TAC(ISPEC `c:int64` LEAF_HALVES) THEN
  MAP_EVERY ABBREV_TAC [`s1 = val(s:int64) DIV 2 EXP 32`; `s0 = val(s:int64) MOD 2 EXP 32`;
                        `c1 = val(c:int64) DIV 2 EXP 32`; `c0 = val(c:int64) MOD 2 EXP 32`] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s1 < 2 EXP 29 /\ c1 < 2 EXP 29` STRIP_ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s1 * c0 < 2 EXP 61 /\ c1 * s0 < 2 EXP 61 /\ s0 * c0 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 EXP 61 = 2 EXP 29 * 2 EXP 32 /\ 2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC LT_MULT2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_mul (word_ushr (s:int64) 32) (word_and (c:int64) (word 4294967295))) = s1 * c0 /\
                val(word_mul (word_ushr c 32) (word_and s (word 4294967295))) = c1 * s0 /\
                val(word_mul (word_and s (word 4294967295)) (word_and c (word 4294967295))) = s0 * c0`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) LEAF_VAL_MUL_EXACT (lhand w))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add (word_mul (word_ushr (s:int64) 32) (word_and (c:int64) (word 4294967295)))
                             (word_mul (word_ushr c 32) (word_and s (word 4294967295)))) =
                s1 * c0 + c1 * s0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD_ADD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(s:int64) * val(c:int64) =
                2 EXP 64 * (s1 * c1) + 2 EXP 32 * (s1 * c0 + c1 * s0) + s0 * c0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_RING; ALL_TAC] THEN
  ASM_CASES_TAC `2 EXP 32 <= val(s:int64) /\ 2 EXP 32 <= val(c:int64)` THENL
   [SUBGOAL_THEN `2 EXP 64 <= val(s:int64) * val(c:int64)` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[GSYM NOT_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s1 * c1 = 0` ASSUME_TAC THENL
   [REWRITE_TAC[MULT_EQ_0] THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(~(val(s:int64) < 2 EXP 32) /\ ~(val(c:int64) < 2 EXP 32))`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s1 * c0 + c1 * s0 < 536870912` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_ARITH_TAC] THEN
  ASM_CASES_TAC `lim < s0 * c0` THEN ASM_REWRITE_TAC[] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_shl (word_add (word_mul (word_ushr (s:int64) 32) (word_and (c:int64) (word 4294967295)))
                                       (word_mul (word_ushr c 32) (word_and s (word 4294967295)))) 32) =
                (s1 * c0 + c1 * s0) * 2 EXP 32` ASSUME_TAC THENL
   [W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) LEAF_VAL_SHL_EXACT (lhand w))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_ADD; DIMINDEX_64] THEN
  SUBGOAL_THEN `((s1 * c0 + c1 * s0) * 2 EXP 32 + s0 * c0) MOD 2 EXP 64 =
                (s1 * c0 + c1 * s0) * 2 EXP 32 + s0 * c0` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_ARITH_TAC);;

let LEAF_PRODUCT_GUARD = prove
 (`!s c:int64 l i w.
     l < 2 EXP 64 /\ i < val c /\ w < val s
     ==> (8 * val s * val c <= l <=>
          ~(l DIV 8 < val s) /\ ~(l DIV 8 < val c) /\
          ~(~(word_ushr s 32 = word 0) /\ ~(word_ushr c 32 = word 0)) /\
          val(word_add (word_mul (word_ushr s 32) (word_and c (word 4294967295)))
                       (word_mul (word_ushr c 32) (word_and s (word 4294967295)))) < 536870912 /\
          ~(l DIV 8 < val(word_mul (word_and s (word 4294967295)) (word_and c (word 4294967295)))) /\
          ~(l DIV 8 < val(word_add
                       (word_shl (word_add (word_mul (word_ushr s 32) (word_and c (word 4294967295)))
                                           (word_mul (word_ushr c 32) (word_and s (word 4294967295)))) 32)
                       (word_mul (word_and s (word 4294967295)) (word_and c (word 4294967295))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * val(s:int64) * val(c:int64) <= l <=> val s * val c <= l DIV 8` SUBST1_TAC THENL
   [SIMP_TAC[LE_RDIV_EQ; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `val(s:int64) <= val(s:int64) * val(c:int64) /\ val c <= val s * val c`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = x * 1`];
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = 1 * x`]] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `l DIV 8 < val(s:int64)` THEN ASM_REWRITE_TAC[] THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `l DIV 8 < val(c:int64)` THEN ASM_REWRITE_TAC[] THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LEAF_PRODUCT_WITHIN THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `l DIV 8 < 2 EXP 61` (fun th -> REWRITE_TAC[th]) THEN
  SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC);;

(* The row's word index s i + w, its value and its place in the rows. *)
let LEAF_ROW_INDEX = prove
 (`!s i w c l:num.
     i < c /\ w < s /\ 8 * s * c <= l
     ==> s * i + w < s * c /\ 8 * (s * i + w) + 8 <= l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `s * i + w < s * c` ASSUME_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `s * (i + 1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN ASM_ARITH_TAC;
      REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC];
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The image side.                                                           *)
(* ------------------------------------------------------------------------- *)

(* The length of the machine code a generator's image defines (NAME_mc). *)
let leaf_mc_length name =
  COMPUTE_LENGTH_RULE
    (find (fun th -> try fst(dest_const(lhs(concl th))) = name with Failure _ -> false)
          (definitions()));;

(* tisa_rw and tisa_readable of a declaration list, at a numeral. *)
let LEAF_DECL_KIND_CONV decls_th =
  REWRITE_CONV[decls_th; tisa_rw; tisa_readable; LENGTH] THENC NUM_REDUCE_CONV THENC
  ONCE_DEPTH_CONV EL_CONV THENC REWRITE_CONV[FST] THENC NUM_REDUCE_CONV;;

let LEAF_FRAME_WORDS = ARITH_RULE
  `2 * 0 = 0 /\ 2 * 0 + 1 = 1 /\ 2 * 1 = 2 /\ 2 * 1 + 1 = 3 /\ 2 * 2 = 4 /\ 2 * 2 + 1 = 5 /\
   2 * 3 = 6 /\ 2 * 3 + 1 = 7 /\ 2 * 4 = 8 /\ 2 * 4 + 1 = 9 /\ 2 * 5 = 10 /\ 2 * 5 + 1 = 11 /\
   2 * 6 = 12 /\ 2 * 6 + 1 = 13 /\ 2 * 7 = 14 /\ 2 * 7 + 1 = 15 /\ 2 * 8 = 16 /\ 2 * 8 + 1 = 17`;;

(* !pc. tisa_leaf_spec prog mc pc, from the image theorem entry_th (over    *)
(* the program's name) of a program with nregions declared regions.         *)
let LEAF_SPEC_TAC nregions decls_th len_th entry_th =
  GEN_TAC THEN REWRITE_TAC[tisa_leaf_spec; tisa_leaf_place; len_th] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "r"
    then MAP_EVERY (fun k -> ASSUME_TAC(SPEC (mk_small_numeral k) th)) (0--(nregions-1))
    else failwith "")) THEN
  let kinds t = try let n = fst(dest_const t) in n = "tisa_rw" || n = "tisa_readable"
                with Failure _ -> false in
  RULE_ASSUM_TAC(fun th -> if can (find_term kinds) (concl th)
                           then CONV_RULE(LEAF_DECL_KIND_CONV decls_th) th else th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tisa_base; tisa_len; LEAF_FRAME_WORDS]) THEN
  MATCH_MP_TAC entry_th THEN ASM_REWRITE_TAC[];;

(* tisa_leaf_wf prog, by computation over its text. *)
let LEAF_WF_TAC decls_th term_th =
  REWRITE_TAC[tisa_leaf_wf; decls_th; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[term_th; tisa_root; tisa_inits; ALL; tisa_stmt_ok; tisa_instr_ok] THEN
  CONV_TAC(TOP_DEPTH_CONV(CHANGED_CONV(LEAF_DECL_KIND_CONV decls_th) ORELSEC NUM_RED_CONV)) THEN
  REWRITE_TAC[];;

(* Every theorem this file states, for the audits. *)
let leaf_lib_theorems =
 ["LEAF_ENTRY_FRAME", LEAF_ENTRY_FRAME;
  "LEAF_RUN_BY_WP", LEAF_RUN_BY_WP;
  "LEAF_WORD_ADD_1", LEAF_WORD_ADD_1;
  "LEAF_DIV8_LT", LEAF_DIV8_LT;
  "LEAF_VAL_MUL_EXACT", LEAF_VAL_MUL_EXACT;
  "LEAF_VAL_SHL_EXACT", LEAF_VAL_SHL_EXACT;
  "LEAF_HALVES", LEAF_HALVES;
  "LEAF_PRODUCT_WITHIN", LEAF_PRODUCT_WITHIN;
  "LEAF_PRODUCT_GUARD", LEAF_PRODUCT_GUARD;
  "LEAF_ROW_INDEX", LEAF_ROW_INDEX;
  "LEAF_FRAME_WORDS", LEAF_FRAME_WORDS];;
