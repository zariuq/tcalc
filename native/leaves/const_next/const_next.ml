(* ========================================================================= *)
(* const_next, the reader's leaf 31 (tcalc/native/PLANS.txt, sections 2    *)
(* and 10): the bytes at the cursor matched against a constant. The program *)
(* is tcalc/native/leaves/const_next/const_next.metta's text                *)
(* (const_next_prog.txt; image record const_next.hol). Region 0 the input,  *)
(* region 1 the reader's state (RW, at least 16 bytes; word 0 the cursor),  *)
(* region 2 the constant. No arguments.                                      *)
(*                                                                           *)
(* CONST_NEXT_RUN: every run from a state entry validation accepts ends in  *)
(* const_next_post: with c the cursor and n the constant's length, when     *)
(* c + n is at most the input's length, UNSUPPORTED if n is longer than the *)
(* comparison loop's cap (2^32 - 1), else FIRED with c + n returned and     *)
(* written to the state's word 0 when the n input bytes at c are the        *)
(* constant's, else REFUSED; REFUSED when c + n is past the input; the fuel *)
(* receipt kept.                                                              *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

(* The program, as its text const_next_prog.txt. *)
let CONST_NEXT_TERM = new_definition
 `const_next = (TProg [(1,0,1); (2,16,8); (1,0,1)] [] (TSeq (TInstr (TLoadFrame TyPtr 1 2)) (TSeq (TInstr (TLoad TyU64 8 1 2 1 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 3 1)) (TSeq (TInstr (TLoadFrame TyU64 4 5)) (TSeq (TInstr (TCmp CondUle TyU64 5 2 (OpReg 3))) (TSeq (TIf 5 (TSeq (TInstr (TBin BinSub TyU64 6 3 2)) (TSeq (TInstr (TCmp CondUle TyU64 5 4 (OpReg 6))) (TIf 5 (TSeq (TInstr (TLoadFrame TyPtr 8 0)) (TSeq (TInstr (TAddr 0 8 8 (SOME 2) 0 (&0:int))) (TSeq (TInstr (TLoadFrame TyPtr 9 4)) (TSeq (TCountLoop 7 4 4294967295 (TSeq (TInstr (TAddr 2 10 9 (SOME 7) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 1 2 10 10 (&0:int))) (TSeq (TInstr (TAddr 0 11 8 (SOME 7) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 1 0 11 11 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 10 10 (OpReg 11))) (TInstr (TBin BinAnd TyBool 5 5 10)))))))) (TIf 5 (TSeq (TInstr (TBin BinAdd TyU64 2 2 4)) (TSeq (TInstr (TStore 8 1 1 (&0:int) 2)) (TReturn 1 2))) TSkip))))) TSkip))) TSkip) (TSeq (TInstr (TImm TyU64 5 (word 0))) (TReturn 0 5)))))))))`;;

let CONST_NEXT_DECLS = prove(`tisa_decls const_next = [(1,0,1); (2,16,8); (1,0,1)]`,
  REWRITE_TAC[CONST_NEXT_TERM; tisa_decls]);;

let CONST_NEXT_LEAF_WF = prove(`tisa_leaf_wf const_next`, LEAF_WF_TAC CONST_NEXT_DECLS CONST_NEXT_TERM);;

(* The comparison loop's body (const_next.metta's block const_cmp_body). *)
let const_cmp_body = new_definition
 `const_cmp_body = (TSeq (TInstr (TAddr 2 10 9 (SOME 7) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 1 2 10 10 (&0:int))) (TSeq (TInstr (TAddr 0 11 8 (SOME 7) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 1 0 11 11 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 10 10 (OpReg 11))) (TInstr (TBin BinAnd TyBool 5 5 10)))))))`;;

let CONST_NEXT_TERM_BODY = REWRITE_RULE[GSYM const_cmp_body] CONST_NEXT_TERM;;

(* The n bytes of the input at offset c are the constant's. *)
let const_bytes_eq = new_definition
 `const_bytes_eq t c n <=>
    !i. i < n ==> tisa_read t (word_add (tisa_base t 0) (word(c + i))) 1 =
                  tisa_read t (word_add (tisa_base t 2) (word i)) 1`;;

(* What every run leaves: the cursor c is word 0 of region 1, n the length *)
(* of region 2.                                                              *)
let const_next_post = new_definition
 `const_next_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    (if val(tisa_read t (tisa_base t 1) 8) + val(tisa_len t 2) <= val(tisa_len t 0)
     then (if 4294967295 < val(tisa_len t 2) then k = 2
           else if const_bytes_eq t (val(tisa_read t (tisa_base t 1) 8)) (val(tisa_len t 2))
           then k = 1 /\
                tisa_fword u 19 = word(val(tisa_read t (tisa_base t 1) 8) + val(tisa_len t 2)) /\
                tisa_read u (tisa_base t 1) 8 = word(val(tisa_read t (tisa_base t 1) 8) + val(tisa_len t 2))
           else k = 0)
     else k = 0)`;;

(* Entry validation: the frame, the three regions below 2^64, the state     *)
(* apart from the frame and from the two read-only regions.                 *)
let CONST_NEXT_ENTRY = prove
 (`!st. tisa_entry_ok const_next st
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
             val(tisa_base st 1) + val(tisa_len st 1) <= val(tisa_base st 0)) /\
            val(tisa_base st 2) + val(tisa_len st 2) < 2 EXP 64 /\
            (val(tisa_len st 2) = 0 \/
             val(tisa_base st 2) + val(tisa_len st 2) <= val(tregs st 0) + 144 \/
             val(tregs st 0) + 192 <= val(tisa_base st 2)) /\
            (val(tisa_len st 2) = 0 \/
             val(tisa_base st 2) + val(tisa_len st 2) <= val(tisa_base st 1) \/
             val(tisa_base st 1) + val(tisa_len st 1) <= val(tisa_base st 2))`,
  GEN_TAC THEN
  REWRITE_TAC[CONST_NEXT_TERM; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok;
              tisa_region_ok; tisa_pair_ok; tisa_frame; tisa_base; tisa_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(val(tisa_fword st 3) = 0)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `val(tisa_fword st 1) = 0` THEN
  ASM_CASES_TAC `val(tisa_fword st 5) = 0` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* The comparison loop (COUNT_LOOP 7 4, body const_cmp_body): from state sq, *)
(* with v9 pointing n = val v4 bytes into the constant and v8 n bytes into  *)
(* the input, it leaves v5 = 1 exactly when the two ranges hold the same    *)
(* bytes; it writes only v5, v7, v10 and v11, and no memory. It runs only  *)
(* when n is within its cap.                                                 *)
let const_cmp_inv = new_definition
 `const_cmp_inv st sq N i s <=>
    tregs s 0 = tregs st 0 /\ tmem s = tmem st /\ N = val(tregs sq 4) /\ N <= 4294967295 /\
    (!r. ~(r = 5) /\ ~(r = 7) /\ ~(r = 10) /\ ~(r = 11) ==> tregs s r = tregs sq r) /\
    tregs s 5 = (if !k. k < i ==> tisa_read st (word_add (tregs sq 9) (word k)) 1 =
                                 tisa_read st (word_add (tregs sq 8) (word k)) 1
                 then word 1 else word 0)`;;

let CONST_CMP_BODY_WP = prove
 (`!st sq N j s0 R.
     val(tregs st 0) + 192 <= 2 EXP 64 /\
     val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64 /\
     val(tisa_base st 2) + val(tisa_len st 2) < 2 EXP 64 /\
     val(tisa_base st 2) <= val(tregs sq 9) /\
     val(tregs sq 9) + val(tregs sq 4) <= val(tisa_base st 2) + val(tisa_len st 2) /\
     val(tisa_base st 0) <= val(tregs sq 8) /\
     val(tregs sq 8) + val(tregs sq 4) <= val(tisa_base st 0) + val(tisa_len st 0) /\
     j < N /\ const_cmp_inv st sq N j s0
     ==> tisa_wp const_cmp_body (const_cmp_inv st sq N (j + 1)) R (tisa_setreg 7 (word j) s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [const_cmp_inv] o
                check (fun th -> tisa_has_tm `const_cmp_inv` th)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = val(tregs sq 4)`)) THEN
  MP_TAC(ISPECL [`s0:tisa_state`; `st:tisa_state`] TISA_SAME_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY (fun r -> FIRST_ASSUM(ASSUME_TAC o C MP (EQT_ELIM(NUM_REDUCE_CONV
      (list_mk_conj (map (fun q -> mk_neg(mk_eq(mk_small_numeral r, mk_small_numeral q))) [5;7;10;11])))) o
      SPEC (mk_small_numeral r) o check (fun th -> is_forall(concl th) && tisa_has_tm `tregs sq` th)))
    [4; 8; 9] THEN
  ASSUME_TAC(ISPEC `tregs sq 4` VAL_BOUND_64) THEN
  SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN TISA_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[const_cmp_body] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[const_cmp_inv] THEN TISA_STATE_NORM_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES] THEN REPEAT CONJ_TAC THEN
  TRY(GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `k < j + 1 <=> k < j \/ k = j`] THEN MESON_TAC[]);;

let CONST_CMP_LOOP = prove
 (`!st sq Q R.
     val(tregs st 0) + 192 <= 2 EXP 64 /\
     val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64 /\
     val(tisa_base st 2) + val(tisa_len st 2) < 2 EXP 64 /\
     tregs sq 0 = tregs st 0 /\ tmem sq = tmem st /\
     val(tisa_base st 2) <= val(tregs sq 9) /\
     val(tregs sq 9) + val(tregs sq 4) <= val(tisa_base st 2) + val(tisa_len st 2) /\
     val(tisa_base st 0) <= val(tregs sq 8) /\
     val(tregs sq 8) + val(tregs sq 4) <= val(tisa_base st 0) + val(tisa_len st 0) /\
     tregs sq 5 = word 1 /\
     (4294967295 < val(tregs sq 4) ==> R 2 (tisa_failst 2 sq)) /\
     (!s. tregs s 0 = tregs st 0 /\ tmem s = tmem st /\ val(tregs sq 4) <= 4294967295 /\
          (!r. ~(r = 5) /\ ~(r = 7) /\ ~(r = 10) /\ ~(r = 11) ==> tregs s r = tregs sq r) /\
          tregs s 5 =
          (if !k. k < val(tregs sq 4) ==> tisa_read st (word_add (tregs sq 9) (word k)) 1 =
                                         tisa_read st (word_add (tregs sq 8) (word k)) 1
           then word 1 else word 0)
          ==> Q s)
     ==> tisa_wp (TCountLoop 7 4 4294967295 const_cmp_body) Q R sq`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC TISA_WP_COUNT_LOOP THEN EXISTS_TAC `const_cmp_inv st sq` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[const_cmp_inv; LT] THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONST_CMP_BODY_WP THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[const_cmp_inv] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = val(tregs sq 4)`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* The loop's comparison, as const_bytes_eq at the cursor. *)
let CONST_BYTES_EQ_LOOP = prove
 (`!t c n. (!k. k < n ==> tisa_read t (word_add (tisa_base t 2) (word k)) 1 =
                          tisa_read t (word_add (word_add (tisa_base t 0) (word c)) (word k)) 1)
           <=> const_bytes_eq t c n`,
  REWRITE_TAC[const_bytes_eq; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN MESON_TAC[]);;

(* A failure stop, as a finish with the outcome as payload. *)
let CONST_NEXT_FAILST = prove
 (`!k st. tisa_failst k st = tisa_finst k (word k) st`,
  REWRITE_TAC[tisa_failst; tisa_finst]);;

(* The cursor and the constant fit in the input, and the input's address at *)
(* the cursor does not wrap.                                                  *)
let CONST_NEXT_RANGE_TAC =
  SUBGOAL_THEN `val(tisa_read t (tisa_base t 1) 8) + val(tisa_len t 2) <= val(tisa_len t 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `val(tisa_len t 2) <= val(word_sub (tisa_len t 0) (tisa_read t (tisa_base t 1) 8))` THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add (tisa_base t 0) (word (val(tisa_read t (tisa_base t 1) 8)))) =
                val(tisa_base t 0) + val(tisa_read t (tisa_base t 1) 8)` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC];;

(* Arithmetic, on inequalities only. *)
let CONST_NEXT_ARITH_TAC : tactic = fun (asl,w) ->
  if (is_binary "<=" w || is_binary "<" w) &&
     not (can (find_term (fun t -> is_const t && fst(dest_const t) = "tisa_wp")) w)
  then ASM_ARITH_TAC (asl,w) else failwith "CONST_NEXT_ARITH_TAC";;

(* A fact and its negation among the assumptions. *)
let CONST_NEXT_CONTRA_TAC : tactic = fun (asl,w) ->
  let ths = map snd asl in
  let neg = find (fun th -> is_neg(concl th) && exists (fun th' -> aconv (concl th') (rand(concl th))) ths) ths in
  let pos = find (fun th' -> aconv (concl th') (rand(concl neg))) ths in
  CONTR_TAC(MP (NOT_ELIM neg) pos) (asl,w);;

(* The post's conditions, case by case. *)
let CONST_NEXT_COND_TAC : tactic =
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(CONST_NEXT_CONTRA_TAC THEN NO_TAC) THEN TRY(ASM_ARITH_TAC THEN NO_TAC);;

(* An end: the frame's words and the state's word 0 read off, the branch    *)
(* conditions as arithmetic on the cursor and the lengths, the loop's       *)
(* result as const_bytes_eq.                                                  *)
let CONST_NEXT_POST_TAC =
  REWRITE_TAC[const_next_post] THEN TISA_STATE_NORM_TAC THEN LEAF_VAL_NUMERALS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_CASES; TISA_COND01_EQ_0]) THEN
  ASM_REWRITE_TAC[WORD_ADD; WORD_VAL] THEN CONST_NEXT_COND_TAC;;

(* After the loop: the registers it kept, the entry state's view, then the  *)
(* rest of the program.                                                       *)
let CONST_NEXT_DONE_TAC =
  X_GEN_TAC `s1:tisa_state` THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun r -> FIRST_ASSUM(ASSUME_TAC o CONV_RULE(RAND_CONV(REWRITE_CONV[ARITH_EQ])) o
      C MP (EQT_ELIM(NUM_REDUCE_CONV
        (list_mk_conj (map (fun q -> mk_neg(mk_eq(mk_small_numeral r, mk_small_numeral q))) [5;7;10;11])))) o
      SPEC (mk_small_numeral r) o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `tregs s1`)) (concl th))))
    [1; 2; 3; 4; 6; 8; 9] THEN
  MP_TAC(ISPECL [`s1:tisa_state`; `t:tisa_state`] TISA_SAME_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONST_BYTES_EQ_LOOP]) THEN
  BETA_TAC THEN TISA_VCG_TAC THEN CONST_NEXT_POST_TAC;;

(* The loop, by CONST_CMP_LOOP: its bounds, its UNSUPPORTED stop, the rest. *)
let CONST_NEXT_LOOP_TAC =
  CONST_NEXT_RANGE_TAC THEN MATCH_MP_TAC CONST_CMP_LOOP THEN EXISTS_TAC `t:tisa_state` THEN
  REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG; ARITH_EQ; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[LE_REFL] THEN REPEAT CONJ_TAC THEN TRY(CONST_NEXT_ARITH_TAC THEN NO_TAC) THEN
  (fun (asl,w) ->
     if is_forall w then CONST_NEXT_DONE_TAC (asl,w)
     else if is_imp w then
       (DISCH_TAC THEN REWRITE_TAC[const_next_post; CONST_NEXT_FAILST] THEN
        TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[]) (asl,w)
     else failwith "CONST_NEXT_LOOP_TAC");;

let CONST_NEXT_WP = prove
 (`!t. tisa_entry_ok const_next t ==> tisa_wp (tisa_root const_next) (\s. F) (const_next_post t) t`,
  GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS(MATCH_MP CONST_NEXT_ENTRY th))) THEN
  REWRITE_TAC[CONST_NEXT_TERM_BODY; tisa_root] THEN TISA_VCG_TAC THEN
  (fun (asl,w) -> if fst(strip_comb w) = `tisa_wp` then CONST_NEXT_LOOP_TAC (asl,w)
                  else CONST_NEXT_POST_TAC (asl,w)));;

let CONST_NEXT_RUN = prove
 (`!t k u. tisa_entry_ok const_next t /\ tisa_run const_next t = TStop k u ==> const_next_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; CONST_NEXT_WP]);;

(* Every theorem this file states, for the audits. *)
let const_next_theorems =
 ["CONST_NEXT_TERM", CONST_NEXT_TERM;
  "CONST_NEXT_DECLS", CONST_NEXT_DECLS;
  "CONST_NEXT_LEAF_WF", CONST_NEXT_LEAF_WF;
  "const_cmp_body", const_cmp_body;
  "CONST_NEXT_TERM_BODY", CONST_NEXT_TERM_BODY;
  "const_bytes_eq", const_bytes_eq;
  "const_next_post", const_next_post;
  "CONST_NEXT_ENTRY", CONST_NEXT_ENTRY;
  "const_cmp_inv", const_cmp_inv;
  "CONST_CMP_BODY_WP", CONST_CMP_BODY_WP;
  "CONST_CMP_LOOP", CONST_CMP_LOOP;
  "CONST_BYTES_EQ_LOOP", CONST_BYTES_EQ_LOOP;
  "CONST_NEXT_FAILST", CONST_NEXT_FAILST;
  "CONST_NEXT_WP", CONST_NEXT_WP;
  "CONST_NEXT_RUN", CONST_NEXT_RUN];;
