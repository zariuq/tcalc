(* ========================================================================= *)
(* le8_next, the reader's leaf 29 (tcalc/native/PLANS.txt, sections 2 and   *)
(* 10): the 8 bytes at the cursor, little-endian. The program is            *)
(* tcalc/native/leaves/le8_next/le8_next.metta's text (le8_next_prog.txt;   *)
(* image record le8_next.hol). Region 0 the input, region 1 the reader's    *)
(* state (RW, at least 16 bytes; word 0 the cursor). No arguments.          *)
(*                                                                           *)
(* LE8_NEXT_RUN: every run from a state entry validation accepts ends in    *)
(* le8_next_post: FIRED with the 8 input bytes at the cursor c, and c + 8   *)
(* written to the state's word 0, when c + 8 is at most the input's length; *)
(* else REFUSED; the fuel receipt kept.                                       *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

(* The program, as its text le8_next_prog.txt. *)
let LE8_NEXT_TERM = new_definition
 `le8_next = (TProg [(1,0,1); (2,16,8)] [] (TSeq (TInstr (TLoadFrame TyPtr 1 2)) (TSeq (TInstr (TLoad TyU64 8 1 2 1 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 3 1)) (TSeq (TInstr (TCmp CondUle TyU64 4 2 (OpReg 3))) (TSeq (TIf 4 (TSeq (TInstr (TBin BinSub TyU64 5 3 2)) (TSeq (TInstr (TImm TyU64 6 (word 8))) (TSeq (TInstr (TCmp CondUle TyU64 4 6 (OpReg 5))) (TIf 4 (TSeq (TInstr (TLoadFrame TyPtr 7 0)) (TSeq (TInstr (TAddr 0 8 7 (SOME 2) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 9 8 (&0:int))) (TSeq (TInstr (TBin BinAdd TyU64 2 2 6)) (TSeq (TInstr (TStore 8 1 1 (&0:int) 2)) (TReturn 1 9)))))) TSkip)))) TSkip) (TSeq (TInstr (TImm TyU64 4 (word 0))) (TReturn 0 4))))))))`;;

let LE8_NEXT_DECLS = prove(`tisa_decls le8_next = [(1,0,1); (2,16,8)]`, REWRITE_TAC[LE8_NEXT_TERM; tisa_decls]);;

let LE8_NEXT_LEAF_WF = prove(`tisa_leaf_wf le8_next`, LEAF_WF_TAC LE8_NEXT_DECLS LE8_NEXT_TERM);;

(* What every run leaves: the cursor c is word 0 of region 1. *)
let le8_next_post = new_definition
 `le8_next_post t k u <=>
    tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\
    (if val(tisa_read t (tisa_base t 1) 8) + 8 <= val(tisa_len t 0)
     then k = 1 /\
          tisa_fword u 19 =
            tisa_read t (word_add (tisa_base t 0) (word(val(tisa_read t (tisa_base t 1) 8)))) 8 /\
          tisa_read u (tisa_base t 1) 8 = word(val(tisa_read t (tisa_base t 1) 8) + 8)
     else k = 0)`;;

(* Entry validation: the frame, both regions below 2^64 and apart. *)
let LE8_NEXT_ENTRY = prove
 (`!st. tisa_entry_ok le8_next st
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
  REWRITE_TAC[LE8_NEXT_TERM; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok;
              tisa_region_ok; tisa_pair_ok; tisa_frame; tisa_base; tisa_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(val(tisa_fword st 3) = 0)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `val(tisa_fword st 1) = 0` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* A sum of words, as one word. *)
let LE8_NEXT_SUM = prove(`!a b:int64. word_add a b = word(val a + val b)`,
  REWRITE_TAC[WORD_ADD; WORD_VAL]);;

(* The load's address: the input's base plus the cursor, which does not wrap *)
(* once the cursor is within the input.                                       *)
let LE8_NEXT_ADDR_TAC =
  TRY(SUBGOAL_THEN `val(word_add (tisa_base t 0) (word(val(tisa_read t (tisa_base t 1) 8)))) =
                    val(tisa_base t 0) + val(tisa_read t (tisa_base t 1) 8)` ASSUME_TAC THENL
       [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC]);;

(* Each path's end: the frame's words and the state's word 0 read off, the  *)
(* branch conditions and the load's bounds as arithmetic on the cursor and  *)
(* the input's length.                                                       *)
let LE8_NEXT_CASE_TAC =
  REWRITE_TAC[le8_next_post] THEN TISA_STATE_NORM_TAC THEN LEAF_VAL_NUMERALS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_CASES; TISA_INSIDE_NUM; MULT_CLAUSES]) THEN
  REWRITE_TAC[LE8_NEXT_SUM; MULT_CLAUSES; WORD_VAL] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  LE8_NEXT_ADDR_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term is_cond) (concl th)))) THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN TRY ASM_ARITH_TAC;;

let LE8_NEXT_WP = prove
 (`!t. tisa_entry_ok le8_next t ==> tisa_wp (tisa_root le8_next) (\s. F) (le8_next_post t) t`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP LE8_NEXT_ENTRY) THEN
  REWRITE_TAC[LE8_NEXT_TERM; tisa_root] THEN TISA_VCG_TAC THEN LE8_NEXT_CASE_TAC);;

let LE8_NEXT_RUN = prove
 (`!t k u. tisa_entry_ok le8_next t /\ tisa_run le8_next t = TStop k u ==> le8_next_post t k u`,
  MESON_TAC[LEAF_RUN_BY_WP; LE8_NEXT_WP]);;

(* Every theorem this file states, for the audits. *)
let le8_next_theorems =
 ["LE8_NEXT_TERM", LE8_NEXT_TERM;
  "LE8_NEXT_DECLS", LE8_NEXT_DECLS;
  "LE8_NEXT_LEAF_WF", LE8_NEXT_LEAF_WF;
  "le8_next_post", le8_next_post;
  "LE8_NEXT_ENTRY", LE8_NEXT_ENTRY;
  "LE8_NEXT_SUM", LE8_NEXT_SUM;
  "LE8_NEXT_WP", LE8_NEXT_WP;
  "LE8_NEXT_RUN", LE8_NEXT_RUN];;
