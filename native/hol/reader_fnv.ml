(* ========================================================================= *)
(* FNV-1a 64 over a byte range, as the standalone t-ISA p1 program fnv       *)
(* (tcalc/native/reader/fnv.metta; its text is tcalc/native/reader/          *)
(* fnv_prog.txt, its image record fnv.hol). The HOLR reader keeps END's      *)
(* checksum with it.                                                         *)
(*                                                                           *)
(* Region 0 input (RO); arg0 the range's offset, arg1 its length; the entry  *)
(* register v1 the initial state h0.                                         *)
(*                                                                           *)
(* FNV_RUN: every run from a state entry validation accepts ends in one of  *)
(* three ways:                                                               *)
(*   FIRED with ret_val = fnv1a h0 (the range's bytes) (holr_spec.ml's      *)
(*     fnv1a), the range lying inside the input;                             *)
(*   REFUSED with ret_val 1, the range not lying inside the input;           *)
(*   UNSUPPORTED (2), the range inside the input but longer than the loop's  *)
(*     cap, 2^32 - 1 bytes.                                                  *)
(* FNV_SOUND and FNV_COMPLETE are its two directions for FIRED; FNV_REFUSED  *)
(* characterizes the refusal.                                                *)
(* ========================================================================= *)

needs "native/hol/reader_common.ml";;
needs "native/hol/holr_bytes.ml";;

let FNV1A_APPEND = prove
 (`!l1 l2 h. fnv1a h (APPEND l1 l2) = fnv1a (fnv1a h l1) l2`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; fnv1a_def]);;

let FNV1A_SEQ_SUC = prove
 (`!h c i. fnv1a h (list_of_seq c (SUC i)) =
           word_mul (word_xor (fnv1a h (list_of_seq c i)) (word (c i))) (word 1099511628211)`,
  REWRITE_TAC[list_of_seq; FNV1A_APPEND; fnv1a_def]);;

(* ------------------------------------------------------------------------- *)
(* The program, as its text fnv_prog.txt; FNV_TERM is that text.            *)
(* ------------------------------------------------------------------------- *)

let fnv_prologue = new_definition
 `fnv_prologue = (TSeq (TInstr (TLoadFrame TyU64 2 22)) (TSeq (TInstr (TLoadFrame TyU64 3 23)) (TSeq (TInstr (TLoadFrame TyU64 4 1)) (TSeq (TInstr (TCmp CondUlt TyU64 9 4 (OpReg 2))) (TSeq (TIf 9 (TSeq (TInstr (TImm TyU64 8 (word 1))) (TReturn 0 8)) TSkip) (TSeq (TInstr (TBin BinSub TyU64 4 4 2)) (TSeq (TInstr (TCmp CondUlt TyU64 9 4 (OpReg 3))) (TSeq (TIf 9 (TSeq (TInstr (TImm TyU64 8 (word 1))) (TReturn 0 8)) TSkip) (TSeq (TInstr (TLoadFrame TyPtr 5 0)) (TSeq (TInstr (TAddr 0 5 5 (SOME 2) 0 (&0:int))) (TInstr (TImm TyU64 10 (word 1099511628211)))))))))))))`;;

let fnv_body = new_definition
 `fnv_body = (TSeq (TInstr (TAddr 0 8 5 (SOME 6) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 1 0 7 8 (&0:int))) (TSeq (TInstr (TBin BinXor TyU64 1 1 7)) (TInstr (TBin BinMulLo TyU64 1 1 10)))))`;;

let fnv = new_definition
 `fnv = TProg [(1,0,1)] [(1,TyU64,0)] (TSeq fnv_prologue (TSeq (TCountLoop 6 3 4294967295 fnv_body) (TReturn 1 1)))`;;

let FNV_TERM = prove
 (`fnv = (TProg [(1,0,1)] [(1,TyU64,0)] (TSeq (TSeq (TInstr (TLoadFrame TyU64 2 22)) (TSeq (TInstr (TLoadFrame TyU64 3 23)) (TSeq (TInstr (TLoadFrame TyU64 4 1)) (TSeq (TInstr (TCmp CondUlt TyU64 9 4 (OpReg 2))) (TSeq (TIf 9 (TSeq (TInstr (TImm TyU64 8 (word 1))) (TReturn 0 8)) TSkip) (TSeq (TInstr (TBin BinSub TyU64 4 4 2)) (TSeq (TInstr (TCmp CondUlt TyU64 9 4 (OpReg 3))) (TSeq (TIf 9 (TSeq (TInstr (TImm TyU64 8 (word 1))) (TReturn 0 8)) TSkip) (TSeq (TInstr (TLoadFrame TyPtr 5 0)) (TSeq (TInstr (TAddr 0 5 5 (SOME 2) 0 (&0:int))) (TInstr (TImm TyU64 10 (word 1099511628211))))))))))))) (TSeq (TCountLoop 6 3 4294967295 (TSeq (TInstr (TAddr 0 8 5 (SOME 6) 0 (&0:int))) (TSeq (TInstr (TLoad TyU64 1 0 7 8 (&0:int))) (TSeq (TInstr (TBin BinXor TyU64 1 1 7)) (TInstr (TBin BinMulLo TyU64 1 1 10)))))) (TReturn 1 1))))`,
  REWRITE_TAC[fnv; fnv_prologue; fnv_body]);;

(* ------------------------------------------------------------------------- *)
(* What a run means.                                                         *)
(* ------------------------------------------------------------------------- *)

(* No run writes memory but the status and return words. *)
let fnv_post = new_definition
 `fnv_post st k s <=>
    (k = 1 /\ val(tisa_fword st 22) + val(tisa_fword st 23) <= val(tisa_len st 0) /\
     tisa_fword s 19 = fnv1a (tregs st 1)
                         (region_range st 0 (val(tisa_fword st 22)) (val(tisa_fword st 23))) /\
     tmem s = tmem (tisa_finst 1 (tisa_fword s 19) st)) \/
    (k = 0 /\ tisa_fword s 19 = word 1 /\
     val(tisa_len st 0) < val(tisa_fword st 22) + val(tisa_fword st 23) /\
     tmem s = tmem (tisa_finst 0 (word 1) st)) \/
    (k = 2 /\ tisa_fword s 19 = word 2 /\
     val(tisa_fword st 22) + val(tisa_fword st 23) <= val(tisa_len st 0) /\
     4294967295 < val(tisa_fword st 23) /\
     tmem s = tmem (tisa_finst 2 (word 2) st))`;;

(* The loop invariant before byte i: the state is FNV-1a of the range's     *)
(* first i bytes from h0.                                                    *)
let fnv_inv = new_definition
 `fnv_inv st N i s <=>
    tregs s 0 = tregs st 0 /\ tmem s = tmem st /\ N = val(tisa_fword st 23) /\
    val(tisa_fword st 22) + val(tisa_fword st 23) <= val(tisa_len st 0) /\
    tregs s 5 = word_add (tisa_base st 0) (word (1 * val (tisa_fword st 22))) /\
    tregs s 10 = word 1099511628211 /\
    tregs s 1 = fnv1a (tregs st 1)
                  (list_of_seq (\j. region_byte st 0 (val(tisa_fword st 22) + j)) i)`;;

let FNV_ENTRY = prove
 (`!st. tisa_entry_ok fnv st
        ==> val(tregs st 0) + 192 <= 2 EXP 64 /\
            val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64 /\
            (val(tisa_len st 0) = 0 \/
             val(tisa_base st 0) + val(tisa_len st 0) <= val(tregs st 0) + 144 \/
             val(tregs st 0) + 192 <= val(tisa_base st 0))`,
  GEN_TAC THEN
  REWRITE_TAC[fnv; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok;
              tisa_region_ok; tisa_pair_ok; tisa_frame; tisa_base; tisa_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The loop body: one byte more.                                             *)
(* ------------------------------------------------------------------------- *)

let FNV_BODY_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [fnv_inv] o
                check (fun th -> tisa_has_tm `fnv_inv` th)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = val(tisa_fword st 23)`)) THEN
  MP_TAC(ISPECL [`s0:tisa_state`; `st:tisa_state`] TISA_SAME_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FNV_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN
    MP_TAC(ISPEC `tisa_fword st 23` VAL_BOUND_64) THEN TISA_ARITH_TAC; ALL_TAC];;

let FNV_CONT_LEAF_TAC =
  FIRST_X_ASSUM(fun th -> if concl th = `val(word j:int64) = j` then
     REWRITE_TAC[th; MULT_CLAUSES] else NO_TAC) THEN
  REWRITE_TAC[READ_REGION_BYTE; fnv_inv; TISA_TREGS_SETREG; TISA_TMEM_SETREG; MULT_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[GSYM ADD1; FNV1A_SEQ_SUC] THEN
  REWRITE_TAC[MULT_CLAUSES];;

let FNV_BODY_WP = prove
 (`!st N j s0. tisa_entry_ok fnv st /\ j < N /\ fnv_inv st N j s0
       ==> tisa_wp fnv_body (fnv_inv st N (j + 1)) (fnv_post st) (tisa_setreg 6 (word j) s0)`,
  FNV_BODY_SETUP_TAC THEN REWRITE_TAC[fnv_body] THEN TISA_VCG_TAC THEN FNV_CONT_LEAF_TAC);;

(* ------------------------------------------------------------------------- *)
(* The prologue: a range outside the input is refused; otherwise the        *)
(* invariant before byte 0.                                                  *)
(* ------------------------------------------------------------------------- *)

(* The memory a stop leaves, against the entry state's. *)
let FNV_MEM_TAC =
  REWRITE_TAC[tisa_finst; tisa_setfword; tisa_store; tmem; tregs; tisa_frame;
              TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

let FNV_REFUSED_LEAF_TAC =
  REWRITE_TAC[fnv_post; ARITH_EQ] THEN REPEAT CONJ_TAC THENL
   [TISA_STATE_NORM_TAC;
    MP_TAC(ISPECL [`tisa_len st 0`; `tisa_fword st 22`] TISA_VAL_SUB_EXACT) THEN
    ASM_ARITH_TAC;
    FNV_MEM_TAC];;

let FNV_PROLOGUE_WP = prove
 (`!st. tisa_entry_ok fnv st
        ==> tisa_wp fnv_prologue
              (\s. tregs s 3 = tisa_fword st 23 /\ fnv_inv st (val(tisa_fword st 23)) 0 s)
              (fnv_post st) st`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FNV_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[fnv_prologue] THEN TISA_VCG_TAC THEN
  REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THENL
   [FNV_REFUSED_LEAF_TAC;
    FNV_REFUSED_LEAF_TAC;
    REWRITE_TAC[fnv_inv; TISA_TREGS_SETREG; TISA_TMEM_SETREG; list_of_seq; fnv1a_def] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`tisa_len st 0`; `tisa_fword st 22`] TISA_VAL_SUB_EXACT) THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The whole program, and its runs.                                          *)
(* ------------------------------------------------------------------------- *)

let TISA_FAILST_FINST = prove
 (`!k st. tisa_failst k st = tisa_finst k (word k) st`,
  REWRITE_TAC[tisa_failst; tisa_finst]);;

let FNV_ROOT_WP = prove
 (`!st. tisa_entry_ok fnv st
        ==> tisa_wp (tisa_root fnv) (\s. F) (fnv_post st) st`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[fnv; tisa_root; TISA_WP_SEQ] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  EXISTS_TAC `\s. tregs s 3 = tisa_fword st 23 /\ fnv_inv st (val(tisa_fword st 23)) 0 s` THEN
  EXISTS_TAC `fnv_post st` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC FNV_PROLOGUE_WP THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `s:tisa_state` THEN STRIP_TAC THEN
  MATCH_MP_TAC TISA_WP_COUNT_LOOP THEN EXISTS_TAC `fnv_inv st` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FNV_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT CONJ_TAC THENL
   [(* a range longer than the loop's cap: UNSUPPORTED *)
    DISCH_TAC THEN REWRITE_TAC[fnv_post; ARITH_EQ; TISA_FAILST_FINST] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [fnv_inv] o
                  check (fun th -> tisa_has_tm `fnv_inv` th)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [TISA_STATE_NORM_TAC; FNV_MEM_TAC];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FNV_BODY_WP THEN ASM_REWRITE_TAC[];
    (* every byte: FIRED with the state *)
    MAP_EVERY X_GEN_TAC [`N:num`; `s1:tisa_state`] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [fnv_inv]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = val(tisa_fword st 23)`)) THEN
    REWRITE_TAC[TISA_WP_RETURN; TISA_TREGS_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[fnv_post; ARITH_EQ; region_range] THEN CONJ_TAC THENL
     [TISA_STATE_NORM_TAC;
      TISA_STATE_NORM_TAC THEN FNV_MEM_TAC]]);;

let FNV_RUN = prove
 (`!st k st'. tisa_entry_ok fnv st /\ tisa_run fnv st = TStop k st'
              ==> fnv_post st k st'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `st:tisa_state` FNV_ROOT_WP) THEN ASM_REWRITE_TAC[tisa_wp] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> tisa_has_tm `tisa_run` th)) THEN
  ASM_REWRITE_TAC[tisa_run] THEN
  MP_TAC(ISPEC `tisa_exec (tisa_root fnv) st` TISA_RESULT_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC)
     (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC))) THEN
  REWRITE_TAC[tisa_then; TISA_RWP_CONT; TISA_RWP_STOP; TISA_RESULT_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN REWRITE_TAC[]);;

(* Soundness: a FIRED run's result is FNV-1a of the range from h0, and the  *)
(* range lies inside the input.                                              *)
let FNV_SOUND = prove
 (`!st st'. tisa_entry_ok fnv st /\ tisa_run fnv st = TStop 1 st'
            ==> val(tisa_fword st 22) + val(tisa_fword st 23) <= val(tisa_len st 0) /\
                tisa_fword st' 19 =
                fnv1a (tregs st 1) (region_range st 0 (val(tisa_fword st 22)) (val(tisa_fword st 23))) /\
                tmem st' = tmem (tisa_finst 1 (tisa_fword st' 19) st)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `1`; `st':tisa_state`] FNV_RUN) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[fnv_post; ARITH_EQ] THEN SIMP_TAC[]);;

(* Completeness: a range inside the input, of at most 2^32 - 1 bytes, fires *)
(* with that result.                                                         *)
let FNV_COMPLETE = prove
 (`!st k st'. tisa_entry_ok fnv st /\
              val(tisa_fword st 22) + val(tisa_fword st 23) <= val(tisa_len st 0) /\
              val(tisa_fword st 23) <= 4294967295 /\
              tisa_run fnv st = TStop k st'
              ==> k = 1 /\
                  tisa_fword st' 19 =
                  fnv1a (tregs st 1) (region_range st 0 (val(tisa_fword st 22)) (val(tisa_fword st 23))) /\
                  tmem st' = tmem (tisa_finst 1 (tisa_fword st' 19) st)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `k:num`; `st':tisa_state`] FNV_RUN) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[fnv_post] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* The refusal is exactly a range outside the input. *)
let FNV_REFUSED = prove
 (`!st k st'. tisa_entry_ok fnv st /\ tisa_run fnv st = TStop k st'
              ==> (val(tisa_len st 0) < val(tisa_fword st 22) + val(tisa_fword st 23) <=>
                   k = 0 /\ tisa_fword st' 19 = word 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `k:num`; `st':tisa_state`] FNV_RUN) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[fnv_post] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_ARITH_TAC);;
