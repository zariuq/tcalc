(* ========================================================================= *)
(* Interning (find-or-make) of 16-byte rows, as the t-ISA p1 program        *)
(* intern16. Regions: 0 rows (16-byte rows), 1 table (8-byte slots), 2      *)
(* header (word 0 = row count); the key is (arg0, arg1).                    *)
(*                                                                           *)
(* INTERN16_SOUND: a FIRED run returns an id whose row is the key, either a  *)
(* row below the count, unchanged, or the row appended at the count; rows   *)
(* below the count are unchanged and the count grows by at most one. The    *)
(* table appears in neither the statement nor the proof.                    *)
(* ========================================================================= *)

needs "tisa/hol/tisa_p1_frame.ml";;

let intern16_prologue = new_definition
 `intern16_prologue = (TSeq (TInstr (TLoadFrame TyU64 1 22)) (TSeq (TInstr (TLoadFrame TyU64 2 23)) (TSeq (TInstr (TLoadFrame TyPtr 8 4)) (TSeq (TInstr (TLoad TyU64 8 2 3 8 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 9 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 9 9 4)) (TSeq (TInstr (TCmp CondUlt TyU64 10 9 (OpReg 3))) (TSeq (TIf 10 (TReturn 2 3) TSkip) (TSeq (TInstr (TLoadFrame TyU64 6 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 6 6 3)) (TSeq (TInstr (TImm TyU64 9 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 4 6 9)) (TSeq (TInstr (TBin BinXor TyU64 5 1 2)) (TSeq (TInstr (TImm TyU64 9 (word 11400714819323198485))) (TSeq (TInstr (TBin BinMulLo TyU64 5 5 9)) (TSeq (TInstr (TShift ShiftRightU TyU64 9 5 29)) (TInstr (TBin BinXor TyU64 5 5 9))))))))))))))))))`;;

let intern16_body = new_definition
 `intern16_body = (TSeq (TInstr (TBin BinAdd TyU64 8 5 7)) (TSeq (TInstr (TBin BinAnd TyU64 8 8 4)) (TSeq (TInstr (TLoadFrame TyPtr 9 2)) (TSeq (TInstr (TAddr 1 9 9 (SOME 8) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 1 10 9 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 11 10 (OpImm (word 0)))) (TIf 11 (TSeq (TInstr (TLoadFrame TyU64 10 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 10 10 4)) (TSeq (TInstr (TCmp CondUlt TyU64 11 3 (OpReg 10))) (TIf 11 (TSeq (TInstr (TShift ShiftLeft TyU64 10 3 1)) (TSeq (TInstr (TLoadFrame TyPtr 11 0)) (TSeq (TInstr (TAddr 0 11 11 (SOME 10) 3 (&0:int))) (TSeq (TInstr (TStore 8 0 11 (&0:int) 1)) (TSeq (TInstr (TStore 8 0 11 (&8:int) 2)) (TSeq (TInstr (TImm TyU64 10 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 10 3 10)) (TSeq (TInstr (TStore 8 1 9 (&0:int) 10)) (TSeq (TInstr (TLoadFrame TyPtr 11 4)) (TSeq (TInstr (TStore 8 2 11 (&0:int) 10)) (TReturn 1 3))))))))))) (TReturn 2 3))))) (TSeq (TInstr (TImm TyU64 11 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 10 10 11)) (TSeq (TInstr (TCmp CondUlt TyU64 11 10 (OpReg 3))) (TIf 11 (TSeq (TInstr (TShift ShiftLeft TyU64 11 10 1)) (TSeq (TInstr (TLoadFrame TyPtr 8 0)) (TSeq (TInstr (TAddr 0 8 8 (SOME 11) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 11 8 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 11 11 (OpReg 1))) (TIf 11 (TSeq (TInstr (TLoad TyU64 8 0 11 8 (&8:int))) (TSeq (TInstr (TCmp CondEq TyU64 11 11 (OpReg 2))) (TIf 11 (TReturn 1 10) TSkip))) TSkip)))))) TSkip)))))))))))`;;

let intern16 = new_definition
 `intern16 = TProg [(2,16,8); (2,8,8); (2,8,8)] []
               (TSeq intern16_prologue
                     (TSeq (TCountLoop 7 6 16777216 intern16_body) (TReturn 2 3)))`;;

(* The row count, and word i of the rows region (row j is words 2j, 2j+1). *)
let intern_count = new_definition
 `intern_count st = tisa_read st (tisa_base st 2) 8`;;

let intern_word = new_definition
 `intern_word st i = tisa_read st (word_add (tisa_base st 0) (word(8 * i))) 8`;;

needs "native/hol/tisa_symex.ml";;

(* ------------------------------------------------------------------------- *)
(* The prologue: reads the key and the count; continues only when the count  *)
(* is within the rows' capacity.                                             *)
(* ------------------------------------------------------------------------- *)

let INTERN16_PROLOGUE = prove
 (`!st r. tisa_exec intern16_prologue st = r
          ==> (!s. r = TCont s
                   ==> tregs s 0 = tregs st 0 /\ tmem s = tmem st /\
                       tregs s 1 = tisa_fword st 22 /\ tregs s 2 = tisa_fword st 23 /\
                       tregs s 3 = intern_count st /\
                       val(intern_count st) <= val(tisa_len st 0) DIV 16) /\
              (!k s. r = TStop k s ==> ~(k = 1))`,
  REPEAT GEN_TAC THEN TISA_PATHS_TAC[intern16_prologue] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_USHR]) THEN
  REWRITE_TAC[intern_count; tisa_base; tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[VAL_WORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN TRY ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* What a FIRED run guarantees, and the facts about the initial state that   *)
(* the body's proof uses: entry validation's region facts and the prologue's *)
(* capacity check.                                                           *)
(* ------------------------------------------------------------------------- *)

let intern16_post = new_definition
 `intern16_post st0 s <=>
    val(tisa_fword s 19) < val(intern_count s) /\
    (val(intern_count s) = val(intern_count st0) \/
     val(intern_count s) = val(intern_count st0) + 1 /\
     val(tisa_fword s 19) = val(intern_count st0)) /\
    intern_word s (2 * val(tisa_fword s 19)) = tisa_fword st0 22 /\
    intern_word s (2 * val(tisa_fword s 19) + 1) = tisa_fword st0 23 /\
    (!i. i < 2 * val(intern_count st0) ==> intern_word s i = intern_word st0 i)`;;

let intern16_regions = new_definition
 `intern16_regions st0 <=>
    val(tregs st0 0) + 192 <= 2 EXP 64 /\
    (!r. r < 3 ==> val(tisa_base st0 r) + val(tisa_len st0 r) < 2 EXP 64 /\
                   (val(tisa_base st0 r) + val(tisa_len st0 r) <= val(tregs st0 0) \/
                    val(tregs st0 0) + 192 <= val(tisa_base st0 r))) /\
    16 <= val(tisa_len st0 0) /\ 8 <= val(tisa_len st0 1) /\ 8 <= val(tisa_len st0 2) /\
    (!r q. r < 3 /\ q < 3 /\ ~(r = q)
           ==> val(tisa_base st0 r) + val(tisa_len st0 r) <= val(tisa_base st0 q) \/
               val(tisa_base st0 q) + val(tisa_len st0 q) <= val(tisa_base st0 r)) /\
    val(intern_count st0) <= val(tisa_len st0 0) DIV 16`;;

(* ------------------------------------------------------------------------- *)
(* Entry validation gives the regions' bounds, their separation from the     *)
(* frame and from each other, and their minimum lengths.                     *)
(* ------------------------------------------------------------------------- *)

let INTERN16_ENTRY = prove
 (`!st. tisa_entry_ok intern16 st
        ==> val(tregs st 0) + 192 <= 2 EXP 64 /\
            (!r. r < 3 ==> val(tisa_base st r) + val(tisa_len st r) < 2 EXP 64 /\
                           (val(tisa_base st r) + val(tisa_len st r) <= val(tregs st 0) \/
                            val(tregs st 0) + 192 <= val(tisa_base st r))) /\
            16 <= val(tisa_len st 0) /\ 8 <= val(tisa_len st 1) /\ 8 <= val(tisa_len st 2) /\
            (!r q. r < 3 /\ q < 3 /\ ~(r = q)
                   ==> val(tisa_base st r) + val(tisa_len st r) <= val(tisa_base st q) \/
                       val(tisa_base st q) + val(tisa_len st q) <= val(tisa_base st r))`,
  GEN_TAC THEN
  REWRITE_TAC[intern16; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok;
              tisa_region_ok; tisa_pair_ok; tisa_frame; tisa_base; tisa_len] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(val(tisa_fword st 1) = 0) /\ ~(val(tisa_fword st 3) = 0) /\
                ~(val(tisa_fword st 5) = 0)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TISA_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(val(tisa_fword st 1) = 0)`;
                              ASSUME `~(val(tisa_fword st 3) = 0)`;
                              ASSUME `~(val(tisa_fword st 5) = 0)`]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REWRITE_TAC[ARITH_RULE `r < 3 <=> r = 0 \/ r = 1 \/ r = 2`] THEN
  REPEAT CONJ_TAC THEN TRY TISA_ARITH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhand(concl th))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN TISA_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop body. Every path that continues keeps the frame register, the    *)
(* memory, the key and the count; each FIRED path (row found, row appended)  *)
(* ends in a state satisfying intern16_post.                                 *)
(* ------------------------------------------------------------------------- *)

let intern16_finst_arg w =
  rand(tisa_find_sub (fun t -> fst(strip_comb t) = `tisa_finst` &&
                               length(snd(strip_comb t)) = 3) w);;

let INTERN16_READ_FINST_ASM th =
  is_forall(concl th) && tisa_has_tm `tisa_finst` th && tisa_has_tm `tisa_read` th;;

(* The region facts of st0, instantiated at regions 0, 1, 2 and their pairs. *)
let INTERN16_REGION_FACTS_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[intern16_regions] o
    check (fun th -> concl th = `intern16_regions st0`)) THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && tisa_has_tm `2 EXP 64` th &&
                          not (tisa_has_tm `tisa_frame` th) &&
                          length(fst(strip_forall(concl th))) = 1
                       then MAP_EVERY (fun n -> MP_TAC(SPEC n th)) [`0`; `1`; `2`] else NO_TAC) THEN
  REWRITE_TAC[tisa_base; tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
                          not (tisa_has_tm `2 EXP 64` th) && tisa_has_tm `tisa_len` th
                       then MAP_EVERY (fun (a,b) -> MP_TAC(SPECL [a;b] th))
                              [(`0`,`1`); (`0`,`2`); (`1`,`2`)]
                       else NO_TAC) THEN
  REWRITE_TAC[tisa_base; tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT DISCH_TAC;;

(* Specializations of the finish lemmas to a state X with st0's frame.      *)
let INTERN16_FINISH_SPECS_TAC =
  SUBGOAL_THEN `!out (v:int64) i. i < 24 ==> tisa_fword (tisa_finst out v X) i =
                  if i = 19 then v else if i = 18 then word out else tisa_fword st0 i`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`X:tisa_state`; `out:num`; `v:int64`; `i:num`] TISA_FWORD_FINST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN TISA_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!out (v:int64) (a:int64). val a + 8 <= 2 EXP 64 /\
                  (val a + 8 <= val(tregs st0 0) \/ val(tregs st0 0) + 192 <= val a)
                  ==> tisa_read (tisa_finst out v X) a 8 = tisa_read X a 8`
   ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC TISA_READ_FINST THEN ASM_REWRITE_TAC[] THEN TISA_ARITH_TAC;
    ALL_TAC];;

(* The row was found: the id is below the count, its row is the key, and     *)
(* the run wrote only the status and the return value.                       *)
let INTERN16_FOUND_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhand(concl th) = `s:tisa_state`)) THEN
  ABBREV_TAC `slotaddr = iword(&(val (tisa_fword st 2)) + &(val (word_and (word_add (tregs st 5) (tregs st 7)) (tregs st 4))) * &2 pow 3):int64` THEN
  ABBREV_TAC `slot = tisa_read st slotaddr 8` THEN
  ABBREV_TAC `id = word_sub (slot:int64) (word 1)` THEN
  INTERN16_REGION_FACTS_TAC THEN
  MP_TAC(ISPECL [`st:tisa_state`; `st0:tisa_state`] TISA_SAME_VIEW) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  W(fun (asl,w) -> ABBREV_TAC(mk_eq(mk_var("X",`:tisa_state`), intern16_finst_arg w))) THEN
  SUBGOAL_THEN `tregs X 0 = tregs st0 0 /\ tmem X = tmem st0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN ASM_REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:tisa_state`; `st0:tisa_state`] TISA_SAME_VIEW) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NUM_REDUCE_CONV) o REWRITE_RULE[tisa_base; tisa_len; intern_count]) THEN
  INTERN16_FINISH_SPECS_TAC THEN
  RULE_ASSUM_TAC(fun th -> if INTERN16_READ_FINST_ASM th
                           then REWRITE_RULE[ASSUME `!a w. tisa_read X a w = tisa_read st0 a w`] th
                           else th) THEN
  REWRITE_TAC[intern16_post; intern_count; intern_word; tisa_base] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH_RULE `19 < 24 /\ 4 < 24 /\ 0 < 24`] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `tisa_read (tisa_finst 1 id X) (tisa_fword st0 4) 8 = tisa_read st0 (tisa_fword st0 4) 8`
   SUBST1_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check INTERN16_READ_FINST_ASM) THEN TISA_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if concl th = `tregs st 3 = tisa_read st0 (tisa_fword st0 4) 8`
                       then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  SUBGOAL_THEN `val(id:int64) < 2 EXP 60` ASSUME_TAC THENL
   [MP_TAC(ISPEC `tisa_fword st0 1` VAL_BOUND_64) THEN TISA_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!k. 8 * k + 8 <= val(tisa_fword st0 1)
                   ==> tisa_read (tisa_finst 1 id X) (word_add (tisa_fword st0 0) (word (8 * k))) 8 =
                       tisa_read st0 (word_add (tisa_fword st0 0) (word (8 * k))) 8`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o check INTERN16_READ_FINST_ASM) THEN
    SUBGOAL_THEN `val(word_add (tisa_fword st0 0) (word (8 * k)):int64) = val(tisa_fword st0 0) + 8 * k`
     SUBST1_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN TISA_ARITH_TAC; TISA_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `iword(&(val (tisa_fword st 0)) + &(val (word_shl (id:int64) 1)) * &2 pow 3):int64 =
                word_add (tisa_fword st0 0) (word (8 * (2 * val id)))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[TISA_ADDR_WORD] THEN
    SUBGOAL_THEN `val(word_shl (id:int64) 1) = 2 * val id` SUBST1_TAC THENL
     [MATCH_MP_TAC TISA_VAL_SHL1 THEN TISA_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!(x:int64) n. iword(&(val x) + &n) = word_add x (word n)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[INT_OF_NUM_ADD; GSYM WORD_IWORD; WORD_ADD; WORD_VAL]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                              ARITH_RULE `8 * (2 * x) + 8 = 8 * (2 * x + 1)`]) THEN
  let ROW_ASM th = is_forall(concl th) && tisa_has_tm `tisa_finst 1 id X` th in
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `2 * val(id:int64)` o check ROW_ASM) THEN
    ANTS_TAC THENL [TISA_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `2 * val(id:int64) + 1` o check ROW_ASM) THEN
    ANTS_TAC THENL [TISA_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o check ROW_ASM) THEN TISA_ARITH_TAC;;

(* The row was appended: the key went to row count, the slot and the count  *)
(* were updated, and rows below the count are untouched.                     *)
let INTERN16_APPEND_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhand(concl th) = `s:tisa_state`)) THEN
  ABBREV_TAC `slotaddr = iword(&(val (tisa_fword st 2)) + &(val (word_and (word_add (tregs st 5) (tregs st 7)) (tregs st 4))) * &2 pow 3):int64` THEN
  INTERN16_REGION_FACTS_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NUM_REDUCE_CONV) o
                 REWRITE_RULE[tisa_base; tisa_len; intern_count; VAL_WORD_USHR]) THEN
  REWRITE_TAC[intern_count; tisa_base] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `c = tisa_read st0 (tisa_fword st0 4) 8` THEN
  MP_TAC(ISPECL [`st:tisa_state`; `st0:tisa_state`] TISA_SAME_VIEW) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let ths = CONJUNCTS th in
    RULE_ASSUM_TAC(REWRITE_RULE (tl ths)) THEN REWRITE_TAC (tl ths) THEN MAP_EVERY ASSUME_TAC ths) THEN
  FIRST_ASSUM(fun th5 -> if concl th5 = `tregs st 3 = c` then
       RULE_ASSUM_TAC(fun th -> if concl th = concl th5 then th else REWRITE_RULE[th5] th) THEN
       REWRITE_TAC[th5] else NO_TAC) THEN
  SUBGOAL_THEN `val(c:int64) < 2 EXP 60 /\ 16 * val c + 16 <= val(tisa_fword st0 1)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `tisa_fword st0 1` VAL_BOUND_64) THEN TISA_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `iword(&(val (tisa_fword st0 0)) + &(val (word_shl (c:int64) 1)) * &2 pow 3):int64 =
                word_add (tisa_fword st0 0) (word (8 * (2 * val c)))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [REWRITE_TAC[TISA_ADDR_WORD] THEN
    SUBGOAL_THEN `val(word_shl (c:int64) 1) = 2 * val c` SUBST1_TAC THENL
     [MATCH_MP_TAC TISA_VAL_SHL1 THEN TISA_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!(x:int64) n. iword(&(val x) + &n) = word_add x (word n)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [REWRITE_TAC[INT_OF_NUM_ADD; GSYM WORD_IWORD; WORD_ADD; WORD_VAL]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                              ARITH_RULE `8 * (2 * x) + 8 = 8 * (2 * x + 1)`]) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ARITH_RULE `8 * (2 * x) + 8 = 8 * (2 * x + 1)`] THEN
  ABBREV_TAC `r0a = word_add (tisa_fword st0 0) (word (8 * 2 * val (c:int64))):int64` THEN
  ABBREV_TAC `r1a = word_add (tisa_fword st0 0) (word (8 * (2 * val (c:int64) + 1))):int64` THEN
  SUBGOAL_THEN `val(r0a:int64) = val(tisa_fword st0 0) + 16 * val(c:int64) /\
                val(r1a:int64) = val(tisa_fword st0 0) + 16 * val c + 8`
   STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r0a"; "r1a"] THEN CONJ_TAC THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) TISA_VAL_OFFSET (lhand w))) THEN
    (ANTS_TAC THENL [TISA_ARITH_TAC; SIMP_TAC[]]) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(tisa_fword st0 2) <= val(slotaddr:int64) /\
                val slotaddr + 8 <= val(tisa_fword st0 2) + val(tisa_fword st0 3)`
   STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `tisa_inside st 1 (&(val (slotaddr:int64))) 8`)) THEN
    ASM_REWRITE_TAC[tisa_inside; tisa_base; tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_LE];
    ALL_TAC] THEN
  W(fun (asl,w) -> let y0 = tisa_find_sub (fun t -> let h,a = strip_comb t in
                    h = `tisa_setreg` && length a = 3 && hd a = `11` && el 1 a = `r0a:int64`) w in
     ABBREV_TAC(mk_eq(mk_var("Y0",`:tisa_state`), y0))) THEN
  SUBGOAL_THEN `tregs Y0 0 = tregs st0 0 /\ tmem Y0 = tmem st0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Y0" THEN ASM_REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  W(fun (asl,w) -> let y4 = tisa_find_sub (fun t -> let h,a = strip_comb t in
                    h = `tisa_store` && length a = 4 && hd a = `slotaddr:int64`) w in
     ABBREV_TAC(mk_eq(mk_var("Y4",`:tisa_state`), y4))) THEN
  SUBGOAL_THEN
   `val(tregs st0 0) + 192 <= 2 EXP 64 /\
    (val(r0a:int64) + 8 <= 2 EXP 64 /\ (val r0a + 8 <= val(tregs st0 0) \/ val(tregs st0 0) + 192 <= val r0a)) /\
    (val(r1a:int64) + 8 <= 2 EXP 64 /\ (val r1a + 8 <= val(tregs st0 0) \/ val(tregs st0 0) + 192 <= val r1a)) /\
    (val(slotaddr:int64) + 8 <= 2 EXP 64 /\
     (val slotaddr + 8 <= val(tregs st0 0) \/ val(tregs st0 0) + 192 <= val slotaddr)) /\
    (val(tisa_fword st0 4) + 8 <= 2 EXP 64 /\
     (val(tisa_fword st0 4) + 8 <= val(tregs st0 0) \/ val(tregs st0 0) + 192 <= val(tisa_fword st0 4)))`
   (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THENL
   [REPEAT CONJ_TAC THEN TISA_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `tregs Y4 0 = tregs st0 0` ASSUME_TAC THENL
   [EXPAND_TAC "Y4" THEN REWRITE_TAC[TISA_TREGS_STORE; TISA_TREGS_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < 24 ==> tisa_fword Y4 i = tisa_fword st0 i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Y4" THEN REPEAT TISA_FWORD_STEP_TAC THEN
    MP_TAC(ISPECL [`Y0:tisa_state`; `st0:tisa_state`] TISA_SAME_VIEW) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `tisa_fword Y4 4 = tisa_fword st0 4` SUBST1_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `4 < 24`]; ALL_TAC] THEN
  W(fun (asl,w) -> ABBREV_TAC(mk_eq(mk_var("X",`:tisa_state`), intern16_finst_arg w))) THEN
  SUBGOAL_THEN `tregs X 0 = tregs st0 0` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[TISA_TREGS_STORE; TISA_TREGS_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < 24 ==> tisa_fword X i = tisa_fword st0 i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "X" THEN REPEAT TISA_FWORD_STEP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  let READS_THROUGH_TAC =
    EXPAND_TAC "X" THEN REPEAT TISA_READ_STEP_TAC THEN EXPAND_TAC "Y4" THEN
    REPEAT TISA_READ_STEP_TAC THEN
    MP_TAC(ISPECL [`Y0:tisa_state`; `st0:tisa_state`] TISA_SAME_VIEW) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[] in
  SUBGOAL_THEN `tisa_read X (tisa_fword st0 4) 8 = word_add c (word 1)` ASSUME_TAC THENL
   [READS_THROUGH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `tisa_read X r0a 8 = tisa_fword st0 22` ASSUME_TAC THENL
   [READS_THROUGH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `tisa_read X r1a 8 = tisa_fword st0 23` ASSUME_TAC THENL
   [READS_THROUGH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!k. 8 * k + 8 <= 16 * val(c:int64)
                   ==> tisa_read X (word_add (tisa_fword st0 0) (word (8 * k))) 8 =
                       tisa_read st0 (word_add (tisa_fword st0 0) (word (8 * k))) 8`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_fword st0 0) (word (8 * k)):int64) = val(tisa_fword st0 0) + 8 * k`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN TISA_ARITH_TAC; ALL_TAC] THEN
    READS_THROUGH_TAC;
    ALL_TAC] THEN
  INTERN16_FINISH_SPECS_TAC THEN
  REWRITE_TAC[intern16_post; intern_count; intern_word; tisa_base] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH_RULE `19 < 24 /\ 4 < 24 /\ 0 < 24`] THEN CONV_TAC NUM_REDUCE_CONV THEN
  let FINST_READ_SPEC_TAC a =
    FIRST_ASSUM(fun th -> if INTERN16_READ_FINST_ASM th then MP_TAC(SPECL [`1`; `c:int64`; a] th)
                          else NO_TAC) in
  SUBGOAL_THEN `tisa_read (tisa_finst 1 c X) (tisa_fword st0 4) 8 = word_add c (word 1)` SUBST1_TAC THENL
   [FINST_READ_SPEC_TAC `tisa_fword st0 4` THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add (c:int64) (word 1)) = val c + 1` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN TISA_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `word_add (tisa_fword st0 0) (word (8 * 2 * val (c:int64))) = r0a`
                         then REWRITE_TAC[th] else NO_TAC) THEN
    FINST_READ_SPEC_TAC `r0a:int64` THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `word_add (tisa_fword st0 0) (word (8 * (2 * val (c:int64) + 1))) = r1a`
                         then REWRITE_TAC[th] else NO_TAC) THEN
    FINST_READ_SPEC_TAC `r1a:int64` THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add (tisa_fword st0 0) (word (8 * i)):int64) = val(tisa_fword st0 0) + 8 * i`
   ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN TISA_ARITH_TAC; ALL_TAC] THEN
  FINST_READ_SPEC_TAC `word_add (tisa_fword st0 0) (word (8 * i)):int64` THEN
  ANTS_TAC THENL [CONJ_TAC THEN TISA_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) && tisa_has_tm `16 * val(c:int64)` th)) THEN
  TISA_ARITH_TAC;;

let INTERN16_BODY = prove
 (`!st0 st r.
     intern16_regions st0 /\
     tregs st 0 = tregs st0 0 /\ tmem st = tmem st0 /\
     tregs st 1 = tisa_fword st0 22 /\ tregs st 2 = tisa_fword st0 23 /\
     tregs st 3 = intern_count st0 /\
     tisa_exec intern16_body st = r
     ==> (!s. r = TCont s ==> tregs s 0 = tregs st0 0 /\ tmem s = tmem st0 /\
                              tregs s 1 = tisa_fword st0 22 /\ tregs s 2 = tisa_fword st0 23 /\
                              tregs s 3 = intern_count st0) /\
         (!k s. r = TStop k s /\ k = 1 ==> intern16_post st0 s)`,
  REPEAT GEN_TAC THEN TISA_PATHS_TAC[intern16_body] THENL
   [INTERN16_FOUND_TAC; INTERN16_APPEND_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The program: after entry validation, a FIRED run returns an id whose row  *)
(* is the key, keeps every row below the old count, and grows the count by  *)
(* at most one, the appended row being the new id.                          *)
(* ------------------------------------------------------------------------- *)

let INTERN16_SOUND = prove
 (`!st st'. tisa_entry_ok intern16 st /\
            tisa_exec (tisa_root intern16) st = TStop 1 st'
            ==> intern16_post st st'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INTERN16_ENTRY) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && tisa_has_tm `tisa_root` th)) THEN
  REWRITE_TAC[intern16; tisa_root; TISA_EXEC_SEQ_EQ; TISA_RESULT_DISTINCT; TISA_RESULT_INJ] THEN
  REWRITE_TAC[GSYM intern16] THEN STRIP_TAC THENL
   [(* the loop ran out: the final return is UNSUPPORTED *)
    FIRST_X_ASSUM(MP_TAC o check (fun th -> tisa_has_tm `TReturn 2 3` th)) THEN
    REWRITE_TAC[TISA_EXEC_RETURN_EQ; TISA_RESULT_INJ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    ALL_TAC;
    (* the prologue never fires *)
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `1 = k`)) THEN
    MP_TAC(SPECL [`st:tisa_state`; `TStop 1 s1`] INTERN16_PROLOGUE) THEN
    ASM_REWRITE_TAC[TISA_RESULT_INJ; TISA_RESULT_DISTINCT] THEN
    DISCH_THEN(MP_TAC o SPECL [`1`; `s1:tisa_state`]) THEN REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `1 = k`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `st':tisa_state = s1'`)) THEN
  MP_TAC(SPECL [`st:tisa_state`; `TCont s1`] INTERN16_PROLOGUE) THEN
  ASM_REWRITE_TAC[TISA_RESULT_INJ; TISA_RESULT_DISTINCT] THEN
  DISCH_THEN(MP_TAC o SPEC `s1:tisa_state`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> tisa_has_tm `TCountLoop` th)) THEN
  REWRITE_TAC[tisa_exec] THEN COND_CASES_TAC THEN
  REWRITE_TAC[TISA_FAIL_STOP; TISA_RESULT_INJ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `intern16_regions st` ASSUME_TAC THENL
   [REWRITE_TAC[intern16_regions] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\st'. tisa_exec intern16_body st'`; `7`;
     `\s. tregs s 0 = tregs st 0 /\ tmem s = tmem st /\
          tregs s 1 = tisa_fword st 22 /\ tregs s 2 = tisa_fword st 23 /\
          tregs s 3 = intern_count st`;
     `\k s. k = 1 ==> intern16_post st s`] TISA_COUNT_ITER_INV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && tisa_has_tm `intern16_body` th
       then MP_TAC(SPECL [`st:tisa_state`; rand(lhand(concl th)); rand(concl th)] INTERN16_BODY)
       else NO_TAC) THEN
    ASM_REWRITE_TAC[TISA_RESULT_INJ; TISA_RESULT_DISTINCT] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`val(tregs s1 6)`; `0`; `s1:tisa_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`1`; `s1':tisa_state`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* intern16 is the program of the image record intern16b.hol, whose x86      *)
(* bytes the t-ISA generator proves.                                         *)
(* ------------------------------------------------------------------------- *)

let INTERN16_TERM = prove
 (`intern16 = (TProg [(2,16,8); (2,8,8); (2,8,8)] [] (TSeq (TSeq (TInstr (TLoadFrame TyU64 1 22)) (TSeq (TInstr (TLoadFrame TyU64 2 23)) (TSeq (TInstr (TLoadFrame TyPtr 8 4)) (TSeq (TInstr (TLoad TyU64 8 2 3 8 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 9 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 9 9 4)) (TSeq (TInstr (TCmp CondUlt TyU64 10 9 (OpReg 3))) (TSeq (TIf 10 (TReturn 2 3) TSkip) (TSeq (TInstr (TLoadFrame TyU64 6 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 6 6 3)) (TSeq (TInstr (TImm TyU64 9 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 4 6 9)) (TSeq (TInstr (TBin BinXor TyU64 5 1 2)) (TSeq (TInstr (TImm TyU64 9 (word 11400714819323198485))) (TSeq (TInstr (TBin BinMulLo TyU64 5 5 9)) (TSeq (TInstr (TShift ShiftRightU TyU64 9 5 29)) (TInstr (TBin BinXor TyU64 5 5 9)))))))))))))))))) (TSeq (TCountLoop 7 6 16777216 (TSeq (TInstr (TBin BinAdd TyU64 8 5 7)) (TSeq (TInstr (TBin BinAnd TyU64 8 8 4)) (TSeq (TInstr (TLoadFrame TyPtr 9 2)) (TSeq (TInstr (TAddr 1 9 9 (SOME 8) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 1 10 9 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 11 10 (OpImm (word 0)))) (TIf 11 (TSeq (TInstr (TLoadFrame TyU64 10 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 10 10 4)) (TSeq (TInstr (TCmp CondUlt TyU64 11 3 (OpReg 10))) (TIf 11 (TSeq (TInstr (TShift ShiftLeft TyU64 10 3 1)) (TSeq (TInstr (TLoadFrame TyPtr 11 0)) (TSeq (TInstr (TAddr 0 11 11 (SOME 10) 3 (&0:int))) (TSeq (TInstr (TStore 8 0 11 (&0:int) 1)) (TSeq (TInstr (TStore 8 0 11 (&8:int) 2)) (TSeq (TInstr (TImm TyU64 10 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 10 3 10)) (TSeq (TInstr (TStore 8 1 9 (&0:int) 10)) (TSeq (TInstr (TLoadFrame TyPtr 11 4)) (TSeq (TInstr (TStore 8 2 11 (&0:int) 10)) (TReturn 1 3))))))))))) (TReturn 2 3))))) (TSeq (TInstr (TImm TyU64 11 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 10 10 11)) (TSeq (TInstr (TCmp CondUlt TyU64 11 10 (OpReg 3))) (TIf 11 (TSeq (TInstr (TShift ShiftLeft TyU64 11 10 1)) (TSeq (TInstr (TLoadFrame TyPtr 8 0)) (TSeq (TInstr (TAddr 0 8 8 (SOME 11) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 11 8 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 11 11 (OpReg 1))) (TIf 11 (TSeq (TInstr (TLoad TyU64 8 0 11 8 (&8:int))) (TSeq (TInstr (TCmp CondEq TyU64 11 11 (OpReg 2))) (TIf 11 (TReturn 1 10) TSkip))) TSkip)))))) TSkip)))))))))))) (TReturn 2 3))))`,
  REWRITE_TAC[intern16; intern16_prologue; intern16_body]);;
