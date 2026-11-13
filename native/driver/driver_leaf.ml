(* ========================================================================= *)
(* What the driver assumes of a leaf, and what every p1 run gives it.        *)
(*                                                                           *)
(* tisa_leaf_spec prog mc pc is the image theorem the t-ISA generator proves *)
(* for one image (tisa_entry_goal in tcalc/tisa/hol/tisa_x86_wrapper.ml),    *)
(* stated once for every program: the placement conditions over the          *)
(* declared regions, quantified instead of unrolled. tisa_leaf_wf is the     *)
(* static side of admission the driver relies on: at most nine regions,      *)
(* stores into read-write regions, v0 never written, and entry registers of  *)
(* type U64 (any value is canonical for them, so the plan may pass any).     *)
(*                                                                           *)
(* From these, every run stops, keeps v0 and every byte outside its          *)
(* read-write regions and frame words 18..21 (TISA_RUN_KEEPS), and reports   *)
(* its outcome in frame word 18 (TISA_RUN_STATUS).                           *)
(* ========================================================================= *)

needs "tisa/hol/tisa_x86_wrapper.ml";;

let tisa_decls = define
 `tisa_decls (TProg decls init root) = decls`;;

let tisa_inits = define
 `tisa_inits (TProg decls init root) = init`;;

let TISA_PROG_CASES = prove
 (`!p. p = TProg (tisa_decls p) (tisa_inits p) (tisa_root p)`,
  MATCH_MP_TAC tisa_prog_INDUCT THEN REWRITE_TAC[tisa_decls; tisa_inits; tisa_root]);;

let tisa_leaf_wf = new_definition
 `tisa_leaf_wf prog <=>
    LENGTH (tisa_decls prog) <= 9 /\
    tisa_stmt_ok (tisa_decls prog) (tisa_root prog) /\
    ALL (\v:num#tisa_ty#num. FST(SND v) = TyU64) (tisa_inits prog)`;;

(* The caller's placement, as the image theorem states it. *)
let tisa_leaf_place = new_definition
 `tisa_leaf_place prog (mc:byte list) pc t (stackpointer:int64) <=>
    nonoverlapping (tregs t 0,192) (word pc,LENGTH mc) /\
    (!r. tisa_rw (tisa_decls prog) r
         ==> nonoverlapping (tisa_base t r,val(tisa_len t r)) (word pc,LENGTH mc)) /\
    40 <= val stackpointer /\ val stackpointer + 8 <= 2 EXP 64 /\
    nonoverlapping (word_sub stackpointer (word 40),48) (word pc,LENGTH mc) /\
    (val(tregs t 0) + 192 <= val stackpointer - 40 \/
     val stackpointer + 8 <= val(tregs t 0)) /\
    (!r. tisa_readable (tisa_decls prog) r
         ==> val(tisa_len t r) = 0 \/
             val(tisa_base t r) + val(tisa_len t r) <= val stackpointer - 40 \/
             val stackpointer + 8 <= val(tisa_base t r))`;;

let tisa_leaf_spec = new_definition
 `tisa_leaf_spec prog mc pc <=>
   !t stackpointer returnaddress r14v r15v.
     tisa_entry_ok prog t /\ tisa_leaf_place prog mc pc t stackpointer
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mc /\ read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               tisa_x86_rel t s /\ read R14 s = r14v /\ read R15 s = r15v)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read RBX s = tregs t 9 /\ read R12 s = tregs t 10 /\
               read R13 s = tregs t 11 /\ read R14 s = r14v /\ read R15 s = r15v /\
               (?k u. tisa_run prog t = TStop k u /\ read RAX s = tisa_fword u 19 /\
                      !a. ~tisa_saved stackpointer a ==> read memory s a = tmem u a))
          (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; R8; R9; R10; R11; R12; R13;
                      R14; R15] ,,
           MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory])`;;

(* ------------------------------------------------------------------------- *)
(* Entry validation gives the frame separation the run lemmas use.           *)
(* ------------------------------------------------------------------------- *)

let TISA_DECLS_OK_REGION = prove
 (`!ds q st. tisa_decls_ok st q ds
             ==> !r. r < LENGTH ds /\ ~(FST(EL r ds) = 0)
                     ==> tisa_region_ok (FST(EL r ds)) (FST(SND(EL r ds))) (SND(SND(EL r ds)))
                           (val(tisa_base st (q + r))) (val(tisa_len st (q + r)))
                           (val(tisa_frame st))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  REWRITE_TAC[tisa_decls_ok] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; ADD_CLAUSES; LT_SUC] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`q + 1`; `st:tisa_state`] o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(q + 1) + r = SUC(q + r)`]);;

let TISA_ENTRY_FRAME_SEP = prove
 (`!decls init root t.
     LENGTH decls <= 9 /\ tisa_entry_ok (TProg decls init root) t
     ==> tisa_frame_sep decls t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_entry_ok; tisa_frame_sep; tisa_frame] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`decls:(num#num#num)list`; `0`; `t:tisa_state`] TISA_DECLS_OK_REGION) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; tisa_frame] THEN DISCH_TAC THEN
  REWRITE_TAC[tisa_readable; tisa_rw] THEN CONJ_TAC THEN X_GEN_TAC `r:num` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN
  ASM_REWRITE_TAC[tisa_region_ok] THEN ARITH_TAC);;

let TISA_INIT_U64 = prove
 (`!init st. ALL (\v:num#tisa_ty#num. FST(SND v) = TyU64) init ==> tisa_init_ok st init`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; tisa_init_ok] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_REWRITE_TAC[tisa_canonical; tisa_norm; distinctness "tisa_ty"]);;

(* ------------------------------------------------------------------------- *)
(* Every run stops, and keeps what its frame and regions do not cover.       *)
(* ------------------------------------------------------------------------- *)

let TISA_RUN_STOP = prove
 (`!prog t. ?k u. tisa_run prog t = TStop k u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_run] THEN COND_CASES_TAC THENL
   [MP_TAC(ISPEC `tisa_exec (tisa_root prog) t` TISA_RESULT_CASES) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[tisa_then; tisa_fail] THEN MESON_TAC[];
    REWRITE_TAC[tisa_fail] THEN MESON_TAC[]]);;

let TISA_RUN_KEEPS = prove
 (`!prog t k u.
     tisa_leaf_wf prog /\ tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
     ==> tisa_keeps (tisa_decls prog) t u`,
  GEN_TAC THEN ONCE_REWRITE_TAC[TISA_PROG_CASES] THEN
  REWRITE_TAC[tisa_leaf_wf; tisa_decls; tisa_inits; tisa_root] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `tisa_frame_sep (tisa_decls prog) t` ASSUME_TAC THENL
   [ASM_MESON_TAC[TISA_ENTRY_FRAME_SEP]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `tisa_run`)) (concl th))) THEN
  ASM_REWRITE_TAC[tisa_run; tisa_root] THEN DISCH_TAC THEN
  SUBGOAL_THEN `tisa_keeps (tisa_decls prog) t
                 (tisa_state_of (tisa_then (tisa_exec (tisa_root prog) t) (\st'. tisa_fail 2 st')))`
  MP_TAC THENL
   [MATCH_MP_TAC TISA_KEEPS_THEN THEN ASM_SIMP_TAC[TISA_KEEPS_EXEC] THEN
    X_GEN_TAC `w:tisa_state` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC TISA_KEEPS_FAIL THEN
    MP_TAC(SPECL [`tisa_root prog`; `tisa_decls prog`; `t:tisa_state`] TISA_KEEPS_EXEC) THEN
    ASM_REWRITE_TAC[tisa_state_of] THEN ASM_MESON_TAC[TISA_KEEPS_WRITABLE];
    ASM_REWRITE_TAC[tisa_state_of]]);;

(* ------------------------------------------------------------------------- *)
(* A run reports its outcome code in frame word 18 of its final state, and   *)
(* the code is a failure code or an outcome its program returns.             *)
(* ------------------------------------------------------------------------- *)

let tisa_returns = define
 `(tisa_returns TSkip k <=> F) /\
  (tisa_returns (TInstr i) k <=> F) /\
  (tisa_returns (TSeq a b) k <=> tisa_returns a k \/ tisa_returns b k) /\
  (tisa_returns (TIf c a b) k <=> tisa_returns a k \/ tisa_returns b k) /\
  (tisa_returns (TCountLoop x n cap body) k <=> tisa_returns body k) /\
  (tisa_returns (TEarlyLoop x n e cap body) k <=> tisa_returns body k) /\
  (tisa_returns (TReturn out r) k <=> k = out) /\
  (tisa_returns (TFund u) k <=> F)`;;

let tisa_stop_ok = new_definition
 `tisa_stop_ok S k u <=>
    tisa_fword u 18 = word k /\ (k = 2 \/ k = 3 \/ k = 4 \/ tisa_returns S k)`;;

(* Writing word 19 after word 18 leaves word 18. *)
let TISA_FWORD18_SET = prove
 (`!st v w. tisa_fword (tisa_setfword 19 w (tisa_setfword 18 v st)) 18 = v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[tisa_fword; tisa_setfword; tisa_store; tisa_read; tisa_frame; tregs; tmem] THEN
  ABBREV_TAC `f = tregs (st:tisa_state) 0` THEN
  SUBGOAL_THEN
   `read (bytes(word_add f (word(8 * 18)),8))
         (write (bytes(word_add f (word(8 * 19)),8)) (val(w:int64))
                (write (bytes(word_add f (word(8 * 18)),8)) (val(v:int64)) (tmem st))) =
    read (bytes(word_add f (word(8 * 18)),8))
         (write (bytes(word_add f (word(8 * 18)),8)) (val v) (tmem st))`
  SUBST1_TAC THENL
   [REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[WRITE_BYTES] THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add (word_add f (word(8 * 18))) (word i))
                     (word_add f (word(8 * 19))):int64) < 8)`
     (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[WORD_RULE `word_sub (word_add (word_add x (word a)) (word i)) (word_add x (word b)):int64 =
                           word_sub (word(a + i)) (word b)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `(144 + i) MOD 18446744073709551616 = 144 + i` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    SIMP_TAC[READ_WRITE_BYTES; DIMINDEX_64; ARITH_RULE `8 <= 2 EXP 64`;
             ARITH_RULE `8 * 8 = 64`; MOD_LT; VAL_BOUND_64; WORD_VAL]]);;

(* A failure stops with its code in word 18. *)
let TISA_FAIL_STOP = prove
 (`!S k st k' u. tisa_fail k st = TStop k' u /\ (k = 2 \/ k = 3 \/ k = 4)
                 ==> tisa_stop_ok S k' u`,
  REWRITE_TAC[tisa_fail; injectivity "tisa_result"] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM))
                             ASSUME_TAC) THEN
  REWRITE_TAC[tisa_stop_ok; TISA_FWORD18_SET] THEN ASM_MESON_TAC[]);;

let TISA_EXEC_STOP = prove
 (`!S t k u. tisa_exec S t = TStop k u ==> tisa_stop_ok S k u`,
  let FAIL2 = prove(`!S st k u. tisa_fail 2 st = TStop k u ==> tisa_stop_ok S k u`,
                    MESON_TAC[TISA_FAIL_STOP])
  and FAIL3 = prove(`!S st k u. tisa_fail 3 st = TStop k u ==> tisa_stop_ok S k u`,
                    MESON_TAC[TISA_FAIL_STOP])
  and FAIL4 = prove(`!S st k u. tisa_fail 4 st = TStop k u ==> tisa_stop_ok S k u`,
                    MESON_TAC[TISA_FAIL_STOP]) in
  let WEAK = prove
   (`!S S' k u. tisa_stop_ok S k u /\ (!k. tisa_returns S k ==> tisa_returns S' k)
                ==> tisa_stop_ok S' k u`,
    REWRITE_TAC[tisa_stop_ok] THEN MESON_TAC[]) in
  let INSTR = prove
   (`!i t k u. tisa_instr i t = TStop k u ==> tisa_stop_ok (TInstr i) k u`,
    MATCH_MP_TAC tisa_instr_INDUCT THEN REWRITE_TAC[tisa_instr] THEN REPEAT CONJ_TAC THEN
    REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "tisa_result"; FAIL3]) in
  let THEN_STOP = prove
   (`!r f k u. tisa_then r f = TStop k u
               ==> r = TStop k u \/ ?w. r = TCont w /\ f w = TStop k u`,
    GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:tisa_result` TISA_RESULT_CASES) THEN
    REWRITE_TAC[tisa_then; injectivity "tisa_result"; distinctness "tisa_result"] THEN
    MESON_TAC[]) in
  let COUNT = prove
   (`!m S x j t k u.
       (!t k u. tisa_exec S t = TStop k u ==> tisa_stop_ok S k u) /\
       tisa_count_iter m (\st'. tisa_exec S st') x j t = TStop k u
       ==> tisa_stop_ok S k u`,
    INDUCT_TAC THEN REWRITE_TAC[tisa_count_iter; distinctness "tisa_result"] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP THEN_STOP) THEN BETA_TAC THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> ASM_MESON_TAC[th])
       (X_CHOOSE_THEN `w:tisa_state` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
       can (find_term ((=) `tisa_count_iter`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`x:num`; `j + 1`; `w:tisa_state`] THEN ASM_REWRITE_TAC[]) in
  let EARLY = prove
   (`!m S x e j t k u.
       (!t k u. tisa_exec S t = TStop k u ==> tisa_stop_ok S k u) /\
       tisa_early_iter m (\st'. tisa_exec S st') x e j t = TStop k u
       ==> tisa_stop_ok S k u`,
    INDUCT_TAC THEN REWRITE_TAC[tisa_early_iter; distinctness "tisa_result"] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[tisa_early_check] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[distinctness "tisa_result"; FAIL3] THEN
    DISCH_THEN(MP_TAC o MATCH_MP THEN_STOP) THEN BETA_TAC THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> ASM_MESON_TAC[th])
       (X_CHOOSE_THEN `w:tisa_state` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[distinctness "tisa_result"; FAIL3] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
       can (find_term ((=) `tisa_early_iter`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`x:num`; `e:num`; `j + 1`; `w:tisa_state`] THEN ASM_REWRITE_TAC[]) in
  MATCH_MP_TAC tisa_stmt_INDUCT THEN REWRITE_TAC[tisa_exec; distinctness "tisa_result"] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[INSTR];
    (* TSeq *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP THEN_STOP) THEN BETA_TAC THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
         (X_CHOOSE_THEN `w:tisa_state` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    MATCH_MP_TAC WEAK THENL
     [EXISTS_TAC `a0:tisa_stmt` THEN REWRITE_TAC[tisa_returns] THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; MESON_TAC[]] THEN
      EXISTS_TAC `t:tisa_state` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `a1:tisa_stmt` THEN REWRITE_TAC[tisa_returns] THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; MESON_TAC[]] THEN
      EXISTS_TAC `w:tisa_state` THEN ASM_REWRITE_TAC[]];
    (* TIf *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[FAIL3] THEN DISCH_TAC THEN
    MATCH_MP_TAC WEAK THENL
     [EXISTS_TAC `a2:tisa_stmt` THEN REWRITE_TAC[tisa_returns] THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; MESON_TAC[]] THEN
      EXISTS_TAC `t:tisa_state` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `a1:tisa_stmt` THEN REWRITE_TAC[tisa_returns] THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; MESON_TAC[]] THEN
      EXISTS_TAC `t:tisa_state` THEN ASM_REWRITE_TAC[]];
    (* TCountLoop *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[FAIL2] THEN DISCH_TAC THEN
    MATCH_MP_TAC WEAK THEN EXISTS_TAC `a3:tisa_stmt` THEN REWRITE_TAC[tisa_returns] THEN
    MATCH_MP_TAC COUNT THEN ASM_MESON_TAC[];
    (* TEarlyLoop *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[FAIL2] THEN DISCH_TAC THEN
    MATCH_MP_TAC WEAK THEN EXISTS_TAC `a4:tisa_stmt` THEN REWRITE_TAC[tisa_returns] THEN
    MATCH_MP_TAC EARLY THEN ASM_MESON_TAC[];
    (* TReturn *)
    REWRITE_TAC[tisa_finish; injectivity "tisa_result"] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[tisa_stop_ok; tisa_returns; TISA_FWORD18_SET];
    (* TFund *)
    REWRITE_TAC[tisa_fund] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[distinctness "tisa_result"; FAIL4]]);;

let TISA_RUN_STATUS = prove
 (`!prog t k u. tisa_run prog t = TStop k u
                ==> tisa_fword u 18 = word k /\
                    (k = 2 \/ k = 3 \/ k = 4 \/ tisa_returns (tisa_root prog) k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_run] THEN
  REWRITE_TAC[GSYM tisa_stop_ok] THEN COND_CASES_TAC THENL
   [MP_TAC(ISPEC `tisa_exec (tisa_root prog) t` TISA_RESULT_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `w:tisa_state` SUBST1_TAC)
       (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `w:tisa_state` (fun th ->
          SUBST1_TAC th THEN ASSUME_TAC th)))) THEN
    REWRITE_TAC[tisa_then] THENL
     [REWRITE_TAC[tisa_fail; injectivity "tisa_result"] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
      REWRITE_TAC[tisa_stop_ok; TISA_FWORD18_SET];
      REWRITE_TAC[injectivity "tisa_result"] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
      MATCH_MP_TAC TISA_EXEC_STOP THEN EXISTS_TAC `t:tisa_state` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[tisa_fail; injectivity "tisa_result"] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[tisa_stop_ok; TISA_FWORD18_SET]]);;
