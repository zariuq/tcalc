(* ========================================================================= *)
(* The reader's leaves as driver leaves: fnv, leb128 and intern_name, their  *)
(* premises of DRV_CORRECT discharged from their image theorems (the        *)
(* LEAF_SPEC theorems) and by computation (the LEAF_WF theorems). None of    *)
(* the three has an initial register that is not U64 (fnv and intern_name   *)
(* take v1, the initial state and the hash), so tisa_leaf_wf holds of each  *)
(* as it is.                                                                 *)
(*                                                                           *)
(* Then the plan fnv, intern_name (DRV_NAME_TWO): the name's FNV-1a 64 is   *)
(* computed from the offset basis and handed to intern_name, which interns  *)
(* the name canonically; the plan is REFUSED exactly when the name lies     *)
(* outside the input, and then at its first step.                            *)
(*                                                                           *)
(* Loaded after the three images (fnv.hol, leb128.hol, intern_name.hol),     *)
(* their joins (fnv_join.ml, leb128_join.ml, intern_name_join.ml),           *)
(* driver_leaf.ml and driver.ml.                                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* A leaf's premises from its image theorem.                                 *)
(* ------------------------------------------------------------------------- *)

let tisa_mc_length name =
  COMPUTE_LENGTH_RULE
    (find (fun th -> try fst(dest_const(lhs(concl th))) = name with Failure _ -> false)
          (definitions()));;

(* tisa_rw and tisa_readable of a declaration list, at a numeral. *)
let TISA_DECL_KIND_CONV decls_th =
  REWRITE_CONV[decls_th; tisa_rw; tisa_readable; LENGTH] THENC NUM_REDUCE_CONV THENC
  ONCE_DEPTH_CONV EL_CONV THENC REWRITE_CONV[FST] THENC NUM_REDUCE_CONV;;

let TISA_FRAME_WORDS = ARITH_RULE
  `2 * 0 = 0 /\ 2 * 0 + 1 = 1 /\ 2 * 1 = 2 /\ 2 * 1 + 1 = 3 /\ 2 * 2 = 4 /\ 2 * 2 + 1 = 5 /\
   2 * 3 = 6 /\ 2 * 3 + 1 = 7 /\ 2 * 4 = 8 /\ 2 * 4 + 1 = 9`;;

(* !pc. tisa_leaf_spec prog mc pc, from the image theorem entry_th (over    *)
(* the program's name) of a program with nregions declared regions.         *)
let TISA_LEAF_SPEC_TAC nregions decls_th len_th entry_th =
  GEN_TAC THEN REWRITE_TAC[tisa_leaf_spec; tisa_leaf_place; len_th] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "r"
    then MAP_EVERY (fun k -> ASSUME_TAC(SPEC (mk_small_numeral k) th)) (0--(nregions-1))
    else failwith "")) THEN
  let kinds t = try let n = fst(dest_const t) in n = "tisa_rw" || n = "tisa_readable"
                with Failure _ -> false in
  RULE_ASSUM_TAC(fun th -> if can (find_term kinds) (concl th)
                           then CONV_RULE(TISA_DECL_KIND_CONV decls_th) th else th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tisa_base; tisa_len; TISA_FRAME_WORDS]) THEN
  MATCH_MP_TAC entry_th THEN ASM_REWRITE_TAC[];;

(* tisa_leaf_wf prog, by computation over its text. *)
let TISA_LEAF_WF_TAC decls_th term_th =
  REWRITE_TAC[tisa_leaf_wf; decls_th; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[term_th; tisa_root; tisa_inits; ALL; tisa_stmt_ok; tisa_instr_ok] THEN
  CONV_TAC(TOP_DEPTH_CONV(CHANGED_CONV(TISA_DECL_KIND_CONV decls_th) ORELSEC NUM_RED_CONV)) THEN
  REWRITE_TAC[];;

let FNV_DECLS = prove(`tisa_decls fnv = [(1,0,1)]`, REWRITE_TAC[fnv; tisa_decls]);;
let LEB128_DECLS = prove(`tisa_decls leb128 = [(1,0,1); (2,16,8)]`, REWRITE_TAC[leb128; tisa_decls]);;
let NAME_DECLS = prove
 (`tisa_decls intern_name = [(1,0,1); (2,16,8); (2,1,1); (2,8,8); (2,16,8)]`,
  REWRITE_TAC[intern_name; tisa_decls]);;

let FNV_LEAF_WF = prove(`tisa_leaf_wf fnv`, TISA_LEAF_WF_TAC FNV_DECLS FNV_TERM);;
let LEB128_LEAF_WF = prove(`tisa_leaf_wf leb128`, TISA_LEAF_WF_TAC LEB128_DECLS LEB128_TERM);;
let NAME_LEAF_WF = prove(`tisa_leaf_wf intern_name`, TISA_LEAF_WF_TAC NAME_DECLS INTERN_NAME_TERM);;

let FNV_ENTRY_X86 = REWRITE_RULE[GSYM FNV_TERM] (assoc "fnv" !tisa_entry_thms);;
let LEB128_ENTRY_X86 = REWRITE_RULE[GSYM LEB128_TERM] (assoc "leb128" !tisa_entry_thms);;
let NAME_ENTRY_X86 = REWRITE_RULE[GSYM INTERN_NAME_TERM] (assoc "intern_name" !tisa_entry_thms);;

let FNV_LEAF_SPEC = prove
 (`!pc. tisa_leaf_spec fnv fnv_mc pc`,
  TISA_LEAF_SPEC_TAC 1 FNV_DECLS (tisa_mc_length "fnv_mc") FNV_ENTRY_X86);;

let LEB128_LEAF_SPEC = prove
 (`!pc. tisa_leaf_spec leb128 leb128_mc pc`,
  TISA_LEAF_SPEC_TAC 2 LEB128_DECLS (tisa_mc_length "leb128_mc") LEB128_ENTRY_X86);;

let NAME_LEAF_SPEC = prove
 (`!pc. tisa_leaf_spec intern_name intern_name_mc pc`,
  TISA_LEAF_SPEC_TAC 5 NAME_DECLS (tisa_mc_length "intern_name_mc") NAME_ENTRY_X86);;

(* ------------------------------------------------------------------------- *)
(* Outcomes: a run's status word is its code, and the codes are small.       *)
(* ------------------------------------------------------------------------- *)

let WORD_SMALL_EQ = prove
 (`!k j. k < 5 /\ j < 5 ==> ((word k:int64) = word j <=> k = j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `k MOD 2 EXP 64 = k /\ j MOD 2 EXP 64 = j` (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let FNV_STATUS = prove
 (`!t k u. tisa_run fnv t = TStop k u ==> tisa_fword u 18 = word k /\ k < 5`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP TISA_RUN_STATUS) THEN
  REWRITE_TAC[FNV_TERM; tisa_root; tisa_returns] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let NAME_STATUS = prove
 (`!t k u. tisa_run intern_name t = TStop k u ==> tisa_fword u 18 = word k /\ k < 5`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP TISA_RUN_STATUS) THEN
  REWRITE_TAC[INTERN_NAME_TERM; tisa_root; tisa_returns] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(* The bytes of a region range in two states with one base, agreeing there. *)
let REGION_RANGE_AGREE = prove
 (`!s t r off n.
     tisa_base t r = tisa_base s r /\
     (!k. k < n ==> tmem t (word_add (tisa_base s r) (word(off + k))) =
                    tmem s (word_add (tisa_base s r) (word(off + k))))
     ==> region_range t r off n = region_range s r off n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[region_range; NAME_LIST_OF_SEQ_EQ] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[region_byte; tisa_read] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* DRV_NAME_TWO: the plan fnv, intern_name over one input. Step 1 hashes the *)
(* name (arg0 the offset, arg1 the length, v1 the FNV offset basis) and      *)
(* stores the hash; step 2 takes the same name and the hash as v1. When both *)
(* FIRED, the hash is the name's FNV-1a 64 and the name is interned          *)
(* canonically: the returned row holds it, it is found when present, and    *)
(* appended only when absent. The plan is REFUSED exactly when the name lies *)
(* outside the input, and then at its first step. The interner lies in     *)
(* step 2's regions 1..4, apart from the driver's stack and the control    *)
(* words, and is well-formed in m.                                          *)
(* ------------------------------------------------------------------------- *)

let drv_name_two_goal =
 `!progs bw ctl nctl budget cfr st1 st2 m used res.
     drv_sem progs bw ctl budget cfr [st1; st2] 0 m used res /\
     progs (val(EL 0 st1)) = fnv /\ progs (val(EL 0 st2)) = intern_name /\
     EL 1 st2 = EL 1 st1 /\ EL 10 st2 = EL 10 st1 /\ EL 11 st2 = EL 11 st1 /\
     EL 12 st2 = EL 17 st1 /\
     ~(val(EL 17 st1) = val(EL 10 st1)) /\ ~(val(EL 17 st1) = val(EL 11 st1)) /\
     drv_cw ctl m (EL 12 st1) = fnv_offset /\
     48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\
     val(EL 10 st1) < nctl /\ val(EL 11 st1) < nctl /\ val(EL 17 st1) < nctl /\
     drv_apart ctl (8 * nctl) (word_sub cfr (word 48)) 304 /\
     (!r. r < 5
          ==> val(drv_base bw st2 r) + val(drv_len bw st2 r) <= 2 EXP 64 /\
              drv_apart (drv_base bw st2 r) (val(drv_len bw st2 r)) (word_sub cfr (word 48)) 304 /\
              drv_apart (drv_base bw st2 r) (val(drv_len bw st2 r)) ctl (8 * nctl)) /\
     (!t. (!r. r < 5 ==> tisa_base t r = drv_base bw st2 r /\ tisa_len t r = drv_len bw st2 r) /\
          (!r a. 1 <= r /\ r < 5 /\ drv_in a (drv_base bw st2 r) (val(drv_len bw st2 r))
                 ==> tmem t a = m a)
          ==> name_ok t)
     ==> (FST res = word 1
          ==> ?t1 u1 t2 u2.
                drv_child bw ctl budget cfr st1 m used t1 /\ tisa_run fnv t1 = TStop 1 u1 /\
                drv_child bw ctl budget cfr st2 (drv_after ctl st1 u1) (tisa_fword u1 21) t2 /\
                tisa_run intern_name t2 = TStop 1 u2 /\
                res = (word 1, 2, drv_after ctl st2 u2, tisa_fword u2 21) /\
                name_key t2 = region_range t1 0 (val(tisa_fword t1 22)) (val(tisa_fword t1 23)) /\
                tisa_fword u1 19 = name_hash (name_key t2) /\
                name_ok u2 /\ name_post t2 u2 /\
                (!i. i < val(name_count t2) /\ name_row_bytes t2 i = name_key t2
                     ==> val(tisa_fword u2 19) = i) /\
                (val(tisa_fword u2 19) = val(name_count t2)
                 ==> !i. i < val(name_count t2) ==> ~(name_row_bytes t2 i = name_key t2))) /\
         (~(val budget < val used)
          ==> (FST res = word 0 <=>
               val(drv_len bw st1 0) < val(drv_cw ctl m (EL 10 st1)) + val(drv_cw ctl m (EL 11 st1)))) /\
         (FST res = word 0 ==> FST(SND res) = 0)`;;

let FNV_NO_RW = prove
 (`!r. ~tisa_rw (tisa_decls fnv) r`,
  GEN_TAC THEN REWRITE_TAC[FNV_DECLS; tisa_rw; LENGTH] THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[EL; HD] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let DRV_NAME_TWO = prove(drv_name_two_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `drv_sem`)) (concl th))) THEN
  REWRITE_TAC[drv_sem] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `val(budget:int64) < val(used:int64)` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[FST] THEN CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  (* Step 1, fnv. *)
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS o
    check (fun th -> concl th = `drv_child bw ctl budget cfr st1 m used t1`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_child] o
    check (fun th -> concl th = `drv_child bw ctl budget cfr st1 m used t1`)) THEN
  SUBGOAL_THEN `tisa_fword t1 22 = drv_cw ctl m (EL 10 st1) /\ tisa_fword t1 23 = drv_cw ctl m (EL 11 st1) /\
                tisa_fword t1 20 = budget /\ tisa_fword t1 21 = used /\ tregs t1 1 = fnv_offset /\
                tisa_len t1 0 = drv_len bw st1 0 /\ tisa_base t1 0 = drv_base bw st1 0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[ARITH; drv_fw; drv_regs] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t1:tisa_state`; `k1:num`; `u1:tisa_state`] FNV_RUN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`t1:tisa_state`; `k1:num`; `u1:tisa_state`] FNV_STATUS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `tisa_fword u1 18 = word 1` THENL
   [ALL_TAC;
    (* fnv did not fire: the plan ends at step 0, REFUSED exactly for a name outside the input *)
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(k1 = 1)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
        can (find_term ((=) `tisa_fword u1 18`)) (concl th))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[WORD_SMALL_EQ; ARITH] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fnv_post] o check (fun th -> concl th = `fnv_post t1 k1 u1`)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC] THEN
  (* fnv fired: the name lies inside the input, the payload is its hash *)
  SUBGOAL_THEN `k1 = 1` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `tisa_fword u1 18 = word 1` THEN ASM_SIMP_TAC[WORD_SMALL_EQ; ARITH]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fnv_post] o check (fun th -> concl th = `fnv_post t1 1 u1`)) THEN
  REWRITE_TAC[ARITH] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`fnv`; `t1:tisa_state`; `1`; `u1:tisa_state`] TISA_RUN_FUEL) THEN
  ASM_REWRITE_TAC[FNV_LEAF_WF] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(val(budget:int64) < val(tisa_fword u1 21))` (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `val(tisa_fword u1 21) <= val(budget:int64)`)) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  (* Step 2, intern_name. *)
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS o
    check (fun th -> concl th = `drv_child bw ctl budget cfr st2 (drv_after ctl st1 u1) (tisa_fword u1 21) t2`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_child] o
    check (fun th -> concl th = `drv_child bw ctl budget cfr st2 (drv_after ctl st1 u1) (tisa_fword u1 21) t2`)) THEN
  (* the memory after step 1: m, but for the payload word and the driver's stack *)
  SUBGOAL_THEN `!a. ~drv_stack cfr a /\ ~drv_in a (word_add ctl (word(8 * val(EL 17 (st1:int64 list))))) 8
                    ==> drv_after ctl st1 u1 a = (m:int64->byte) a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`fnv`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `used:int64`;
                          `t1:tisa_state`; `1`] THEN
    ASM_REWRITE_TAC[FNV_LEAF_WF; FNV_NO_RW];
    ALL_TAC] THEN
  (* the control words step 2 reads *)
  SUBGOAL_THEN `!e. val(e:int64) < nctl /\ ~(val e = val(EL 17 (st1:int64 list)))
                    ==> drv_cw ctl (drv_after ctl st1 u1) e = drv_cw ctl m e` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[drv_cw] THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_after ctl st1 u1`)) (concl th) && can (find_term ((=) `drv_stack`)) (concl th) &&
      can (find_term ((=) `m:int64->byte`)) (concl th))) THEN
    SUBGOAL_THEN `val(word_add (word_add ctl (word(8 * val(e:int64)))) (word i):int64) = val ctl + 8 * val e + i /\
                  val(word_add ctl (word(8 * val(EL 17 (st1:int64 list)))):int64) = val ctl + 8 * val(EL 17 st1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN MATCH_MP_TAC TISA_VAL_OFFSET;
        MATCH_MP_TAC TISA_VAL_OFFSET] THEN
      UNDISCH_TAC `val(ctl:int64) + 8 * nctl <= 2 EXP 64` THEN
      UNDISCH_TAC `val(e:int64) < nctl` THEN UNDISCH_TAC `val(EL 17 (st1:int64 list)) < nctl` THEN
      UNDISCH_TAC `i < 8` THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [`ctl:int64`; `8 * nctl`] THEN
      ONCE_REWRITE_TAC[DRV_APART_SYM] THEN ASM_REWRITE_TAC[drv_in] THEN
      UNDISCH_TAC `val(e:int64) < nctl` THEN UNDISCH_TAC `i < 8` THEN ARITH_TAC;
      ASM_REWRITE_TAC[drv_in] THEN
      UNDISCH_TAC `~(val(e:int64) = val(EL 17 (st1:int64 list)))` THEN UNDISCH_TAC `i < 8` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `drv_cw ctl (drv_after ctl st1 u1) (EL 17 st1) = tisa_fword u1 19` ASSUME_TAC THENL
   [REWRITE_TAC[drv_cw; drv_after; DRV_WORD_WRITE_SAME]; ALL_TAC] THEN
  SUBGOAL_THEN `tisa_fword t2 22 = tisa_fword t1 22 /\ tisa_fword t2 23 = tisa_fword t1 23 /\
                tregs t2 1 = tisa_fword u1 19 /\
                tisa_len t2 0 = tisa_len t1 0 /\ tisa_base t2 0 = tisa_base t1 0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[ARITH; drv_fw; drv_regs] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_cw ctl (drv_after ctl st1 u1)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* a byte of one of step 2's regions: outside the stack and the payload word *)
  SUBGOAL_THEN `!r a. r < 5 /\ drv_in a (drv_base bw st2 r) (val(drv_len bw st2 r))
                      ==> ~drv_stack cfr a /\ tmem t2 a = (m:int64->byte) a /\ tmem t1 a = m a`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_apart`)) (concl th) && can (find_term ((=) `st2:int64 list`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~drv_stack cfr a` ASSUME_TAC THENL
     [MATCH_MP_TAC DRV_IN_NOT_STACK THEN
      MAP_EVERY EXISTS_TAC [`drv_base bw st2 r`; `val(drv_len bw st2 r)`] THEN
      ONCE_REWRITE_TAC[DRV_APART_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_after ctl st1 u1`)) (concl th) && can (find_term ((=) `drv_stack`)) (concl th) &&
      can (find_term ((=) `m:int64->byte`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[drv_in] THEN
    SUBGOAL_THEN `val(word_add ctl (word(8 * val(EL 17 (st1:int64 list)))):int64) = val ctl + 8 * val(EL 17 st1)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC TISA_VAL_OFFSET THEN UNDISCH_TAC `val(ctl:int64) + 8 * nctl <= 2 EXP 64` THEN
      UNDISCH_TAC `val(EL 17 (st1:int64 list)) < nctl` THEN ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `drv_apart (drv_base bw st2 r) (val(drv_len bw st2 r)) ctl (8 * nctl)` THEN
    UNDISCH_TAC `drv_in a (drv_base bw st2 r) (val(drv_len bw st2 r))` THEN
    REWRITE_TAC[drv_apart; drv_in] THEN UNDISCH_TAC `val(EL 17 (st1:int64 list)) < nctl` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* step 2's name is the range step 1 hashed *)
  SUBGOAL_THEN `name_key t2 = region_range t1 0 (val(tisa_fword t1 22)) (val(tisa_fword t1 23))`
  ASSUME_TAC THENL
   [REWRITE_TAC[name_key] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REGION_RANGE_AGREE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `word_add (drv_base bw st1 0) (word (val (drv_cw ctl m (EL 10 st1)) + k)):int64`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `tmem t2`)) (concl th) &&
                       length(fst(strip_forall(concl th))) = 2)) THEN
    REWRITE_TAC[drv_base; drv_len; ARITH] THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    FIRST_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_apart`)) (concl th) && can (find_term ((=) `st2:int64 list`)) (concl th))) THEN
    REWRITE_TAC[drv_base; drv_len; ARITH] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `val(tisa_fword t1 22) + val(tisa_fword t1 23) <= val(tisa_len t1 0)`)) THEN
    REWRITE_TAC[ASSUME `tisa_fword t1 22 = drv_cw ctl m (EL 10 st1)`; ASSUME `tisa_fword t1 23 = drv_cw ctl m (EL 11 st1)`;
                ASSUME `tisa_len t1 0 = drv_len bw st1 0`; drv_len; ARITH] THEN DISCH_TAC THEN
    REWRITE_TAC[drv_in] THEN
    MP_TAC(SPECL [`bw (val (EL 1 (st1:int64 list))):int64`; `val (drv_cw ctl m (EL 10 st1)) + k`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `tisa_fword u1 19 = name_hash (name_key t2) /\ name_hash_ok t2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[name_hash_ok; name_hash] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `name_ok t2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "name_ok")) (concl th))) THEN
    CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `tisa_base t2 r`)) (concl th))) THEN
      ANTS_TAC THENL [UNDISCH_TAC `r < 5` THEN ARITH_TAC; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`r:num`; `a:int64`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `tmem t2`)) (concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t2:tisa_state`; `k2:num`; `u2:tisa_state`] NAME_RUN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`t2:tisa_state`; `k2:num`; `u2:tisa_state`] NAME_STATUS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(k2 = 0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [name_result] o
      check (fun th -> concl th = `name_result t2 k2 u2`)) THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `val(tisa_fword t1 22) + val(tisa_fword t1 23) <= val(tisa_len t1 0)`)) THEN
    REWRITE_TAC[ASSUME `tisa_fword t2 22 = tisa_fword t1 22`; ASSUME `tisa_fword t2 23 = tisa_fword t1 23`;
                ASSUME `tisa_len t2 0 = tisa_len t1 0`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val(drv_len bw st1 0) < val(drv_cw ctl m (EL 10 st1)) + val(drv_cw ctl m (EL 11 st1)))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `val(tisa_fword t1 22) + val(tisa_fword t1 23) <= val(tisa_len t1 0)`)) THEN
    REWRITE_TAC[ASSUME `tisa_fword t1 22 = drv_cw ctl m (EL 10 st1)`; ASSUME `tisa_fword t1 23 = drv_cw ctl m (EL 11 st1)`;
                ASSUME `tisa_len t1 0 = drv_len bw st1 0`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `k2 = 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[]] THEN
    MAP_EVERY EXISTS_TAC [`t1:tisa_state`; `u1:tisa_state`; `t2:tisa_state`; `u2:tisa_state`] THEN
    ASM_REWRITE_TAC[name_hash] THEN
    MP_TAC(SPECL [`t2:tisa_state`; `1`; `u2:tisa_state`] NAME_RUN_COMPLETE) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `region_range t1 0 (val (drv_cw ctl m (EL 10 st1))) (val (drv_cw ctl m (EL 11 st1))) = name_key t2`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC NAME_PRESENT_FOUND THEN EXISTS_TAC `t2:tisa_state` THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC NAME_APPEND_ABSENT THEN EXISTS_TAC `u2:tisa_state` THEN
      ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[WORD_SMALL_EQ; ARITH] THEN
    DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[FST; SND] THEN ASM_SIMP_TAC[WORD_SMALL_EQ; ARITH]]);;

(* ------------------------------------------------------------------------- *)
(* DRV_NAME_X86: the native run of the plan fnv, intern_name, with fnv's     *)
(* image linked at fpc and intern_name's at npc (leaves 0 and 1).            *)
(* ------------------------------------------------------------------------- *)

let DRV_NAME_X86 = prove
 (`!pc fpc npc stackpointer d plan ctl nctl bind nbw leaves bw st1 st2 budget used0 m0
    ret rbxv rbpv r12v r13v r14v r15v.
     drv_layout pc (word_sub stackpointer (word 248)) d plan 2 ctl nctl bind nbw leaves 2
                (\j. if j = 0 then fpc else npc) (\j. if j = 0 then fnv_mc else intern_name_mc) /\
     ALL (drv_step_ok (\j. if j = 0 then fnv else intern_name) pc (word_sub stackpointer (word 248))
                      d plan 2 nctl bind nbw leaves 2 (\j. if j = 0 then fpc else npc)
                      (\j. if j = 0 then fnv_mc else intern_name_mc) bw) [st1; st2] /\
     drv_holds m0 d plan 2 ctl bind leaves budget used0 [st1; st2] bw nbw
               (\j. if j = 0 then fpc else npc) 2 /\
     drv_code m0 pc drv_mc /\ drv_code m0 fpc fnv_mc /\ drv_code m0 npc intern_name_mc /\
     val(EL 0 st1) = 0 /\ val(EL 0 st2) = 1 /\
     EL 1 st2 = EL 1 st1 /\ EL 10 st2 = EL 10 st1 /\ EL 11 st2 = EL 11 st1 /\
     EL 12 st2 = EL 17 st1 /\
     ~(val(EL 17 st1) = val(EL 10 st1)) /\ ~(val(EL 17 st1) = val(EL 11 st1)) /\
     drv_cw ctl m0 (EL 12 st1) = fnv_offset /\
     (!r. r < 5
          ==> val(drv_base bw st2 r) + val(drv_len bw st2 r) <= 2 EXP 64 /\
              drv_apart (drv_base bw st2 r) (val(drv_len bw st2 r)) ctl (8 * nctl)) /\
     (!t. (!r. r < 5 ==> tisa_base t r = drv_base bw st2 r /\ tisa_len t r = drv_len bw st2 r) /\
          (!r a. 1 <= r /\ r < 5 /\ drv_in a (drv_base bw st2 r) (val(drv_len bw st2 r))
                 ==> tmem t a = m0 a)
          ==> name_ok t)
     ==> ensures x86
          (\s. read RIP s = word pc /\ read RSP s = stackpointer /\ read RDI s = d /\
               read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
               read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
               read memory s = m0 /\ read (memory :> bytes64 stackpointer) s = ret)
          (\s. read RIP s = ret /\ read RSP s = word_add stackpointer (word 8) /\
               read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
               read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
               ?res. drv_sem (\j. if j = 0 then fnv else intern_name) bw ctl budget
                             (word_sub stackpointer (word 248)) [st1; st2] 0 m0 used0 res /\
                     read RAX s = FST res /\
                     (!a. ~drv_stack (word_sub stackpointer (word 248)) a
                          ==> read memory s a = drv_final d plan res a) /\
                     (read RAX s = word 1
                      ==> ?t1 u1 t2 u2.
                            drv_child bw ctl budget (word_sub stackpointer (word 248)) st1 m0 used0 t1 /\
                            tisa_run fnv t1 = TStop 1 u1 /\
                            drv_child bw ctl budget (word_sub stackpointer (word 248)) st2
                                      (drv_after ctl st1 u1) (tisa_fword u1 21) t2 /\
                            tisa_run intern_name t2 = TStop 1 u2 /\
                            FST(SND(SND res)) = drv_after ctl st2 u2 /\
                            tisa_fword u1 19 = name_hash (name_key t2) /\
                            name_ok u2 /\ name_post t2 u2 /\
                            (!i. i < val(name_count t2) /\ name_row_bytes t2 i = name_key t2
                                 ==> val(tisa_fword u2 19) = i) /\
                            (val(tisa_fword u2 19) = val(name_count t2)
                             ==> !i. i < val(name_count t2)
                                     ==> ~(name_row_bytes t2 i = name_key t2))) /\
                     (val used0 <= val budget
                      ==> (read RAX s = word 0 <=>
                           val(drv_len bw st1 0) <
                           val(drv_cw ctl m0 (EL 10 st1)) + val(drv_cw ctl m0 (EL 11 st1)))) /\
                     (read RAX s = word 0 ==> FST(SND res) = 0))
          (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                      R12; R13; R14; R15; RBP] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`\j:num. if j = 0 then fnv else intern_name`; `\j:num. if j = 0 then (fpc:num) else npc`;
                `\j:num. if j = 0 then fnv_mc else intern_name_mc`; `2`; `pc:num`;
                `stackpointer:int64`; `d:int64`; `plan:int64`; `2`; `ctl:int64`; `nctl:num`;
                `bind:int64`; `nbw:num`; `leaves:int64`; `bw:num->int64`;
                `[st1; st2]:(int64 list)list`; `budget:int64`; `used0:int64`; `m0:int64->byte`;
                `ret:int64`; `rbxv:int64`; `rbpv:int64`; `r12v:int64`; `r13v:int64`; `r14v:int64`;
                `r15v:int64`] DRV_CORRECT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `j < 2 <=> j = 0 \/ j = 1`] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[ARITH] THEN
      REWRITE_TAC[FNV_LEAF_WF; FNV_LEAF_SPEC; NAME_LEAF_WF; NAME_LEAF_SPEC];
      REWRITE_TAC[ARITH_RULE `j < 2 <=> j = 0 \/ j = 1`] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[ARITH]];
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP DRV_ENSURES_WEAKEN)] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ALL] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "ALL")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[drv_step_ok] o BETA_RULE o
    check (fun th -> can (find_term ((=) `st1:int64 list`)) (concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "drv_step_ok")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[drv_step_ok] o BETA_RULE o
    check (fun th -> can (find_term ((=) `st2:int64 list`)) (concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "drv_step_ok")) (concl th))) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\j:num. if j = 0 then fnv else intern_name`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                   `budget:int64`; `word_sub stackpointer (word 248):int64`; `st1:int64 list`;
                   `st2:int64 list`; `m0:int64->byte`; `used0:int64`;
                   `res:int64#num#(int64->byte)#int64`] DRV_NAME_TWO) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `~(1 = 0)`; NOT_LT] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `10` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `nctl:num`)) (concl th) && can (find_term ((=) `st1:int64 list`)) (concl th))) THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `11` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `nctl:num`)) (concl th) && can (find_term ((=) `st1:int64 list`)) (concl th))) THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `17` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `nctl:num`)) (concl th) && can (find_term ((=) `st1:int64 list`)) (concl th))) THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
        ONCE_REWRITE_TAC[DRV_APART_SYM] THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `r:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "tisa_readable")) (concl th) &&
          can (find_term ((=) `st2:int64 list`)) (concl th))) THEN
        ASM_REWRITE_TAC[ARITH_RULE `~(1 = 0)`; NAME_DECLS; tisa_readable; LENGTH] THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o
          REWRITE_RULE[ARITH_RULE `r < 5 <=> r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4`] o
          check (fun th -> concl th = `r < 5`)) THEN
        CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[FST] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[]];
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
          can (find_term ((=) `name_post`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MAP_EVERY EXISTS_TAC [`t1:tisa_state`; `u1:tisa_state`; `t2:tisa_state`; `u2:tisa_state`] THEN
        ASM_REWRITE_TAC[];
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC]);;
