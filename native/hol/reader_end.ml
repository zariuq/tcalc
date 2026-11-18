(* ========================================================================= *)
(* The END record (PLANS.txt section 10). fnv at the plan level             *)
(* (pl_fnv_spec); the reader's steps at_end, fnv and le8_next under         *)
(* plan_rel and rd_rel; and the END plan in four pieces composed by         *)
(* DRV_SEM_APPEND. A FIRED END plan saw the header, and the input from the  *)
(* cursor is the count CNT followed by the FNV-1a 64 of the bytes before    *)
(* the END opcode, little-endian, to the input's end; ENDW is then 1, the   *)
(* other words below 24 are kept, and both relations hold at the input's   *)
(* end (END_REL).                                                            *)
(*                                                                           *)
(* Loaded after reader_rel.ml.                                               *)
(* ========================================================================= *)

needs "native/hol/reader_rel.ml";;

(* fnv: region 0 the input (read-only); arg0 the range's offset, arg1 its    *)
(* length, v1 the initial state. FIRED with FNV-1a of the range when it lies *)
(* inside the input; REFUSED when it does not; UNSUPPORTED when it is longer *)
(* than the loop's cap, 2^32 - 1 bytes (FNV_RUN's three ends).               *)
let pl_fnv_spec = new_definition
 `pl_fnv_spec prog <=>
    pl_leaf_ok prog [(1,0,1)] /\
    !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
      ==> (k = 1 /\ val(tisa_fword t 22) + val(tisa_fword t 23) <= val(tisa_len t 0) /\
           tisa_fword u 19 = fnv1a (tregs t 1)
                               (region_range t 0 (val(tisa_fword t 22)) (val(tisa_fword t 23)))) \/
          (k = 0 /\ val(tisa_len t 0) < val(tisa_fword t 22) + val(tisa_fword t 23)) \/
          (k = 2 /\ val(tisa_fword t 22) + val(tisa_fword t 23) <= val(tisa_len t 0) /\
           4294967295 < val(tisa_fword t 23))`;;

(* The frame words after fnv: its run writes the status and the payload. *)
let FNV_FRAME = prove
 (`!t k u. tisa_entry_ok fnv t /\ tisa_run fnv t = TStop k u
           ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] FNV_STATUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`fnv`; `t:tisa_state`; `k:num`; `u:tisa_state`] TISA_RUN_KEEPS) THEN
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] FNV_RUN) THEN
  ASM_REWRITE_TAC[FNV_LEAF_WF; tisa_keeps; fnv_post] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FNV_ENTRY) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  STRIP_TAC THEN STRIP_TAC THEN
  (FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `tmem u` then
     let s = rand(rhs(concl th)) in
     SUBGOAL_THEN (mk_eq(`tisa_fword u 21`, list_mk_icomb "tisa_fword" [s; `21`])) SUBST1_TAC
     THENL [MATCH_MP_TAC LEB_NEXT_VIEW THEN ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[tisa_finst; TISA_SETFWORD_REGS] THEN ASM_REWRITE_TAC[];
            ALL_TAC]
   else failwith "no tmem") THEN
   TISA_STATE_NORM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]));;

let PL_FNV_SPEC = prove
 (`pl_fnv_spec fnv`,
  REWRITE_TAC[pl_fnv_spec; pl_leaf_ok; FNV_LEAF_WF; FNV_DECLS; FNV_FRAME] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] FNV_RUN) THEN
  ASM_REWRITE_TAC[fnv_post] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The read-only steps: at_end and fnv keep both relations, with the payload *)
(* in the step's word.                                                       *)
(* ------------------------------------------------------------------------- *)

let AT_END_RO = prove(`!r. ~tisa_rw (tisa_decls at_end) r`, RD_RW_CASES_TAC AT_END_DECLS);;
let FNV_RO = prove(`!r. ~tisa_rw (tisa_decls fnv) r`, RD_RW_CASES_TAC FNV_DECLS);;

let RD_STEP_AT_END = prove
 (`!bw ctl nctl budget cfr st m used t k u cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok at_end t /\ tisa_run at_end t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         (if c = LENGTH inp
          then tisa_fword u 18 = word 1 /\
               plan_rel bw ctl nctl cfr (drv_after ctl st u)
                 (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [plan_rel] o
    check (fun th -> is_const_app "plan_rel" (concl th))) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DRV_CHILD_RECEIPT) THEN
  (* the input's length through the relation *)
  SUBGOAL_THEN `val(tisa_len t 0) = LENGTH(inp:num list)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
      STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC PL_AT_END_SPEC THEN REWRITE_TAC[pl_at_end_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `c:num`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_REL_RO_STEP THEN
    MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `at_end`; `k:num`] THEN
    ASM_REWRITE_TAC[AT_END_LEAF_WF; AT_END_RO];
    MATCH_MP_TAC RD_STEP_RO THEN
    MAP_EVERY EXISTS_TAC [`at_end`; `budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[AT_END_LEAF_WF; AT_END_RO]]);;

(* ------------------------------------------------------------------------- *)
(* fnv over the input: region 0 bound to the input; any range inside it      *)
(* reads the relation's bytes.                                               *)
(* ------------------------------------------------------------------------- *)

let RD_CHILD_INP = prove
 (`!bw ctl nctl budget cfr st m used t inp c.
     drv_child bw ctl budget cfr st m used t /\ pl_layout bw ctl nctl cfr /\
     rd_rel bw ctl nctl cfr m inp c /\ val(EL 1 st) = 54
     ==> tisa_base t 0 = bw 54 /\ tisa_len t 0 = bw 55 /\
         (!off n. off + n <= LENGTH inp
                  ==> region_range t 0 off n = list_of_seq (\j. EL (off + j) inp) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `drv_base`)) (concl th) then
     MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC `0` th)) else failwith "") THEN
  ASM_REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[region_range; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `n':num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[region_byte; tisa_read; READ_BYTES_1] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `drv_in (word_add (bw 54) (word(off + n')):int64) (bw 54) (val(bw 55:int64))` ASSUME_TAC THENL
   [REWRITE_TAC[drv_in] THEN MP_TAC(SPECL [`bw 54:int64`; `off + n':num`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `tmem t (word_add (bw 54) (word(off + n')):int64) = (m:int64->byte) (word_add (bw 54) (word(off + n')))`
    SUBST1_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
      check (fun th -> is_const_app "drv_child" (concl th))) THEN
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `word_add (bw 54) (word(off + n')):int64`]
                 RD_INP_ADDR) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `val((m:int64->byte) (word_add (bw 54) (word(off + n')))) < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(m:int64->byte) (word_add (bw 54) (word(off + n')))` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let RD_STEP_FNV = prove
 (`!bw ctl nctl budget cfr st m used t k u cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok fnv t /\ tisa_run fnv t = TStop k u /\
     val(EL 1 st) = 54 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         (tisa_fword u 18 = word 1
          ==> cw(val(EL 10 st)) + cw(val(EL 11 st)) <= LENGTH inp /\
              tisa_fword u 19 = fnv1a (word(cw(val(EL 12 st))))
                                  (list_of_seq (\j. EL (cw(val(EL 10 st)) + j) inp) (cw(val(EL 11 st)))) /\
              plan_rel bw ctl nctl cfr (drv_after ctl st u)
                (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
              rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c) /\
         (cw(val(EL 10 st)) + cw(val(EL 11 st)) <= LENGTH inp /\ cw(val(EL 11 st)) <= 4294967295
          ==> tisa_fword u 18 = word 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RD_CHILD_ARGS_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD_INP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(tisa_len t 0) = LENGTH(inp:num list)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
      STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* v1 as a word *)
  SUBGOAL_THEN `tregs t 1 = word(cw(val(EL 12 (st:int64 list))))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tregs`)) (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC PL_FNV_SPEC THEN REWRITE_TAC[pl_fnv_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* the three ends: k substituted, so no rewrite touches the payload word *)
  FIRST_X_ASSUM(fun th -> if is_disj(concl th) then
    DISJ_CASES_THEN2 STRIP_ASSUME_TAC (DISJ_CASES_THEN STRIP_ASSUME_TAC) th else failwith "") THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `k:num`)) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[] THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[];
      MATCH_MP_TAC PL_REL_RO_STEP THEN
      MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `fnv`; `1`] THEN
      ASM_REWRITE_TAC[FNV_LEAF_WF; FNV_RO] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) && can (find_term ((=) `nctl:num`)) (concl th))) THEN
      ARITH_TAC;
      MATCH_MP_TAC RD_STEP_RO THEN
      MAP_EVERY EXISTS_TAC [`fnv`; `budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`] THEN
      ASM_REWRITE_TAC[FNV_LEAF_WF; FNV_RO] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) && can (find_term ((=) `nctl:num`)) (concl th))) THEN
      ARITH_TAC];
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* le8_next: FIRED with the 8 input bytes at the cursor, little-endian; the  *)
(* cursor advanced by 8 (as leb_next: only the state and the payload word    *)
(* change).                                                                  *)
(* ------------------------------------------------------------------------- *)

let LE8_NEXT_RW = prove
 (`!r. tisa_rw (tisa_decls le8_next) r <=> r = 1`, RD_RW_CASES_TAC LE8_NEXT_DECLS);;
let LE8_NEXT_READABLE = prove
 (`!r. tisa_readable (tisa_decls le8_next) r <=> r = 0 \/ r = 1`, RD_RW_CASES_TAC LE8_NEXT_DECLS);;

let RD_LE8_KEEPS = prove
 (`!bw ctl nctl budget cfr st m used t k u a.
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok le8_next t /\ tisa_run le8_next t = TStop k u /\
     val(EL 2 st) = 58 /\ val ctl + 8 * nctl <= 2 EXP 64 /\ val(EL 17 st) < nctl /\
     ~drv_stack cfr a /\ ~drv_in a (bw 58) (val(bw 59)) /\
     ~drv_in a (word_add ctl (word(8 * val(EL 17 st)))) 8
     ==> drv_after ctl st u a = m a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
  MAP_EVERY EXISTS_TAC [`le8_next`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                        `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[LE8_NEXT_LEAF_WF; LE8_NEXT_RW] THEN
  X_GEN_TAC `r:num` THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let RD_STEP_LE8 = prove
 (`!bw ctl nctl budget cfr st m used t k u cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok le8_next t /\ tisa_run le8_next t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         (if c + 8 <= LENGTH inp
          then tisa_fword u 18 = word 1 /\
               le8 (tisa_fword u 19) = list_of_seq (\j. EL (c + j) inp) 8 /\
               plan_rel bw ctl nctl cfr (drv_after ctl st u)
                 (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp (c + 8)
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [plan_rel] o
    check (fun th -> is_const_app "plan_rel" (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout] o
    check (fun th -> is_const_app "pl_layout" (concl th))) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD_INP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DRV_CHILD_RECEIPT) THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  SUBGOAL_THEN `val(tisa_len t 0) = LENGTH(inp:num list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC PL_LE8_NEXT_SPEC THEN REWRITE_TAC[pl_le8_next_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* the 8 bytes: the input's, by the relation *)
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* What le8_next keeps: everything outside the state and the payload word. *)
  SUBGOAL_THEN `!a. ~drv_stack cfr a /\ ~drv_in a (bw 58) (val(bw 59)) /\
                    ~drv_in a (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8
                    ==> drv_after ctl st u a = (m:int64->byte) a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RD_LE8_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `used:int64`;
                          `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_REL_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`;
                    `val(EL 17 (st:int64 list))`; `a:int64`] PL_SLOT_ADDR) THEN
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`; `a:int64`] RD_SLOT_NOT_RD) THEN
      ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] PL_CTL_ADDR) THEN
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] RD_CTL_NOT_RD) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME]];
    (* rd_rel: the input kept; the cursor advanced by 8. *)
    REWRITE_TAC[rd_rel] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `drv_in (word_add (bw 54) (word i)) (bw 54) (val(bw 55:int64))` ASSUME_TAC THENL
       [REWRITE_TAC[drv_in] THEN MP_TAC(SPECL [`bw 54:int64`; `i:num`] TISA_VAL_OFFSET) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `word_add (bw 54) (word i):int64`]
                   RD_INP_ADDR) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `drv_after ctl st u (word_add (bw 54) (word i)) = (m:int64->byte) (word_add (bw 54) (word i))`
        SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        UNDISCH_TAC `~drv_in (word_add (bw 54) (word i):int64) ctl (8 * nctl)` THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC DRV_CTL_WORD_IN THEN EXISTS_TAC `val(EL 17 (st:int64 list))` THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]];
      SUBGOAL_THEN `tisa_base u 1 = tisa_base t 1` ASSUME_TAC THENL
       [MP_TAC(SPECL [`le8_next`; `t:tisa_state`; `k:num`; `u:tisa_state`; `1`] TISA_RUN_REGIONS) THEN
        ASM_REWRITE_TAC[LE8_NEXT_LEAF_WF; LE8_NEXT_READABLE] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `drv_word (drv_after ctl st u) (word_add (bw 58) (word 0)) =
                    drv_word (tmem u) (word_add (bw 58) (word 0))` ASSUME_TAC THENL
       [MATCH_MP_TAC DRV_WORD_AREA THEN EXISTS_TAC `val(bw 59:int64)` THEN
        REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `a:int64` THEN DISCH_TAC THEN REWRITE_TAC[drv_after] THEN
        MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN
        MP_TAC(SPECL [`ctl:int64`; `8 * val(EL 17 (st:int64 list))`] TISA_VAL_OFFSET) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] RD_ST_ADDR) THEN
        ASM_REWRITE_TAC[drv_in] THEN STRIP_TAC THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[pl_mw; MULT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `drv_word (tmem u) (word_add (bw 58) (word 0)) = pl_w u 1 0` SUBST1_TAC THENL
       [REWRITE_TAC[pl_w; tisa_read; drv_word; MULT_CLAUSES] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The END plan (PLANS.txt section 10): header seen; FNV-1a 64 of the bytes  *)
(* before the END opcode (offset 0, length RST, from FNVB); the count, which *)
(* must be CNT; the checksum, which must be the FNV-1a; the end of the       *)
(* input; then ENDW := 1.                                                    *)
(*   eqw HDR K1 -> T24; fnv INP K0 RST (v1 FNVB) -> T25; leb_next -> T26;    *)
(*   eqw T26 CNT -> T27; le8_next -> T28; eqw T25 T28 -> T29; at_end -> T30; *)
(*   eqw K1 K1 -> ENDW.                                                       *)
(* ------------------------------------------------------------------------- *)

let pl_step_tm leaf binds a0 a1 vs pay =
  let w n = mk_comb(`word:num->int64`, mk_small_numeral n) in
  let pad l n x = l @ replicate x (n - length l) in
  mk_list(map w ([leaf] @ pad binds 9 56 @ [a0; a1] @ pad vs 5 0 @ [pay]), `:int64`);;

let pl_end_a = new_definition(mk_eq(`pl_end_a:(int64 list)list`, mk_list(
  [pl_step_tm 3 [] 20 1 [] 24; pl_step_tm 22 [54] 0 21 [22] 25], `:int64 list`)));;
let pl_end_b = new_definition(mk_eq(`pl_end_b:(int64 list)list`, mk_list(
  [pl_step_tm 26 [54; 58] 0 0 [] 26; pl_step_tm 3 [] 26 17 [] 27], `:int64 list`)));;
let pl_end_c = new_definition(mk_eq(`pl_end_c:(int64 list)list`, mk_list(
  [pl_step_tm 29 [54; 58] 0 0 [] 28; pl_step_tm 3 [] 25 28 [] 29], `:int64 list`)));;
let pl_end_d = new_definition(mk_eq(`pl_end_d:(int64 list)list`, mk_list(
  [pl_step_tm 30 [54; 58] 0 0 [] 30; pl_step_tm 3 [] 1 1 [] 19], `:int64 list`)));;
let pl_plan_end = new_definition
 `pl_plan_end = APPEND pl_end_a (APPEND pl_end_b (APPEND pl_end_c pl_end_d))`;;

(* The pieces' relations (FIRED direction).                                  *)
(*   a: the header seen; T25 the FNV-1a 64 of the RST bytes before END.      *)
(*   b: the count at the cursor is CNT.                                       *)
(*   c: the 8 bytes after it are T25's, little-endian.                        *)
(*   d: the input ends there; ENDW := 1.                                      *)
let end_b_rel_goal =
 `!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     progs 3 = eqw /\ rd_progs_ok progs /\ 27 < nctl /\
     drv_sem progs bw ctl budget cfr pl_end_b i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> leb_fires (rd_from inp c) (cw 17) /\
              plan_rel bw ctl nctl cfr (FST(SND(SND r)))
                (pl_set (pl_set cw 26 (cw 17)) 27 (cw 17),(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
              rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + LENGTH(leb_enc (cw 17))))`;;

(* The END record's relation: a FIRED run had the header, and the input from *)
(* the cursor is the count CNT and the checksum of the bytes before RST, to  *)
(* its end; the relations hold after it with ENDW = 1 (other words below 24  *)
(* kept), the cursor at the input's end.                                     *)
let end_rel_goal =
 `!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     progs 3 = eqw /\ progs 22 = fnv /\ rd_progs_ok progs /\ progs 29 = le8_next /\ progs 30 = at_end /\
     30 < nctl /\ cw 22 = val fnv_offset /\
     drv_sem progs bw ctl budget cfr pl_plan_end i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> cw 20 = 1 /\ cw 21 <= LENGTH inp /\
              rd_from inp c = APPEND (leb_enc (cw 17))
                                     (le8 (fnv1a fnv_offset (list_of_seq (\j. EL j inp) (cw 21)))) /\
              ?cw'. cw' 19 = 1 /\ (!j. j < 24 /\ ~(j = 19) ==> cw' j = cw j) /\
                    plan_rel bw ctl nctl cfr (FST(SND(SND r)))
                      (cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
                    rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (LENGTH inp))`;;

let pl_end_b_st1 = el 0 (dest_list(rhs(concl pl_end_b)))
and pl_end_b_st2 = el 1 (dest_list(rhs(concl pl_end_b)));;

let END_B_REL = prove(end_b_rel_goal,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_progs_ok] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_end_b; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_end_b_st1;
                 `m:int64->byte`; `used:int64`; `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`] @
                RD_NS_VARS @ [`inp:num list`; `c:num`]) RD_STEP_LEB) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THENL
   [ALL_TAC;
    (* REFUSED at leb_next: the plan ends there *)
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_end_b_st2;
                 list_mk_comb(`drv_after`, [`ctl:int64`; pl_end_b_st1; `u1:tisa_state`]);
                 `used:int64`; `t2:tisa_state`; `k2:num`; `u2:tisa_state`; `pl_set cw 26 v`] @
                RD_NS_VARS @ [`inp:num list`; `c + LENGTH(leb_enc v)`]) RD_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
  (* the comparison: word 26 is v, word 17 is CNT *)
  SUBGOAL_THEN `pl_set cw 26 v 26 = v /\ pl_set cw 26 v 17 = (cw:num->num) 17` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_CASES_TAC `v = (cw:num->num) 17` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let pl_end_a_st1 = el 0 (dest_list(rhs(concl pl_end_a)))
and pl_end_a_st2 = el 1 (dest_list(rhs(concl pl_end_a)));;

let end_a_rel_goal =
 `!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     progs 3 = eqw /\ progs 22 = fnv /\ 25 < nctl /\ cw 22 = val fnv_offset /\
     drv_sem progs bw ctl budget cfr pl_end_a i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> cw 20 = 1 /\ cw 21 <= LENGTH inp /\
              plan_rel bw ctl nctl cfr (FST(SND(SND r)))
                (pl_set (pl_set cw 24 1) 25 (val(fnv1a fnv_offset (list_of_seq (\j. EL j inp) (cw 21)))),
                 (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
              rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp c)`;;

let END_A_REL = prove(end_a_rel_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cw:num->num) 1 = 1 /\ cw 0 = 0` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "plan_rel" (concl th))) THEN
    REWRITE_TAC[plan_rel] THEN STRIP_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_end_a; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_end_a_st1;
                 `m:int64->byte`; `used:int64`; `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`] @
                RD_NS_VARS @ [`inp:num list`; `c:num`]) RD_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(cw:num->num) 20 = 1` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_end_a_st2;
                 list_mk_comb(`drv_after`, [`ctl:int64`; pl_end_a_st1; `u1:tisa_state`]);
                 `used:int64`; `t2:tisa_state`; `k2:num`; `u2:tisa_state`; `pl_set cw 24 1`] @
                RD_NS_VARS @ [`inp:num list`; `c:num`]) RD_STEP_FNV) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `pl_set cw 24 1 0 = 0 /\ pl_set cw 24 1 21 = (cw:num->num) 21 /\ pl_set cw 24 1 22 = cw 22`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; WORD_VAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  ASM_CASES_TAC `tisa_fword u2 18 = word 1` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `tisa_fword u2 19`)) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[]]);;

let pl_end_c_st1 = el 0 (dest_list(rhs(concl pl_end_c)))
and pl_end_c_st2 = el 1 (dest_list(rhs(concl pl_end_c)));;
let pl_end_d_st1 = el 0 (dest_list(rhs(concl pl_end_d)))
and pl_end_d_st2 = el 1 (dest_list(rhs(concl pl_end_d)));;

(* c: the 8 bytes at the cursor are T25's, little-endian. *)
let end_c_rel_goal =
 `!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     progs 3 = eqw /\ progs 29 = le8_next /\ 29 < nctl /\
     drv_sem progs bw ctl budget cfr pl_end_c i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> c + 8 <= LENGTH inp /\ le8 (word(cw 25)) = list_of_seq (\j. EL (c + j) inp) 8 /\
              plan_rel bw ctl nctl cfr (FST(SND(SND r)))
                (pl_set (pl_set cw 28 (cw 25)) 29 (cw 25),(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
              rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + 8))`;;

let END_C_REL = prove(end_c_rel_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_end_c; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_end_c_st1;
                 `m:int64->byte`; `used:int64`; `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`] @
                RD_NS_VARS @ [`inp:num list`; `c:num`]) RD_STEP_LE8) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `c + 8 <= LENGTH(inp:num list)` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ALL_TAC;
    (* fewer than 8 bytes left: le8_next REFUSES, and so does the plan *)
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_end_c_st2;
                 list_mk_comb(`drv_after`, [`ctl:int64`; pl_end_c_st1; `u1:tisa_state`]);
                 `used:int64`; `t2:tisa_state`; `k2:num`; `u2:tisa_state`;
                 `pl_set cw 28 (val(tisa_fword u1 19))`] @
                RD_NS_VARS @ [`inp:num list`; `c + 8`]) RD_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `pl_set cw 28 (val(tisa_fword u1 19)) 25 = (cw:num->num) 25 /\
                pl_set cw 28 (val(tisa_fword u1 19)) 28 = val(tisa_fword u1 19)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  (* the checksum is T25 exactly when the 8 bytes read are its *)
  ASM_CASES_TAC `(cw:num->num) 25 = val(tisa_fword u1 19)` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `word((cw:num->num) 25):int64 = tisa_fword u1 19` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(cw:num->num) 25 = val(tisa_fword u1 19)`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
    ASM_REWRITE_TAC[]]);;

(* d: the input ends at the cursor; ENDW := 1. *)
let end_d_rel_goal =
 `!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     progs 3 = eqw /\ progs 30 = at_end /\ 30 < nctl /\
     drv_sem progs bw ctl budget cfr pl_end_d i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> c = LENGTH inp /\
              ?x. plan_rel bw ctl nctl cfr (FST(SND(SND r)))
                    (pl_set (pl_set cw 30 x) 19 1,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
                  rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp c)`;;

(* The bytes from c are a prefix l and then the bytes from c + LENGTH l. *)
let RD_FROM_APPEND = prove
 (`!inp c l rest. rd_from inp c = APPEND l rest ==> rest = rd_from inp (c + LENGTH l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_from] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:num list->num`) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_APPEND] THEN DISCH_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH(inp:num list) - (c + LENGTH(l:num list))` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `EL (LENGTH(l:num list) + n):num list->num` o
    check (fun th -> is_eq(concl th) && can (find_term ((=) `list_of_seq:(num->num)->num->num list`)) (lhs(concl th)))) THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `n < a - (c + l) ==> l + n < a - c`; EL_APPEND] THEN
  REWRITE_TAC[ARITH_RULE `~(l + n < l:num)`; ADD_SUB2; ADD_ASSOC] THEN SIMP_TAC[]);;

let END_D_REL = prove(end_d_rel_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cw:num->num) 1 = 1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "plan_rel" (concl th))) THEN
    REWRITE_TAC[plan_rel] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_end_d; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_end_d_st1;
                 `m:int64->byte`; `used:int64`; `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`] @
                RD_NS_VARS @ [`inp:num list`; `c:num`]) RD_STEP_AT_END) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `c = LENGTH(inp:num list)` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ALL_TAC;
    (* not at the end: at_end REFUSES, and so does the plan *)
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_end_d_st2;
                 list_mk_comb(`drv_after`, [`ctl:int64`; pl_end_d_st1; `u1:tisa_state`]);
                 `used:int64`; `t2:tisa_state`; `k2:num`; `u2:tisa_state`;
                 `pl_set cw 30 (val(tisa_fword u1 19))`] @
                RD_NS_VARS @ [`inp:num list`; `LENGTH(inp:num list)`]) RD_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `pl_set cw 30 (val(tisa_fword u1 19)) 1 = 1` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `val(tisa_fword u1 19)` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The END plan, composed: DRV_SEM_APPEND over the four pieces.              *)
(* ------------------------------------------------------------------------- *)

(* A control word written at n, read at a numeral k. *)
let PL_SET_AT = prove(`!f n (v:num) k. pl_set f n v k = if k = n then v else f k`, REWRITE_TAC[pl_set]);;

let PL_SET_NUM_CONV tm =
  match strip_comb tm with
    Const("pl_set",_), [f; n; v; k] when is_numeral k && is_numeral n ->
      (REWR_CONV PL_SET_AT THENC RATOR_CONV(RATOR_CONV(RAND_CONV NUM_EQ_CONV)) THENC
       (REWR_CONV(CONJUNCT1(SPEC_ALL COND_CLAUSES)) ORELSEC REWR_CONV(CONJUNCT2(SPEC_ALL COND_CLAUSES)))) tm
  | _ -> failwith "PL_SET_NUM_CONV";;

let PL_SET_NUM_TAC =
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV PL_SET_NUM_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV PL_SET_NUM_CONV);;

(* The control words of the plan_rel assumption on memory mem. *)
let pl_cw_of mem (asl,w) =
  let th = find (fun th -> is_const_app "plan_rel" (concl th) && el 4 (snd(strip_comb(concl th))) = mem)
                (map snd asl) in
  fst(dest_pair(el 5 (snd(strip_comb(concl th)))));;

(* A piece's run: its theorem at the drv_sem assumption of its plan, the     *)
(* control words and memory the relation holds there, the cursor given.      *)
let END_APPLY_TAC th plan mem cursor =
  W(fun g -> let cwv = pl_cw_of mem g in
    FIRST_ASSUM(fun dc -> if is_const_app "drv_sem" (concl dc) &&
                             (try el 5 (snd(strip_comb(concl dc))) = plan with _ -> false) then
      let args = snd(strip_comb(concl dc)) in
      MP_TAC(SPECL ([`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                     el 6 args; el 7 args; el 8 args; el 9 args; cwv] @ RD_NS_VARS @ [`inp:num list`; cursor]) th)
      else failwith "END_APPLY_TAC")) THEN
  ASM_REWRITE_TAC[] THEN TRY(ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN STRIP_TAC THEN PL_SET_NUM_TAC;;

(* A piece that did not FIRE ends the plan with its result (the other case  *)
(* closes); one that did leaves its relations, conjunct by conjunct.         *)
let END_PIECE_CASE_TAC rv =
  let eq = mk_eq(mk_icomb(`FST:int64#num#(int64->byte)#int64->int64`, rv), `word 1:int64`) in
  ASM_CASES_TAC eq THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ASSUME eq]) THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[]];;

(* The next piece's run, named; its receipt is the plan's. *)
let END_NEXT_TAC rv rnext =
  FIRST_X_ASSUM(X_CHOOSE_THEN rnext STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
  FIRST_ASSUM(fun th ->
    if concl th = mk_eq(list_mk_icomb "SND" [list_mk_icomb "SND" [mk_icomb(`SND:int64#num#(int64->byte)#int64->num#(int64->byte)#int64`, rv)]], `used:int64`)
    then RULE_ASSUM_TAC(PURE_REWRITE_RULE[th]) else failwith "END_NEXT_TAC");;

let END_REL = prove(end_rel_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_plan_end; DRV_SEM_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `ra:int64#num#(int64->byte)#int64` STRIP_ASSUME_TAC) THEN
  (* a: the header seen; T25 the checksum of the bytes before RST *)
  END_APPLY_TAC END_A_REL `pl_end_a` `m:int64->byte` `c:num` THEN
  END_PIECE_CASE_TAC `ra:int64#num#(int64->byte)#int64` THEN
  (* b: the count is CNT *)
  END_NEXT_TAC `ra:int64#num#(int64->byte)#int64` `rb:int64#num#(int64->byte)#int64` THEN
  END_APPLY_TAC END_B_REL `pl_end_b` `FST(SND(SND(ra:int64#num#(int64->byte)#int64)))` `c:num` THEN
  END_PIECE_CASE_TAC `rb:int64#num#(int64->byte)#int64` THEN
  (* c: the 8 bytes after it are T25's *)
  END_NEXT_TAC `rb:int64#num#(int64->byte)#int64` `rc:int64#num#(int64->byte)#int64` THEN
  END_APPLY_TAC END_C_REL `pl_end_c` `FST(SND(SND(rb:int64#num#(int64->byte)#int64)))`
    `c + LENGTH(leb_enc((cw:num->num) 17))` THEN
  END_PIECE_CASE_TAC `rc:int64#num#(int64->byte)#int64` THEN
  (* d: the input ends there; ENDW := 1 *)
  FIRST_ASSUM(fun th -> if concl th = `SND(SND(SND(rc:int64#num#(int64->byte)#int64))) = used`
                        then RULE_ASSUM_TAC(PURE_REWRITE_RULE[th]) else failwith "") THEN
  END_APPLY_TAC END_D_REL `pl_end_d` `FST(SND(SND(rc:int64#num#(int64->byte)#int64)))`
    `(c + LENGTH(leb_enc((cw:num->num) 17))) + 8` THEN
  (* the conclusion *)
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    lhand(concl th) = `FST(r:int64#num#(int64->byte)#int64) = word 1`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_VAL]) THEN
  CONJ_TAC THENL
   [(* the bytes from the cursor: the count's encoding, then the checksum's 8 *)
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[leb_fires] o check (fun th -> is_const_app "leb_fires" (concl th))) THEN
    DISCH_THEN(X_CHOOSE_TAC `rest:num list` o CONJUNCT2) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RD_FROM_APPEND) THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN REWRITE_TAC[rd_from] THEN
    SUBGOAL_THEN `LENGTH(inp:num list) - (c + LENGTH(leb_enc((cw:num->num) 17))) = 8` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    (* ENDW set, the other words below 24 kept *)
    W(fun g -> EXISTS_TAC (pl_cw_of `FST(SND(SND(r:int64#num#(int64->byte)#int64)))` g)) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC(TOP_DEPTH_CONV PL_SET_NUM_CONV) THEN REFL_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[pl_set] THEN
      REPEAT(COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN REFL_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) = `LENGTH(inp:num list)` then
        RULE_ASSUM_TAC(PURE_REWRITE_RULE[th]) else failwith "") THEN
      FIRST_ASSUM ACCEPT_TAC]]);;

let reader_end_theorems =
 ["FNV_FRAME", FNV_FRAME; "PL_FNV_SPEC", PL_FNV_SPEC; "AT_END_RO", AT_END_RO; "FNV_RO", FNV_RO;
  "RD_STEP_AT_END", RD_STEP_AT_END; "RD_CHILD_INP", RD_CHILD_INP; "RD_STEP_FNV", RD_STEP_FNV;
  "LE8_NEXT_RW", LE8_NEXT_RW; "LE8_NEXT_READABLE", LE8_NEXT_READABLE; "RD_LE8_KEEPS", RD_LE8_KEEPS;
  "RD_STEP_LE8", RD_STEP_LE8; "END_A_REL", END_A_REL; "END_B_REL", END_B_REL; "END_C_REL", END_C_REL;
  "RD_FROM_APPEND", RD_FROM_APPEND; "END_D_REL", END_D_REL; "PL_SET_AT", PL_SET_AT; "END_REL", END_REL];;
