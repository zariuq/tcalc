(* ========================================================================= *)
(* The HOLR header (PLANS.txt section 10), the reader's plan for opcode 72.  *)
(* The 39 bytes after it up to the version, the rest of the magic and the    *)
(* kernel id (holr_hdr_const), are a host constant in slot 60: rd_hdr_rel    *)
(* bw cfr m. The header's new leaves against their specifications:          *)
(* PL_POL_MAX_SPEC (leaf 20) and PL_CONST_NEXT_SPEC (leaf 31, with its       *)
(* comparison as const_bytes_eq, CONST_REGION_RANGE). Their steps at the     *)
(* plan level: RD_STEP_CONST_NEXT (FIRED exactly when the input from the     *)
(* cursor starts with the constant; the cursor past it) and RD_STEP_POL_MAX  *)
(* (FIRED exactly when its second argument is at most 2; the payload the     *)
(* larger argument). The header plan pl_plan_hdr: the constant; HDR 0; the  *)
(* version 1 0; the policy p <= 2, validated into candidate word 25; flags  *)
(* 0; publish the policy; HDR := 1. Its pieces' relations and               *)
(* PL_HDR_REL (DRV_SEM_APPEND over the pieces); HDR_CONTRACT_FORM: a FIRED  *)
(* run read the header after its opcode (TL (holr_body p 0 [])) and leaves   *)
(* the relations past it at the state with the policy raised to p and HDR   *)
(* set, the words 17..23 but HDR kept.                                       *)
(*                                                                           *)
(* Loaded after reader_end.ml.                                               *)
(* ========================================================================= *)

needs "native/hol/header_commit.ml";;
needs "native/hol/reader_end.ml";;
needs "native/leaves/pol_max/pol_max.ml";;
needs "native/leaves/const_next/const_next.ml";;

(* ------------------------------------------------------------------------- *)
(* The leaves' specifications.                                               *)
(* ------------------------------------------------------------------------- *)

let PL_POL_MAX_SPEC = prove
 (`pl_pol_max_spec pol_max`,
  LEAF_BRIDGE_TAC pl_pol_max_spec POL_MAX_RUN pol_max_post POL_MAX_LEAF_WF POL_MAX_DECLS);;

(* Two ranges of bytes, as lists, are equal exactly when they agree byte for *)
(* byte.                                                                      *)
let CONST_REGION_RANGE = prove
 (`!t c n. region_range t 0 c n = region_range t 2 0 n <=> const_bytes_eq t c n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[region_range; const_bytes_eq; LIST_EQ; LENGTH_LIST_OF_SEQ; region_byte; ADD_CLAUSES] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ; VAL_EQ];
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; VAL_EQ]]);;

let PL_CONST_NEXT_SPEC = prove
 (`pl_const_next_spec const_next`,
  REWRITE_TAC[pl_const_next_spec; pl_leaf_ok; CONST_NEXT_LEAF_WF; CONST_NEXT_DECLS] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RD_REGION1_TAC `const_next` CONST_NEXT_LEAF_WF CONST_NEXT_DECLS THEN
  MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] CONST_NEXT_RUN) THEN
  ASM_REWRITE_TAC[const_next_post; pl_cursor; pl_w; MULT_CLAUSES; WORD_ADD_0; CONST_REGION_RANGE] THEN
  SIMP_TAC[] THEN
  MAP_EVERY ASM_CASES_TAC [`val(tisa_read t (tisa_base t 1) 8) + val(tisa_len t 2) <= val(tisa_len t 0)`;
                           `4294967295 < val(tisa_len t 2)`;
                           `const_bytes_eq t (val(tisa_read t (tisa_base t 1) 8)) (val(tisa_len t 2))`] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The header's constant in slot 60.                                         *)
(* ------------------------------------------------------------------------- *)

(* The header's constant: the 39 bytes after its opcode 'H' up to the       *)
(* version, the rest of the magic and the kernel id.                         *)
let holr_hdr_const = new_definition
 `holr_hdr_const = APPEND (TL holr_magic) holr_kernel_id`;;

let HOLR_HDR_CONST_LENGTH = prove
 (`LENGTH holr_hdr_const = 39`,
  REWRITE_TAC[holr_hdr_const; holr_magic; holr_kernel_id; TL; LENGTH_APPEND; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Slot 60 holds the header's constant in memory m, apart from the driver's  *)
(* stack window around cfr and not wrapping.                                 *)
let rd_hdr_rel = new_definition
 `rd_hdr_rel (bw:num->int64) (cfr:int64) (m:int64->byte) <=>
    val(bw 61) = LENGTH holr_hdr_const /\ val(bw 60) + val(bw 61) < 2 EXP 64 /\
    drv_apart (word_sub cfr (word 48)) 304 (bw 60) (val(bw 61)) /\
    !i. i < LENGTH holr_hdr_const ==> val(m(word_add (bw 60) (word i))) = EL i holr_hdr_const`;;

(* The regions' modes, by cases on the region (three regions). *)
let CONST_NEXT_CASES_TAC =
  GEN_TAC THEN REWRITE_TAC[CONST_NEXT_DECLS; tisa_rw; tisa_readable; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `r = 1` THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `r = 2` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[FST] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC;;

let CONST_NEXT_RW = prove
 (`!r. tisa_rw (tisa_decls const_next) r <=> r = 1`, CONST_NEXT_CASES_TAC);;
let CONST_NEXT_READABLE = prove
 (`!r. tisa_readable (tisa_decls const_next) r <=> r = 0 \/ r = 1 \/ r = 2`, CONST_NEXT_CASES_TAC);;

(* Two memories that agree on slot 60 agree on rd_hdr_rel. *)
let RD_HDR_AGREE = prove
 (`!bw cfr m m'. rd_hdr_rel bw cfr m /\ (!a. drv_in a (bw 60) (val(bw 61)) ==> m' a = m a)
                 ==> rd_hdr_rel bw cfr m'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_hdr_rel] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(m':int64->byte) (word_add (bw 60) (word i)) = m (word_add (bw 60) (word i))` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[drv_in] THEN
    MP_TAC(SPECL [`(bw:num->int64) 60`; `i:num`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
    ASM_SIMP_TAC[]]);;

(* const_next's region 2 bound to slot 60: the child reads the constant.     *)
let RD_CHILD_HDR = prove
 (`!bw ctl budget cfr st m used t.
     drv_child bw ctl budget cfr st m used t /\ rd_hdr_rel bw cfr m /\ 48 <= val cfr /\ val(EL 3 st) = 60
     ==> tisa_base t 2 = bw 60 /\ tisa_len t 2 = bw 61 /\
         region_range t 2 0 (LENGTH holr_hdr_const) = holr_hdr_const`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `drv_base`)) (concl th) then
     MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC `2` th)) else failwith "") THEN
  ASM_REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_hdr_rel] o
    check (fun th -> is_const_app "rd_hdr_rel" (concl th))) THEN
  REWRITE_TAC[region_range; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `n':num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[region_byte; tisa_read; READ_BYTES_1; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `tmem t (word_add (bw 60) (word n'):int64) = (m:int64->byte) (word_add (bw 60) (word n'))`
    SUBST1_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
      check (fun th -> is_const_app "drv_child" (concl th))) THEN
    MATCH_MP_TAC DRV_IN_NOT_STACK THEN
    MAP_EVERY EXISTS_TAC [`(bw:num->int64) 60`; `val((bw:num->int64) 61)`] THEN ASM_REWRITE_TAC[drv_in] THEN
    MP_TAC(SPECL [`(bw:num->int64) 60`; `n':num`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `val((m:int64->byte) (word_add (bw 60) (word n'))) < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(m:int64->byte) (word_add (bw 60) (word n'))` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]]);;

(* ------------------------------------------------------------------------- *)
(* The steps.                                                                *)
(* ------------------------------------------------------------------------- *)

(* What const_next keeps: everything outside the state and the payload word. *)
let RD_CONST_KEEPS = prove
 (`!bw ctl nctl budget cfr st m used t k u a.
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok const_next t /\ tisa_run const_next t = TStop k u /\
     val(EL 2 st) = 58 /\ val ctl + 8 * nctl <= 2 EXP 64 /\ val(EL 17 st) < nctl /\
     ~drv_stack cfr a /\ ~drv_in a (bw 58) (val(bw 59)) /\
     ~drv_in a (word_add ctl (word(8 * val(EL 17 st)))) 8
     ==> drv_after ctl st u a = m a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
  MAP_EVERY EXISTS_TAC [`const_next`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                        `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[CONST_NEXT_LEAF_WF; CONST_NEXT_RW] THEN
  X_GEN_TAC `r:num` THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let HOLR_HDR_CONST_CAP = prove
 (`~(4294967295 < LENGTH holr_hdr_const)`, REWRITE_TAC[HOLR_HDR_CONST_LENGTH] THEN ARITH_TAC);;

(* A const_next step against the header's constant: FIRED exactly when the  *)
(* input from the cursor starts with the constant; then the cursor is past  *)
(* it and the payload is recorded.                                           *)
let RD_STEP_CONST_NEXT = prove
 (`!bw ctl nctl budget cfr st m used t k u cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ rd_hdr_rel bw cfr m /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok const_next t /\ tisa_run const_next t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 3 st) = 60 /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         (if c + LENGTH holr_hdr_const <= LENGTH inp /\
             list_of_seq (\j. EL (c + j) inp) (LENGTH holr_hdr_const) = holr_hdr_const
          then tisa_fword u 18 = word 1 /\
               plan_rel bw ctl nctl cfr (drv_after ctl st u)
                 (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp (c + LENGTH holr_hdr_const)
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
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`] RD_CHILD_HDR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DRV_CHILD_RECEIPT) THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_hdr_rel] o
    check (fun th -> is_const_app "rd_hdr_rel" (concl th))) THEN
  SUBGOAL_THEN `val(tisa_len t 0) = LENGTH(inp:num list)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(tisa_len t 2) = LENGTH holr_hdr_const` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC PL_CONST_NEXT_SPEC THEN REWRITE_TAC[pl_const_next_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  REWRITE_TAC[HOLR_HDR_CONST_CAP] THEN
  ASM_CASES_TAC `c + LENGTH holr_hdr_const <= val((bw:num->int64) 55)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `c + LENGTH holr_hdr_const <= LENGTH(inp:num list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `region_range t 0`)) (concl th)
                        then REWRITE_TAC[MP (SPECL [`c:num`; `LENGTH holr_hdr_const`] th)
                                            (ASSUME `c + LENGTH holr_hdr_const <= LENGTH(inp:num list)`)]
                        else failwith "") THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* What const_next keeps: everything outside the state and the payload word. *)
  SUBGOAL_THEN `!a. ~drv_stack cfr a /\ ~drv_in a (bw 58) (val(bw 59)) /\
                    ~drv_in a (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8
                    ==> drv_after ctl st u a = (m:int64->byte) a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RD_CONST_KEEPS THEN
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
    (* rd_rel: the input kept; the cursor past the constant. *)
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
       [MP_TAC(SPECL [`const_next`; `t:tisa_state`; `k:num`; `u:tisa_state`; `1`] TISA_RUN_REGIONS) THEN
        ASM_REWRITE_TAC[CONST_NEXT_LEAF_WF; CONST_NEXT_READABLE] THEN SIMP_TAC[];
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

(* pol_max at the plan level: FIRED exactly when its second argument is at   *)
(* most 2, with the larger of its arguments as the payload.                  *)
let RD_STEP_POL_MAX = prove
 (`!bw ctl nctl budget cfr st m used t k u cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok pol_max t /\ tisa_run pol_max t = TStop k u /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         (if cw(val(EL 11 st)) <= 2
          then tisa_fword u 18 = word 1 /\
               plan_rel bw ctl nctl cfr (drv_after ctl st u)
                 (pl_set cw (val(EL 17 st)) (MAX (cw(val(EL 10 st))) (cw(val(EL 11 st)))),
                  (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RD_CHILD_ARGS_TAC THEN
  MP_TAC PL_POL_MAX_SPEC THEN REWRITE_TAC[pl_pol_max_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `MAX (cw(val(EL 10 (st:int64 list)))) (cw(val(EL 11 st))) = val(tisa_fword u 19)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `tisa_fword t 22` VAL_BOUND_64) THEN MP_TAC(ISPEC `tisa_fword t 23` VAL_BOUND_64) THEN
    ASM_REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_REL_RO_STEP THEN
    MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `pol_max`; `1`] THEN
    ASM_REWRITE_TAC[POL_MAX_LEAF_WF; POL_MAX_DECLS; NO_DECLS_RW] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    MATCH_MP_TAC RD_STEP_RO THEN
    MAP_EVERY EXISTS_TAC [`pol_max`; `budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`] THEN
    ASM_REWRITE_TAC[POL_MAX_LEAF_WF; POL_MAX_DECLS; NO_DECLS_RW] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The header plan: the constant; no header before (HDR 0); the version 1 0; *)
(* policy validated into T25; flags 0; publish POL; HDR := 1.              *)
(*   const_next -> T25; eqw HDR K0 -> T24; leb_next -> T26; eqw T26 K1 ->    *)
(*   T27; leb_next -> T26; eqw T26 K0 -> T27; leb_next -> T26; pol_max POL   *)
(*   T26 -> T25; leb_next -> T26; eqw T26 K0 -> T27; eqw T25 T25 -> POL;     *)
(*   eqw K1 K1 -> HDR.                                                       *)
(* ------------------------------------------------------------------------- *)

let pl_hdr_b = new_definition(mk_eq(`pl_hdr_b:(int64 list)list`, mk_list(
  [pl_step_tm 31 [54; 58; 60] 0 0 [] 25], `:int64 list`)));;
let pl_hdr_a = new_definition(mk_eq(`pl_hdr_a:(int64 list)list`, mk_list(
  [pl_step_tm 3 [] 20 0 [] 24], `:int64 list`)));;
let pl_hdr_v1 = new_definition(mk_eq(`pl_hdr_v1:(int64 list)list`, mk_list(
  [pl_step_tm 26 [54; 58] 0 0 [] 26; pl_step_tm 3 [] 26 1 [] 27], `:int64 list`)));;
let pl_hdr_v0 = new_definition(mk_eq(`pl_hdr_v0:(int64 list)list`, mk_list(
  [pl_step_tm 26 [54; 58] 0 0 [] 26; pl_step_tm 3 [] 26 0 [] 27], `:int64 list`)));;
let pl_hdr_p = new_definition(mk_eq(`pl_hdr_p:(int64 list)list`, mk_list(
  [pl_step_tm 26 [54; 58] 0 0 [] 26; pl_step_tm 20 [] 7 26 [] 25], `:int64 list`)));;
let pl_hdr_g = new_definition(mk_eq(`pl_hdr_g:(int64 list)list`, mk_list(
  [pl_step_tm 3 [] 1 1 [] 20], `:int64 list`)));;
let pl_plan_hdr = new_definition
 `pl_plan_hdr = APPEND pl_hdr_b (APPEND pl_hdr_a (APPEND pl_hdr_v1 (APPEND pl_hdr_v0
                  (APPEND pl_hdr_p (APPEND pl_hdr_v0 (APPEND pl_hdr_commit pl_hdr_g))))))`;;

let pl_st i def = el i (dest_list(rhs(concl def)));;

(* The words 0 and 1 hold 0 and 1. *)
let HDR_K01_TAC =
  SUBGOAL_THEN `(cw:num->num) 1 = 1 /\ cw 0 = 0` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> is_const_app "plan_rel" (concl th))) THEN
    REWRITE_TAC[plan_rel] THEN STRIP_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC];;

(* A one-step piece: the drv_sem run's single step, named t1 k1 u1. *)
let HDR_ONE_STEP_TAC def =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[def; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC)));;

(* The run's end after its last step: FIRED (the empty rest) or stopped. *)
let HDR_END_FIRED_TAC =
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[drv_sem] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[];;
let HDR_END_STOP_TAC =
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  ASM_REWRITE_TAC[];;

let hdr_ns = `(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`;;

(* b: the constant at the cursor. *)
let HDR_B_REL = prove
 (`!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     progs 31 = const_next /\ 25 < nctl /\ rd_hdr_rel bw cfr m /\
     drv_sem progs bw ctl budget cfr pl_hdr_b i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> c + LENGTH holr_hdr_const <= LENGTH inp /\
              list_of_seq (\j. EL (c + j) inp) (LENGTH holr_hdr_const) = holr_hdr_const /\
              ?x. plan_rel bw ctl nctl cfr (FST(SND(SND r)))
                    (pl_set cw 25 x,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
                  rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + LENGTH holr_hdr_const))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN HDR_ONE_STEP_TAC pl_hdr_b THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_st 0 pl_hdr_b;
                 `m:int64->byte`; `used:int64`; `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`] @
                RD_NS_VARS @ [`inp:num list`; `c:num`]) RD_STEP_CONST_NEXT) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  TRY(ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  COND_CASES_TAC THEN STRIP_TAC THENL
   [HDR_END_FIRED_TAC THEN EXISTS_TAC `val(tisa_fword u1 19)` THEN ASM_REWRITE_TAC[];
    HDR_END_STOP_TAC]);;

(* a: no header before (HDR 0). *)
let HDR_A_REL = prove
 (`!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     progs 3 = eqw /\ 24 < nctl /\
     drv_sem progs bw ctl budget cfr pl_hdr_a i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> cw 20 = 0 /\
              plan_rel bw ctl nctl cfr (FST(SND(SND r)))
                (pl_set cw 24 0,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
              rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN HDR_K01_TAC THEN HDR_ONE_STEP_TAC pl_hdr_a THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_st 0 pl_hdr_a;
                 `m:int64->byte`; `used:int64`; `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`] @
                RD_NS_VARS @ [`inp:num list`; `c:num`]) RD_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  TRY(ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  COND_CASES_TAC THEN STRIP_TAC THENL
   [HDR_END_FIRED_TAC THEN FIRST_X_ASSUM(fun th -> if concl th = `(cw:num->num) 20 = 0`
      then REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "") THEN ASM_REWRITE_TAC[];
    HDR_END_STOP_TAC]);;

(* g: HDR := 1 (always FIRED). *)
let HDR_G_REL = prove
 (`!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     progs 3 = eqw /\ 24 < nctl /\
     drv_sem progs bw ctl budget cfr pl_hdr_g i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> plan_rel bw ctl nctl cfr (FST(SND(SND r)))
                (pl_set cw 20 1,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
              rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN HDR_K01_TAC THEN HDR_ONE_STEP_TAC pl_hdr_g THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_st 0 pl_hdr_g;
                 `m:int64->byte`; `used:int64`; `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`] @
                RD_NS_VARS @ [`inp:num list`; `c:num`]) RD_STEP_EQW) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  TRY(ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC]) THEN
  STRIP_TAC THEN HDR_END_FIRED_TAC);;

(* The first step of a two-step piece (leb_next): its value v, or the plan    *)
(* stopped REFUSED there.                                                      *)
let HDR_LEB_FIRST_TAC def =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[def; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_st 0 def;
                 `m:int64->byte`; `used:int64`; `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`] @
                RD_NS_VARS @ [`inp:num list`; `c:num`]) RD_STEP_LEB) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  TRY(ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THENL
   [ALL_TAC; HDR_END_STOP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
    STRIP_ASSUME_TAC)));;

let hdr_second_args def =
  [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_st 1 def;
   list_mk_comb(`drv_after`, [`ctl:int64`; pl_st 0 def; `u1:tisa_state`]);
   `used:int64`; `t2:tisa_state`; `k2:num`; `u2:tisa_state`; `pl_set cw 26 v`] @
  RD_NS_VARS @ [`inp:num list`; `c + LENGTH(leb_enc v)`];;

(* c (k = 1, the version's first number) and d (k = 0, its second, and the  *)
(* flags): the number at the cursor is k.                                    *)
let hdr_v_goal def k =
  let kt = mk_small_numeral k in
  let g = `!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     progs 3 = eqw /\ rd_progs_ok progs /\ 27 < nctl /\
     drv_sem progs bw ctl budget cfr PIECE i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> leb_fires (rd_from inp c) KK /\
              plan_rel bw ctl nctl cfr (FST(SND(SND r)))
                (pl_set (pl_set cw 26 KK) 27 KK,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
              rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + LENGTH(leb_enc KK)))` in
  subst [lhs(concl def), mk_var("PIECE", `:(int64 list)list`); kt, mk_var("KK", `:num`)] g;;

let HDR_V_REL def k =
  let kt = mk_small_numeral k in
  prove(hdr_v_goal def k,
    REPEAT GEN_TAC THEN REWRITE_TAC[rd_progs_ok] THEN STRIP_TAC THEN HDR_K01_TAC THEN
    HDR_LEB_FIRST_TAC def THEN
    MP_TAC(SPECL (hdr_second_args def) RD_STEP_EQW) THEN
    CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC]) THEN
    SUBGOAL_THEN (mk_conj(`pl_set cw 26 v 26 = v`, mk_eq(list_mk_icomb "pl_set" [`cw:num->num`; `26`; `v:num`; kt], kt)))
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC (mk_eq(`v:num`, kt)) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = mk_eq(`v:num`, kt))) THEN
      HDR_END_FIRED_TAC;
      HDR_END_STOP_TAC]);;

let HDR_V1_REL = HDR_V_REL pl_hdr_v1 1;;
let HDR_V0_REL = HDR_V_REL pl_hdr_v0 0;;

(* p: validate the policy into candidate word 25; POL is committed later. *)
let HDR_P_REL = prove
 (`!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     progs 20 = pol_max /\ rd_progs_ok progs /\ 26 < nctl /\
     drv_sem progs bw ctl budget cfr pl_hdr_p i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> ?p. p <= 2 /\ leb_fires (rd_from inp c) p /\
                  plan_rel bw ctl nctl cfr (FST(SND(SND r)))
                    (pl_set (pl_set cw 26 p) 25 (MAX (cw 7) p),(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
                  rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + LENGTH(leb_enc p)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_progs_ok] THEN STRIP_TAC THEN
  HDR_LEB_FIRST_TAC pl_hdr_p THEN
  MP_TAC(SPECL (hdr_second_args pl_hdr_p) RD_STEP_POL_MAX) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  TRY(ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC]) THEN
  SUBGOAL_THEN `pl_set cw 26 v 26 = v /\ pl_set cw 26 v 7 = (cw:num->num) 7` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_CASES_TAC `v <= 2` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [HDR_END_FIRED_TAC THEN EXISTS_TAC `v:num` THEN ASM_REWRITE_TAC[];
    HDR_END_STOP_TAC]);;

(* The header's bytes after its opcode: the constant, the version 1 0, the   *)
(* policy, the flags 0.                                                       *)
let HDR_BODY_TL = prove
 (`!p. TL (holr_body p 0 []) =
       APPEND holr_hdr_const (APPEND (leb_enc 1) (APPEND (leb_enc 0) (APPEND (leb_enc p) (leb_enc 0))))`,
  REWRITE_TAC[holr_body; holr_hdr_const; holr_magic; MAP; holr_flat; ITLIST; APPEND_NIL] THEN
  REWRITE_TAC[APPEND; TL; GSYM APPEND_ASSOC]);;

(* Bytes l matched at offset c are the front of the bytes from c. *)
let RD_FROM_PREFIX = prove
 (`!inp c (l:num list).
     c + LENGTH l <= LENGTH inp /\ list_of_seq (\j. EL (c + j) inp) (LENGTH l) = l
     ==> rd_from inp c = APPEND l (rd_from inp (c + LENGTH l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[rd_from] THEN
  SUBGOAL_THEN `LENGTH(inp:num list) - c = LENGTH(l:num list) + (LENGTH inp - (c + LENGTH l))` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LIST_OF_SEQ_ADD] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC[ADD_ASSOC]);;

(* The header's pieces' facts about the bytes give its bytes and cursor. *)
let HDR_BYTES = prove
 (`!inp c p.
     c + LENGTH holr_hdr_const <= LENGTH inp /\
     list_of_seq (\j. EL (c + j) inp) (LENGTH holr_hdr_const) = holr_hdr_const /\
     leb_fires (rd_from inp (c + LENGTH holr_hdr_const)) 1 /\
     leb_fires (rd_from inp ((c + LENGTH holr_hdr_const) + LENGTH(leb_enc 1))) 0 /\
     leb_fires (rd_from inp (((c + LENGTH holr_hdr_const) + LENGTH(leb_enc 1)) + LENGTH(leb_enc 0))) p /\
     leb_fires (rd_from inp ((((c + LENGTH holr_hdr_const) + LENGTH(leb_enc 1)) + LENGTH(leb_enc 0)) +
                             LENGTH(leb_enc p))) 0
     ==> (?rest. rd_from inp c = APPEND (TL (holr_body p 0 [])) rest) /\
         ((((c + LENGTH holr_hdr_const) + LENGTH(leb_enc 1)) + LENGTH(leb_enc 0)) + LENGTH(leb_enc p)) +
         LENGTH(leb_enc 0) = c + LENGTH (TL (holr_body p 0 []))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[leb_fires] THEN STRIP_TAC THEN
  REWRITE_TAC[HDR_BODY_TL; LENGTH_APPEND] THEN CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
  (* each rest is the bytes after its prefix *)
  REPEAT(FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_const_app "rd_from" (lhs(concl th)) &&
                                    is_const_app "APPEND" (rhs(concl th)) && is_var(rand(rhs(concl th)))
     then ASSUME_TAC(PURE_ONCE_REWRITE_RULE[MATCH_MP RD_FROM_APPEND th] th) else failwith "")) THEN
  MP_TAC(SPECL [`inp:num list`; `c:num`; `holr_hdr_const`] RD_FROM_PREFIX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  EXISTS_TAC `rd_from inp (((((c + LENGTH holr_hdr_const) + LENGTH(leb_enc 1)) + LENGTH(leb_enc 0)) +
                            LENGTH(leb_enc p)) + LENGTH(leb_enc 0))` THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC]);;

(* The header plan's relation: a FIRED run saw no header before (HDR 0); the *)
(* input from the cursor is the header after its opcode for a policy p <= 2; *)
(* the relations hold after it with HDR = 1, POL raised to p, the other      *)
(* words below 24 kept, the cursor past the header.                          *)
let hdr_rel_goal =
 `!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     progs 3 = eqw /\ rd_progs_ok progs /\ progs 31 = const_next /\ progs 20 = pol_max /\ 27 < nctl /\
     rd_hdr_rel bw cfr m /\
     drv_sem progs bw ctl budget cfr pl_plan_hdr i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1
          ==> cw 20 = 0 /\
              ?p cw'. p <= 2 /\ (?rest. rd_from inp c = APPEND (TL (holr_body p 0 [])) rest) /\
                      cw' 20 = 1 /\ cw' 7 = MAX (cw 7) p /\
                      (!j. j < 24 /\ ~(j = 7) /\ ~(j = 20) ==> cw' j = cw j) /\
                      plan_rel bw ctl nctl cfr (FST(SND(SND r)))
                        (cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
                      rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + LENGTH (TL (holr_body p 0 []))))`;;

let PL_HDR_REL = prove(hdr_rel_goal,
  let rv s = mk_var(s, `:int64#num#(int64->byte)#int64`) in
  let mem s = mk_icomb(`FST:(int64->byte)#int64->int64->byte`,
                mk_icomb(`SND:num#(int64->byte)#int64->(int64->byte)#int64`,
                  mk_icomb(`SND:int64#num#(int64->byte)#int64->num#(int64->byte)#int64`, rv s))) in
  let c1 = `c + LENGTH holr_hdr_const` in
  let c2 = `(c + LENGTH holr_hdr_const) + LENGTH(leb_enc 1)` in
  let c3 = `((c + LENGTH holr_hdr_const) + LENGTH(leb_enc 1)) + LENGTH(leb_enc 0)` in
  let c4 = `(((c + LENGTH holr_hdr_const) + LENGTH(leb_enc 1)) + LENGTH(leb_enc 0)) + LENGTH(leb_enc p)` in
  let c5 = `((((c + LENGTH holr_hdr_const) + LENGTH(leb_enc 1)) + LENGTH(leb_enc 0)) + LENGTH(leb_enc p)) +
            LENGTH(leb_enc 0)` in
  let choose_named n ty = FIRST_X_ASSUM(X_CHOOSE_THEN (mk_var(n, ty)) STRIP_ASSUME_TAC o
    check (fun th -> is_exists(concl th) && fst(dest_var(fst(dest_exists(concl th)))) = n)) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_plan_hdr; DRV_SEM_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN (rv "rb") STRIP_ASSUME_TAC) THEN
  (* b: the constant *)
  END_APPLY_TAC HDR_B_REL `pl_hdr_b` `m:int64->byte` `c:num` THEN
  END_PIECE_CASE_TAC (rv "rb") THEN choose_named "x" `:num` THEN
  (* a: no header before *)
  END_NEXT_TAC (rv "rb") (rv "ra") THEN
  END_APPLY_TAC HDR_A_REL `pl_hdr_a` (mem "rb") c1 THEN
  END_PIECE_CASE_TAC (rv "ra") THEN
  (* the version 1 0 *)
  END_NEXT_TAC (rv "ra") (rv "r1") THEN
  END_APPLY_TAC HDR_V1_REL `pl_hdr_v1` (mem "ra") c1 THEN
  END_PIECE_CASE_TAC (rv "r1") THEN
  END_NEXT_TAC (rv "r1") (rv "r0") THEN
  END_APPLY_TAC HDR_V0_REL `pl_hdr_v0` (mem "r1") c2 THEN
  END_PIECE_CASE_TAC (rv "r0") THEN
  (* the policy *)
  END_NEXT_TAC (rv "r0") (rv "rp") THEN
  END_APPLY_TAC HDR_P_REL `pl_hdr_p` (mem "r0") c3 THEN
  END_PIECE_CASE_TAC (rv "rp") THEN choose_named "p" `:num` THEN
  (* the flags *)
  END_NEXT_TAC (rv "rp") (rv "rf") THEN
  END_APPLY_TAC HDR_V0_REL `pl_hdr_v0` (mem "rp") c4 THEN
  END_PIECE_CASE_TAC (rv "rf") THEN
  (* The flags passed: publish the validated policy, then mark HDR. *)
  END_NEXT_TAC (rv "rf") (rv "rc") THEN
  END_APPLY_TAC HDR_COMMIT_REL `pl_hdr_commit` (mem "rf") c5 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `FST(rc:int64#num#(int64->byte)#int64) = word 1`]) THEN
  (* HDR := 1: the last piece's run is r *)
  FIRST_ASSUM(fun th -> if concl th = mk_eq(mk_icomb(`SND:(int64->byte)#int64->int64`,
                                              mk_icomb(`SND:num#(int64->byte)#int64->(int64->byte)#int64`,
                                                mk_icomb(`SND:int64#num#(int64->byte)#int64->num#(int64->byte)#int64`,
                                                  rv "rc"))), `used:int64`)
                        then RULE_ASSUM_TAC(PURE_REWRITE_RULE[th]) else failwith "") THEN
  END_APPLY_TAC HDR_G_REL `pl_hdr_g` (mem "rc") c5 THEN
  (* the conclusion *)
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    lhand(concl th) = `FST(r:int64#num#(int64->byte)#int64) = word 1`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`inp:num list`; `c:num`; `p:num`] HDR_BYTES) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> RULE_ASSUM_TAC(PURE_REWRITE_RULE[th]))) THEN
  TRY(CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  W(fun g -> MAP_EVERY EXISTS_TAC [`p:num`; pl_cw_of `FST(SND(SND(r:int64#num#(int64->byte)#int64)))` g]) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    CONV_TAC(TOP_DEPTH_CONV PL_SET_NUM_CONV) THEN REFL_TAC;
    CONV_TAC(TOP_DEPTH_CONV PL_SET_NUM_CONV) THEN REFL_TAC;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[pl_set] THEN
    REPEAT(COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN REFL_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

(* plan_rel does not read the policy. *)
let PL_REL_POL = prove
 (`!bw ctl nctl cfr m cw ctx nms tys ntms dbs ths nmap ymap drops pol pol' stk.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol'),stk)`,
  REWRITE_TAC[plan_rel]);;

(* pl_inv holds under any policy: the native rows and canonicity ignore it,  *)
(* and the simulated HOLR state takes the same policy.                       *)
let PL_INV_POL = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol pol' stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol'),stk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_inv; nat_ok; nat_rows_ok] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "nat_sim" (concl th))) THEN
  SPEC_TAC(`hr:hrstate`,`hr:hrstate`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM; nat_sim] THEN
  W(fun (asl,w) -> let vs, _ = strip_forall w in
    MAP_EVERY X_GEN_TAC vs THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC (butlast vs @ [`pol':num`]) THEN ASM_REWRITE_TAC[]));;

(* pl_inv reads the control words only at 0..6. *)
let PL_INV_CW = prove
 (`!cw cw' ns stk. pl_inv (cw,ns,stk) /\ (!n. n <= 6 ==> cw' n = cw n) ==> pl_inv (cw',ns,stk)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; pl_inv] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `hr:hrstate` THEN FIRST_ASSUM ACCEPT_TAC; REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* The header plan meets the header's contract form: run from relations at  *)
(* the cursor with the constant in slot 60, a FIRED run saw HDR 0, read the  *)
(* header of a policy p <= 2, and leaves the relations past it at the state  *)
(* with the policy raised to p and HDR set.                                  *)
let HDR_CONTRACT_FORM = prove
 (`!progs bw ctl nctl budget cfr.
     progs 3 = eqw /\ rd_progs_ok progs /\ progs 31 = const_next /\ progs 20 = pol_max /\ 27 < nctl
     ==> !m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
           drv_sem progs bw ctl budget cfr pl_plan_hdr 0 m used res /\
           plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
           pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
           rd_rel bw ctl nctl cfr m inp c /\ rd_hdr_rel bw cfr m /\ ~(val budget < val used)
           ==> (FST res = word 1
                ==> cw 20 = 0 /\
                    ?p rest s'. p <= 2 /\ rd_from inp c = APPEND (TL (holr_body p 0 [])) rest /\
                                FST(SND s') = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,MAX pol p) /\
                                pl_inv s' /\
                                plan_rel bw ctl nctl cfr (FST(SND(SND res))) s' /\
                                rd_rel bw ctl nctl cfr (FST(SND(SND res))) inp
                                       (c + LENGTH (TL (holr_body p 0 []))) /\
                                FST s' 20 = 1 /\
                                (!j. 17 <= j /\ j < 24 /\ ~(j = 20) ==> FST s' j = cw j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL ([`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                 `0`; `m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`] @
                RD_NS_VARS @ [`inp:num list`; `c:num`]) PL_HDR_REL) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(MP (CONJUNCT2 th) (ASSUME `FST(res:int64#num#(int64->byte)#int64) = word 1`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `cw':num->num`
    STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `rest:num list`;
    `(cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,MAX pol p),stk):pstate`] THEN
  REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC PL_INV_POL THEN EXISTS_TAC `pol:num` THEN
    MATCH_MP_TAC PL_INV_CW THEN EXISTS_TAC `cw:num->num` THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `cw':num->num`)) (concl th))) THEN ASM_ARITH_TAC];
    MATCH_MP_TAC PL_REL_POL THEN EXISTS_TAC `pol:num` THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `cw':num->num`)) (concl th))) THEN ASM_ARITH_TAC]);;

(* Every theorem this file states, for the audits. *)
let reader_hdr_theorems =
 ["PL_POL_MAX_SPEC", PL_POL_MAX_SPEC; "CONST_REGION_RANGE", CONST_REGION_RANGE;
  "PL_CONST_NEXT_SPEC", PL_CONST_NEXT_SPEC; "HOLR_HDR_CONST_LENGTH", HOLR_HDR_CONST_LENGTH;
  "CONST_NEXT_RW", CONST_NEXT_RW; "CONST_NEXT_READABLE", CONST_NEXT_READABLE;
  "RD_CHILD_HDR", RD_CHILD_HDR; "RD_CONST_KEEPS", RD_CONST_KEEPS;
  "HOLR_HDR_CONST_CAP", HOLR_HDR_CONST_CAP; "RD_STEP_CONST_NEXT", RD_STEP_CONST_NEXT;
  "RD_STEP_POL_MAX", RD_STEP_POL_MAX; "HDR_B_REL", HDR_B_REL; "HDR_A_REL", HDR_A_REL;
  "HDR_G_REL", HDR_G_REL; "HDR_V1_REL", HDR_V1_REL; "HDR_V0_REL", HDR_V0_REL;
  "HDR_P_REL", HDR_P_REL; "HDR_BODY_TL", HDR_BODY_TL; "RD_FROM_PREFIX", RD_FROM_PREFIX;
  "HDR_BYTES", HDR_BYTES; "PL_HDR_REL", PL_HDR_REL; "PL_REL_POL", PL_REL_POL;
  "PL_INV_POL", PL_INV_POL; "PL_INV_CW", PL_INV_CW; "HDR_CONTRACT_FORM", HDR_CONTRACT_FORM;
  "RD_HDR_AGREE", RD_HDR_AGREE];;
