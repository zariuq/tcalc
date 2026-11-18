(* ========================================================================= *)
(* The reader beside plan_rel (PLANS.txt, sections 10 and 11). The input    *)
(* bytes and the cursor are a relation of their own, rd_rel: the input is   *)
(* slot 54 (read-only), the reader's state slot 58 (16 bytes, word 0 the    *)
(* cursor). Both regions lie apart from every slot plan_rel reads, from the *)
(* control words and from the driver's stack window, so                     *)
(*   - a record plan, whose writable regions are plan_rel's slots, keeps    *)
(*     rd_rel (RD_PLAN_KEEPS) and every control word it does not write      *)
(*     (PL_PLAN_CW_KEPT): the frame rule;                                   *)
(*   - the reader's leaves, which write only the state and their payload    *)
(*     word, keep plan_rel (RD_STEP_CUR, RD_STEP_LEB; PL_REL_AGREE).         *)
(* The reader's control words (17 CNT, 18 OPC, 20 HDR, 21 RST) are plan_rel's *)
(* control words.                                                            *)
(*                                                                           *)
(* The plans:                                                                *)
(*   dd              cur -> RST, leb_next -> OPC (DD_REL);                   *)
(*   pl_prefix_op0   eqw HDR K1 (the header seen), leb_next -> OP0           *)
(*                   (PREFIX_OP0_REL);                                       *)
(*   pl_inc_cnt      inc CNT -> CNT;                                         *)
(*   pl_handler_refl the prefix, REFL's plan, the increment                 *)
(*                   (HANDLER_REFL_REL), composed by DRV_SEM_APPEND, with   *)
(*                   REFL's plan renumbered to step 0 (DRV_SEM_AT0) for     *)
(*                   PL_REFL_REL.                                            *)
(* A dd plan that the input's end refuses keeps both relations, the cursor  *)
(* kept (DD_REL_REFUSED). Agreement on a set of addresses that covers what  *)
(* the relations read carries both of them (rel_reads).                      *)
(*                                                                           *)
(* Loaded after plans_rel.ml, in the audits' order (records.ml before it).  *)
(* ========================================================================= *)

needs "native/driver/driver_seq.ml";;
needs "native/leaves/reader_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The relation.                                                            *)
(* ------------------------------------------------------------------------- *)

(* The input bytes from offset c on. *)
let rd_from = new_definition
 `rd_from (inp:num list) c = list_of_seq (\j. EL (c + j) inp) (LENGTH inp - c)`;;

(* The reader's regions, the input (slot 54) and the state (slot 58): neither *)
(* wraps; they lie apart from each other, from every slot plan_rel reads,    *)
(* from the control words and from the driver's stack window; the state     *)
(* holds its two words.                                                      *)
let rd_layout = new_definition
 `rd_layout (bw:num->int64) (ctl:int64) nctl (cfr:int64) <=>
    val(bw 54) + val(bw 55) < 2 EXP 64 /\ val(bw 58) + val(bw 59) < 2 EXP 64 /\ 16 <= val(bw 59) /\
    drv_apart (bw 54) (val(bw 55)) (bw 58) (val(bw 59)) /\
    (!j. j = 54 \/ j = 58
         ==> drv_apart (bw j) (val(bw(j + 1))) ctl (8 * nctl) /\
             drv_apart (word_sub cfr (word 48)) 304 (bw j) (val(bw(j + 1))) /\
             (!j'. MEM j' pl_slots ==> drv_apart (bw j) (val(bw(j + 1))) (bw j') (val(bw(j' + 1)))))`;;

(* The input region holds the bytes inp; state word 0 is the cursor c. *)
let rd_rel = new_definition
 `rd_rel (bw:num->int64) (ctl:int64) nctl (cfr:int64) (m:int64->byte) (inp:num list) c <=>
    rd_layout bw ctl nctl cfr /\ LENGTH inp = val(bw 55) /\
    (!i. i < LENGTH inp ==> val(m(word_add (bw 54) (word i))) = EL i inp) /\
    pl_mw m (bw 58) 0 = c`;;

(* ------------------------------------------------------------------------- *)
(* Addresses.                                                               *)
(* ------------------------------------------------------------------------- *)

let DRV_APART_IN = prove
 (`!(a:int64) b1 n1 b2 n2.
     (drv_apart b1 n1 b2 n2 \/ drv_apart b2 n2 b1 n1) /\ drv_in a b1 n1 ==> ~drv_in a b2 n2`,
  REWRITE_TAC[drv_apart; drv_in] THEN ARITH_TAC);;

let DRV_CTL_WORD_IN = prove
 (`!(ctl:int64) nctl p a.
     val ctl + 8 * nctl <= 2 EXP 64 /\ p < nctl /\ drv_in a (word_add ctl (word(8 * p))) 8
     ==> drv_in a ctl (8 * nctl)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ctl:int64`; `8 * p`] TISA_VAL_OFFSET) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  UNDISCH_TAC `drv_in a (word_add ctl (word(8 * p))) 8` THEN ASM_REWRITE_TAC[drv_in] THEN
  ASM_ARITH_TAC);;

(* The layout's facts about each reader region. *)
let RD_LAYOUT_AT = prove
 (`!bw ctl nctl cfr. rd_layout bw ctl nctl cfr
     ==> (drv_apart (bw 54) (val(bw 55)) ctl (8 * nctl) /\
          drv_apart (word_sub cfr (word 48)) 304 (bw 54) (val(bw 55)) /\
          (!j'. MEM j' pl_slots ==> drv_apart (bw 54) (val(bw 55)) (bw j') (val(bw(j' + 1))))) /\
         (drv_apart (bw 58) (val(bw 59)) ctl (8 * nctl) /\
          drv_apart (word_sub cfr (word 48)) 304 (bw 58) (val(bw 59)) /\
          (!j'. MEM j' pl_slots ==> drv_apart (bw 58) (val(bw 59)) (bw j') (val(bw(j' + 1)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_layout] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `pl_slots`)) (concl th)
    then MP_TAC(SPEC `54` th) THEN MP_TAC(SPEC `58` th) else failwith "") THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[] THEN MESON_TAC[]);;

(* An address of the input or the state is not in the driver's stack       *)
(* window, a control word, the other reader region, or any slot plan_rel    *)
(* reads.                                                                    *)
let RD_ADDR_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RD_LAYOUT_AT) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  FIRST_ASSUM(fun th -> if is_const_app "drv_in" (concl th) then
     let [_; b; n] = snd(strip_comb(concl th)) in
     REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [b; n] THEN ASM_REWRITE_TAC[] THEN
       FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_layout]);
       MATCH_MP_TAC DRV_APART_IN THEN MAP_EVERY EXISTS_TAC [b; n] THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC DRV_APART_IN THEN MAP_EVERY EXISTS_TAC [b; n] THEN ASM_REWRITE_TAC[];
       X_GEN_TAC `j':num` THEN DISCH_TAC THEN MATCH_MP_TAC DRV_APART_IN THEN
       MAP_EVERY EXISTS_TAC [b; n] THEN ASM_SIMP_TAC[]]
     else failwith "");;

let RD_INP_ADDR = prove
 (`!bw ctl nctl cfr a.
     rd_layout bw ctl nctl cfr /\ pl_layout bw ctl nctl cfr /\ drv_in a (bw 54) (val(bw 55))
     ==> ~drv_stack cfr a /\ ~drv_in a ctl (8 * nctl) /\ ~drv_in a (bw 58) (val(bw 59)) /\
         (!j'. MEM j' pl_slots ==> ~drv_in a (bw j') (val(bw(j' + 1))))`,
  RD_ADDR_TAC);;

let RD_ST_ADDR = prove
 (`!bw ctl nctl cfr a.
     rd_layout bw ctl nctl cfr /\ pl_layout bw ctl nctl cfr /\ drv_in a (bw 58) (val(bw 59))
     ==> ~drv_stack cfr a /\ ~drv_in a ctl (8 * nctl) /\ ~drv_in a (bw 54) (val(bw 55)) /\
         (!j'. MEM j' pl_slots ==> ~drv_in a (bw j') (val(bw(j' + 1))))`,
  RD_ADDR_TAC);;

(* An address of a slot plan_rel reads, or of the control words, is in      *)
(* neither reader region.                                                    *)
let RD_SLOT_NOT_RD = prove
 (`!bw ctl nctl cfr j a.
     rd_layout bw ctl nctl cfr /\ MEM j pl_slots /\ drv_in a (bw j) (val(bw(j + 1)))
     ==> ~drv_in a (bw 54) (val(bw 55)) /\ ~drv_in a (bw 58) (val(bw 59))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RD_LAYOUT_AT) THEN
  CONJ_TAC THEN MATCH_MP_TAC DRV_APART_IN THEN
  MAP_EVERY EXISTS_TAC [`bw(j:num):int64`; `val(bw(j + 1):int64)`] THEN ASM_SIMP_TAC[]);;

let RD_CTL_NOT_RD = prove
 (`!bw ctl nctl cfr a.
     rd_layout bw ctl nctl cfr /\ drv_in a ctl (8 * nctl)
     ==> ~drv_in a (bw 54) (val(bw 55)) /\ ~drv_in a (bw 58) (val(bw 59))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RD_LAYOUT_AT) THEN
  CONJ_TAC THEN MATCH_MP_TAC DRV_APART_IN THEN
  MAP_EVERY EXISTS_TAC [`ctl:int64`; `8 * nctl`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Agreement.                                                               *)
(* ------------------------------------------------------------------------- *)

(* Memories that agree on the input and the state are related alike. *)
let RD_REL_AGREE = prove
 (`!bw ctl nctl cfr (m:int64->byte) m' inp c.
     rd_rel bw ctl nctl cfr m inp c /\
     (!a. drv_in a (bw 54) (val(bw 55)) \/ drv_in a (bw 58) (val(bw 59)) ==> m' a = m a)
     ==> rd_rel bw ctl nctl cfr m' inp c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_rel] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `m' (word_add (bw 54) (word i):int64) = (m:int64->byte) (word_add (bw 54) (word i))`
      SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN REWRITE_TAC[drv_in] THEN
      MP_TAC(SPECL [`bw 54:int64`; `i:num`] TISA_VAL_OFFSET) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
      ASM_SIMP_TAC[]];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && is_const_app "pl_mw" (lhs(concl th)))) THEN
    MATCH_MP_TAC PL_MW_REGION THEN EXISTS_TAC `val(bw 59:int64)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* plan_rel through a step that writes control word p and, outside the      *)
(* control words, nothing plan_rel reads.                                    *)
let PL_REL_AGREE = prove
 (`!bw ctl nctl cfr m m' cw ctx nms tys ntms dbs ths nmap ymap drops pol stk p v.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ p < nctl /\ 6 < p /\
     (!j a. MEM j pl_slots /\ drv_in a (bw j) (val(bw(j + 1))) ==> m' a = m a) /\
     (!a. drv_in a ctl (8 * nctl) /\ ~drv_in a (word_add ctl (word(8 * p))) 8 ==> m' a = m a) /\
     drv_word m' (word_add ctl (word(8 * p))) = v
     ==> plan_rel bw ctl nctl cfr m'
           (pl_set cw p (val v),(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[plan_rel] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY PL_SLOT_FACTS_TAC [`12`; `14`; `16`; `18`; `20`; `22`; `40`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_set] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC PL_CWORDS_SET THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_ITAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_ITAB_SLOTS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_ITAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_ITAB_SLOTS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_RTAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MARKS_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_RTAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MARKS_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_STK_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The child of a reader step: regions 0 and 1 bound to the input and the   *)
(* state; its cursor and its bytes from the cursor on are the relation's.   *)
(* ------------------------------------------------------------------------- *)

let RD_CHILD = prove
 (`!bw ctl nctl budget cfr st m used t inp c.
     drv_child bw ctl budget cfr st m used t /\ pl_layout bw ctl nctl cfr /\
     rd_rel bw ctl nctl cfr m inp c /\ val(EL 1 st) = 54 /\ val(EL 2 st) = 58
     ==> tisa_base t 0 = bw 54 /\ tisa_len t 0 = bw 55 /\ tisa_base t 1 = bw 58 /\ tisa_len t 1 = bw 59 /\
         pl_cursor t = c /\ region_from t 0 (pl_cursor t) = rd_from inp c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `drv_base`)) (concl th) then
     MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC `0` th)) THEN MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC `1` th))
     else failwith "") THEN
  ASM_REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!a. drv_in a (bw 54) (val(bw 55)) \/ drv_in a (bw 58) (val(bw 59)) ==> tmem t a = (m:int64->byte) a`
    ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
      check (fun th -> is_const_app "drv_child" (concl th))) THEN
    FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
       ASSUME_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)) else failwith "") THENL
     [MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] RD_INP_ADDR);
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] RD_ST_ADDR)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_rel] o
    check (fun th -> is_const_app "rd_rel" (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  SUBGOAL_THEN `pl_cursor t = c` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && is_const_app "pl_mw" (lhs(concl th)))) THEN
    REWRITE_TAC[pl_cursor; pl_w; pl_mw; tisa_read; GSYM drv_word] THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC DRV_WORD_AREA THEN EXISTS_TAC `val(bw 59:int64)` THEN
    REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[region_from; rd_from; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[region_byte; tisa_read; READ_BYTES_1] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `tmem t (word_add (bw 54) (word(c + n)):int64) = (m:int64->byte) (word_add (bw 54) (word(c + n)))`
    SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN REWRITE_TAC[drv_in] THEN
    MP_TAC(SPECL [`bw 54:int64`; `c + n:num`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `val((m:int64->byte) (word_add (bw 54) (word(c + n)))) < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(m:int64->byte) (word_add (bw 54) (word(c + n)))` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;
(* ------------------------------------------------------------------------- *)
(* The reader leaves' writable regions (a leaf's run keeps its regions:     *)
(* TISA_RUN_REGIONS, reader_spec.ml).                                        *)
(* ------------------------------------------------------------------------- *)

(* The reader leaves' writable regions. *)
let RD_RW_CASES_TAC decls_th =
  GEN_TAC THEN REWRITE_TAC[decls_th; tisa_rw; tisa_readable; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `r = 1` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[FST] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC;;

let CUR_RW = prove
 (`!r. ~tisa_rw (tisa_decls cur) r`, RD_RW_CASES_TAC CUR_DECLS);;
let LEB_NEXT_RW = prove
 (`!r. tisa_rw (tisa_decls leb_next) r <=> r = 1`, RD_RW_CASES_TAC LEB_NEXT_DECLS);;
let LEB_NEXT_READABLE = prove
 (`!r. tisa_readable (tisa_decls leb_next) r <=> r = 0 \/ r = 1`, RD_RW_CASES_TAC LEB_NEXT_DECLS);;
let INC_RW = prove
 (`!r. ~tisa_rw (tisa_decls inc) r`, REWRITE_TAC[INC_DECLS; tisa_rw; LENGTH] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The frame: a step whose writable regions are slots plan_rel reads keeps  *)
(* the reader's regions.                                                     *)
(* ------------------------------------------------------------------------- *)

let RD_STEP_KEEP = prove
 (`!prog bw ctl nctl budget cfr st m used t k u inp c.
     rd_rel bw ctl nctl cfr m inp c /\ pl_layout bw ctl nctl cfr /\
     drv_child bw ctl budget cfr st m used t /\ tisa_leaf_wf prog /\ tisa_entry_ok prog t /\
     tisa_run prog t = TStop k u /\ val(EL 17 st) < nctl /\
     (!r. tisa_rw (tisa_decls prog) r ==> MEM (val(EL (1 + r) st)) pl_slots)
     ==> !a. drv_in a (bw 54) (val(bw 55)) \/ drv_in a (bw 58) (val(bw 59)) ==> drv_after ctl st u a = m a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     ASSUME_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)) else failwith "") THEN
  SUBGOAL_THEN `~drv_stack cfr a /\ ~drv_in a ctl (8 * nctl) /\
                (!j'. MEM j' pl_slots ==> ~drv_in a (bw j') (val(bw(j' + 1))))` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] RD_INP_ADDR);
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] RD_ST_ADDR)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  MATCH_MP_TAC DRV_STEP_KEEPS THEN
  MAP_EVERY EXISTS_TAC [`prog:tisa_prog`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                        `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[drv_base; drv_len] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    UNDISCH_TAC `~drv_in (a:int64) ctl (8 * nctl)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC DRV_CTL_WORD_IN THEN EXISTS_TAC `val(EL 17 (st:int64 list))` THEN ASM_REWRITE_TAC[]]);;

let RD_STEP_RO = prove
 (`!prog bw ctl nctl budget cfr st m used t k u inp c.
     rd_rel bw ctl nctl cfr m inp c /\ pl_layout bw ctl nctl cfr /\
     drv_child bw ctl budget cfr st m used t /\ tisa_leaf_wf prog /\ tisa_entry_ok prog t /\
     tisa_run prog t = TStop k u /\ val(EL 17 st) < nctl /\ (!r. ~tisa_rw (tisa_decls prog) r)
     ==> rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RD_REL_AGREE THEN EXISTS_TAC `m:int64->byte` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RD_STEP_KEEP THEN
  MAP_EVERY EXISTS_TAC [`prog:tisa_prog`; `nctl:num`; `budget:int64`; `cfr:int64`; `used:int64`; `t:tisa_state`;
                        `k:num`; `inp:num list`; `c:num`] THEN
  ASM_REWRITE_TAC[]);;

(* The frame for a plan: its run keeps the reader's state when every step's *)
(* writable regions are slots plan_rel reads.                                *)
let rd_plan_ok = new_definition
 `rd_plan_ok (progs:num->tisa_prog) nctl (P:(int64 list)list) <=>
    !st. MEM st P ==> tisa_leaf_wf (progs (val(EL 0 st))) /\ val(EL 17 st) < nctl /\
                      (!r. tisa_rw (tisa_decls (progs (val(EL 0 st)))) r ==> MEM (val(EL (1 + r) st)) pl_slots)`;;

let RD_PLAN_KEEPS = prove
 (`!progs bw ctl nctl budget cfr P i m used res inp c.
     drv_sem progs bw ctl budget cfr P i m used res /\ rd_rel bw ctl nctl cfr m inp c /\
     pl_layout bw ctl nctl cfr /\ rd_plan_ok progs nctl P
     ==> rd_rel bw ctl nctl cfr (FST(SND(SND res))) inp c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_plan_ok] THEN STRIP_TAC THEN
  MATCH_MP_TAC RD_REL_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     ASSUME_TAC(CONJUNCT1(GEN_REWRITE_RULE I [rd_rel] th)) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `P:(int64 list)list`; `i:num`; `m:int64->byte`; `used:int64`;
                `res:int64#num#(int64->byte)#int64`] DRV_SEM_KEEPS) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(fun keeps -> X_GEN_TAC `a:int64` THEN DISCH_TAC THEN MATCH_MP_TAC keeps) THEN
  SUBGOAL_THEN `~drv_stack cfr a /\ ~drv_in a ctl (8 * nctl) /\
                (!j'. MEM j' pl_slots ==> ~drv_in a (bw j') (val(bw(j' + 1))))` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] RD_INP_ADDR);
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `a:int64`] RD_ST_ADDR)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[drv_base; drv_len] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~drv_in (a:int64) ctl (8 * nctl)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC DRV_CTL_WORD_IN THEN EXISTS_TAC `val(EL 17 (st:int64 list))` THEN ASM_MESON_TAC[]]);;

(* A control word no step of the plan writes keeps its value. *)
let PL_PLAN_CW_KEPT = prove
 (`!progs bw ctl nctl budget cfr P i m used res j.
     drv_sem progs bw ctl budget cfr P i m used res /\ pl_layout bw ctl nctl cfr /\ j < nctl /\
     rd_plan_ok progs nctl P /\ (!st. MEM st P ==> ~(val(EL 17 st) = j))
     ==> pl_mw (FST(SND(SND res))) ctl j = pl_mw m ctl j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_plan_ok] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `P:(int64 list)list`; `i:num`; `m:int64->byte`; `used:int64`;
                `res:int64#num#(int64->byte)#int64`] DRV_SEM_KEEPS) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[pl_mw] THEN AP_TERM_TAC THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `val(word_add (word_add ctl (word(8 * j))) (word q):int64) = val ctl + 8 * j + q` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_ADDR_VAL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `drv_in (word_add (word_add ctl (word(8 * j))) (word q)) ctl (8 * nctl)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_CTL_ADDR THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`; `ctl:int64`; `nctl:num`] THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[drv_base; drv_len] THEN
    SUBGOAL_THEN `MEM (val(EL (1 + r) (st:int64 list))) pl_slots` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `val(EL (1 + r) (st:int64 list))`]
                 PL_LAYOUT_SLOT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC DRV_APART_IN THEN MAP_EVERY EXISTS_TAC [`ctl:int64`; `8 * nctl`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(EL 17 (st:int64 list)) < nctl /\ ~(val(EL 17 st) = j)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`ctl:int64`; `8 * val(EL 17 (st:int64 list))`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ASM_REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC]);;
(* ------------------------------------------------------------------------- *)
(* One step of a reader leaf from related memory.                           *)
(* ------------------------------------------------------------------------- *)

(* A value that fires at offset c ends within the input. *)
let RD_FROM_FIRES_LE = prove
 (`!inp c v. leb_fires (rd_from inp c) v ==> c + LENGTH(leb_enc v) <= LENGTH inp`,
  REWRITE_TAC[leb_fires; rd_from] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:num list->num`) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_APPEND] THEN
  MP_TAC(SPEC `v:num` LEB_ENC_LENGTH_POS) THEN ARITH_TAC);;

(* The receipt word of a step's child is the receipt. *)
let DRV_CHILD_RECEIPT = prove
 (`!bw ctl budget cfr st m used t. drv_child bw ctl budget cfr st m used t ==> tisa_fword t 21 = used`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `21` o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child]) THEN
  REWRITE_TAC[drv_fw] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* leb_next writes only the state and the step's payload word. *)
let RD_LEB_KEEPS = prove
 (`!bw ctl nctl budget cfr st m used t k u a.
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok leb_next t /\ tisa_run leb_next t = TStop k u /\
     val(EL 2 st) = 58 /\ val ctl + 8 * nctl <= 2 EXP 64 /\ val(EL 17 st) < nctl /\
     ~drv_stack cfr a /\ ~drv_in a (bw 58) (val(bw 59)) /\
     ~drv_in a (word_add ctl (word(8 * val(EL 17 st)))) 8
     ==> drv_after ctl st u a = m a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
  MAP_EVERY EXISTS_TAC [`leb_next`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                        `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[LEB_NEXT_LEAF_WF; LEB_NEXT_RW] THEN
  X_GEN_TAC `r:num` THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* cur: FIRED with the cursor, which goes to the step's word; the reader's  *)
(* state and plan_rel kept.                                                  *)
let RD_STEP_CUR = prove
 (`!bw ctl nctl budget cfr st m used t k u cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok cur t /\ tisa_run cur t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st)
     ==> tisa_fword u 18 = word 1 /\ tisa_fword u 21 = used /\
         plan_rel bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) c,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
         rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [plan_rel] o
    check (fun th -> is_const_app "plan_rel" (concl th))) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DRV_CHILD_RECEIPT) THEN
  MP_TAC PL_CUR_SPEC THEN REWRITE_TAC[pl_cur_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `c = val(tisa_fword u 19)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[GSYM pl_cursor]; ALL_TAC] THEN
    MATCH_MP_TAC PL_REL_RO_STEP THEN
    MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `cur`; `1`] THEN
    ASM_REWRITE_TAC[CUR_LEAF_WF; CUR_RW];
    MATCH_MP_TAC RD_STEP_RO THEN
    MAP_EVERY EXISTS_TAC [`cur`; `budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`] THEN
    ASM_REWRITE_TAC[CUR_LEAF_WF; CUR_RW]]);;

(* leb_next: FIRED with the minimal LEB128 value at the cursor, which goes  *)
(* to the step's word, the cursor advanced past it; or REFUSED when there   *)
(* is none.                                                                   *)
let RD_STEP_LEB = prove
 (`!bw ctl nctl budget cfr st m used t k u cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok leb_next t /\ tisa_run leb_next t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         ((?v. leb_fires (rd_from inp c) v /\ tisa_fword u 18 = word 1 /\
               plan_rel bw ctl nctl cfr (drv_after ctl st u)
                 (pl_set cw (val(EL 17 st)) v,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp (c + LENGTH(leb_enc v))) \/
          ((!v. ~leb_fires (rd_from inp c) v) /\ tisa_fword u 18 = word 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [plan_rel] o
    check (fun th -> is_const_app "plan_rel" (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout] o
    check (fun th -> is_const_app "pl_layout" (concl th))) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DRV_CHILD_RECEIPT) THEN
  MP_TAC PL_LEB_NEXT_SPEC THEN REWRITE_TAC[pl_leb_next_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && is_const_app "region_from" (lhs(concl th))
                        then REWRITE_TAC[th] else failwith "") THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC o
    check (fun th -> is_disj(concl th))) THENL
   [ALL_TAC; DISJ2_TAC THEN ASM_REWRITE_TAC[]] THEN
  DISJ1_TAC THEN EXISTS_TAC `v:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RD_FROM_FIRES_LE) THEN
  SUBGOAL_THEN `v < 2 EXP 62` ASSUME_TAC THENL
   [ASM_MESON_TAC[leb_fires]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  (* What leb_next keeps: everything outside the state and the payload word. *)
  SUBGOAL_THEN `!a. ~drv_stack cfr a /\ ~drv_in a (bw 58) (val(bw 59)) /\
                    ~drv_in a (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8
                    ==> drv_after ctl st u a = (m:int64->byte) a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RD_LEB_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `used:int64`;
                          `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* plan_rel: only the state (apart from every slot) and the payload changed. *)
    SUBGOAL_THEN `v = val(tisa_fword u 19)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC(GSYM MOD_LT) THEN
      UNDISCH_TAC `v < 2 EXP 62` THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC PL_REL_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
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
      REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME] THEN ASM_REWRITE_TAC[]];
    (* rd_rel: the input kept; the cursor advanced. *)
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
      (* the cursor: the state's word 0 after the run, the payload elsewhere *)
      SUBGOAL_THEN `tisa_base u 1 = tisa_base t 1` ASSUME_TAC THENL
       [MP_TAC(SPECL [`leb_next`; `t:tisa_state`; `k:num`; `u:tisa_state`; `1`] TISA_RUN_REGIONS) THEN
        ASM_REWRITE_TAC[LEB_NEXT_LEAF_WF; LEB_NEXT_READABLE] THEN SIMP_TAC[];
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
(* eqw and inc, from related memory: no regions, so both relations are kept *)
(* with the payload in the step's word.                                      *)
(* ------------------------------------------------------------------------- *)

let NO_DECLS_RW = prove
 (`!r. ~tisa_rw [] r`, REWRITE_TAC[tisa_rw; LENGTH] THEN ARITH_TAC);;

(* The step's arguments under the relation. *)
let RD_CHILD_ARGS_TAC =
  FIRST_ASSUM(fun th -> if is_const_app "plan_rel" (concl th) then
     STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [plan_rel] th) else failwith "") THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

let RD_STEP_EQW = prove
 (`!bw ctl nctl budget cfr st m used t k u cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok eqw t /\ tisa_run eqw t = TStop k u /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         (if cw(val(EL 10 st)) = cw(val(EL 11 st))
          then tisa_fword u 18 = word 1 /\
               plan_rel bw ctl nctl cfr (drv_after ctl st u)
                 (pl_set cw (val(EL 17 st)) (cw(val(EL 10 st))),(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c
          else tisa_fword u 18 = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RD_CHILD_ARGS_TAC THEN
  MP_TAC PL_EQW_SPEC THEN REWRITE_TAC[pl_eqw_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `tisa_fword t 22 = tisa_fword t 23 <=>
                (cw:num->num)(val(EL 10 (st:int64 list))) = cw(val(EL 11 st))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM VAL_EQ]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun eq -> FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[eq] o check (is_cond o concl))) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(cw:num->num)(val(EL 11 (st:int64 list))) = val(tisa_fword u 19)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_REL_RO_STEP THEN
    MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `eqw`; `1`] THEN
    ASM_REWRITE_TAC[EQW_LEAF_WF; EQW_DECLS; NO_DECLS_RW] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    MATCH_MP_TAC RD_STEP_RO THEN
    MAP_EVERY EXISTS_TAC [`eqw`; `budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`] THEN
    ASM_REWRITE_TAC[EQW_LEAF_WF; EQW_DECLS; NO_DECLS_RW] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

let RD_STEP_INC = prove
 (`!bw ctl nctl budget cfr st m used t k u cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok inc t /\ tisa_run inc t = TStop k u /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tisa_fword u 21 = used /\
         (if cw(val(EL 10 st)) + 1 < 2 EXP 62
          then tisa_fword u 18 = word 1 /\
               plan_rel bw ctl nctl cfr (drv_after ctl st u)
                 (pl_set cw (val(EL 17 st)) (cw(val(EL 10 st)) + 1),(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
               rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c
          else tisa_fword u 18 = word 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RD_CHILD_ARGS_TAC THEN
  MP_TAC PL_INC_SPEC THEN REWRITE_TAC[pl_inc_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(cw:num->num)(val(EL 10 (st:int64 list))) + 1 = val(tisa_fword u 19)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `(cw:num->num)(val(EL 10 (st:int64 list))) + 1 < 2 EXP 62` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_REL_RO_STEP THEN
    MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `inc`; `1`] THEN
    ASM_REWRITE_TAC[INC_LEAF_WF; INC_RW] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    MATCH_MP_TAC RD_STEP_RO THEN
    MAP_EVERY EXISTS_TAC [`inc`; `budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`] THEN
    ASM_REWRITE_TAC[INC_LEAF_WF; INC_RW] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Step indices: a run's steps can be renumbered.                            *)
(* ------------------------------------------------------------------------- *)

let DRV_SEM_SHIFT = prove
 (`!progs bw ctl budget cfr P i d m used kk j mm uu.
     drv_sem progs bw ctl budget cfr P (i + d) m used (kk,j + d,mm,uu) <=>
     drv_sem progs bw ctl budget cfr P i m used (kk,j,mm,uu)`,
  REPLICATE_TAC 5 GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[drv_sem; PAIR_EQ; EQ_ADD_RCANCEL] THEN
  ASM_REWRITE_TAC[ARITH_RULE `(i + d) + 1 = (i + 1) + d`]);;

let DRV_SEM_INDEX_GE = prove
 (`!progs bw ctl budget cfr P i m used res.
     drv_sem progs bw ctl budget cfr P i m used res ==> i <= FST(SND res)`,
  REPLICATE_TAC 5 GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[drv_sem] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND; LE_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_sem] THEN
  COND_CASES_TAC THENL [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND; LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tc:tisa_state` (X_CHOOSE_THEN `kc:num` (X_CHOOSE_THEN `u:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`; `drv_after ctl h u`; `tisa_fword u 21`;
                                  `res:int64#num#(int64->byte)#int64`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `drv_sem`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND; LE_REFL]]);;

(* A run from step i is the run from step 0, renumbered. *)
let DRV_SEM_AT0 = prove
 (`!progs bw ctl budget cfr P i m used res.
     drv_sem progs bw ctl budget cfr P i m used res
     ==> ?r. drv_sem progs bw ctl budget cfr P 0 m used r /\
             FST r = FST res /\ FST(SND res) = FST(SND r) + i /\ SND(SND r) = SND(SND res)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DRV_SEM_INDEX_GE) THEN
  EXISTS_TAC `(FST res,FST(SND res) - i,SND(SND res)):int64#num#(int64->byte)#int64` THEN
  REWRITE_TAC[FST; SND] THEN CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`;
                `P:(int64 list)list`; `0`; `i:num`; `m:int64->byte`; `used:int64`;
                `FST(res:int64#num#(int64->byte)#int64)`; `FST(SND(res:int64#num#(int64->byte)#int64)) - i`;
                `FST(SND(SND(res:int64#num#(int64->byte)#int64)))`;
                `SND(SND(SND(res:int64#num#(int64->byte)#int64)))`] DRV_SEM_SHIFT) THEN
  ASM_SIMP_TAC[ADD_CLAUSES; SUB_ADD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The reader's plans (PLANS.txt, section 10).                              *)
(* ------------------------------------------------------------------------- *)

(* Leaves 25 cur, 26 leb_next, 32 inc; slots 54 the input, 58 the state;   *)
(* control words 17 CNT, 18 OPC, 20 HDR, 21 RST.                            *)
let pl_RD = [54; 58];;

(* dd: RST the cursor (the record's first byte), OPC the opcode [REFUSED     *)
(* when no minimal LEB128 lies at the cursor].                              *)
let pl_plan_dd = new_definition(mk_eq(`pl_plan_dd:(int64 list)list`,
  mk_list([pl_step 25 pl_RD 0 0 [] 21; pl_step 26 pl_RD 0 0 [] 18], `:int64 list`)));;

(* A record handler's prefix for one operand: the header seen [REFUSED      *)
(* otherwise], the operand to OP0 [REFUSED when no minimal LEB128 lies at    *)
(* the cursor]; and its suffix, the count's increment.                       *)
let pl_prefix_op0 = new_definition(mk_eq(`pl_prefix_op0:(int64 list)list`,
  mk_list([pl_step 3 [] 20 1 [] 24; pl_step 26 pl_RD 0 0 [] 8], `:int64 list`)));;
let pl_inc_cnt = new_definition(mk_eq(`pl_inc_cnt:(int64 list)list`,
  mk_list([pl_step 32 [] 17 0 [] 17], `:int64 list`)));;

(* REFL's handler. *)
let pl_handler_refl = new_definition
 `pl_handler_refl = APPEND pl_prefix_op0 (APPEND pl_plan_refl pl_inc_cnt)`;;

(* The reader's leaves in the host's leaf table. *)
let rd_progs_ok = new_definition
 `rd_progs_ok (progs:num->tisa_prog) <=> progs 25 = cur /\ progs 26 = leb_next /\ progs 32 = inc`;;

(* The facts of a literal step. *)
let STEP_EL_CONV = DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV;;
(* ------------------------------------------------------------------------- *)
(* Facts of literal steps and plans.                                         *)
(* ------------------------------------------------------------------------- *)

let STEP_EL_CONV2 = NUM_REDUCE_CONV THENC STEP_EL_CONV;;

let RW_CASES_TAC decls_th =
  GEN_TAC THEN REWRITE_TAC[decls_th; tisa_rw; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r = 1` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r = 2` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[FST] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC;;

let INTERN16_RW = prove
 (`!r. tisa_rw (tisa_decls intern16) r <=> r = 0 \/ r = 1 \/ r = 2`, RW_CASES_TAC INTERN16_DECLS);;
let APPEND_ROW_RW = prove
 (`!r. tisa_rw (tisa_decls append_row) r <=> r = 0 \/ r = 1`, RW_CASES_TAC APPEND_ROW_DECLS);;
let ROW_WORD_RW = prove
 (`!r. ~tisa_rw (tisa_decls row_word) r`, RW_CASES_TAC ROW_WORD_DECLS);;
let LIVE_RW = prove
 (`!r. ~tisa_rw (tisa_decls live) r`, RW_CASES_TAC LIVE_DECLS);;
let PACK_RW = prove
 (`!r. ~tisa_rw (tisa_decls pack) r`, REWRITE_TAC[PACK_DECLS; NO_DECLS_RW]);;
let UNPACK_RW = prove
 (`!r. ~tisa_rw (tisa_decls unpack) r`, REWRITE_TAC[UNPACK_DECLS; NO_DECLS_RW]);;
let EQW_RW = prove
 (`!r. ~tisa_rw (tisa_decls eqw) r`, REWRITE_TAC[EQW_DECLS; NO_DECLS_RW]);;

let PL_LEAVES_WF = [INTERN16_LEAF_WF; PACK_LEAF_WF; UNPACK_LEAF_WF; EQW_LEAF_WF; ROW_WORD_LEAF_WF;
                    LIVE_LEAF_WF; APPEND_ROW_LEAF_WF];;
let PL_LEAVES_RW = [INTERN16_RW; APPEND_ROW_RW; ROW_WORD_RW; LIVE_RW; PACK_RW; UNPACK_RW; EQW_RW];;

(* A record plan's steps write only slots plan_rel reads, by computation on  *)
(* the plan's data under the host's leaf table.                              *)
let RD_PLAN_OK_TAC plan_def =
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_progs_ok; pl_cw_range; rd_plan_ok] THEN STRIP_TAC THEN
  X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(EL 17 (st:int64 list)) < nctl` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "MEM" (concl th))) THEN
  REWRITE_TAC[plan_def; MEM] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC)) THEN TRY(DISCH_THEN SUBST1_TAC) THEN
  CONV_TAC STEP_EL_CONV2 THEN ASM_REWRITE_TAC(PL_LEAVES_WF @ PL_LEAVES_RW) THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`; FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  CONV_TAC STEP_EL_CONV2 THEN REWRITE_TAC[pl_slots; MEM] THEN CONV_TAC NUM_REDUCE_CONV;;

let RD_PLAN_OK_REFL = prove
 (`!progs nctl. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_refl ==> rd_plan_ok progs nctl pl_plan_refl`,
  RD_PLAN_OK_TAC pl_plan_refl);;

(* REFL's plan writes only temporaries. *)
let REFL_PAYLOADS = prove
 (`!st. MEM st pl_plan_refl ==> 24 <= val(EL 17 st)`,
  GEN_TAC THEN REWRITE_TAC[pl_plan_refl; MEM] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC)) THEN TRY(DISCH_THEN SUBST1_TAC) THEN
  CONV_TAC STEP_EL_CONV2);;

(* The invariant does not see control words above 6. *)
let PL_INV_SET = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk j v.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ 6 < j
     ==> pl_inv (pl_set cw j v,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`,
  REWRITE_TAC[pl_inv; pl_set] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]]);;

(* A control word below nctl, read through the relation. *)
let PL_REL_CW = prove
 (`!bw ctl nctl cfr m s j. plan_rel bw ctl nctl cfr m s /\ j < nctl ==> pl_mw m ctl j = FST s j`,
  REWRITE_TAC[FORALL_PAIR_THM; plan_rel; pl_cwords; FST] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The decode plan.                                                          *)
(* ------------------------------------------------------------------------- *)

let RD_NS_VARS = [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`;
                  `dbs:(num#num#num)list`; `ths:(num#num)list`; `nmap:num list`; `ymap:num list`;
                  `drops:(num#num)list`; `pol:num`; `stk:num list`];;

let pl_plan_dd_st1 = el 0 (dest_list(rhs(concl pl_plan_dd)))
and pl_plan_dd_st2 = el 1 (dest_list(rhs(concl pl_plan_dd)));;

let DD_REL = prove
 (`!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     rd_progs_ok progs /\ 21 < nctl /\
     drv_sem progs bw ctl budget cfr pl_plan_dd i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1 <=> ?op. leb_fires (rd_from inp c) op) /\
         (FST r = word 0 <=> !op. ~leb_fires (rd_from inp c) op) /\
         (FST r = word 1
          ==> ?op. leb_fires (rd_from inp c) op /\
                   plan_rel bw ctl nctl cfr (FST(SND(SND r)))
                     (pl_set (pl_set cw 21 c) 18 op,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
                   rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + LENGTH(leb_enc op)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_progs_ok] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_plan_dd; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_plan_dd_st1;
                 `m:int64->byte`; `used:int64`; `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`] @
                RD_NS_VARS @ [`inp:num list`; `c:num`]) RD_STEP_CUR) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_plan_dd_st2;
                 list_mk_comb(`drv_after`, [`ctl:int64`; pl_plan_dd_st1; `u1:tisa_state`]);
                 `used:int64`; `t2:tisa_state`; `k2:num`; `u2:tisa_state`; `pl_set cw 21 c`] @
                RD_NS_VARS @ [`inp:num list`; `c:num`]) RD_STEP_LEB) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A record handler's prefix for one operand.                                *)
(* ------------------------------------------------------------------------- *)

let pl_prefix_op0_st1 = el 0 (dest_list(rhs(concl pl_prefix_op0)))
and pl_prefix_op0_st2 = el 1 (dest_list(rhs(concl pl_prefix_op0)));;

let STEP_RANGE_TAC =
  REWRITE_TAC[ARITH_RULE `10 <= f /\ f < 18 <=> f = 10 \/ f = 11 \/ f = 12 \/ f = 13 \/ f = 14 \/
                                               f = 15 \/ f = 16 \/ f = 17`] THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`; FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  CONV_TAC STEP_EL_CONV2 THEN ASM_ARITH_TAC;;

let PREFIX_OP0_REL = prove
 (`!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     progs 3 = eqw /\ rd_progs_ok progs /\ 24 < nctl /\
     drv_sem progs bw ctl budget cfr pl_prefix_op0 i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> SND(SND(SND r)) = used /\
         (FST r = word 1 <=> cw 20 = 1 /\ ?t. leb_fires (rd_from inp c) t) /\
         (FST r = word 0 <=> ~(cw 20 = 1 /\ ?t. leb_fires (rd_from inp c) t)) /\
         (FST r = word 1
          ==> ?t. leb_fires (rd_from inp c) t /\
                  plan_rel bw ctl nctl cfr (FST(SND(SND r)))
                    (pl_set (pl_set cw 24 1) 8 t,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
                  rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + LENGTH(leb_enc t)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_progs_ok] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cw:num->num) 1 = 1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "plan_rel" (concl th))) THEN
    REWRITE_TAC[plan_rel] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_prefix_op0; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_prefix_op0_st1;
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
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_prefix_op0_st2;
                 list_mk_comb(`drv_after`, [`ctl:int64`; pl_prefix_op0_st1; `u1:tisa_state`]);
                 `used:int64`; `t2:tisa_state`; `k2:num`; `u2:tisa_state`; `pl_set cw 24 1`] @
                RD_NS_VARS @ [`inp:num list`; `c:num`]) RD_STEP_LEB) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* REFL's plan inside a handler: from any step index, the reader's state    *)
(* kept and the control words below 24 kept.                                 *)
(* ------------------------------------------------------------------------- *)

let REFL_IN_HANDLER = prove
 (`!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c t.
     pl_progs_ok progs /\ pl_cw_range nctl pl_plan_refl /\ 24 < nctl /\
     drv_sem progs bw ctl budget cfr pl_plan_refl i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used) /\ cw 8 = t
     ==> rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp c /\
         (FST r = word 1
          ==> ?s'. nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t) (FST(SND s')) /\
                   pl_inv s' /\ plan_rel bw ctl nctl cfr (FST(SND(SND r))) s' /\
                   (!j. j < 24 ==> FST s' j = cw j)) /\
         (FST r = word 0 <=>
          ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t) /\
            ?tm. fdtm nms tys ntms t tm))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [plan_rel] o
    check (fun th -> is_const_app "plan_rel" (concl th))) THEN
  SUBGOAL_THEN `rd_plan_ok progs nctl pl_plan_refl` ASSUME_TAC THENL
   [MATCH_MP_TAC RD_PLAN_OK_REFL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RD_PLAN_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`progs:num->tisa_prog`; `budget:int64`; `pl_plan_refl`; `i:num`;
                          `m:int64->byte`; `used:int64`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `r0:int64#num#(int64->byte)#int64` STRIP_ASSUME_TAC o MATCH_MP DRV_SEM_AT0 o
    check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  MP_TAC(SPECL ([`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                 `cfr:int64`; `m:int64->byte`; `used:int64`; `r0:int64#num#(int64->byte)#int64`;
                 `cw:num->num`] @ RD_NS_VARS @ [`t:num`]) PL_REFL_REL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FST(SND(SND(r0:int64#num#(int64->byte)#int64))) = FST(SND(SND(r:int64#num#(int64->byte)#int64)))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s':pstate` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`;
                `FST(SND(SND(r:int64#num#(int64->byte)#int64)))`; `s':pstate`; `j:num`] PL_REL_CW) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `m:int64->byte`;
                `(cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate`; `j:num`] PL_REL_CW) THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `pl_plan_refl`; `i:num`; `m:int64->byte`; `used:int64`;
                `r:int64#num#(int64->byte)#int64`; `j:num`] PL_PLAN_CW_KEPT) THEN
  ASM_REWRITE_TAC[FST] THEN
  SUBGOAL_THEN `j < nctl` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `st:int64 list` THEN DISCH_THEN(MP_TAC o MATCH_MP REFL_PAYLOADS) THEN ASM_ARITH_TAC;
    MESON_TAC[]]);;
(* ------------------------------------------------------------------------- *)
(* REFL's handler: the header checked, the operand read to OP0, REFL's plan, *)
(* the count incremented. When it FIRES, the operand was the minimal LEB128  *)
(* at the cursor, the record's nat_step holds, both relations hold after it *)
(* with the cursor past the operand, the count is one more, and no other     *)
(* control word below 24 but OP0 changed. It is REFUSED exactly when the     *)
(* header is not checked, no operand lies at the cursor, or REFL's clause    *)
(* refuses that operand.                                                     *)
(* ------------------------------------------------------------------------- *)

let WORD_SMALL_NE = prove
 (`~(word 1:int64 = word 0) /\ ~(word 3:int64 = word 0) /\ ~(word 3:int64 = word 1) /\
   ~(word 2:int64 = word 0) /\ ~(word 2:int64 = word 1)`,
  CONV_TAC WORD_REDUCE_CONV);;

let rec RD_CHOOSE_ALL vs ttac =
  match vs with [] -> ttac | v::rest -> X_CHOOSE_THEN v (RD_CHOOSE_ALL rest ttac);;

let RD_S2_VARS = [`cw2:num->num`; `ctx2:hupdate list`; `nms2:string list`; `tys2:(num#num#num)list`;
                  `ntms2:(num#num#num#num#num)list`; `dbs2:(num#num#num)list`; `ths2:(num#num)list`;
                  `nmap2:num list`; `ymap2:num list`; `drops2:(num#num)list`; `pol2:num`; `stk2:num list`];;

let pl_inc_cnt_st = el 0 (dest_list(rhs(concl pl_inc_cnt)));;

let HANDLER_REFL_REL = prove
 (`!progs bw ctl nctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     pl_progs_ok progs /\ rd_progs_ok progs /\ pl_cw_range nctl pl_plan_refl /\ 24 < nctl /\
     drv_sem progs bw ctl budget cfr pl_handler_refl 0 m used res /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> (FST res = word 1
          ==> ?t s'. cw 20 = 1 /\ leb_fires (rd_from inp c) t /\
                     nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t) (FST(SND s')) /\
                     pl_inv s' /\ plan_rel bw ctl nctl cfr (FST(SND(SND res))) s' /\
                     rd_rel bw ctl nctl cfr (FST(SND(SND res))) inp (c + LENGTH(leb_enc t)) /\
                     FST s' 17 = cw 17 + 1 /\
                     (!j. j < 24 /\ ~(j = 8) /\ ~(j = 17) ==> FST s' j = cw j)) /\
         (FST res = word 0 <=>
          ~(cw 20 = 1) \/ (!t. ~leb_fires (rd_from inp c) t) \/
          (?t. leb_fires (rd_from inp c) t /\
               ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t) /\
                 ?tm. fdtm nms tys ntms t tm)))`,
  let r1 = `r1:int64#num#(int64->byte)#int64` and r2 = `r2:int64#num#(int64->byte)#int64` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `progs 3 = eqw` ASSUME_TAC THENL [ASM_MESON_TAC[pl_progs_ok]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_handler_refl; DRV_SEM_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN r1 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(SPECL ([`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                 `0`; `m:int64->byte`; `used:int64`; r1; `cw:num->num`] @ RD_NS_VARS @
                [`inp:num list`; `c:num`]) PREFIX_OP0_REL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `FST(r1:int64#num#(int64->byte)#int64) = word 1` THENL
   [(* The prefix FIRED: the header checked, the operand t read. *)
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) && is_eq(lhand(concl th)) then
       X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC
         (MP th (ASSUME `FST(r1:int64#num#(int64->byte)#int64) = word 1`))
     else failwith "") THEN
    SUBGOAL_THEN `(cw:num->num) 20 = 1` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `FST(r1:int64#num#(int64->byte)#int64) = word 1`;
                ASSUME `SND(SND(SND(r1:int64#num#(int64->byte)#int64))) = used`] THEN
    DISCH_THEN(X_CHOOSE_THEN r2 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MP_TAC(SPECL ([`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                   `0 + LENGTH pl_prefix_op0`; `FST(SND(SND(r1:int64#num#(int64->byte)#int64)))`; `used:int64`;
                   r2; `pl_set (pl_set cw 24 1) 8 t`] @ RD_NS_VARS @
                  [`inp:num list`; `c + LENGTH(leb_enc t)`; `t:num`]) REFL_IN_HANDLER) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC PL_INV_SET THEN CONJ_TAC THENL
         [MATCH_MP_TAC PL_INV_SET THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ARITH_TAC];
        REWRITE_TAC[pl_set]];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    ASM_CASES_TAC `FST(r2:int64#num#(int64->byte)#int64) = word 1` THENL
     [(* REFL's plan FIRED: its final state, then the count's increment. *)
      FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can (find_term ((=) `RRefl t`)) (concl th) then
         MP_TAC(REWRITE_RULE[EXISTS_PAIR_THM]
           (MP th (ASSUME `FST(r2:int64#num#(int64->byte)#int64) = word 1`)))
       else failwith "") THEN
      REWRITE_TAC[FST; SND] THEN DISCH_THEN(RD_CHOOSE_ALL RD_S2_VARS STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[ASSUME `FST(r2:int64#num#(int64->byte)#int64) = word 1`] THEN
      REWRITE_TAC[pl_inc_cnt; drv_sem] THEN CONV_TAC STEP_EL_CONV THEN
      ASM_CASES_TAC `val(budget:int64) < val(SND(SND(SND(r2:int64#num#(int64->byte)#int64))))` THEN
      ASM_REWRITE_TAC[] THENL
       [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; WORD_SMALL_NE] THEN
        ASM_MESON_TAC[LEB_FIRES_UNIQUE; WORD_SMALL_NE];
        ALL_TAC] THEN
      SUBGOAL_THEN `progs 32 = inc` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[rd_progs_ok]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t3:tisa_state` (X_CHOOSE_THEN `k3:num` (X_CHOOSE_THEN `u3:tisa_state`
        STRIP_ASSUME_TAC))) THEN
      MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_inc_cnt_st;
                     `FST(SND(SND(r2:int64#num#(int64->byte)#int64)))`;
                     `SND(SND(SND(r2:int64#num#(int64->byte)#int64)))`;
                     `t3:tisa_state`; `k3:num`; `u3:tisa_state`] @ RD_S2_VARS @
                    [`inp:num list`; `c + LENGTH(leb_enc t)`]) RD_STEP_INC) THEN
      CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(cw2:num->num) 17 = cw 17` ASSUME_TAC THENL
       [FIRST_ASSUM(MP_TAC o SPEC `17` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `cw2:num->num`)) (concl th))) THEN
        REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(cw:num->num) 17 + 1 < 4611686018427387904` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th) &&
         can (find_term ((=) `res:int64#num#(int64->byte)#int64`)) (concl th))) THEN
      ASM_REWRITE_TAC[WORD_SMALL_NE] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND; WORD_SMALL_NE] THENL
       [CONJ_TAC THENL
         [EXISTS_TAC `t:num` THEN
          EXISTS_TAC `(pl_set cw2 17 (cw 17 + 1),(ctx2,nms2,tys2,ntms2,dbs2,ths2,nmap2,ymap2,drops2,pol2),
                       stk2):pstate` THEN
          ASM_REWRITE_TAC[FST; SND] THEN CONJ_TAC THENL
           [MATCH_MP_TAC PL_INV_SET THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          CONJ_TAC THENL [REWRITE_TAC[pl_set]; ALL_TAC] THEN
          X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[pl_set] THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `~(j = 24)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `cw2:num->num`)) (concl th))) THEN
          REWRITE_TAC[pl_set] THEN ASM_REWRITE_TAC[];
          ASM_MESON_TAC[LEB_FIRES_UNIQUE; WORD_SMALL_NE]];
        ASM_MESON_TAC[LEB_FIRES_UNIQUE; WORD_SMALL_NE]];
      (* REFL's plan did not FIRE: the handler's outcome is the plan's. *)
      REWRITE_TAC[ASSUME `~(FST(r2:int64#num#(int64->byte)#int64) = word 1)`] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LEB_FIRES_UNIQUE; WORD_SMALL_NE]];
    (* The prefix did not FIRE: the handler's outcome is the prefix's. *)
    REWRITE_TAC[ASSUME `~(FST(r1:int64#num#(int64->byte)#int64) = word 1)`] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A REFUSED leb_next, and so a REFUSED dd plan. leb_next refuses without a *)
(* store, so the memory after the step is the entry memory with the payload *)
(* word written; both relations hold of it, the cursor kept. This is the    *)
(* record loop's final memory when the input's end refuses a decode.        *)
(* ------------------------------------------------------------------------- *)

let RD_STEP_LEB_REFUSED = prove
 (`!bw ctl nctl budget cfr st m used t k u cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok leb_next t /\ tisa_run leb_next t = TStop k u /\
     val(EL 1 st) = 54 /\ val(EL 2 st) = 58 /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st) /\
     ~(tisa_fword u 18 = word 1)
     ==> plan_rel bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
         rd_rel bw ctl nctl cfr (drv_after ctl st u) inp c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [plan_rel] o
    check (fun th -> is_const_app "plan_rel" (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout] o
    check (fun th -> is_const_app "pl_layout" (concl th))) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `inp:num list`; `c:num`] RD_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC PL_LEB_NEXT_SPEC THEN REWRITE_TAC[pl_leb_next_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])))
    (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN
  (* FIRED would leave status 1 *)
  FIRST_X_ASSUM(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC o
    check (fun th -> is_disj(concl th))) THENL
   [UNDISCH_TAC `~(tisa_fword u 18 = word 1)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) then
     STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rd_layout]) THEN
  (* What leb_next keeps: everything outside the state and the payload word. *)
  SUBGOAL_THEN `!a. ~drv_stack cfr a /\ ~drv_in a (bw 58) (val(bw 59)) /\
                    ~drv_in a (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8
                    ==> drv_after ctl st u a = (m:int64->byte) a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RD_LEB_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `used:int64`;
                          `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* plan_rel: only the state (apart from every slot) and the payload changed. *)
    MATCH_MP_TAC PL_REL_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
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
    (* rd_rel: the input and the cursor kept. *)
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
      (* the cursor: the state's word 0 after the run is the one before *)
      SUBGOAL_THEN `tisa_base u 1 = tisa_base t 1` ASSUME_TAC THENL
       [MP_TAC(SPECL [`leb_next`; `t:tisa_state`; `k:num`; `u:tisa_state`; `1`] TISA_RUN_REGIONS) THEN
        ASM_REWRITE_TAC[LEB_NEXT_LEAF_WF; LEB_NEXT_READABLE] THEN SIMP_TAC[];
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
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `pl_cursor t` then
        MP_TAC th else failwith "") THEN
      REWRITE_TAC[pl_cursor]]]);;

let DD_REL_REFUSED = prove
 (`!progs bw ctl nctl budget cfr i m used r cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     rd_progs_ok progs /\ 21 < nctl /\
     drv_sem progs bw ctl budget cfr pl_plan_dd i m used r /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used) /\ ~(FST r = word 1)
     ==> ?v. plan_rel bw ctl nctl cfr (FST(SND(SND r)))
               (pl_set (pl_set cw 21 c) 18 v,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
             rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rd_progs_ok] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[pl_plan_dd; drv_sem] THEN ASM_REWRITE_TAC[] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_plan_dd_st1;
                 `m:int64->byte`; `used:int64`; `t1:tisa_state`; `k1:num`; `u1:tisa_state`; `cw:num->num`] @
                RD_NS_VARS @ [`inp:num list`; `c:num`]) RD_STEP_CUR) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  ASM_CASES_TAC `tisa_fword u2 18 = word 1` THEN ASM_REWRITE_TAC[] THENL
   [(* FIRED: the plan would end with outcome 1 *)
    DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
    FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`));
    (* REFUSED at leb_next: the step's memory *)
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN
    EXISTS_TAC `val(tisa_fword u2 19)` THEN
    MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_plan_dd_st2;
                   list_mk_comb(`drv_after`, [`ctl:int64`; pl_plan_dd_st1; `u1:tisa_state`]);
                   `used:int64`; `t2:tisa_state`; `k2:num`; `u2:tisa_state`; `pl_set cw 21 c`] @
                  RD_NS_VARS @ [`inp:num list`; `c:num`]) RD_STEP_LEB_REFUSED) THEN
    CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The relations under agreement. plan_rel reads only its slots and the     *)
(* control words (PL_REL_SAME: PL_REL_AGREE with control word 7 written     *)
(* with its own value); rd_rel reads only the input and the state           *)
(* (RD_REL_AGREE). A set of addresses R covering what both read is a frame  *)
(* for both: rel_reads.                                                      *)
(* ------------------------------------------------------------------------- *)

let PL_SET_SAME = prove
 (`!(f:num->num) p. pl_set f p (f p) = f`,
  REWRITE_TAC[pl_set; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let PL_REL_SAME = prove
 (`!bw ctl nctl cfr m m' cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ 7 < nctl /\
     (!j a. MEM j pl_slots /\ drv_in a (bw j) (val(bw(j + 1))) ==> m' a = m a) /\
     (!a. drv_in a ctl (8 * nctl) ==> m' a = m a)
     ==> plan_rel bw ctl nctl cfr m' (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [plan_rel] o
    check (fun th -> is_const_app "plan_rel" (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout] o
    check (fun th -> is_const_app "pl_layout" (concl th))) THEN
  (* control word 7 reads the same from both memories, and is cw 7 *)
  SUBGOAL_THEN `val(drv_word (m':int64->byte) (word_add ctl (word(8 * 7)))) = (cw:num->num) 7` ASSUME_TAC THENL
   [SUBGOAL_THEN `drv_word (m':int64->byte) (word_add ctl (word(8 * 7))) = drv_word m (word_add ctl (word(8 * 7)))`
      SUBST1_TAC THENL
     [MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC DRV_IN_OFFSET THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM pl_mw] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[pl_cwords] o check (fun th -> is_const_app "pl_cwords" (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_set (cw:num->num) 7 (val(drv_word (m':int64->byte) (word_add ctl (word(8 * 7))))) = cw`
    (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
   [ASM_REWRITE_TAC[PL_SET_SAME]; ALL_TAC] THEN
  MATCH_MP_TAC PL_REL_AGREE THEN EXISTS_TAC `m:int64->byte` THEN
  ASM_SIMP_TAC[ARITH_RULE `6 < 7`] THEN FIRST_ASSUM ACCEPT_TAC);;

let rel_reads = new_definition
 `rel_reads bw ctl nctl cfr (R:int64->bool) <=>
    !M M'. (!a. R a ==> M' a = M a)
           ==> (!s. plan_rel bw ctl nctl cfr M s ==> plan_rel bw ctl nctl cfr M' s) /\
               (!inp c. rd_rel bw ctl nctl cfr M inp c ==> rd_rel bw ctl nctl cfr M' inp c)`;;

let REL_READS_PLAN = prove
 (`!bw ctl nctl cfr R M M' s.
     rel_reads bw ctl nctl cfr R /\ (!a. R a ==> M' a = M a) /\ plan_rel bw ctl nctl cfr M s
     ==> plan_rel bw ctl nctl cfr M' s`,
  REWRITE_TAC[rel_reads] THEN MESON_TAC[]);;

let REL_READS_RD = prove
 (`!bw ctl nctl cfr R M M' inp c.
     rel_reads bw ctl nctl cfr R /\ (!a. R a ==> M' a = M a) /\ rd_rel bw ctl nctl cfr M inp c
     ==> rd_rel bw ctl nctl cfr M' inp c`,
  REWRITE_TAC[rel_reads] THEN MESON_TAC[]);;

(* A byte below 128 at the head of a list is the one LEB128 value there. *)
let LEB_FIRES_BYTE = prove
 (`!b rest v. b < 128 /\ leb_fires (CONS b rest) v ==> v = b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LEB_FIRES_UNIQUE THEN
  EXISTS_TAC `CONS (b:num) rest` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[leb_fires] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `rest:num list` THEN ONCE_REWRITE_TAC[leb_enc_def] THEN
  ASM_REWRITE_TAC[APPEND]);;

let LEB_ENC_LEN_SMALL = prove
 (`!b. b < 128 ==> LENGTH (leb_enc b) = 1`,
  REWRITE_TAC[LEB_ENC_LENGTH_1]);;

(* The input left at a cursor, evaluated (a literal list, a numeral cursor). *)
let RD_FROM_CONV =
  REWRITE_CONV[rd_from; LENGTH] THENC NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV LIST_OF_SEQ_CONV THENC
  DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV THENC DEPTH_CONV EL_CONV;;

let RD_FROM_EVAL_CONV tm =
  match tm with
    Comb(Comb(Const("rd_from",_),_),_) -> RD_FROM_CONV tm
  | _ -> failwith "RD_FROM_EVAL_CONV";;

let reader_rel_theorems =
 ["RD_CHILD", RD_CHILD; "RD_REL_AGREE", RD_REL_AGREE; "PL_REL_AGREE", PL_REL_AGREE;
  "RD_STEP_KEEP", RD_STEP_KEEP; "RD_STEP_RO", RD_STEP_RO; "RD_PLAN_KEEPS", RD_PLAN_KEEPS;
  "PL_PLAN_CW_KEPT", PL_PLAN_CW_KEPT; "RD_STEP_CUR", RD_STEP_CUR; "RD_STEP_LEB", RD_STEP_LEB;
  "RD_STEP_EQW", RD_STEP_EQW; "RD_STEP_INC", RD_STEP_INC; "DRV_SEM_SHIFT", DRV_SEM_SHIFT;
  "DRV_SEM_INDEX_GE", DRV_SEM_INDEX_GE; "DRV_SEM_AT0", DRV_SEM_AT0; "RD_PLAN_OK_REFL", RD_PLAN_OK_REFL;
  "REFL_PAYLOADS", REFL_PAYLOADS; "PL_INV_SET", PL_INV_SET; "DD_REL", DD_REL;
  "PREFIX_OP0_REL", PREFIX_OP0_REL; "REFL_IN_HANDLER", REFL_IN_HANDLER;
  "HANDLER_REFL_REL", HANDLER_REFL_REL; "RD_STEP_LEB_REFUSED", RD_STEP_LEB_REFUSED;
  "DD_REL_REFUSED", DD_REL_REFUSED; "PL_SET_SAME", PL_SET_SAME; "PL_REL_SAME", PL_REL_SAME;
  "REL_READS_PLAN", REL_READS_PLAN; "REL_READS_RD", REL_READS_RD; "LEB_FIRES_BYTE", LEB_FIRES_BYTE;
  "LEB_ENC_LEN_SMALL", LEB_ENC_LEN_SMALL];;
