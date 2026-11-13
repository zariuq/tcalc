(* ========================================================================= *)
(* plan_rel: the memory of a plan's run represents the abstract state of the *)
(* record plans (plans_abs.ml), and each built leaf implements its abstract  *)
(* semantics under it (pl_impl, plans_drv.ml): the bridges that discharge  *)
(* LEDGER.txt part 4's LEAF_<name> premises.                                *)
(*                                                                           *)
(* plan_rel bw ctl nctl cfr m s: the layout (every region the relation reads *)
(* lies apart from the others, from the control words and from the driver's *)
(* stack window at cfr); control words 0 .. 6 hold 0 .. 6 and the control    *)
(* words are cw; the type and de Bruijn interners (slots 0, 2, 4 and 6, 8,   *)
(* 10) are well-formed intern16 tables holding the rows; the term rows (12,  *)
(* count 14, marks 16) and theorem rows (18, count 20, marks 22) hold the    *)
(* rows, a mark being 0 exactly for a live id; the operand stack (40) holds  *)
(* the stack. A FIRED step's memory is related to the abstract state after  *)
(* the step: PL_REL_RO_STEP for the read-only leaves, PL_REL_APPEND_TH and   *)
(* PL_REL_ITAB_TY / _DB for the writing ones.                                *)
(*                                                                           *)
(* Bridges (PL_IMPL_<leaf>_<table>): from the leaves' functional theorems    *)
(* (intern16: INTERN16_TISA_RUN_COMPLETE, _APPEND_ABSENT, TISA_RUN_STATUS; *)
(* pack, unpack, eqw, row_word, live, append_row: leaves_spec.ml's          *)
(* PL_<LEAF>_SPEC). Then each plan's leaf premises (PL_LEAF_<KIND>_<LEAF>,   *)
(* by computation on the plan's data under the host's leaf table and the    *)
(* control-word range) and the records' theorems under the relation         *)
(* (PL_<KIND>_REL). hyps_union and hyps_find are not built yet: their        *)
(* premises stay in EQ_MP, TRANS, MK_COMB and EXPECT_ALPHA.                  *)
(*                                                                           *)
(* Loaded after plans_drv.ml and leaves_spec.ml, in a session on s2n-bignum's *)
(* base.                                                                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The relation: definitions.                                               *)
(* ------------------------------------------------------------------------- *)

(* Word i of the area at b, as a number. *)
let pl_mw = new_definition
 `pl_mw (m:int64->byte) (b:int64) i = val(drv_word m (word_add b (word(8 * i))))`;;

(* The binding slots the relation reads (PLANS.txt, section 2): the type and *)
(* de Bruijn interners, the term and theorem rows with counts and marks, the *)
(* operand stack and the work region. Slot j's region is bw j, of length    *)
(* val(bw(j + 1)).                                                           *)
let pl_slots = new_definition
 `pl_slots = [0; 2; 4; 6; 8; 10; 12; 14; 16; 18; 20; 22; 40; 42]`;;

(* The layout: control words and regions do not wrap and lie apart from one *)
(* another and from the driver's stack window around cfr; the interners'    *)
(* and counts' minimum sizes; mark regions large enough for every row their *)
(* row region can hold.                                                      *)
let pl_layout = new_definition
 `pl_layout (bw:num->int64) (ctl:int64) nctl (cfr:int64) <=>
    48 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\ val ctl + 8 * nctl <= 2 EXP 64 /\
    drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl) /\
    (!j. MEM j pl_slots
         ==> val(bw j) + val(bw(j + 1)) < 2 EXP 64 /\
             drv_apart (bw j) (val(bw(j + 1))) ctl (8 * nctl) /\
             drv_apart (word_sub cfr (word 48)) 304 (bw j) (val(bw(j + 1)))) /\
    (!j j'. MEM j pl_slots /\ MEM j' pl_slots /\ ~(j = j')
            ==> drv_apart (bw j) (val(bw(j + 1))) (bw j') (val(bw(j' + 1)))) /\
    16 <= val(bw 1) /\ 8 <= val(bw 3) /\ 8 <= val(bw 5) /\
    16 <= val(bw 7) /\ 8 <= val(bw 9) /\ 8 <= val(bw 11) /\
    8 <= val(bw 15) /\ 8 <= val(bw 21) /\
    val(bw 13) <= 5 * val(bw 17) /\ val(bw 19) <= 2 * val(bw 23)`;;

(* Control words 0 .. nctl - 1 hold cw. *)
let pl_cwords = new_definition
 `pl_cwords (ctl:int64) nctl (m:int64->byte) (cw:num->num) <=>
    !k. k < nctl ==> pl_mw m ctl k = cw k`;;

(* An interner at slots j, j + 2, j + 4 (rows, hash slots, count) holding   *)
(* rows: a well-formed intern16 table in those regions, row i the packed    *)
(* key (tag + 8a, b) read back as (tag, a, b).                               *)
let pl_itab = new_definition
 `pl_itab (bw:num->int64) j (m:int64->byte) (rows:(num#num#num)list) <=>
    ?t. (!r. r < 3 ==> tisa_base t r = bw(j + 2 * r) /\ tisa_len t r = bw(j + 2 * r + 1)) /\
        (!r a. r < 3 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1))) ==> tmem t a = m a) /\
        intern_ok t /\ val(intern_count t) = LENGTH rows /\
        !i. i < LENGTH rows
            ==> EL i rows = (val(intern_word t (2 * i)) MOD 8, val(intern_word t (2 * i)) DIV 8,
                             val(intern_word t (2 * i + 1)))`;;

(* A row table at slot jr with its count at slot jc: n rows of wd words,    *)
(* word w of row i being fw i w.                                             *)
let pl_rtab = new_definition
 `pl_rtab (bw:num->int64) jr jc wd (m:int64->byte) (fw:num->num->num) n <=>
    pl_mw m (bw jc) 0 = n /\ 8 * wd * n <= val(bw(jr + 1)) /\
    !i w. i < n /\ w < wd ==> pl_mw m (bw jr) (wd * i + w) = fw i w`;;

(* The dropped marks at slot jm of a space spc with n ids: one word per id, *)
(* 0 exactly for the live ids; zero beyond n; no id at or beyond n dropped. *)
let pl_marks = new_definition
 `pl_marks (bw:num->int64) jm (m:int64->byte) spc n (drops:(num#num)list) <=>
    8 * n <= val(bw(jm + 1)) /\
    (!i. i < n ==> (pl_mw m (bw jm) i = 0 <=> ~MEM (spc,i) drops)) /\
    (!i. n <= i /\ 8 * i + 8 <= val(bw(jm + 1)) ==> pl_mw m (bw jm) i = 0) /\
    (!i. n <= i ==> ~MEM (spc,i) drops)`;;

(* The operand stack at slot 40 holds stk. *)
let pl_stk = new_definition
 `pl_stk (bw:num->int64) (m:int64->byte) (stk:num list) <=>
    8 * LENGTH stk <= val(bw 41) /\ !j. j < LENGTH stk ==> pl_mw m (bw 40) j = EL j stk`;;

let plan_rel = new_definition
 `plan_rel (bw:num->int64) (ctl:int64) nctl (cfr:int64) (m:int64->byte)
           ((cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate) <=>
    pl_layout bw ctl nctl cfr /\ 7 <= nctl /\ (!k. k <= 6 ==> cw k = k) /\ pl_cwords ctl nctl m cw /\
    pl_itab bw 0 m tys /\ pl_itab bw 6 m dbs /\
    pl_rtab bw 12 14 5 m (\i w. pl_f5 (EL i ntms) w) (LENGTH ntms) /\
    pl_marks bw 16 m 2 (LENGTH ntms) drops /\
    pl_rtab bw 18 20 2 m (\i w. pl_f2 (EL i ths) w) (LENGTH ths) /\
    pl_marks bw 22 m 3 (LENGTH ths) drops /\
    pl_stk bw m stk`;;

(* ------------------------------------------------------------------------- *)
(* Memory agreement.                                                        *)
(* ------------------------------------------------------------------------- *)

let PL_ADDR_VAL = prove
 (`!(b:int64) x y. val b + x + y < 2 EXP 64
                   ==> val(word_add (word_add b (word x)) (word y)) = val b + x + y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DRV_ADDR_ASSOC] THEN
  MP_TAC(SPECL [`b:int64`; `x + y`] TISA_VAL_OFFSET) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC]);;

(* A word of an area two memories agree on. *)
let PL_MW_REGION = prove
 (`!m1 m2 (b:int64) n i.
     val b + n <= 2 EXP 64 /\ 8 * i + 8 <= n /\ (!a. drv_in a b n ==> m1 a = m2 a)
     ==> pl_mw m1 b i = pl_mw m2 b i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_mw] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC DRV_WORD_AREA THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]);;

(* Row-major words: word w of row i of n rows of wd words lies in the first *)
(* 8 * wd * n bytes.                                                         *)
let PL_ROW_WORD_BOUND = prove
 (`!wd i w n. i < n /\ w < wd ==> 8 * (wd * i + w) + 8 <= 8 * wd * n`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `wd * (i + 1) <= wd * n` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC]);;

(* The layout's facts about one slot. *)
let PL_LAYOUT_SLOT = prove
 (`!bw ctl nctl cfr j.
     pl_layout bw ctl nctl cfr /\ MEM j pl_slots
     ==> val(bw j) + val(bw(j + 1)) < 2 EXP 64 /\
         drv_apart (bw j) (val(bw(j + 1))) ctl (8 * nctl) /\
         drv_apart (word_sub cfr (word 48)) 304 (bw j) (val(bw(j + 1)))`,
  REWRITE_TAC[pl_layout] THEN MESON_TAC[]);;

(* An address of a slot's region is neither in the driver's stack window nor *)
(* in control word p.                                                        *)
let PL_SLOT_ADDR = prove
 (`!bw ctl nctl cfr j p a.
     pl_layout bw ctl nctl cfr /\ MEM j pl_slots /\ p < nctl /\ drv_in a (bw j) (val(bw(j + 1)))
     ==> ~drv_stack cfr a /\ ~drv_in a (word_add ctl (word(8 * p))) 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`] PL_LAYOUT_SLOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN CONJ_TAC THENL
   [MATCH_MP_TAC DRV_IN_NOT_STACK THEN
    MAP_EVERY EXISTS_TAC [`bw(j:num):int64`; `val(bw(j + 1):int64)`] THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`ctl:int64`; `8 * p`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    UNDISCH_TAC `drv_apart (bw(j:num)) (val(bw(j + 1):int64)) ctl (8 * nctl)` THEN
    UNDISCH_TAC `drv_in (a:int64) (bw(j:num)) (val(bw(j + 1):int64))` THEN
    ASM_REWRITE_TAC[drv_apart; drv_in] THEN ASM_ARITH_TAC]);;

(* A control-word address is not in the driver's stack window. *)
let PL_CTL_ADDR = prove
 (`!bw ctl nctl cfr a. pl_layout bw ctl nctl cfr /\ drv_in a ctl (8 * nctl) ==> ~drv_stack cfr a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_layout] THEN STRIP_TAC THEN
  MATCH_MP_TAC DRV_IN_NOT_STACK THEN
  MAP_EVERY EXISTS_TAC [`ctl:int64`; `8 * nctl`] THEN ASM_REWRITE_TAC[]);;

(* Control words after a step that writes control word p with v and leaves  *)
(* the others.                                                               *)
let PL_CWORDS_SET = prove
 (`!ctl nctl m m' cw p v.
     pl_cwords ctl nctl m cw /\ val ctl + 8 * nctl <= 2 EXP 64 /\ p < nctl /\
     (!a. drv_in a ctl (8 * nctl) /\ ~drv_in a (word_add ctl (word(8 * p))) 8 ==> m' a = m a) /\
     drv_word m' (word_add ctl (word(8 * p))) = v
     ==> pl_cwords ctl nctl m' (pl_set cw p (val v))`,
  REWRITE_TAC[pl_cwords; pl_set] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[pl_mw]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `pl_mw`)) (concl th)
     then SUBST1_TAC(SYM(MATCH_MP th (ASSUME `k < nctl`))) else failwith "") THEN
  REWRITE_TAC[pl_mw] THEN AP_TERM_TAC THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[drv_in] THEN
  MP_TAC(SPECL [`ctl:int64`; `8 * k`; `i:num`] PL_ADDR_VAL) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`ctl:int64`; `8 * p`] TISA_VAL_OFFSET) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_ARITH_TAC);;

let PL_ITAB_AGREE = prove
 (`!bw j m m' rows.
     pl_itab bw j m rows /\
     (!r a. r < 3 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1))) ==> m' a = m a)
     ==> pl_itab bw j m' rows`,
  REWRITE_TAC[pl_itab] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `t:tisa_state` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let PL_RTAB_AGREE = prove
 (`!bw jr jc wd m m' fw n.
     pl_rtab bw jr jc wd m fw n /\
     val(bw jr) + val(bw(jr + 1)) <= 2 EXP 64 /\ val(bw jc) + val(bw(jc + 1)) <= 2 EXP 64 /\
     8 <= val(bw(jc + 1)) /\
     (!a. drv_in a (bw jr) (val(bw(jr + 1))) ==> m' a = m a) /\
     (!a. drv_in a (bw jc) (val(bw(jc + 1))) ==> m' a = m a)
     ==> pl_rtab bw jr jc wd m' fw n`,
  REWRITE_TAC[pl_rtab] THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_const_app "pl_mw" (lhs(concl th))
                            then SUBST1_TAC(SYM th) else failwith "") THEN
    MATCH_MP_TAC PL_MW_REGION THEN EXISTS_TAC `val(bw(jc + 1):int64)` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `fw:num->num->num`)) (concl th)
      then SUBST1_TAC(SYM(MATCH_MP th (CONJ (ASSUME `i < n`) (ASSUME `w < wd`)))) else failwith "") THEN
    MATCH_MP_TAC PL_MW_REGION THEN EXISTS_TAC `val(bw(jr + 1):int64)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`wd:num`; `i:num`; `w:num`; `n:num`] PL_ROW_WORD_BOUND) THEN ASM_ARITH_TAC]);;

let PL_MARKS_AGREE = prove
 (`!bw jm m m' spc n drops.
     pl_marks bw jm m spc n drops /\ val(bw jm) + val(bw(jm + 1)) <= 2 EXP 64 /\
     (!a. drv_in a (bw jm) (val(bw(jm + 1))) ==> m' a = m a)
     ==> pl_marks bw jm m' spc n drops`,
  REWRITE_TAC[pl_marks] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. 8 * i + 8 <= val(bw(jm + 1):int64)
                    ==> pl_mw m' (bw(jm:num)) i = pl_mw (m:int64->byte) (bw jm) i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MW_REGION THEN EXISTS_TAC `val(bw(jm + 1):int64)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THENL
   [SUBGOAL_THEN `8 * i + 8 <= val(bw(jm + 1):int64)` (fun th -> ASM_SIMP_TAC[th]) THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[]]);;

let PL_STK_AGREE = prove
 (`!bw m m' stk.
     pl_stk bw m stk /\ val(bw 40) + val(bw 41) <= 2 EXP 64 /\
     (!a. drv_in a (bw 40) (val(bw 41)) ==> m' a = m a)
     ==> pl_stk bw m' stk`,
  REWRITE_TAC[pl_stk] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pl_mw m' (bw 40) j = pl_mw m (bw 40) j` SUBST1_TAC THENL
   [MATCH_MP_TAC PL_MW_REGION THEN EXISTS_TAC `val(bw 41:int64)` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A step that changes no slot region.                                      *)
(* ------------------------------------------------------------------------- *)

let PL_SLOT_MEMS = prove
 (`MEM 0 pl_slots /\ MEM 2 pl_slots /\ MEM 4 pl_slots /\ MEM 6 pl_slots /\ MEM 8 pl_slots /\
   MEM 10 pl_slots /\ MEM 12 pl_slots /\ MEM 14 pl_slots /\ MEM 16 pl_slots /\ MEM 18 pl_slots /\
   MEM 20 pl_slots /\ MEM 22 pl_slots /\ MEM 40 pl_slots /\ MEM 42 pl_slots`,
  REWRITE_TAC[pl_slots; MEM] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Agreement on every slot region gives agreement on an interner's three. *)
let PL_ITAB_SLOTS = prove
 (`!bw (m:int64->byte) m' j.
     (j = 0 \/ j = 6) /\
     (!j' a. MEM j' pl_slots /\ drv_in a (bw j') (val(bw(j' + 1))) ==> m' a = m a)
     ==> !r a. r < 3 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1))) ==> m' a = m a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `r < 3 <=> r = 0 \/ r = 1 \/ r = 2`] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_var(lhs(concl th))
                                 then SUBST_ALL_TAC th else failwith "")) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) then MATCH_MP_TAC th else failwith "") THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC(rand(rand(rator(concl th)))) THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[PL_SLOT_MEMS]));;

(* The agreement and bound facts for slot j, as assumptions. *)
let PL_SLOT_FACTS_TAC j =
  let mem = EQT_ELIM(REWRITE_CONV[PL_SLOT_MEMS] (mk_comb(mk_comb(`MEM:num->num list->bool`, j), `pl_slots`))) in
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `pl_slots`)) (concl th) &&
                           can (find_term ((=) `m':int64->byte`)) (concl th)
     then ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV) (REWRITE_RULE[PL_SLOT_MEMS] (SPEC j th)))
     else failwith "") THEN
  FIRST_ASSUM(fun th -> if is_const_app "pl_layout" (concl th) then
     ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
       (MATCH_MP LT_IMP_LE (CONJUNCT1(MATCH_MP PL_LAYOUT_SLOT (CONJ th mem)))))
     else failwith "");;

let PL_REL_KEEP = prove
 (`!bw ctl nctl cfr m m' cw ctx nms tys ntms dbs ths nmap ymap drops pol stk p v.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ p < nctl /\ 6 < p /\
     (!a. ~drv_stack cfr a /\ ~drv_in a (word_add ctl (word(8 * p))) 8 ==> m' a = m a) /\
     drv_word m' (word_add ctl (word(8 * p))) = v
     ==> plan_rel bw ctl nctl cfr m'
           (pl_set cw p (val v),(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[plan_rel] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!j a. MEM j pl_slots /\ drv_in a (bw j) (val(bw(j + 1))) ==> m' a = (m:int64->byte) a`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC PL_SLOT_ADDR THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`; `nctl:num`; `j:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY PL_SLOT_FACTS_TAC [`12`; `14`; `16`; `18`; `20`; `22`; `40`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_set] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC PL_CWORDS_SET THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `drv_stack`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_CTL_ADDR THEN
    MAP_EVERY EXISTS_TAC [`bw:num->int64`; `ctl:int64`; `nctl:num`] THEN ASM_REWRITE_TAC[];
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

(* A leaf without read-write regions: after its step the relation holds of *)
(* the memory the driver keeps, with the payload in the step's word.       *)
let PL_REL_RO_STEP = prove
 (`!bw ctl nctl budget cfr st m used t prog k u
    cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     drv_child bw ctl budget cfr st m used t /\ tisa_leaf_wf prog /\ tisa_entry_ok prog t /\
     tisa_run prog t = TStop k u /\ (!r. ~tisa_rw (tisa_decls prog) r) /\ val(EL 17 st) < nctl /\
     6 < val(EL 17 st)
     ==> plan_rel bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),
            (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_REL_KEEP THEN EXISTS_TAC `m:int64->byte` THEN
  ASM_REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME] THEN
  X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM drv_after] THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
  MAP_EVERY EXISTS_TAC [`prog:tisa_prog`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                        `used:int64`; `t:tisa_state`; `k:num`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "plan_rel" (concl th))) THEN
  REWRITE_TAC[plan_rel; pl_layout] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The child state of a step against the relation.                          *)
(* ------------------------------------------------------------------------- *)

(* A child's arguments, registers, allowance and receipt, from the control  *)
(* words.                                                                    *)
let PL_CHILD_ARGS = prove
 (`!bw ctl nctl budget cfr st m used t cw.
     drv_child bw ctl budget cfr st m used t /\ pl_cwords ctl nctl m cw /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl)
     ==> val(tisa_fword t 22) = cw(val(EL 10 st)) /\ val(tisa_fword t 23) = cw(val(EL 11 st)) /\
         (!r. 1 <= r /\ r <= 5 ==> val(tregs t r) = cw(val(EL (11 + r) st))) /\
         tisa_fword t 21 = used /\ tisa_fword t 20 = budget`,
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_child; pl_cwords] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `22` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_fw`)) (concl th))) THEN
    REWRITE_TAC[drv_fw; drv_cw] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM pl_mw] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `23` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_fw`)) (concl th))) THEN
    REWRITE_TAC[drv_fw; drv_cw] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM pl_mw] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[drv_regs; drv_cw] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= r ==> ~(r = 0)`] THEN REWRITE_TAC[GSYM pl_mw] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `21` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_fw`)) (concl th))) THEN
    REWRITE_TAC[drv_fw] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `20` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_fw`)) (concl th))) THEN
    REWRITE_TAC[drv_fw] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]]);;

(* Word i of a child's region r, bound to slot j, is the memory's. *)
let PL_CHILD_W = prove
 (`!bw ctl nctl budget cfr st m used t r j i.
     drv_child bw ctl budget cfr st m used t /\ pl_layout bw ctl nctl cfr /\
     r < 9 /\ val(EL (1 + r) st) = j /\ MEM j pl_slots /\ 8 * i + 8 <= val(bw(j + 1))
     ==> tisa_base t r = bw j /\ tisa_len t r = bw(j + 1) /\ val(pl_w t r i) = pl_mw m (bw j) i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[drv_base; drv_len] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pl_w; pl_mw] THEN AP_TERM_TAC THEN
  REWRITE_TAC[tisa_read; GSYM drv_word] THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
    check (fun th -> is_const_app "drv_child" (concl th))) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`] PL_LAYOUT_SLOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  MATCH_MP_TAC DRV_IN_NOT_STACK THEN
  MAP_EVERY EXISTS_TAC [`bw(j:num):int64`; `val(bw(j + 1):int64)`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DRV_IN_OFFSET THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* A child's region r bound to slot j. *)
let PL_CHILD_REGION = prove
 (`!bw ctl budget cfr st m used t r j.
     drv_child bw ctl budget cfr st m used t /\ r < 9 /\ val(EL (1 + r) st) = j
     ==> tisa_base t r = bw j /\ tisa_len t r = bw(j + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[drv_base; drv_len]);;

(* ------------------------------------------------------------------------- *)
(* A read-only leaf implements its abstract semantics under plan_rel when   *)
(* its outcome and payload are the abstract ones.                           *)
(* ------------------------------------------------------------------------- *)

let PL_IMPL_RO = prove
 (`!progs bw ctl nctl budget cfr st prog.
     progs (val(EL 0 st)) = prog /\ tisa_leaf_wf prog /\ (!r. ~tisa_rw (tisa_decls prog) r) /\
     (!t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
              ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\ k < 8) /\
     val(EL 17 st) < nctl /\ 6 < val(EL 17 st) /\
     (!m used s t k u.
        plan_rel bw ctl nctl cfr m s /\ drv_child bw ctl budget cfr st m used t /\
        tisa_entry_ok prog t /\ tisa_run prog t = TStop k u
        ==> pl_leaf st s k (val(tisa_fword u 19)) (FST(SND s)))
     ==> pl_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_impl; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`m:int64->byte`; `used:int64`; `cw:num->num`; `ctx:hupdate list`; `nms:string list`;
    `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`;
    `ths:(num#num)list`; `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`;
    `stk:num list`; `t:tisa_state`; `k:num`; `u:tisa_state`] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `pl_leaf`)) (concl th)
    then MP_TAC(SPECL [`m:int64->byte`; `used:int64`;
                       `(cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate`;
                       `t:tisa_state`; `k:num`; `u:tisa_state`] th) else failwith "") THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `tisa_fword u 18`)) (concl th) &&
                     not(can (find_term ((=) `pl_leaf`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `21` o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
      check (fun th -> is_const_app "drv_child" (concl th))) THEN
    REWRITE_TAC[drv_fw] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC PL_REL_RO_STEP THEN
    MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`;
                          `prog:tisa_prog`; `k:num`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* row_word against a row table of the relation.                            *)
(* ------------------------------------------------------------------------- *)

(* pl_leaf at a step whose leaf and region-0 slot are numerals. *)
let PL_LEAF_AT_TAC =
  REWRITE_TAC[pl_leaf; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

(* row_word on a table of n rows of wd words at slots jr (rows), jc (count). *)
let PL_SEM_ROWW = prove
 (`!bw ctl nctl budget cfr st m used t k u cw jr jc wd fw n.
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\
     val(EL 1 st) = jr /\ val(EL 2 st) = jc /\ MEM jr pl_slots /\ MEM jc pl_slots /\
     pl_layout bw ctl nctl cfr /\ pl_cwords ctl nctl m cw /\ pl_rtab bw jr jc wd m fw n /\
     8 <= val(bw(jc + 1)) /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok row_word t /\
     tisa_run row_word t = TStop k u
     ==> pl_roww fw n wd (cw(val(EL 10 st))) (cw(val(EL 11 st))) (cw(val(EL 12 st))) k
                 (val(tisa_fword u 19))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pl_rtab]) THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `0`; `jr:num`] PL_CHILD_REGION) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `jc:num`] PL_CHILD_REGION) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `jc:num`; `0`] PL_CHILD_W) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC PL_ROW_WORD_SPEC THEN REWRITE_TAC[pl_row_word_spec] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[pl_roww] THEN
  DISCH_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `0`; `jr:num`;
                `wd * cw(val(EL 10 (st:int64 list))) + cw(val(EL 11 st))`] PL_CHILD_W) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`wd:num`; `cw(val(EL 10 (st:int64 list))):num`; `cw(val(EL 11 (st:int64 list))):num`;
                  `n:num`] PL_ROW_WORD_BOUND) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`cw(val(EL 10 (st:int64 list))):num`; `cw(val(EL 11 (st:int64 list))):num`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `fw:num->num->num`)) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

let PL_F3_WORDS = prove
 (`!x y. pl_f3 (x MOD 8, x DIV 8, y) 0 = x /\ pl_f3 (x MOD 8, x DIV 8, y) 1 = y`,
  REWRITE_TAC[pl_f3; FST; SND; ARITH_EQ] THEN REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`x:num`; `8`] DIVISION) THEN ARITH_TAC);;

let PL_MEM_AGREE_TAC (asl,w) =
  let w' = if is_eq w then w else failwith "PL_MEM_AGREE_TAC" in
  let addr = rand(lhs w') in
  let rec base t = try if is_const_app "word_add" t then base (lhand t) else t with Failure _ -> t in
  let b0 = base addr in
  let fact = find (fun th -> let c = concl th in is_forall c &&
                     (try let _,b = dest_forall c in
                          let d = lhand b in is_const_app "drv_in" d && rand(rator d) = b0
                      with Failure _ -> false)) (map snd asl) in
  ((if is_const_app "tmem" (rator(lhs w')) then ALL_TAC else CONV_TAC SYM_CONV) THEN
   MATCH_MP_TAC fact) (asl,w);;
(* Every slot's bound val(bw j) + val(bw(j + 1)) <= 2 EXP 64, from the layout. *)
let PL_SLOT_BOUNDS_TAC =
  FIRST_ASSUM(fun th -> if is_const_app "pl_layout" (concl th) then
    MAP_EVERY (fun j ->
      let mem = EQT_ELIM(REWRITE_CONV[PL_SLOT_MEMS] (mk_comb(mk_comb(`MEM:num->num list->bool`, j), `pl_slots`))) in
      ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
        (MATCH_MP LT_IMP_LE (CONJUNCT1(MATCH_MP PL_LAYOUT_SLOT (CONJ th mem))))))
     [`0`; `2`; `4`; `6`; `8`; `10`; `12`; `14`; `16`; `18`; `20`; `22`; `40`; `42`]
    else failwith "");;

(* An interner of the relation, read as a row table of two-word rows. *)
let PL_ITAB_RTAB = prove
 (`!bw ctl nctl cfr j m rows.
     pl_layout bw ctl nctl cfr /\ (j = 0 \/ j = 6) /\ pl_itab bw j m rows
     ==> pl_rtab bw j (j + 4) 2 m (\i w. pl_f3 (EL i rows) w) (LENGTH rows)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_itab; pl_rtab] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:tisa_state` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `tisa_base`)) (concl th)
     then MAP_EVERY (fun r -> ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV) (MP (SPEC r th)
            (EQT_ELIM(NUM_REDUCE_CONV(mk_comb(mk_comb(`(<):num->num->bool`, r), `3`))))))) [`0`; `1`; `2`]
     else failwith "") THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `tmem`)) (concl th)
     then MAP_EVERY (fun r -> ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
            (REWRITE_RULE[EQT_ELIM(NUM_REDUCE_CONV(mk_comb(mk_comb(`(<):num->num->bool`, r), `3`)))]
              (SPEC r th)))) [`0`; `1`; `2`]
     else failwith "") THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [intern_ok] o
      check (fun th -> is_const_app "intern_ok" (concl th))) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && can (find_term ((=) `intern_count`)) (concl th)
                        then SUBST1_TAC th else failwith "") THEN
  SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj(concl th) &&
    can (find_term ((=) `tisa_base`)) (concl th)))) THEN
  (CONJ_TAC THENL
   [REWRITE_TAC[pl_mw; MULT_CLAUSES; WORD_ADD_0] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && can (find_term ((=) `intern_count`)) (concl th)
                        then SUBST1_TAC(SYM th) else failwith "") THEN
  AP_TERM_TAC THEN REWRITE_TAC[intern_count; tisa_read; GSYM drv_word] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN PL_MEM_AGREE_TAC THEN MATCH_MP_TAC DRV_IN_BASE THEN PL_SLOT_BOUNDS_TAC THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [UNDISCH_TAC `16 * LENGTH (rows:(num#num#num)list) <= val(tisa_len t 0)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `intern_word`)) (concl th)
     then REWRITE_TAC[MATCH_MP th (ASSUME `i < LENGTH (rows:(num#num#num)list)`)] else failwith "") THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o REWRITE_RULE[ARITH_RULE `w < 2 <=> w = 0 \/ w = 1`] o
    check (fun th -> concl th = `w < 2`)) THEN
  REWRITE_TAC[PL_F3_WORDS; ADD_CLAUSES] THEN
  REWRITE_TAC[pl_mw; intern_word; tisa_read; GSYM drv_word] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  PL_MEM_AGREE_TAC THEN MATCH_MP_TAC DRV_IN_OFFSET THEN PL_SLOT_BOUNDS_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `16 * LENGTH (rows:(num#num#num)list) <= val(tisa_len t 0)` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `i < LENGTH (rows:(num#num#num)list)` THEN ARITH_TAC]]));;

(* ------------------------------------------------------------------------- *)
(* row_word implements its abstract semantics on the four row tables.        *)
(* ------------------------------------------------------------------------- *)

let PL_DECLS_RO = prove
 (`!decls. ALL (\d:num#num#num. FST d = 1) decls ==> !r. ~tisa_rw decls r`,
  REWRITE_TAC[tisa_rw; GSYM ALL_EL] THEN MESON_TAC[ALL_EL; ARITH_RULE `~(1 = 2)`]);;

let PL_ROW_WORD_STATUS = prove
 (`!t k u. tisa_entry_ok row_word t /\ tisa_run row_word t = TStop k u
           ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\ k < 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC PL_ROW_WORD_SPEC THEN REWRITE_TAC[pl_row_word_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o CONJUNCT2 o CONJUNCT2)
                             (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN SIMP_TAC[] THEN ARITH_TAC);;

(* The bridge for row_word bound to rows slot jr and count slot jc. *)
let PL_ROWW_BRIDGE_TAC jr jc rtab_tac =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_IMPL_RO THEN EXISTS_TAC `row_word` THEN
  ASM_REWRITE_TAC[ROW_WORD_LEAF_WF; PL_ROW_WORD_STATUS] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_DECLS_RO THEN REWRITE_TAC[ROW_WORD_DECLS; ALL] THEN CONV_TAC NUM_REDUCE_CONV;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN PL_LEAF_AT_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [plan_rel]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
    rtab_tac THEN
    MATCH_MP_TAC PL_SEM_ROWW THEN
    W(fun (asl,_) ->
      let dc = concl(find (fun th -> is_const_app "drv_child" (concl th)) (map snd asl)) in
      let args = snd(strip_comb dc) in
      MAP_EVERY EXISTS_TAC [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                            el 5 args; el 6 args; el 7 args; jr; jc]) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS]];;

let PL_IMPL_ROWW_TH = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 4 = row_word /\ val(EL 0 st) = 4 /\ val(EL 1 st) = 18 /\ val(EL 2 st) = 20 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_ROWW_BRIDGE_TAC `18` `20` ALL_TAC);;

let PL_IMPL_ROWW_TM = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 4 = row_word /\ val(EL 0 st) = 4 /\ val(EL 1 st) = 12 /\ val(EL 2 st) = 14 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_ROWW_BRIDGE_TAC `12` `14` ALL_TAC);;

let PL_IMPL_ROWW_TY = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 4 = row_word /\ val(EL 0 st) = 4 /\ val(EL 1 st) = 0 /\ val(EL 2 st) = 4 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_ROWW_BRIDGE_TAC `0` `4`
   (W(fun (asl,_) ->
      let lay = find (fun th -> is_const_app "pl_layout" (concl th)) (map snd asl) in
      let it = find (fun th -> is_const_app "pl_itab" (concl th) &&
                               rand(rator(rator(concl th))) = `0`) (map snd asl) in
      ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
        (MATCH_MP PL_ITAB_RTAB (CONJ lay (CONJ (DISJ1 (REFL `0`) `0 = 6`) it)))))));;

let PL_IMPL_ROWW_DB = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 4 = row_word /\ val(EL 0 st) = 4 /\ val(EL 1 st) = 6 /\ val(EL 2 st) = 10 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_ROWW_BRIDGE_TAC `6` `10`
   (W(fun (asl,_) ->
      let lay = find (fun th -> is_const_app "pl_layout" (concl th)) (map snd asl) in
      let it = find (fun th -> is_const_app "pl_itab" (concl th) &&
                               rand(rator(rator(concl th))) = `6`) (map snd asl) in
      ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
        (MATCH_MP PL_ITAB_RTAB (CONJ lay (CONJ (DISJ2 `6 = 0` (REFL `6`)) it)))))));;

(* ------------------------------------------------------------------------- *)
(* pack, unpack, eqw, live.                                                  *)
(* ------------------------------------------------------------------------- *)

(* The status premise of PL_IMPL_RO from a specification's leaf_ok part and *)
(* its outcomes.                                                             *)
let PL_STATUS_TAC spec_th spec_def =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC spec_th THEN REWRITE_TAC[spec_def; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o CONJUNCT2 o CONJUNCT2)
                             (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN SIMP_TAC[] THEN ARITH_TAC;;

let PL_PACK_STATUS = prove
 (`!t k u. tisa_entry_ok pack t /\ tisa_run pack t = TStop k u
           ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\ k < 8`,
  PL_STATUS_TAC PL_PACK_SPEC pl_pack_spec);;
let PL_UNPACK_STATUS = prove
 (`!t k u. tisa_entry_ok unpack t /\ tisa_run unpack t = TStop k u
           ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\ k < 8`,
  PL_STATUS_TAC PL_UNPACK_SPEC pl_unpack_spec);;
let PL_EQW_STATUS = prove
 (`!t k u. tisa_entry_ok eqw t /\ tisa_run eqw t = TStop k u
           ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\ k < 8`,
  PL_STATUS_TAC PL_EQW_SPEC pl_eqw_spec);;
let PL_LIVE_STATUS = prove
 (`!t k u. tisa_entry_ok live t /\ tisa_run live t = TStop k u
           ==> tisa_fword u 18 = word k /\ tisa_fword u 21 = tisa_fword t 21 /\ k < 8`,
  PL_STATUS_TAC PL_LIVE_SPEC pl_live_spec);;

(* A small payload's value. *)
let PL_VAL_WORD_LT = prove
 (`!n. n < 2 EXP 64 ==> val(word n:int64) = n`,
  SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT]);;

(* The bridge of a pure leaf (no regions). *)
let PL_PURE_BRIDGE_TAC prog_tm wf decls status spec spec_def =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_IMPL_RO THEN EXISTS_TAC prog_tm THEN
  ASM_REWRITE_TAC[wf; status] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[decls; tisa_rw; LENGTH] THEN ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN PL_LEAF_AT_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [plan_rel]) THEN
    W(fun (asl,_) ->
      let dc = find (fun th -> is_const_app "drv_child" (concl th)) (map snd asl) in
      let cws = find (fun th -> is_const_app "pl_cwords" (concl th)) (map snd asl) in
      let rng = find (fun th -> is_forall(concl th) && can (find_term ((=) `nctl:num`)) (concl th) &&
                                not(is_const_app "plan_rel" (concl th))) (map snd asl) in
      MP_TAC(MATCH_MP PL_CHILD_ARGS (CONJ dc (CONJ cws rng)))) THEN
    STRIP_TAC THEN
    MP_TAC spec THEN REWRITE_TAC[spec_def] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[pl_pack; pl_unpack; pl_eqw; GSYM VAL_EQ] THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(MATCH_MP_TAC PL_VAL_WORD_LT THEN ASM_ARITH_TAC) THEN
    TRY(MATCH_MP_TAC PL_VAL_WORD_LT THEN
        MP_TAC(SPEC `tisa_fword t 22` VAL_BOUND_64) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)];;

let PL_IMPL_PACK = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 1 = pack /\ val(EL 0 st) = 1 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_PURE_BRIDGE_TAC `pack` PACK_LEAF_WF PACK_DECLS PL_PACK_STATUS PL_PACK_SPEC pl_pack_spec);;

let PL_IMPL_UNPACK = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 2 = unpack /\ val(EL 0 st) = 2 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_PURE_BRIDGE_TAC `unpack` UNPACK_LEAF_WF UNPACK_DECLS PL_UNPACK_STATUS PL_UNPACK_SPEC pl_unpack_spec);;

let PL_IMPL_EQW = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 3 = eqw /\ val(EL 0 st) = 3 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_PURE_BRIDGE_TAC `eqw` EQW_LEAF_WF EQW_DECLS PL_EQW_STATUS PL_EQW_SPEC pl_eqw_spec);;

let PL_SEM_LIVE = prove
 (`!bw ctl nctl budget cfr st m used t k u cw jc jm spc n drops.
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\
     val(EL 1 st) = jc /\ val(EL 2 st) = jm /\ MEM jc pl_slots /\ MEM jm pl_slots /\
     pl_layout bw ctl nctl cfr /\ pl_cwords ctl nctl m cw /\ pl_mw m (bw jc) 0 = n /\
     8 <= val(bw(jc + 1)) /\ pl_marks bw jm m spc n drops /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok live t /\ tisa_run live t = TStop k u
     ==> pl_live spc n drops (cw(val(EL 10 st))) k (val(tisa_fword u 19))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pl_marks]) THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `jm:num`] PL_CHILD_REGION) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `0`; `jc:num`; `0`] PL_CHILD_W) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC PL_LIVE_SPEC THEN REWRITE_TAC[pl_live_spec] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[pl_live; holr_live] THEN
  ASM_CASES_TAC `(cw:num->num)(val(EL 10 (st:int64 list))) < n` THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                  `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `jm:num`;
                  `(cw:num->num)(val(EL 10 (st:int64 list)))`] PL_CHILD_W) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
                               is_iff(rand(snd(dest_forall(concl th))))
       then REWRITE_TAC[MATCH_MP th (ASSUME `(cw:num->num)(val(EL 10 (st:int64 list))) < n`)] else failwith "") THEN
    COND_CASES_TAC THEN SIMP_TAC[] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN TRY(COND_CASES_TAC THEN SIMP_TAC[])]);;

let PL_LIVE_BRIDGE_TAC jc jm =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_IMPL_RO THEN EXISTS_TAC `live` THEN
  ASM_REWRITE_TAC[LIVE_LEAF_WF; PL_LIVE_STATUS] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_DECLS_RO THEN REWRITE_TAC[LIVE_DECLS; ALL] THEN CONV_TAC NUM_REDUCE_CONV;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN PL_LEAF_AT_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [plan_rel]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pl_rtab]) THEN
    MATCH_MP_TAC PL_SEM_LIVE THEN
    W(fun (asl,_) ->
      let dc = concl(find (fun th -> is_const_app "drv_child" (concl th)) (map snd asl)) in
      let args = snd(strip_comb dc) in
      MAP_EVERY EXISTS_TAC [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                            el 5 args; el 6 args; el 7 args; jc; jm]) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS]];;

let PL_IMPL_LIVE_TM = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 5 = live /\ val(EL 0 st) = 5 /\ val(EL 1 st) = 14 /\ val(EL 2 st) = 16 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_LIVE_BRIDGE_TAC `14` `16`);;

let PL_IMPL_LIVE_TH = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 5 = live /\ val(EL 0 st) = 5 /\ val(EL 1 st) = 20 /\ val(EL 2 st) = 22 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_LIVE_BRIDGE_TAC `20` `22`);;


(* A leaf's run keeps frame words 0 .. 17 (the regions' bases and lengths). *)
let PL_RUN_FRAME = prove
 (`!prog t k u j. tisa_leaf_wf prog /\ tisa_entry_ok prog t /\ tisa_run prog t = TStop k u /\ j < 18
                  ==> tisa_fword u j = tisa_fword t j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`prog:tisa_prog`; `t:tisa_state`; `k:num`; `u:tisa_state`] TISA_RUN_KEEPS) THEN
  ASM_REWRITE_TAC[tisa_keeps] THEN STRIP_TAC THEN
  SUBGOAL_THEN `tisa_frame_sep (tisa_decls prog) t` MP_TAC THENL
   [MATCH_MP_TAC TISA_ENTRY_FRAME_SEP THEN
    MAP_EVERY EXISTS_TAC [`tisa_inits prog`; `tisa_root prog`] THEN
    REWRITE_TAC[GSYM TISA_PROG_CASES] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "tisa_leaf_wf" (concl th))) THEN
    SIMP_TAC[tisa_leaf_wf];
    REWRITE_TAC[tisa_frame_sep] THEN STRIP_TAC] THEN
  ASM_REWRITE_TAC[DRV_FWORD] THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `val(word_add (word_add (tregs t 0) (word(8 * j))) (word i):int64) = val(tregs t 0) + 8 * j + i`
    SUBST1_TAC THENL [MATCH_MP_TAC PL_ADDR_VAL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[tisa_writable; DE_MORGAN_THM; NOT_EXISTS_THM] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `val(word_add (word_add (tregs t 0) (word(8 * j))) (word i):int64) = val(tregs t 0) + 8 * j + i`
      SUBST1_TAC THENL [MATCH_MP_TAC PL_ADDR_VAL THEN ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `r:num` THEN ASM_CASES_TAC `tisa_rw (tisa_decls prog) r` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `192`)) (concl th))) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `val(word_add (word_add (tregs t 0) (word(8 * j))) (word i):int64) = val(tregs t 0) + 8 * j + i`
      SUBST1_TAC THENL [MATCH_MP_TAC PL_ADDR_VAL THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_ARITH_TAC]);;

(* The memory after a step, in a slot region bound to the step's region r: the leaf's. *)
let PL_AFTER_WORD = prove
 (`!bw ctl nctl budget cfr st m used t prog k u r j i.
     pl_layout bw ctl nctl cfr /\ drv_child bw ctl budget cfr st m used t /\
     tisa_leaf_wf prog /\ tisa_entry_ok prog t /\ tisa_run prog t = TStop k u /\
     r < 9 /\ val(EL (1 + r) st) = j /\ MEM j pl_slots /\ 8 * i + 8 <= val(bw(j + 1)) /\
     val(EL 17 st) < nctl
     ==> pl_mw (drv_after ctl st u) (bw j) i = val(pl_w u r i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `r:num`; `j:num`] PL_CHILD_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `tisa_base u r = (bw:num->int64) j` ASSUME_TAC THENL
   [REWRITE_TAC[tisa_base] THEN
    MP_TAC(SPECL [`prog:tisa_prog`; `t:tisa_state`; `k:num`; `u:tisa_state`; `2 * r`] PL_RUN_FRAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[GSYM tisa_base];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pl_mw; pl_w; tisa_read; GSYM drv_word] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  REWRITE_TAC[drv_after] THEN MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`] PL_LAYOUT_SLOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  MP_TAC(SPECL [`ctl:int64`; `8 * val(EL 17 (st:int64 list))`] TISA_VAL_OFFSET) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`bw(j:num):int64`; `8 * i`; `q:num`] PL_ADDR_VAL) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `drv_apart (bw(j:num)) (val(bw(j + 1):int64)) ctl (8 * nctl)` THEN
  REWRITE_TAC[drv_apart] THEN ASM_ARITH_TAC);;

let PL_MARKS_EXTEND = prove
 (`!bw jm m spc n drops.
     pl_marks bw jm m spc n drops /\ 8 * (n + 1) <= val(bw(jm + 1))
     ==> pl_marks bw jm m spc (n + 1) drops`,
  REWRITE_TAC[pl_marks] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `i < n:num` THENL
     [ASM_SIMP_TAC[];
      SUBGOAL_THEN `i = n:num` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `pl_mw m (bw(jm:num)) n = 0` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          is_eq(rand(snd(dest_forall(concl th)))))) THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          is_neg(rand(snd(dest_forall(concl th)))))) THEN ARITH_TAC];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          is_eq(rand(snd(dest_forall(concl th)))))) THEN ASM_ARITH_TAC;
    ASM_MESON_TAC[ARITH_RULE `n + 1 <= i ==> n <= i`]]);;

let PL_SLOT_APART_IN = prove
 (`!bw ctl nctl cfr j j' x.
     pl_layout bw ctl nctl cfr /\ MEM j pl_slots /\ MEM j' pl_slots /\ ~(j = j') /\
     drv_in x (bw j) (val(bw(j + 1)))
     ==> ~drv_in x (bw j') (val(bw(j' + 1)))`,
  REWRITE_TAC[pl_layout] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `j':num`] o check (fun th ->
    let vs,_ = strip_forall(concl th) in length vs = 2)) THEN
  ASM_REWRITE_TAC[drv_apart] THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_in]) THEN ASM_ARITH_TAC);;
let PL_AGREE_SLOT_TAC j =
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `drv_after`)) (concl th) &&
                           length(fst(strip_forall(concl th))) = 2
     then ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV THENC REWRITE_CONV[] THENC NUM_REDUCE_CONV)
                       (REWRITE_RULE[PL_SLOT_MEMS] (SPEC j th)))
     else failwith "");;
let PL_ITAB_KEEP_TAC =
  MATCH_MP_TAC PL_ITAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `r < 3 <=> r = 0 \/ r = 1 \/ r = 2`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_SIMP_TAC[];;
let PL_AFTER_TAC r j i =
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `append_row`; `k:num`; `u:tisa_state`;
                r; j; i] PL_AFTER_WORD) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[APPEND_ROW_LEAF_WF; PL_SLOT_MEMS] THEN
  CONV_TAC NUM_REDUCE_CONV;;

(* After a FIRED append_row of (a, b) to the theorem rows, the relation    *)
(* holds of the new theorem table.                                          *)
let PL_REL_APPEND_TH = prove
 (`!bw ctl nctl budget cfr st m used t k u cw ctx nms tys ntms dbs ths nmap ymap drops pol stk a b.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok append_row t /\
     tisa_run append_row t = TStop k u /\
     val(EL 1 st) = 18 /\ val(EL 2 st) = 20 /\ val(EL 17 st) < nctl /\ 6 < val(EL 17 st) /\
     val(pl_w u 1 0) = LENGTH ths + 1 /\ 8 * 2 * (LENGTH ths + 1) <= val(bw 19) /\
     (!j. j < 2 * LENGTH ths ==> pl_w u 0 j = pl_w t 0 j) /\
     val(pl_w u 0 (2 * LENGTH ths)) = a /\ val(pl_w u 0 (2 * LENGTH ths + 1)) = b
     ==> plan_rel bw ctl nctl cfr (drv_after ctl st u)
           (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),
            (ctx,nms,tys,ntms,dbs,APPEND ths [(a,b)],nmap,ymap,drops,pol),stk)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [plan_rel]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  (* the memory after agrees with m off the stack, the two regions and the payload word *)
  SUBGOAL_THEN `!x. ~drv_stack cfr x /\ ~drv_in x (bw 18) (val(bw 19)) /\ ~drv_in x (bw 20) (val(bw 21)) /\
                    ~drv_in x (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8
                    ==> drv_after ctl st u x = (m:int64->byte) x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`append_row`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                          `used:int64`; `t:tisa_state`; `k:num`] THEN
    ASM_REWRITE_TAC[APPEND_ROW_LEAF_WF; APPEND_ROW_DECLS; tisa_rw; LENGTH] THEN
    X_GEN_TAC `r:num` THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `r < 2 <=> r = 0 \/ r = 1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!j x. MEM j pl_slots /\ ~(j = 18) /\ ~(j = 20) /\ drv_in x (bw j) (val(bw(j + 1)))
                     ==> drv_after ctl st u x = (m:int64->byte) x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_after`)) (concl th))) THEN
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`;
                  `val(EL 17 (st:int64 list))`; `x:int64`] PL_SLOT_ADDR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`; `18`; `x:int64`]
        PL_SLOT_APART_IN) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`; `20`; `x:int64`]
        PL_SLOT_APART_IN) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]];
    ALL_TAC]) THEN
  (MAP_EVERY PL_AGREE_SLOT_TAC [`0`; `2`; `4`; `6`; `8`; `10`; `12`; `14`; `16`; `22`; `40`] THEN
  PL_SLOT_BOUNDS_TAC THEN
  REWRITE_TAC[plan_rel] THEN ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN REPEAT CONJ_TAC) THENL
   [(REWRITE_TAC[pl_set] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);
    (MATCH_MP_TAC PL_CWORDS_SET THEN EXISTS_TAC `m:int64->byte` THEN
  ASM_REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME] THEN REWRITE_TAC[GSYM drv_after] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_stack`)) (concl th) && can (find_term ((=) `drv_after`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_CTL_ADDR THEN MAP_EVERY EXISTS_TAC [`bw:num->int64`; `ctl:int64`; `nctl:num`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `18`] PL_LAYOUT_SLOT) THEN
    REWRITE_TAC[PL_SLOT_MEMS] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[drv_apart] THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_in]) THEN REWRITE_TAC[drv_in] THEN
    ASM_ARITH_TAC;
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `20`] PL_LAYOUT_SLOT) THEN
    REWRITE_TAC[PL_SLOT_MEMS] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[drv_apart] THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_in]) THEN REWRITE_TAC[drv_in] THEN
    ASM_ARITH_TAC]);
    (PL_ITAB_KEEP_TAC);
    (PL_ITAB_KEEP_TAC);
    (MATCH_MP_TAC PL_RTAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_SIMP_TAC[]);
    (MATCH_MP_TAC PL_MARKS_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_SIMP_TAC[]);
    (REWRITE_TAC[pl_rtab; LENGTH_APPEND; LENGTH; ARITH_RULE `n + SUC 0 = n + 1`] THEN REPEAT CONJ_TAC) THENL
     [(PL_AFTER_TAC `1` `20` `0` THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);
      (CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[]);
      (REPEAT STRIP_TAC THEN
  PL_AFTER_TAC `0` `18` `2 * i + w` THEN ANTS_TAC THENL
   [MP_TAC(SPECL [`2`; `i:num`; `w:num`; `LENGTH(ths:(num#num)list) + 1`] PL_ROW_WORD_BOUND) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_CASES_TAC `i < LENGTH(ths:(num#num)list)` THENL
   [ASM_SIMP_TAC[EL_APPEND] THEN
    SUBGOAL_THEN `2 * i + w < 2 * LENGTH(ths:(num#num)list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                  `m:int64->byte`; `used:int64`; `t:tisa_state`; `0`; `18`; `2 * i + w`] PL_CHILD_W) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS] THEN
    ANTS_TAC THENL
     [MP_TAC(SPECL [`2`; `i:num`; `w:num`; `LENGTH(ths:(num#num)list)`] PL_ROW_WORD_BOUND) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "pl_rtab" (concl th) &&
        can (find_term ((=) `pl_f2`)) (concl th))) THEN REWRITE_TAC[pl_rtab] THEN ARITH_TAC;
      STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "pl_rtab" (concl th) &&
        can (find_term ((=) `pl_f2`)) (concl th))) THEN REWRITE_TAC[pl_rtab] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `w:num`] o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `i = LENGTH(ths:(num#num)list)` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o REWRITE_RULE[ARITH_RULE `w < 2 <=> w = 0 \/ w = 1`] o
      check (fun th -> concl th = `w < 2`)) THEN
    REWRITE_TAC[pl_f2; ARITH_EQ; ADD_CLAUSES; FST; SND] THEN ASM_REWRITE_TAC[]])];
    (REWRITE_TAC[ARITH_RULE `n + SUC 0 = n + 1`] THEN MATCH_MP_TAC PL_MARKS_EXTEND THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MARKS_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[];
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    UNDISCH_TAC `8 * 2 * (LENGTH (ths:(num#num)list) + 1) <= val(bw 19:int64)` THEN
    UNDISCH_TAC `val(bw 19:int64) <= 2 * val(bw 23:int64)` THEN ARITH_TAC]);
    (MATCH_MP_TAC PL_STK_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_SIMP_TAC[])]);;

(* append_row on the theorem rows, with the width 2 in control word 2.       *)
let PL_IMPL_APPEND_TH = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 6 = append_row /\ val(EL 0 st) = 6 /\ val(EL 1 st) = 18 /\ val(EL 2 st) = 20 /\
     val(EL 12 st) = 2 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_impl; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`m:int64->byte`; `used:int64`; `cw:num->num`; `ctx:hupdate list`; `nms:string list`;
    `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`;
    `ths:(num#num)list`; `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`;
    `stk:num list`; `t:tisa_state`; `k:num`; `u:tisa_state`] THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [plan_rel]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(cw:num->num) 2 = 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `cw:num->num`)) (concl th) &&
      is_imp(snd(dest_forall(concl th))) && is_eq(rand(snd(dest_forall(concl th)))) &&
      rhs(rand(snd(dest_forall(concl th)))) = fst(dest_forall(concl th)))) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `0`; `18`] PL_CHILD_REGION) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `20`] PL_CHILD_REGION) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `20`; `0`] PL_CHILD_W) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if is_const_app "pl_rtab" (concl th) && can (find_term ((=) `pl_f2`)) (concl th)
     then STRIP_ASSUME_TAC(REWRITE_RULE[pl_rtab] th) else failwith "") THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (MP_TAC PL_APPEND_ROW_SPEC THEN REWRITE_TAC[pl_append_row_spec; pl_leaf_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o CONJUNCT2 o CONJUNCT2)
                             (MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`])) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `8 * 2 * (LENGTH (ths:(num#num)list) + 1) <= val(bw 19:int64)` THEN ASM_REWRITE_TAC[]) THENL
   [(DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k = 1`)) THEN
  MAP_EVERY EXISTS_TAC [`1`; `(ctx:hupdate list,nms:string list,tys:(num#num#num)list,
     ntms:(num#num#num#num#num)list,dbs:(num#num#num)list,
     APPEND (ths:(num#num)list) [((cw:num->num)(val(EL 10 (st:int64 list))), cw(val(EL 11 st)))],
     nmap:num list,ymap:num list,drops:(num#num)list,pol:num)`] THEN
  SUBGOAL_THEN `LENGTH (ths:(num#num)list) + 1 < 2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(ISPEC `bw 19:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [PL_LEAF_AT_TAC THEN ASM_REWRITE_TAC[pl_append_th] THEN
    EXISTS_TAC `APPEND ths [((cw:num->num)(val(EL 10 (st:int64 list))), cw(val(EL 11 st)))]` THEN
    REWRITE_TAC[] THEN DISJ1_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPEC `bw 19:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC;
    ARITH_TAC;
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC PL_REL_APPEND_TH THEN
    MAP_EVERY EXISTS_TAC [`budget:int64`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[PL_VAL_WORD_LT] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `EL j [tisa_fword t 22; tisa_fword t 23; tregs t 2; tregs t 3; tregs t 4]`)) (concl th)
       then MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) else failwith "") THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[ADD_CLAUSES; ARITH] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `nctl:num`)) (concl th) && can (find_term ((=) `10`)) (concl th))) THEN ARITH_TAC]);
    (DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k = 2`)) THEN
  MAP_EVERY EXISTS_TAC [`2`; `(ctx:hupdate list,nms:string list,tys:(num#num#num)list,
     ntms:(num#num#num#num#num)list,dbs:(num#num#num)list,ths:(num#num)list,
     nmap:num list,ymap:num list,drops:(num#num)list,pol:num)`] THEN
  REPEAT CONJ_TAC THENL
   [PL_LEAF_AT_TAC THEN ASM_REWRITE_TAC[pl_append_th] THEN EXISTS_TAC `ths:(num#num)list` THEN
    REWRITE_TAC[ARITH_EQ];
    ARITH_TAC;
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ARITH_EQ]])]);;

(* Agreement facts for one slot, from a slot agreement whose memory is mv. *)
let PL_AGREE_SLOT_MV_TAC mv j =
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) mv)) (concl th) &&
                           can (find_term ((=) `pl_slots`)) (concl th) &&
                           length(fst(strip_forall(concl th))) = 2
     then ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV THENC REWRITE_CONV[] THENC NUM_REDUCE_CONV)
                       (REWRITE_RULE[PL_SLOT_MEMS] (SPEC j th)))
     else failwith "");;

let PL_REL_ITAB_TY = prove
 (`!bw ctl nctl cfr m A cw ctx nms tys ntms dbs ths nmap ymap drops pol stk p v rows.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ p < nctl /\ 6 < p /\
     (!x. ~drv_stack cfr x /\ ~drv_in x (word_add ctl (word(8 * p))) 8 /\
          ~drv_in x (bw 0) (val(bw 1)) /\ ~drv_in x (bw 2) (val(bw 3)) /\ ~drv_in x (bw 4) (val(bw 5))
          ==> A x = (m:int64->byte) x) /\
     drv_word A (word_add ctl (word(8 * p))) = v /\ pl_itab bw 0 A rows
     ==> plan_rel bw ctl nctl cfr A (pl_set cw p (val v),(ctx,nms,rows,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[plan_rel] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  SUBGOAL_THEN `!j x. MEM j pl_slots /\ ~(j = 0) /\ ~(j = 2) /\ ~(j = 4) /\
                      drv_in x (bw j) (val(bw(j + 1))) ==> A x = (m:int64->byte) x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_stack`)) (concl th))) THEN
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`; `p:num`; `x:int64`]
      PL_SLOT_ADDR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`; `0`; `x:int64`]
       PL_SLOT_APART_IN) THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS];
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`; `2`; `x:int64`]
       PL_SLOT_APART_IN) THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS];
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`; `4`; `x:int64`]
       PL_SLOT_APART_IN) THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS]];
    ALL_TAC] THEN
  MAP_EVERY (PL_AGREE_SLOT_MV_TAC `A:int64->byte`) [`6`; `8`; `10`; `12`; `14`; `16`; `18`; `20`; `22`; `40`] THEN
  PL_SLOT_BOUNDS_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_set] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC PL_CWORDS_SET THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_stack`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_CTL_ADDR THEN MAP_EVERY EXISTS_TAC [`bw:num->int64`; `ctl:int64`; `nctl:num`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `0`] PL_LAYOUT_SLOT) THEN
      REWRITE_TAC[PL_SLOT_MEMS] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[drv_apart] THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_in]) THEN REWRITE_TAC[drv_in] THEN
      ASM_ARITH_TAC; MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `2`] PL_LAYOUT_SLOT) THEN
      REWRITE_TAC[PL_SLOT_MEMS] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[drv_apart] THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_in]) THEN REWRITE_TAC[drv_in] THEN
      ASM_ARITH_TAC; MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `4`] PL_LAYOUT_SLOT) THEN
      REWRITE_TAC[PL_SLOT_MEMS] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[drv_apart] THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_in]) THEN REWRITE_TAC[drv_in] THEN
      ASM_ARITH_TAC];
    PL_ITAB_KEEP_TAC;
    MATCH_MP_TAC PL_RTAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC PL_MARKS_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC PL_RTAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC PL_MARKS_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC PL_STK_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_SIMP_TAC[]]);;

let PL_REL_ITAB_DB = prove
 (`!bw ctl nctl cfr m A cw ctx nms tys ntms dbs ths nmap ymap drops pol stk p v rows.
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ p < nctl /\ 6 < p /\
     (!x. ~drv_stack cfr x /\ ~drv_in x (word_add ctl (word(8 * p))) 8 /\
          ~drv_in x (bw 6) (val(bw 7)) /\ ~drv_in x (bw 8) (val(bw 9)) /\ ~drv_in x (bw 10) (val(bw 11))
          ==> A x = (m:int64->byte) x) /\
     drv_word A (word_add ctl (word(8 * p))) = v /\ pl_itab bw 6 A rows
     ==> plan_rel bw ctl nctl cfr A (pl_set cw p (val v),(ctx,nms,tys,ntms,rows,ths,nmap,ymap,drops,pol),stk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[plan_rel] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  SUBGOAL_THEN `!j x. MEM j pl_slots /\ ~(j = 6) /\ ~(j = 8) /\ ~(j = 10) /\
                      drv_in x (bw j) (val(bw(j + 1))) ==> A x = (m:int64->byte) x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_stack`)) (concl th))) THEN
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`; `p:num`; `x:int64`]
      PL_SLOT_ADDR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`; `6`; `x:int64`]
       PL_SLOT_APART_IN) THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS];
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`; `8`; `x:int64`]
       PL_SLOT_APART_IN) THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS];
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`; `10`; `x:int64`]
       PL_SLOT_APART_IN) THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[PL_SLOT_MEMS]];
    ALL_TAC] THEN
  MAP_EVERY (PL_AGREE_SLOT_MV_TAC `A:int64->byte`) [`0`; `2`; `4`; `12`; `14`; `16`; `18`; `20`; `22`; `40`] THEN
  PL_SLOT_BOUNDS_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_set] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC PL_CWORDS_SET THEN EXISTS_TAC `m:int64->byte` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `drv_stack`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_CTL_ADDR THEN MAP_EVERY EXISTS_TAC [`bw:num->int64`; `ctl:int64`; `nctl:num`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `6`] PL_LAYOUT_SLOT) THEN
      REWRITE_TAC[PL_SLOT_MEMS] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[drv_apart] THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_in]) THEN REWRITE_TAC[drv_in] THEN
      ASM_ARITH_TAC; MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `8`] PL_LAYOUT_SLOT) THEN
      REWRITE_TAC[PL_SLOT_MEMS] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[drv_apart] THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_in]) THEN REWRITE_TAC[drv_in] THEN
      ASM_ARITH_TAC; MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `10`] PL_LAYOUT_SLOT) THEN
      REWRITE_TAC[PL_SLOT_MEMS] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[drv_apart] THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_in]) THEN REWRITE_TAC[drv_in] THEN
      ASM_ARITH_TAC];
    PL_ITAB_KEEP_TAC;
    MATCH_MP_TAC PL_RTAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC PL_MARKS_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC PL_RTAB_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC PL_MARKS_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC PL_STK_AGREE THEN EXISTS_TAC `m:int64->byte` THEN ASM_SIMP_TAC[]]);;


(* An interner of the relation, seen from any state with its regions and   *)
(* their bytes: well formed, with the relation's rows.                      *)
let PL_ITAB_STATE = prove
 (`!bw j m rows t.
     pl_itab bw j m rows /\
     (!r. r < 3 ==> tisa_base t r = bw(j + 2 * r) /\ tisa_len t r = bw(j + 2 * r + 1)) /\
     (!r. r < 3 ==> val(bw(j + 2 * r)) + val(bw(j + 2 * r + 1)) < 2 EXP 64) /\
     8 <= val(bw(j + 5)) /\
     (!r a. r < 3 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1))) ==> tmem t a = m a)
     ==> intern_ok t /\ val(intern_count t) = LENGTH rows /\
         (!i. i < LENGTH rows
              ==> EL i rows = (val(intern_word t (2 * i)) MOD 8, val(intern_word t (2 * i)) DIV 8,
                               val(intern_word t (2 * i + 1))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_itab] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t0:tisa_state` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`t0:tisa_state`; `t:tisa_state`] INTERN16_SAME_REGIONS) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `2` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `t0:tisa_state`)) (concl th) && can (find_term ((=) `tisa_base`)) (concl th))) THEN
      REWRITE_TAC[ARITH] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `drv_in a (bw(j + 2 * r):int64) (val(bw(j + 2 * r + 1):int64))` ASSUME_TAC THENL
       [REWRITE_TAC[drv_in] THEN UNDISCH_TAC `val(a:int64) < val(tisa_base t0 r) + val(tisa_len t0 r)` THEN
        UNDISCH_TAC `val(tisa_base t0 r) <= val(a:int64)` THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(fun th -> let c = concl th in
         if is_forall c && length(fst(strip_forall c)) = 2 && can (find_term ((=) `tmem t`)) c
         then MP_TAC(SPECL [`r:num`; `a:int64`] th) else failwith "") THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      FIRST_ASSUM(fun th -> let c = concl th in
         if is_forall c && length(fst(strip_forall c)) = 2 && can (find_term ((=) `tmem t0`)) c
         then MP_TAC(SPECL [`r:num`; `a:int64`] th) else failwith "") THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "EL" with Failure _ -> false)) (concl th)
       then REWRITE_TAC[MATCH_MP th (ASSUME `i < LENGTH (rows:(num#num#num)list)`)] else failwith "") THEN
    SUBGOAL_THEN `2 * i < 2 * val(intern_count t0) /\ 2 * i + 1 < 2 * val(intern_count t0)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[]]]);;

let PL_SLOT_NOT_STACK = prove
 (`!bw ctl nctl cfr j a.
     pl_layout bw ctl nctl cfr /\ MEM j pl_slots /\ drv_in a (bw j) (val(bw(j + 1)))
     ==> ~drv_stack cfr a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`] PL_LAYOUT_SLOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cfr:int64`; `a:int64`; `bw(j:num):int64`; `val(bw(j + 1):int64)`] DRV_IN_NOT_STACK) THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[pl_layout]) THEN ASM_REWRITE_TAC[]);;

(* The facts PL_ITAB_STATE needs, for the child of an intern16 step on the  *)
(* interner at slot j and for the leaf's final state.                         *)
let PL_I16_CHILD = prove
 (`!bw ctl nctl budget cfr st m used t j.
     pl_layout bw ctl nctl cfr /\ (j = 0 \/ j = 6) /\ drv_child bw ctl budget cfr st m used t /\
     val(EL 1 st) = j /\ val(EL 2 st) = j + 2 /\ val(EL 3 st) = j + 4
     ==> (!r. r < 3 ==> tisa_base t r = bw(j + 2 * r) /\ tisa_len t r = bw(j + 2 * r + 1)) /\
         (!r. r < 3 ==> val(bw(j + 2 * r)) + val(bw(j + 2 * r + 1)) < 2 EXP 64) /\
         8 <= val(bw(j + 5)) /\
         (!r a. r < 3 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1))) ==> tmem t a = m a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th -> concl th = `j = 0 \/ j = 6`)) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
  REWRITE_TAC[ARITH_RULE `r < 3 <=> r = 0 \/ r = 1 \/ r = 2`] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  (DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) ORELSE ALL_TAC) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV THENC DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV THENC DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV)) THEN
  ASM_REWRITE_TAC[] THEN
  TRY(W(fun (asl,w) -> let e = lhand w in let r = rand(lhs e) and j = rand(rhs e) in
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                  `m:int64->byte`; `used:int64`; `t:tisa_state`; r; j] PL_CHILD_REGION) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_LT_CONV) THEN
    SIMP_TAC[]) THEN NO_TAC) THEN
  TRY(W(fun (asl,w) ->
    let lay = find (fun th -> is_const_app "pl_layout" (concl th)) (map snd asl) in
    let j = rand(rand(lhand(lhand w))) in
    let mem = EQT_ELIM(REWRITE_CONV[PL_SLOT_MEMS] (mk_comb(mk_comb(`MEM:num->num list->bool`, j), `pl_slots`))) in
    ACCEPT_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV) (CONJUNCT1(MATCH_MP PL_LAYOUT_SLOT (CONJ lay mem))))) THEN NO_TAC) THEN
  W(fun (asl,w) ->
    let d = concl(find (fun th -> is_const_app "drv_in" (concl th)) (map snd asl)) in
    let j = rand(rand(rator d)) in
    let lay = find (fun th -> is_const_app "pl_layout" (concl th)) (map snd asl) in
    let mem = EQT_ELIM(REWRITE_CONV[PL_SLOT_MEMS] (mk_comb(mk_comb(`MEM:num->num list->bool`, j), `pl_slots`))) in
    let dc = find (fun th -> is_const_app "drv_child" (concl th)) (map snd asl) in
    let a = rand(rator(rator d)) in
    let lem = CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
                (SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; j; a] PL_SLOT_NOT_STACK) in
    let ns = MP lem (CONJ lay (CONJ mem (ASSUME d))) in
    ACCEPT_TAC(MATCH_MP (CONJUNCT2(CONJUNCT2(GEN_REWRITE_RULE I [drv_child] dc))) ns)));;

let PL_I16_AFTER = prove
 (`!bw ctl nctl budget cfr st m used t k u j.
     pl_layout bw ctl nctl cfr /\ (j = 0 \/ j = 6) /\ drv_child bw ctl budget cfr st m used t /\
     val(EL 1 st) = j /\ val(EL 2 st) = j + 2 /\ val(EL 3 st) = j + 4 /\ val(EL 17 st) < nctl /\
     tisa_entry_ok intern16 t /\ tisa_run intern16 t = TStop k u
     ==> (!r. r < 3 ==> tisa_base u r = bw(j + 2 * r) /\ tisa_len u r = bw(j + 2 * r + 1)) /\
         (!r a. r < 3 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1)))
                ==> tmem u a = drv_after ctl st u a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `j:num`] PL_I16_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[tisa_base; tisa_len] THEN
    MP_TAC(SPECL [`intern16`; `t:tisa_state`; `k:num`; `u:tisa_state`; `2 * r`] PL_RUN_FRAME) THEN
    MP_TAC(SPECL [`intern16`; `t:tisa_state`; `k:num`; `u:tisa_state`; `2 * r + 1`] PL_RUN_FRAME) THEN
    ASM_REWRITE_TAC[INTERN16_LEAF_WF] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM tisa_base; GSYM tisa_len] THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[drv_after] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN
    SUBGOAL_THEN `MEM (j + 2 * r) pl_slots` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th -> concl th = `j = 0 \/ j = 6`)) THEN
      FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o
        REWRITE_RULE[ARITH_RULE `r < 3 <=> r = 0 \/ r = 1 \/ r = 2`] o check (fun th -> concl th = `r < 3`)) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[PL_SLOT_MEMS];
      ALL_TAC] THEN
    MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j + 2 * r`;
                  `val(EL 17 (st:int64 list))`; `a:int64`] PL_SLOT_ADDR) THEN
    ASM_REWRITE_TAC[ARITH_RULE `(j + 2 * r) + 1 = j + 2 * r + 1`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`ctl:int64`; `8 * val(EL 17 (st:int64 list))`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    UNDISCH_TAC `~drv_in (a:int64) (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8` THEN
    ASM_REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC]);;

let PL_I16_GOAL = `!bw ctl nctl budget cfr st m used t k u j rows.
     pl_layout bw ctl nctl cfr /\ (j = 0 \/ j = 6) /\ pl_itab bw j m rows /\
     drv_child bw ctl budget cfr st m used t /\
     val(EL 1 st) = j /\ val(EL 2 st) = j + 2 /\ val(EL 3 st) = j + 4 /\ val(EL 17 st) < nctl /\
     tisa_entry_ok intern16 t /\ tisa_run intern16 t = TStop k u
     ==> k < 8 /\ ~(k = 0) /\ tisa_fword u 18 = word k /\
         (k = 1
          ==> val(tisa_fword u 19) < 2 EXP 60 /\
              ?md. pl_interned rows (pl_key (val(tisa_fword t 22)) (val(tisa_fword t 23)))
                               (val(tisa_fword u 19)) md /\
                   pl_itab bw j (drv_after ctl st u) (APPEND rows md))`;;

let PL_I16_PAY_TAC =
  SUBGOAL_THEN `val(intern_count u) < 2 EXP 60` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [intern_ok] o
      check (fun th -> concl th = `intern_ok u`)) THEN
    MP_TAC(ISPEC `tisa_len u 0` VAL_BOUND_64) THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC];;
let PL_I16_ROWS_TAC =
  (* rows of the relation decode u's words below the old count *)
  SUBGOAL_THEN `!i. i < LENGTH (rows:(num#num#num)list)
                    ==> EL i rows = (val(intern_word u (2 * i)) MOD 8, val(intern_word u (2 * i)) DIV 8,
                                     val(intern_word u (2 * i + 1)))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "EL" with Failure _ -> false)) (concl th) &&
         can (find_term ((=) `intern_word t`)) (concl th)
       then REWRITE_TAC[MATCH_MP th (ASSUME `i < LENGTH (rows:(num#num#num)list)`)] else failwith "") THEN
    SUBGOAL_THEN `2 * i < 2 * LENGTH (rows:(num#num#num)list) /\ 2 * i + 1 < 2 * LENGTH rows`
      STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC];;
let PL_I16_KEPT_TAC =
  (* the kept words, oriented from u to t, as a conditional rewrite *)
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `intern_word u i`)) (concl th) &&
                           can (find_term ((=) `intern_word t i`)) (concl th)
     then ASSUME_TAC th else failwith "");;
let PL_DIVMOD_EQ = prove
 (`!x y. x MOD 8 = y MOD 8 /\ x DIV 8 = y DIV 8 ==> x = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:num`; `8`] DIVISION) THEN MP_TAC(SPECL [`y:num`; `8`] DIVISION) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* intern16 on the interner at slot j (0 types, 6 de Bruijn terms): its     *)
(* outcome is never REFUSED, and when it FIRED the key's row was found or   *)
(* appended, the interner of the memory after the step holding the rows.    *)
let PL_I16_STEP = prove
 (`!bw ctl nctl budget cfr st m used t k u j rows.
     pl_layout bw ctl nctl cfr /\ (j = 0 \/ j = 6) /\ pl_itab bw j m rows /\
     drv_child bw ctl budget cfr st m used t /\
     val(EL 1 st) = j /\ val(EL 2 st) = j + 2 /\ val(EL 3 st) = j + 4 /\ val(EL 17 st) < nctl /\
     tisa_entry_ok intern16 t /\ tisa_run intern16 t = TStop k u
     ==> k < 8 /\ ~(k = 0) /\ tisa_fword u 18 = word k /\
         (k = 1
          ==> val(tisa_fword u 19) < 2 EXP 60 /\
              ?md. pl_interned rows (pl_key (val(tisa_fword t 22)) (val(tisa_fword t 23)))
                               (val(tisa_fword u 19)) md /\
                   pl_itab bw j (drv_after ctl st u) (APPEND rows md))`,
  (REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`intern16`; `t:tisa_state`; `k:num`; `u:tisa_state`] TISA_RUN_STATUS) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[intern16; intern16_prologue; intern16_body; tisa_root; tisa_returns] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `k < 8 /\ ~(k = 0)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k = 1`)) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `j:num`] PL_I16_CHILD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `j:num`; `m:int64->byte`; `rows:(num#num#num)list`; `t:tisa_state`]
    PL_ITAB_STATE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:tisa_state`; `1`; `u:tisa_state`] INTERN16_TISA_RUN_COMPLETE) THEN
  ASM_REWRITE_TAC[intern16_post] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `u:tisa_state`; `j:num`] PL_I16_AFTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC) THENL
   [(PL_I16_PAY_TAC THEN PL_I16_ROWS_TAC THEN EXISTS_TAC `[]:(num#num#num)list` THEN
  REWRITE_TAC[pl_interned; APPEND_NIL; pl_key] THEN CONJ_TAC THENL
   [DISJ1_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(tisa_fword u 19) < LENGTH (rows:(num#num#num)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "EL" with Failure _ -> false)) (concl th) &&
         can (find_term ((=) `intern_word u`)) (concl th)
       then REWRITE_TAC[MATCH_MP th (ASSUME `val(tisa_fword u 19) < LENGTH (rows:(num#num#num)list)`)]
       else failwith "") THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[pl_itab] THEN EXISTS_TAC `u:tisa_state` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "EL" with Failure _ -> false)) (concl th) &&
         can (find_term ((=) `intern_word u`)) (concl th)
       then ACCEPT_TAC th else failwith "")]);
    (PL_I16_PAY_TAC THEN PL_I16_ROWS_TAC THEN
  EXISTS_TAC `[pl_key (val(tisa_fword t 22)) (val(tisa_fword t 23))]` THEN
  REWRITE_TAC[pl_interned; NOT_CONS_NIL] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[MEM_EXISTS_EL; pl_key] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPECL [`t:tisa_state`; `u:tisa_state`] INTERN16_TISA_RUN_APPEND_ABSENT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[intern_has] THEN
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
           can (find_term (fun t -> try fst(dest_const t) = "EL" with Failure _ -> false)) (concl th) &&
           can (find_term ((=) `intern_word t`)) (concl th)
         then MP_TAC(MATCH_MP th (ASSUME `i < LENGTH (rows:(num#num#num)list)`)) else failwith "") THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && is_pair(lhs(concl th)))) THEN
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
      CONJ_TAC THEN MATCH_MP_TAC PL_DIVMOD_EQ THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    REWRITE_TAC[pl_itab] THEN EXISTS_TAC `u:tisa_state` THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; ARITH_RULE `n + SUC 0 = n + 1`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i < LENGTH (rows:(num#num#num)list)` THENL
     [ASM_SIMP_TAC[EL_APPEND] THEN
      SUBGOAL_THEN `2 * i < 2 * LENGTH (rows:(num#num#num)list) /\ 2 * i + 1 < 2 * LENGTH rows` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
      SUBGOAL_THEN `i = LENGTH (rows:(num#num#num)list)` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD; pl_key] THEN
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `val(tisa_fword u 19)` then
         (RULE_ASSUM_TAC(REWRITE_RULE[th])) else failwith "") THEN
      ASM_REWRITE_TAC[]]])]);;

(* intern16 on the type interner: outcome, receipt, and when it FIRED, the  *)
(* abstract intern fact and the relation after the step.                      *)
let PL_I16_CORE_TY = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 0 = intern16 /\ val(EL 0 st) = 0 /\ val(EL 1 st) = 0 /\ val(EL 2 st) = 2 /\ val(EL 3 st) = 4 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> !m used cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t k u.
           plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
           ~(val budget < val used) /\ drv_child bw ctl budget cfr st m used t /\
           tisa_entry_ok (progs (val(EL 0 st))) t /\ tisa_run (progs (val(EL 0 st))) t = TStop k u
           ==> k < 8 /\ tisa_fword u 18 = word k /\ ~(val budget < val(tisa_fword u 21)) /\
               ((k = 1 /\ val(tisa_fword u 19) < 2 EXP 60 /\
                 ?md. pl_interned tys (pl_key (cw(val(EL 10 st))) (cw(val(EL 11 st)))) (val(tisa_fword u 19)) md /\
                      plan_rel bw ctl nctl cfr (drv_after ctl st u)
                        (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),
                         (ctx,nms,APPEND tys md,ntms,dbs,ths,nmap,ymap,drops,pol),stk)) \/
                (~(k = 0) /\ ~(k = 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [plan_rel]) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; `0`;
                `tys:(num#num#num)list`] PL_I16_STEP) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`intern16`; `t:tisa_state`; `k:num`; `u:tisa_state`] TISA_RUN_FUEL) THEN
  ASM_REWRITE_TAC[INTERN16_LEAF_WF] THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k = 1`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && lhand(concl th) = `1 = 1`)) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `md:(num#num#num)list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_REL_ITAB_TY THEN EXISTS_TAC `m:int64->byte` THEN EXISTS_TAC `tys:(num#num#num)list` THEN
  ASM_REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME] THEN REWRITE_TAC[GSYM drv_after] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC THEN NO_TAC) THEN
  X_GEN_TAC `x:int64` THEN STRIP_TAC THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
  MAP_EVERY EXISTS_TAC [`intern16`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                        `used:int64`; `t:tisa_state`; `1`] THEN
  ASM_REWRITE_TAC[INTERN16_LEAF_WF; REWRITE_RULE[INTERN16_DECLS] INTERN16_REGION_KINDS; INTERN16_DECLS] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    X_GEN_TAC `r:num` THEN REWRITE_TAC[ARITH_RULE `r < 3 <=> r = 0 \/ r = 1 \/ r = 2`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]);;

let PL_I16_CORE_DB = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 0 = intern16 /\ val(EL 0 st) = 0 /\ val(EL 1 st) = 6 /\ val(EL 2 st) = 8 /\ val(EL 3 st) = 10 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> !m used cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t k u.
           plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
           ~(val budget < val used) /\ drv_child bw ctl budget cfr st m used t /\
           tisa_entry_ok (progs (val(EL 0 st))) t /\ tisa_run (progs (val(EL 0 st))) t = TStop k u
           ==> k < 8 /\ tisa_fword u 18 = word k /\ ~(val budget < val(tisa_fword u 21)) /\
               ((k = 1 /\ val(tisa_fword u 19) < 2 EXP 60 /\
                 ?md. pl_interned dbs (pl_key (cw(val(EL 10 st))) (cw(val(EL 11 st)))) (val(tisa_fword u 19)) md /\
                      plan_rel bw ctl nctl cfr (drv_after ctl st u)
                        (pl_set cw (val(EL 17 st)) (val(tisa_fword u 19)),
                         (ctx,nms,tys,ntms,APPEND dbs md,ths,nmap,ymap,drops,pol),stk)) \/
                (~(k = 0) /\ ~(k = 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [plan_rel]) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `k:num`; `u:tisa_state`; `6`;
                `dbs:(num#num#num)list`] PL_I16_STEP) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`intern16`; `t:tisa_state`; `k:num`; `u:tisa_state`] TISA_RUN_FUEL) THEN
  ASM_REWRITE_TAC[INTERN16_LEAF_WF] THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k = 1`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && lhand(concl th) = `1 = 1`)) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `md:(num#num#num)list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_REL_ITAB_DB THEN EXISTS_TAC `m:int64->byte` THEN EXISTS_TAC `dbs:(num#num#num)list` THEN
  ASM_REWRITE_TAC[drv_after; DRV_WORD_WRITE_SAME] THEN REWRITE_TAC[GSYM drv_after] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC THEN NO_TAC) THEN
  X_GEN_TAC `x:int64` THEN STRIP_TAC THEN MATCH_MP_TAC DRV_STEP_KEEPS THEN
  MAP_EVERY EXISTS_TAC [`intern16`; `bw:num->int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                        `used:int64`; `t:tisa_state`; `1`] THEN
  ASM_REWRITE_TAC[INTERN16_LEAF_WF; REWRITE_RULE[INTERN16_DECLS] INTERN16_REGION_KINDS; INTERN16_DECLS] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_layout]) THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    X_GEN_TAC `r:num` THEN REWRITE_TAC[ARITH_RULE `r < 3 <=> r = 0 \/ r = 1 \/ r = 2`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]);;

(* The host's leaf table for the record plans (PLANS.txt, section 2). *)
let pl_progs_ok = new_definition
 `pl_progs_ok (progs:num->tisa_prog) <=>
    progs 0 = intern16 /\ progs 1 = pack /\ progs 2 = unpack /\ progs 3 = eqw /\
    progs 4 = row_word /\ progs 5 = live /\ progs 6 = append_row`;;

(* Every step of a plan has its control words below nctl. *)
let pl_cw_range = new_definition
 `pl_cw_range nctl (P:(int64 list)list) <=>
    !st f. MEM st P /\ 10 <= f /\ f < 18 ==> val(EL f st) < nctl`;;







(* intern16 on the two interners. Its outcome is FIRED (the key's row found *)
(* or appended), or one that is neither FIRED nor REFUSED (pl_intern).      *)
let PL_I16_BRIDGE_TAC core tab =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP core) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  REWRITE_TAC[pl_impl; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`m:int64->byte`; `used:int64`; `cw:num->num`; `ctx:hupdate list`; `nms:string list`;
    `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`;
    `ths:(num#num)list`; `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`;
    `stk:num list`; `t:tisa_state`; `k:num`; `u:tisa_state`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `m:int64->byte`; `used:int64`; `cw:num->num`; `ctx:hupdate list`; `nms:string list`;
    `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`;
    `ths:(num#num)list`; `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`;
    `stk:num list`; `t:tisa_state`; `k:num`; `u:tisa_state`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `drv_after`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 ASSUME_TAC
         (X_CHOOSE_THEN `md:(num#num#num)list` STRIP_ASSUME_TAC)))
      STRIP_ASSUME_TAC)))) THENL
   [EXISTS_TAC `1` THEN
    EXISTS_TAC (if tab = 0 then
      `(ctx:hupdate list,nms:string list,APPEND (tys:(num#num#num)list) md,ntms:(num#num#num#num#num)list,
        dbs:(num#num#num)list,ths:(num#num)list,nmap:num list,ymap:num list,drops:(num#num)list,pol:num)`
     else
      `(ctx:hupdate list,nms:string list,tys:(num#num#num)list,ntms:(num#num#num#num#num)list,
        APPEND (dbs:(num#num#num)list) md,ths:(num#num)list,nmap:num list,ymap:num list,drops:(num#num)list,pol:num)`) THEN
    ASM_REWRITE_TAC[FST; SND; ARITH] THEN PL_LEAF_AT_TAC THEN
    EXISTS_TAC (if tab = 0 then `APPEND (tys:(num#num#num)list) md` else `APPEND (dbs:(num#num#num)list) md`) THEN
    REWRITE_TAC[pl_intern; ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `md:(num#num#num)list` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `k:num` THEN
    EXISTS_TAC `(ctx:hupdate list,nms:string list,tys:(num#num#num)list,ntms:(num#num#num#num#num)list,
        dbs:(num#num#num)list,ths:(num#num)list,nmap:num list,ymap:num list,drops:(num#num)list,pol:num)` THEN
    ASM_REWRITE_TAC[] THEN PL_LEAF_AT_TAC THEN
    EXISTS_TAC (if tab = 0 then `tys:(num#num#num)list` else `dbs:(num#num#num)list`) THEN
    REWRITE_TAC[pl_intern] THEN ASM_REWRITE_TAC[]];;

let PL_IMPL_INTERN_TY = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 0 = intern16 /\ val(EL 0 st) = 0 /\ val(EL 1 st) = 0 /\ val(EL 2 st) = 2 /\ val(EL 3 st) = 4 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_I16_BRIDGE_TAC PL_I16_CORE_TY 0);;

let PL_IMPL_INTERN_DB = prove
 (`!progs bw ctl nctl budget cfr st.
     progs 0 = intern16 /\ val(EL 0 st) = 0 /\ val(EL 1 st) = 6 /\ val(EL 2 st) = 8 /\ val(EL 3 st) = 10 /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> pl_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr st`,
  PL_I16_BRIDGE_TAC PL_I16_CORE_DB 6);;

let PL_BRIDGES = [PL_IMPL_INTERN_TY; PL_IMPL_INTERN_DB; PL_IMPL_PACK; PL_IMPL_UNPACK; PL_IMPL_EQW;
                  PL_IMPL_ROWW_TY; PL_IMPL_ROWW_DB; PL_IMPL_ROWW_TM; PL_IMPL_ROWW_TH;
                  PL_IMPL_LIVE_TM; PL_IMPL_LIVE_TH; PL_IMPL_APPEND_TH];;

(* pl_leaf_impl of leaf n in plan P from the bridges: every step of P that  *)
(* calls n is one of the bridged forms, by computation on P's data.         *)
let PL_LEAF_IMPL_TAC plan_def =
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_progs_ok; pl_cw_range] THEN STRIP_TAC THEN
  REWRITE_TAC[pl_leaf_impl] THEN X_GEN_TAC `st:int64 list` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!f. 10 <= f /\ f < 18 ==> val(EL f (st:int64 list)) < nctl` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "MEM" (concl th))) THEN
  REWRITE_TAC[plan_def; MEM] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC)) THEN TRY(DISCH_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV)) THEN
  TRY(FIRST_ASSUM(fun th -> if concl th = `F` then CONTR_TAC th else NO_TAC)) THEN
  FIRST(map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN
                       CONV_TAC(DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) THEN
                       ASM_REWRITE_TAC[] THEN NO_TAC) PL_BRIDGES);;

(* Each plan's bridged leaves, by computation on the plan's data. *)
let PL_LEAF_ASSUME_INTERN16 = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_assume
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_assume 0`,
  PL_LEAF_IMPL_TAC pl_plan_assume);;
let PL_LEAF_ASSUME_PACK = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_assume
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_assume 1`,
  PL_LEAF_IMPL_TAC pl_plan_assume);;
let PL_LEAF_ASSUME_EQW = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_assume
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_assume 3`,
  PL_LEAF_IMPL_TAC pl_plan_assume);;
let PL_LEAF_ASSUME_ROW_WORD = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_assume
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_assume 4`,
  PL_LEAF_IMPL_TAC pl_plan_assume);;
let PL_LEAF_ASSUME_LIVE = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_assume
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_assume 5`,
  PL_LEAF_IMPL_TAC pl_plan_assume);;
let PL_LEAF_ASSUME_APPEND_ROW = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_assume
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_assume 6`,
  PL_LEAF_IMPL_TAC pl_plan_assume);;
let PL_LEAF_REFL_INTERN16 = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_refl
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_refl 0`,
  PL_LEAF_IMPL_TAC pl_plan_refl);;
let PL_LEAF_REFL_PACK = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_refl
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_refl 1`,
  PL_LEAF_IMPL_TAC pl_plan_refl);;
let PL_LEAF_REFL_ROW_WORD = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_refl
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_refl 4`,
  PL_LEAF_IMPL_TAC pl_plan_refl);;
let PL_LEAF_REFL_LIVE = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_refl
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_refl 5`,
  PL_LEAF_IMPL_TAC pl_plan_refl);;
let PL_LEAF_REFL_APPEND_ROW = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_refl
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_refl 6`,
  PL_LEAF_IMPL_TAC pl_plan_refl);;
let PL_LEAF_EQMP_UNPACK = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_eqmp
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_eqmp 2`,
  PL_LEAF_IMPL_TAC pl_plan_eqmp);;
let PL_LEAF_EQMP_EQW = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_eqmp
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_eqmp 3`,
  PL_LEAF_IMPL_TAC pl_plan_eqmp);;
let PL_LEAF_EQMP_ROW_WORD = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_eqmp
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_eqmp 4`,
  PL_LEAF_IMPL_TAC pl_plan_eqmp);;
let PL_LEAF_EQMP_LIVE = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_eqmp
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_eqmp 5`,
  PL_LEAF_IMPL_TAC pl_plan_eqmp);;
let PL_LEAF_EQMP_APPEND_ROW = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_eqmp
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_eqmp 6`,
  PL_LEAF_IMPL_TAC pl_plan_eqmp);;
let PL_LEAF_TRANS_INTERN16 = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_trans
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_trans 0`,
  PL_LEAF_IMPL_TAC pl_plan_trans);;
let PL_LEAF_TRANS_PACK = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_trans
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_trans 1`,
  PL_LEAF_IMPL_TAC pl_plan_trans);;
let PL_LEAF_TRANS_UNPACK = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_trans
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_trans 2`,
  PL_LEAF_IMPL_TAC pl_plan_trans);;
let PL_LEAF_TRANS_EQW = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_trans
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_trans 3`,
  PL_LEAF_IMPL_TAC pl_plan_trans);;
let PL_LEAF_TRANS_ROW_WORD = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_trans
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_trans 4`,
  PL_LEAF_IMPL_TAC pl_plan_trans);;
let PL_LEAF_TRANS_LIVE = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_trans
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_trans 5`,
  PL_LEAF_IMPL_TAC pl_plan_trans);;
let PL_LEAF_TRANS_APPEND_ROW = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_trans
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_trans 6`,
  PL_LEAF_IMPL_TAC pl_plan_trans);;
let PL_LEAF_MKCOMB_INTERN16 = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_mkcomb
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_mkcomb 0`,
  PL_LEAF_IMPL_TAC pl_plan_mkcomb);;
let PL_LEAF_MKCOMB_PACK = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_mkcomb
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_mkcomb 1`,
  PL_LEAF_IMPL_TAC pl_plan_mkcomb);;
let PL_LEAF_MKCOMB_UNPACK = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_mkcomb
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_mkcomb 2`,
  PL_LEAF_IMPL_TAC pl_plan_mkcomb);;
let PL_LEAF_MKCOMB_EQW = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_mkcomb
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_mkcomb 3`,
  PL_LEAF_IMPL_TAC pl_plan_mkcomb);;
let PL_LEAF_MKCOMB_ROW_WORD = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_mkcomb
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_mkcomb 4`,
  PL_LEAF_IMPL_TAC pl_plan_mkcomb);;
let PL_LEAF_MKCOMB_LIVE = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_mkcomb
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_mkcomb 5`,
  PL_LEAF_IMPL_TAC pl_plan_mkcomb);;
let PL_LEAF_MKCOMB_APPEND_ROW = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_mkcomb
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_mkcomb 6`,
  PL_LEAF_IMPL_TAC pl_plan_mkcomb);;
let PL_LEAF_EXPECT_ALPHA_EQW = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_expect_alpha
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_expect_alpha 3`,
  PL_LEAF_IMPL_TAC pl_plan_expect_alpha);;
let PL_LEAF_EXPECT_ALPHA_ROW_WORD = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_expect_alpha
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_expect_alpha 4`,
  PL_LEAF_IMPL_TAC pl_plan_expect_alpha);;
let PL_LEAF_EXPECT_ALPHA_LIVE = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_expect_alpha
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_expect_alpha 5`,
  PL_LEAF_IMPL_TAC pl_plan_expect_alpha);;

(* The records through the driver under plan_rel: the bridged leaves' premises *)
(* discharged; the leaves not yet built stay premises (LEDGER.txt part 4).     *)
let PL_ASSUME_REL = prove
 (`!progs bw ctl nctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t.
     pl_progs_ok progs /\ pl_cw_range nctl pl_plan_assume /\
     drv_sem progs bw ctl budget cfr pl_plan_assume 0 m used res /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = t
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAssume t) (FST(SND s')) /\
                    pl_inv s') /\ plan_rel bw ctl nctl cfr (FST(SND(SND res))) s') /\
         (FST res = word 0 <=>
          ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAssume t) /\
            ?p. fdtm nms tys ntms t p /\ htypeof p = HBool))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`plan_rel bw ctl nctl cfr`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
                `budget:int64`; `cfr:int64`; `m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`; `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `t:num`] PL_ASSUME_DRV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN FIRST(map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC)
    [PL_LEAF_ASSUME_INTERN16; PL_LEAF_ASSUME_PACK; PL_LEAF_ASSUME_EQW; PL_LEAF_ASSUME_ROW_WORD; PL_LEAF_ASSUME_LIVE; PL_LEAF_ASSUME_APPEND_ROW]));;

let PL_REFL_REL = prove
 (`!progs bw ctl nctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t.
     pl_progs_ok progs /\ pl_cw_range nctl pl_plan_refl /\
     drv_sem progs bw ctl budget cfr pl_plan_refl 0 m used res /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = t
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t) (FST(SND s')) /\
                    pl_inv s') /\ plan_rel bw ctl nctl cfr (FST(SND(SND res))) s') /\
         (FST res = word 0 <=>
          ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t) /\
            ?tm. fdtm nms tys ntms t tm))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`plan_rel bw ctl nctl cfr`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
                `budget:int64`; `cfr:int64`; `m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`; `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `t:num`] PL_REFL_DRV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN FIRST(map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC)
    [PL_LEAF_REFL_INTERN16; PL_LEAF_REFL_PACK; PL_LEAF_REFL_ROW_WORD; PL_LEAF_REFL_LIVE; PL_LEAF_REFL_APPEND_ROW]));;

let PL_EQMP_REL = prove
 (`!progs bw ctl nctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2.
     pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_eqmp 7 /\
     pl_progs_ok progs /\ pl_cw_range nctl pl_plan_eqmp /\
     drv_sem progs bw ctl budget cfr pl_plan_eqmp 0 m used res /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = h1 /\ cw 9 = h2
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REqMp h1 h2) (FST(SND s')) /\
                    pl_inv s') /\ plan_rel bw ctl nctl cfr (FST(SND(SND res))) s') /\
         (FST res = word 0 <=>
          ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REqMp h1 h2) /\
            ?ty p q. fddb nms tys dbs (SND(EL h1 ths)) (hdbComb (hdbComb (hdbConst "=" ty) p) q) /\
                     fddb nms tys dbs (SND(EL h2 ths)) p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`plan_rel bw ctl nctl cfr`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
                `budget:int64`; `cfr:int64`; `m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`; `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `h1:num`; `h2:num`] PL_EQMP_DRV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN FIRST(map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC)
    [PL_LEAF_EQMP_UNPACK; PL_LEAF_EQMP_EQW; PL_LEAF_EQMP_ROW_WORD; PL_LEAF_EQMP_LIVE; PL_LEAF_EQMP_APPEND_ROW]));;

let PL_TRANS_REL = prove
 (`!progs bw ctl nctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2.
     pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_trans 7 /\
     pl_progs_ok progs /\ pl_cw_range nctl pl_plan_trans /\
     drv_sem progs bw ctl budget cfr pl_plan_trans 0 m used res /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = h1 /\ cw 9 = h2
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTrans h1 h2) (FST(SND s')) /\
                    pl_inv s') /\ plan_rel bw ctl nctl cfr (FST(SND(SND res))) s') /\
         (FST res = word 0 <=>
          ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTrans h1 h2) /\
            ?ty1 ty2 l mid r.
              fddb nms tys dbs (SND(EL h1 ths)) (hdbComb (hdbComb (hdbConst "=" ty1) l) mid) /\
              fddb nms tys dbs (SND(EL h2 ths)) (hdbComb (hdbComb (hdbConst "=" ty2) mid) r)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`plan_rel bw ctl nctl cfr`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
                `budget:int64`; `cfr:int64`; `m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`; `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `h1:num`; `h2:num`] PL_TRANS_DRV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN FIRST(map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC)
    [PL_LEAF_TRANS_INTERN16; PL_LEAF_TRANS_PACK; PL_LEAF_TRANS_UNPACK; PL_LEAF_TRANS_EQW; PL_LEAF_TRANS_ROW_WORD; PL_LEAF_TRANS_LIVE; PL_LEAF_TRANS_APPEND_ROW]));;

let PL_MKCOMB_REL = prove
 (`!progs bw ctl nctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2.
     pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_mkcomb 7 /\
     pl_progs_ok progs /\ pl_cw_range nctl pl_plan_mkcomb /\
     drv_sem progs bw ctl budget cfr pl_plan_mkcomb 0 m used res /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = h1 /\ cw 9 = h2
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RMkComb h1 h2) (FST(SND s')) /\
                    pl_inv s') /\ plan_rel bw ctl nctl cfr (FST(SND(SND res))) s') /\
         (FST res = word 0 <=>
          ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RMkComb h1 h2) /\
            ?f g a b tx ty.
              fddb nms tys dbs (SND(EL h1 ths))
                (hdbComb (hdbComb (hdbConst "=" (HFun (HFun tx ty) (HFun (HFun tx ty) HBool))) f) g) /\
              fddb nms tys dbs (SND(EL h2 ths))
                (hdbComb (hdbComb (hdbConst "=" (HFun tx (HFun tx HBool))) a) b)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`plan_rel bw ctl nctl cfr`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
                `budget:int64`; `cfr:int64`; `m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`; `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `h1:num`; `h2:num`] PL_MKCOMB_DRV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN FIRST(map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC)
    [PL_LEAF_MKCOMB_INTERN16; PL_LEAF_MKCOMB_PACK; PL_LEAF_MKCOMB_UNPACK; PL_LEAF_MKCOMB_EQW; PL_LEAF_MKCOMB_ROW_WORD; PL_LEAF_MKCOMB_LIVE; PL_LEAF_MKCOMB_APPEND_ROW]));;

let PL_EXPECT_ALPHA_REL = prove
 (`!progs bw ctl nctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h c hl.
     pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_expect_alpha 8 /\
     pl_progs_ok progs /\ pl_cw_range nctl pl_plan_expect_alpha /\
     drv_sem progs bw ctl budget cfr pl_plan_expect_alpha 0 m used res /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     cw 8 = h /\ cw 10 = c /\ cw 13 + cw 12 <= LENGTH stk /\
     list_of_seq (\j. EL (cw 13 + j) stk) (cw 12) = hl
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RExpectAlpha h hl c) (FST(SND s')) /\
                    pl_inv s') /\ plan_rel bw ctl nctl cfr (FST(SND(SND res))) s') /\
         (FST res = word 0 <=>
          ~(?hsd cn hyps. nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RExpectAlpha h hl c) /\
                          fddbs nms tys dbs (FST(EL h ths)) hsd /\
                          fdtm nms tys ntms c cn /\ fddb nms tys dbs (SND(EL h ths)) (hdb cn) /\
                          ALL2 (fdtm nms tys ntms) hl hyps /\ ALL (\p. htypeof p = HBool) hyps /\
                          (!x. MEM x hsd <=> MEM x (MAP hdb hyps))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`plan_rel bw ctl nctl cfr`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
                `budget:int64`; `cfr:int64`; `m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`; `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`; `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `h:num`; `c:num`; `hl:num list`] PL_EXPECT_ALPHA_DRV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN FIRST(map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC)
    [PL_LEAF_EXPECT_ALPHA_EQW; PL_LEAF_EXPECT_ALPHA_ROW_WORD; PL_LEAF_EXPECT_ALPHA_LIVE]));;

