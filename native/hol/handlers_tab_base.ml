(* ========================================================================= *)
(* Handlers by composition over the general table layer: the handlers.ml   *)
(* construction with plan_rel replaced by tab_rel tb L inp and pl_inv by an *)
(* invariant parameter Inv. A plan lifted over the tables (tab_lifts: from  *)
(* memory related to a state satisfying Inv, it does Q when it FIRES and is *)
(* REFUSED exactly when G, Q and G reading the input) keeps the reader's   *)
(* relation and the control words below 24 inside a handler                *)
(* (TAB_PLAN_IN_HANDLER); an operand prefix (tab_prefix_rd) composes        *)
(* with any lifted plan and the count's increment (TAB_HANDLER_GEN), given *)
(* that Inv survives the prefix's writes and the count's.                   *)
(*                                                                           *)
(* Loaded after reader_tab.ml.                                               *)
(* ========================================================================= *)

let TAB_PLAN_CW_KEPT = prove
 (`!L progs bw ctl nctl budget cfr P i m used res j.
     drv_sem progs bw ctl budget cfr P i m used res /\ tab_layout L bw ctl nctl cfr /\ j < nctl /\
     tab_rd_plan_ok L progs nctl P /\ (!st. MEM st P ==> ~(val(EL 17 st) = j))
     ==> pl_mw (FST(SND(SND res))) ctl j = pl_mw m ctl j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_rd_plan_ok] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
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
   [MATCH_MP_TAC TAB_CTL_ADDR THEN
    MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`] THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[drv_base; drv_len] THEN
    SUBGOAL_THEN `MEM (val(EL (1 + r) (st:int64 list))) (tab_slots L)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `val(EL (1 + r) (st:int64 list))`]
                 TAB_LAYOUT_SLOT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC DRV_APART_IN THEN MAP_EVERY EXISTS_TAC [`ctl:int64`; `8 * nctl`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(EL 17 (st:int64 list)) < nctl /\ ~(val(EL 17 st) = j)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`ctl:int64`; `8 * val(EL 17 (st:int64 list))`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ASM_REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC]);;

let TAB_REL_LAYOUT = prove
 (`!tb L inp bw ctl nctl cfr m (s:(num->num)#S#num list).
     tab_rel tb L inp bw ctl nctl cfr m s
     ==> tab_layout L bw ctl nctl cfr /\ 48 <= val cfr /\ val ctl + 8 * nctl <= 2 EXP 64 /\ 7 <= nctl`,
  REWRITE_TAC[FORALL_PAIR_THM; tab_rel; tab_layout] THEN SIMP_TAC[]);;

let TAB_REL_CW = prove
 (`!tb L inp bw ctl nctl cfr m (s:(num->num)#S#num list) j.
     tab_rel tb L inp bw ctl nctl cfr m s /\ j < nctl ==> pl_mw m ctl j = FST s j`,
  REWRITE_TAC[FORALL_PAIR_THM; tab_rel; pl_cwords; FST] THEN MESON_TAC[]);;

(* A plan lifted over the tables: run by the driver from memory related to a *)
(* state satisfying I, it does Q when it FIRES (I and the relation kept) and *)
(* is REFUSED exactly when G; PK admits the leaf table.                      *)
let tab_lifts = new_definition
 `tab_lifts (tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) L (PK:(num->tisa_prog)->bool) P
            (Q:num list->(num->num)#S#num list->S->bool) (G:num list->(num->num)#S#num list->bool)
            (Inv:(num->num)#S#num list->bool) <=>
    !inp progs bw ctl nctl budget cfr m used res s.
      PK progs /\ pl_cw_range nctl P /\
      drv_sem progs bw ctl budget cfr P 0 m used res /\
      tab_rel tb L inp bw ctl nctl cfr m s /\ ~(val budget < val used) /\ Inv s
      ==> (FST res = word 1
           ==> ?s'. (Q inp s (FST(SND s')) /\ Inv s') /\ tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND res))) s') /\
          (FST res = word 0 <=> G inp s)`;;

let TAB_PLAN_IN_HANDLER = prove
 (`!(tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) L PK P Q G Inv inp progs bw ctl nctl budget cfr i m used r
    (s:(num->num)#S#num list) c.
     tab_lifts tb L PK P Q G Inv /\ tab_rd_plan_ok L progs nctl P /\ rd_tab_apart L bw /\
     (!st. MEM st P ==> ~(17 <= val(EL 17 st) /\ val(EL 17 st) < 24)) /\
     PK progs /\ pl_cw_range nctl P /\ 24 < nctl /\
     drv_sem progs bw ctl budget cfr P i m used r /\
     tab_rel tb L inp bw ctl nctl cfr m s /\ Inv s /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp c /\
         (FST r = word 1
          ==> ?s'. Q inp s (FST(SND s')) /\ Inv s' /\ tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r))) s' /\
                   (!j. 17 <= j /\ j < 24 ==> FST s' j = FST s j)) /\
         (FST r = word 0 <=> G inp s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_LAYOUT o
    check (fun th -> is_const_app "tab_rel" (concl th))) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TAB_PLAN_KEEPS_RD THEN
    MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `progs:num->tisa_prog`; `budget:int64`; `P:(int64 list)list`; `i:num`;
                          `m:int64->byte`; `used:int64`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `r0:int64#num#(int64->byte)#int64` STRIP_ASSUME_TAC o MATCH_MP DRV_SEM_AT0 o
    check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`inp:num list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                             `budget:int64`; `cfr:int64`; `m:int64->byte`; `used:int64`;
                             `r0:int64#num#(int64->byte)#int64`; `s:(num->num)#S#num list`] o
    REWRITE_RULE[tab_lifts] o check (fun th -> is_const_app "tab_lifts" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FST(SND(SND(r0:int64#num#(int64->byte)#int64))) = FST(SND(SND(r:int64#num#(int64->byte)#int64)))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_eq(lhand(concl th)))) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':(num->num)#S#num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s':(num->num)#S#num list` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`;
                `FST(SND(SND(r:int64#num#(int64->byte)#int64)))`; `s':(num->num)#S#num list`; `j:num`] TAB_REL_CW) THEN
  MP_TAC(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`;
                `m:int64->byte`; `s:(num->num)#S#num list`; `j:num`] TAB_REL_CW) THEN
  MP_TAC(SPECL [`L:tabdesc list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `P:(int64 list)list`; `i:num`; `m:int64->byte`; `used:int64`;
                `r:int64#num#(int64->byte)#int64`; `j:num`] TAB_PLAN_CW_KEPT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `j < nctl` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `!x j. 17 <= j /\ j < 24 /\ ~(17 <= x /\ x < 24) ==> ~(x = j)`) THEN
    ASM_SIMP_TAC[];
    MESON_TAC[]]);;

(* A prefix's reading: run from cursor c over the tables and the reader, it *)
(* FIREs exactly when the header is seen and D decodes some v from the bytes *)
(* at c, and then it has written W cw c v and moved the cursor by Ln v. R is *)
(* what it needs of the leaf table beyond eqw and the reader's cur, leb_next *)
(* and inc.                                                                   *)
let tab_prefix_rd = new_definition
 `tab_prefix_rd (tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) L (R:(num->tisa_prog)->bool) pfx (D:num list->A->bool)
                   (W:(num->num)->num->A->num->num) (Ln:A->num) <=>
    !inp progs bw ctl nctl budget cfr i m used r cw (s:S) stk c.
      progs 3 = eqw /\ rd_progs_ok progs /\ R progs /\ 24 < nctl /\ rd_tab_apart L bw /\
      drv_sem progs bw ctl budget cfr pfx i m used r /\
      tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
      ==> SND(SND(SND r)) = used /\
          (FST r = word 1 <=> cw 20 = 1 /\ ?v. D (rd_from inp c) v) /\
          (FST r = word 0 <=> ~(cw 20 = 1 /\ ?v. D (rd_from inp c) v)) /\
          (FST r = word 1
           ==> ?v. D (rd_from inp c) v /\
                   tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND r))) (W cw c v,s,stk) /\
                   rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + Ln v))`;;

(* A prefix needing less of the leaf table reads the same under more. *)
let TAB_PREFIX_RD_MONO = prove
 (`!(tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) L R R' pfx (D:num list->A->bool) W Ln.
     tab_prefix_rd tb L R pfx D W Ln /\ (!progs. R' progs ==> R progs) ==> tab_prefix_rd tb L R' pfx D W Ln`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_prefix_rd] THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `drv_sem`)) (concl th))) THEN
  MAP_EVERY EXISTS_TAC [`progs:num->tisa_prog`; `budget:int64`; `i:num`; `m:int64->byte`] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Drop the invariant's preservation premises (Inv x ==> Inv (f x)), which   *)
(* send MESON round in circles; the outcome reasoning does not need them.   *)
let THIN_INV_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_var t) = "Inv" with Failure _ -> false)) (concl th))));;

