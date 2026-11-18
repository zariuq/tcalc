(* ========================================================================= *)
(* The memory relation over tables given by the interface: a layout is a    *)
(* list of table descriptions,                                               *)
(*   RowTab j c wd     rows of wd words at slot j (room for fewer than 2^60  *)
(*                     rows), their count at slot c;                         *)
(*   KeyTab j          an intern16 table: rows j, hash slots j+2, count j+4; *)
(*   MarkTab jm j c wd one mark word per id at slot jm, for the rows at j   *)
(*                     (width wd) counted at c;                              *)
(*   NameTab j         a names interner (intern_name's regions 1..4): rows  *)
(*                     j, arena j+2, hash slots j+4, header j+6 (its count); *)
(*   InTab j           the input, the bytes inp.                             *)
(* tab_rel holds when the control words, the stack and every described      *)
(* region hold the interface's view and the input, the described slots     *)
(* apart from one another, the control words and the driver's stack window. *)
(* HOL's tables the record plans already use form the layout               *)
(* hol_layout_old, under which tab_rel is plan_rel (PLAN_REL_TAB).          *)
(*                                                                           *)
(* Loaded after tables_hol.ml, plans_rel.ml and intern_name.ml.             *)
(* ========================================================================= *)

let tabdesc_INDUCT, tabdesc_RECURSION = define_type
 "tabdesc = RowTab num num num | KeyTab num | MarkTab num num num num | NameTab num | InTab num";;

let tab_dslots = define
 `(tab_dslots (RowTab j c wd) = [j; c]) /\
  (tab_dslots (KeyTab j) = [j; j + 2; j + 4]) /\
  (tab_dslots (MarkTab jm j c wd) = [jm]) /\
  (tab_dslots (NameTab j) = [j; j + 2; j + 4; j + 6]) /\
  (tab_dslots (InTab j) = [j])`;;

let tab_slots = new_definition
 `tab_slots L = ITLIST (\d l. APPEND (tab_dslots d) l) L [40; 42]`;;

let tab_layout = new_definition
 `tab_layout L (bw:num->int64) (ctl:int64) nctl (cfr:int64) <=>
    48 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\ val ctl + 8 * nctl <= 2 EXP 64 /\
    drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl) /\
    (!j. MEM j (tab_slots L)
         ==> val(bw j) + val(bw(j + 1)) < 2 EXP 64 /\
             drv_apart (bw j) (val(bw(j + 1))) ctl (8 * nctl) /\
             drv_apart (word_sub cfr (word 48)) 304 (bw j) (val(bw(j + 1)))) /\
    (!j j'. MEM j (tab_slots L) /\ MEM j' (tab_slots L) /\ ~(j = j')
            ==> drv_apart (bw j) (val(bw(j + 1))) (bw j') (val(bw(j' + 1))))`;;

let tab_mem = define
 `(tab_mem ((trow,tn,twd,tdrop,tapp,tput):(num->S->num->num list)#(num->S->num)#(num->num)#
                                      (num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool))
           (inp:num list) (bw:num->int64) (m:int64->byte) (s:S) (RowTab j c wd) <=>
     val(bw(j + 1)) < 8 * wd * 2 EXP 60 /\ 8 <= val(bw(c + 1)) /\
     pl_rtab bw j c wd m (\i w. EL w (trow j s i)) (tn c s) /\
     !i. i < tn c s ==> LENGTH (trow j s i) = wd) /\
  (tab_mem (trow,tn,twd,tdrop,tapp,tput) inp bw m s (KeyTab j) <=>
     16 <= val(bw(j + 1)) /\ 8 <= val(bw(j + 3)) /\ 8 <= val(bw(j + 5)) /\
     ?t. (!r. r < 3 ==> tisa_base t r = bw(j + 2 * r) /\ tisa_len t r = bw(j + 2 * r + 1)) /\
         (!r a. r < 3 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1))) ==> tmem t a = m a) /\
         intern_ok t /\ val(intern_count t) = tn (j + 4) s /\
         !i. i < tn (j + 4) s
             ==> trow j s i = [val(intern_word t (2 * i)); val(intern_word t (2 * i + 1))]) /\
  (tab_mem (trow,tn,twd,tdrop,tapp,tput) inp bw m s (MarkTab jm j c wd) <=>
     val(bw(j + 1)) <= wd * val(bw(jm + 1)) /\ 8 * tn c s <= val(bw(jm + 1)) /\
     (!i. i < tn c s ==> (pl_mw m (bw jm) i = 0 <=> ~tdrop jm s i)) /\
     (!i. tn c s <= i /\ 8 * i + 8 <= val(bw(jm + 1)) ==> pl_mw m (bw jm) i = 0) /\
     (!i. tn c s <= i ==> ~tdrop jm s i)) /\
  (tab_mem (trow,tn,twd,tdrop,tapp,tput) inp bw m s (NameTab j) <=>
     16 <= val(bw(j + 7)) /\
     ?t. (!r. r < 4 ==> tisa_base t (r + 1) = bw(j + 2 * r) /\ tisa_len t (r + 1) = bw(j + 2 * r + 1)) /\
         (!r a. r < 4 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1))) ==> tmem t a = m a) /\
         name_ok t /\ val(name_count t) = tn (j + 6) s /\
         !i. i < tn (j + 6) s ==> trow j s i = name_row_bytes t i) /\
  (tab_mem (trow,tn,twd,tdrop,tapp,tput) inp bw m s (InTab j) <=>
     LENGTH inp = val(bw(j + 1)) /\ !i. i < LENGTH inp ==> val(m(word_add (bw j) (word i))) = EL i inp)`;;

let tab_rel = new_definition
 `tab_rel (tb:(num->S->num->num list)#(num->S->num)#(num->num)#
              (num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool))
          L (inp:num list) (bw:num->int64) (ctl:int64) nctl (cfr:int64) (m:int64->byte)
          ((cw,s,stk):(num->num)#S#num list) <=>
    tab_layout L bw ctl nctl cfr /\ 7 <= nctl /\ (!k. k <= 6 ==> cw k = k) /\ pl_cwords ctl nctl m cw /\
    ALL (tab_mem tb inp bw m s) L /\ pl_stk bw m stk`;;

(* HOL's tables the record plans of plans_abs.ml use. *)
let hol_layout_old = new_definition
 `hol_layout_old = [KeyTab 0; KeyTab 6; RowTab 12 14 5; MarkTab 16 12 14 5; RowTab 18 20 2; MarkTab 22 18 20 2]`;;

let TAB_SLOTS_OLD = prove
 (`tab_slots hol_layout_old = pl_slots`,
  REWRITE_TAC[tab_slots; hol_layout_old; pl_slots; ITLIST; tab_dslots; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* A row table whose rows are lists of words holds their words. *)
let TAB_RTAB_SEQ = prove
 (`!bw jr jc wd m (f:num->num->num) n.
     pl_rtab bw jr jc wd m (\i w. EL w (list_of_seq (f i) wd)) n <=> pl_rtab bw jr jc wd m (\i w. f i w) n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_rtab] THEN
  SUBGOAL_THEN `!i w. w < wd ==> EL w (list_of_seq ((f:num->num->num) i) wd) = f i w` ASSUME_TAC THENL
   [SIMP_TAC[EL_LIST_OF_SEQ]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* An intern16 table holds canonical rows exactly when it holds their two  *)
(* words.                                                                    *)
let ITAB_KEY_HOL = prove
 (`!bw j m rows.
     (!i. i < LENGTH rows ==> FST(EL i rows) < 8)
     ==> (pl_itab bw j m rows <=>
          ?t. (!r. r < 3 ==> tisa_base t r = bw(j + 2 * r) /\ tisa_len t r = bw(j + 2 * r + 1)) /\
              (!r a. r < 3 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1))) ==> tmem t a = m a) /\
              intern_ok t /\ val(intern_count t) = LENGTH rows /\
              !i. i < LENGTH rows
                  ==> pl_f3 (EL i rows) 0 = val(intern_word t (2 * i)) /\
                      pl_f3 (EL i rows) 1 = val(intern_word t (2 * i + 1)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_itab] THEN
  SUBGOAL_THEN `!i a b. i < LENGTH (rows:(num#num#num)list)
                        ==> (EL i rows = (a MOD 8,a DIV 8,b) <=> a = pl_f3 (EL i rows) 0 /\ b = pl_f3 (EL i rows) 1)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`EL i (rows:(num#num#num)list)`; `a:num`; `b:num`] PL_F3_KEY) THEN
    ASM_SIMP_TAC[pl_key] THEN MESON_TAC[];
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `t:tisa_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:tisa_state` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_MESON_TAC[]);;

(* On HOL's tables the record plans already use, tab_rel is plan_rel. *)
let PLAN_REL_TAB = prove
 (`!inp bw ctl nctl cfr m cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     tab_canon (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
     ==> (plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) <=>
          tab_rel hol_tables hol_layout_old inp bw ctl nctl cfr m
            (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_canon] THEN STRIP_TAC THEN
  REWRITE_TAC[plan_rel; tab_rel; pl_layout; tab_layout; TAB_SLOTS_OLD; hol_layout_old; ALL; hol_tables;
              tab_mem; pl_marks] THEN
  ASM_SIMP_TAC[ITAB_KEY_HOL] THEN
  REWRITE_TAC[hol_trow; hol_twd] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[TAB_RTAB_SEQ; LENGTH_LIST_OF_SEQ] THEN CONV_TAC(DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[CONS_11; hol_tw; hol_tn; hol_tdrop] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  (* rows regions of widths 5 and 2 always have room for fewer than 2^60 rows *)
  SIMP_TAC[CONV_RULE NUM_REDUCE_CONV VAL_BOUND_64;
           ARITH_RULE `a < 18446744073709551616 ==> a < 46116860184273879040`] THEN
  W(fun (asl,w) -> ACCEPT_TAC(CONJ_ACI_RULE w)));;

(* Every theorem this file states, for the audits. *)
let tables_rel_theorems =
 ["TAB_SLOTS_OLD", TAB_SLOTS_OLD; "TAB_RTAB_SEQ", TAB_RTAB_SEQ; "ITAB_KEY_HOL", ITAB_KEY_HOL;
  "PLAN_REL_TAB", PLAN_REL_TAB];;
