(* Totality of represented mark writes follows from the interface law. *)
needs "native/hol/kernel_table_repr_load.ml";;

(* A mark write is enabled because the interface supplies its successor. *)
let TAB_EN_PUTW_MARK = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput inp st cw s stk.
     val(EL 0 st) = 9 /\ cw(val(EL 12 st)) = 1 /\ twd (val(EL 1 st)) = 1 /\
     cw(val(EL 13 st)) = 0 /\
     tab_put_mark_ok (trow,tn,twd,tdrop,tapp,tput) (val(EL 1 st)) (val(EL 2 st))
     ==> ?k pay s'. tab_leaf (trow,tn,twd,tdrop,tapp,tput) inp st (cw,s,stk) k pay s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `cw(val(EL 10 (st:int64 list))) < (tn:num->S->num)(val(EL 2 st)) s` THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[tab_put_mark_ok] o
      check (is_const_app "tab_put_mark_ok" o concl)) THEN
    DISCH_THEN(MP_TAC o SPECL [`s:S`;`cw(val(EL 10 (st:int64 list))):num`;
                              `cw(val(EL 11 (st:int64 list))):num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `s':S`) THEN
    MAP_EVERY EXISTS_TAC [`1`;`cw(val(EL 11 (st:int64 list))):num`;`s':S`];
    MAP_EVERY EXISTS_TAC [`2`;`0`;`s:S`]] THEN
  REWRITE_TAC[tab_leaf;tab_putw;LET_DEF;LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

