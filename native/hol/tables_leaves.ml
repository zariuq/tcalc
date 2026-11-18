(* ========================================================================= *)
(* The leaves' bridges over the interface: each leaf implements its meaning *)
(* (tab_impl) under tab_rel at every step whose slots a description of the  *)
(* layout gives, for any interface (trow,tn,twd,tdrop,tapp,tput): pack, unpack   *)
(* and eqw at any step; row_word on a row table; live on the count of a row *)
(* table and its marks.                                                      *)
(*                                                                           *)
(* Loaded after tables_frame.ml.                                             *)
(* ========================================================================= *)

(* The slots a description of the layout names are described slots. *)
let TAB_DESC_SLOTS = prove
 (`!L d. MEM d L ==> ALL (\j. MEM j (tab_slots L)) (tab_dslots d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN BETA_TAC THEN ASM_MESON_TAC[TAB_SLOTS_DESC]);;

(* Whether a term mentions the constant called name. *)
let tab_has_const name tm = can (find_term (fun t -> is_const t && fst(dest_const t) = name)) tm;;

(* tab_leaf at a step whose leaf is a numeral. *)
let TAB_LEAF_AT_TAC =
  REWRITE_TAC[tab_leaf; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

(* The facts of description d of the layout, as assumptions: its slots are  *)
(* described, and its memory relation, unfolded.                             *)
let TAB_DESC_TAC d =
  FIRST_ASSUM(fun th -> if is_const_app "MEM" (concl th) && rand(rator(concl th)) = d
    then ASSUME_TAC(CONV_RULE(DEPTH_CONV BETA_CONV) (REWRITE_RULE[tab_dslots; ALL] (MATCH_MP TAB_DESC_SLOTS th)))
    else failwith "TAB_DESC_TAC: MEM") THEN
  FIRST_ASSUM(fun th -> if is_const_app "ALL" (concl th) && tab_has_const "tab_mem" (concl th)
    then MP_TAC(SPEC d (REWRITE_RULE[GSYM ALL_MEM] th)) else failwith "TAB_DESC_TAC: ALL") THEN
  ASM_REWRITE_TAC[tab_mem] THEN STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th) && tab_has_const "tab_slots" (concl th))));;

(* ------------------------------------------------------------------------- *)
(* pack, unpack, eqw: no regions.                                            *)
(* ------------------------------------------------------------------------- *)

let TAB_PURE_BRIDGE_TAC prog_tm wf decls status spec spec_def =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TAB_IMPL_RO THEN EXISTS_TAC prog_tm THEN
  ASM_REWRITE_TAC[wf; status] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[decls; tisa_rw; LENGTH] THEN ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN TAB_LEAF_AT_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_rel]) THEN
    W(fun (asl,_) ->
      let dc = find (fun th -> is_const_app "drv_child" (concl th)) (map snd asl) in
      let cws = find (fun th -> is_const_app "pl_cwords" (concl th)) (map snd asl) in
      let rng = find (fun th -> is_forall(concl th) && can (find_term ((=) `nctl:num`)) (concl th) &&
                                not(is_const_app "tab_rel" (concl th))) (map snd asl) in
      MP_TAC(MATCH_MP PL_CHILD_ARGS (CONJ dc (CONJ cws rng)))) THEN
    STRIP_TAC THEN
    MP_TAC spec THEN REWRITE_TAC[spec_def] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[pl_pack; pl_unpack; pl_eqw; tab_polmax; GSYM VAL_EQ] THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(MATCH_MP_TAC PL_VAL_WORD_LT THEN ASM_ARITH_TAC) THEN
    TRY(MATCH_MP_TAC PL_VAL_WORD_LT THEN
        MP_TAC(SPEC `tisa_fword t 22` VAL_BOUND_64) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)];;

let TAB_IMPL_PACK = prove
 (`!(trow:num->S->num->num list) (tn:num->S->num) (twd:num->num) (tdrop:num->S->num->bool)
    (tapp:num->num->S->num list->S->bool) (tput:num->num->S->num->num->num->S->bool) L inp progs bw ctl nctl budget cfr st.
     progs 1 = pack /\ val(EL 0 st) = 1 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tab_impl (tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr) (trow,tn,twd,tdrop,tapp,tput) inp
                  progs bw ctl budget cfr st`,
  TAB_PURE_BRIDGE_TAC `pack` PACK_LEAF_WF PACK_DECLS PL_PACK_STATUS PL_PACK_SPEC pl_pack_spec);;

let TAB_IMPL_UNPACK = prove
 (`!(trow:num->S->num->num list) (tn:num->S->num) (twd:num->num) (tdrop:num->S->num->bool)
    (tapp:num->num->S->num list->S->bool) (tput:num->num->S->num->num->num->S->bool) L inp progs bw ctl nctl budget cfr st.
     progs 2 = unpack /\ val(EL 0 st) = 2 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tab_impl (tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr) (trow,tn,twd,tdrop,tapp,tput) inp
                  progs bw ctl budget cfr st`,
  TAB_PURE_BRIDGE_TAC `unpack` UNPACK_LEAF_WF UNPACK_DECLS PL_UNPACK_STATUS PL_UNPACK_SPEC pl_unpack_spec);;

let TAB_IMPL_EQW = prove
 (`!(trow:num->S->num->num list) (tn:num->S->num) (twd:num->num) (tdrop:num->S->num->bool)
    (tapp:num->num->S->num list->S->bool) (tput:num->num->S->num->num->num->S->bool) L inp progs bw ctl nctl budget cfr st.
     progs 3 = eqw /\ val(EL 0 st) = 3 /\ (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tab_impl (tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr) (trow,tn,twd,tdrop,tapp,tput) inp
                  progs bw ctl budget cfr st`,
  TAB_PURE_BRIDGE_TAC `eqw` EQW_LEAF_WF EQW_DECLS PL_EQW_STATUS PL_EQW_SPEC pl_eqw_spec);;

(* ------------------------------------------------------------------------- *)
(* row_word on a row table.                                                  *)
(* ------------------------------------------------------------------------- *)

let TAB_SEM_ROWW = prove
 (`!L bw ctl nctl budget cfr st m used t k u cw jr jc wd fw n.
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\
     val(EL 1 st) = jr /\ val(EL 2 st) = jc /\ MEM jr (tab_slots L) /\ MEM jc (tab_slots L) /\
     tab_layout L bw ctl nctl cfr /\ pl_cwords ctl nctl m cw /\ pl_rtab bw jr jc wd m fw n /\
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
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `jc:num`; `0`] TAB_CHILD_W) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC PL_ROW_WORD_SPEC THEN REWRITE_TAC[pl_row_word_spec] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[pl_roww] THEN
  DISCH_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `0`; `jr:num`;
                `wd * cw(val(EL 10 (st:int64 list))) + cw(val(EL 11 st))`] TAB_CHILD_W) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`wd:num`; `cw(val(EL 10 (st:int64 list))):num`; `cw(val(EL 11 (st:int64 list))):num`;
                  `n:num`] PL_ROW_WORD_BOUND) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`cw(val(EL 10 (st:int64 list))):num`; `cw(val(EL 11 (st:int64 list))):num`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `fw:num->num->num`)) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

let TAB_IMPL_ROWW = prove
 (`!(trow:num->S->num->num list) (tn:num->S->num) (twd:num->num) (tdrop:num->S->num->bool)
    (tapp:num->num->S->num list->S->bool) (tput:num->num->S->num->num->num->S->bool) L inp progs bw ctl nctl budget cfr st j c wd.
     progs 4 = row_word /\ val(EL 0 st) = 4 /\ val(EL 1 st) = j /\ val(EL 2 st) = c /\
     MEM (RowTab j c wd) L /\ twd j = wd /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tab_impl (tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr) (trow,tn,twd,tdrop,tapp,tput) inp
                  progs bw ctl budget cfr st`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TAB_IMPL_RO THEN EXISTS_TAC `row_word` THEN
  ASM_REWRITE_TAC[ROW_WORD_LEAF_WF; PL_ROW_WORD_STATUS] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_DECLS_RO THEN REWRITE_TAC[ROW_WORD_DECLS; ALL] THEN CONV_TAC NUM_REDUCE_CONV;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN TAB_LEAF_AT_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_rel]) THEN
    TAB_DESC_TAC `RowTab j c wd` THEN
    MATCH_MP_TAC TAB_SEM_ROWW THEN
    W(fun (asl,_) ->
      let dc = concl(find (fun th -> is_const_app "drv_child" (concl th)) (map snd asl)) in
      let args = snd(strip_comb dc) in
      MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                            `cfr:int64`; el 5 args; el 6 args; el 7 args; `j:num`; `c:num`]) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* live on the count of a row table and its marks.                           *)
(* ------------------------------------------------------------------------- *)

let TAB_SEM_LIVE = prove
 (`!L bw ctl nctl budget cfr st m used t k u cw jc jm n (dr:num->bool).
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\
     val(EL 1 st) = jc /\ val(EL 2 st) = jm /\ MEM jc (tab_slots L) /\ MEM jm (tab_slots L) /\
     tab_layout L bw ctl nctl cfr /\ pl_cwords ctl nctl m cw /\ pl_mw m (bw jc) 0 = n /\
     8 <= val(bw(jc + 1)) /\ 8 * n <= val(bw(jm + 1)) /\
     (!i. i < n ==> (pl_mw m (bw jm) i = 0 <=> ~dr i)) /\
     drv_child bw ctl budget cfr st m used t /\ tisa_entry_ok live t /\ tisa_run live t = TStop k u
     ==> (if cw(val(EL 10 st)) < n /\ ~dr(cw(val(EL 10 st)))
          then k = 1 /\ val(tisa_fword u 19) = cw(val(EL 10 st)) else k = 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `cw:num->num`] PL_CHILD_ARGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`; `st:int64 list`;
                `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `jm:num`] PL_CHILD_REGION) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `0`; `jc:num`; `0`] TAB_CHILD_W) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC PL_LIVE_SPEC THEN REWRITE_TAC[pl_live_spec] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(cw:num->num)(val(EL 10 (st:int64 list))) < n` THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                  `st:int64 list`; `m:int64->byte`; `used:int64`; `t:tisa_state`; `1`; `jm:num`;
                  `(cw:num->num)(val(EL 10 (st:int64 list)))`] TAB_CHILD_W) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
                               is_iff(rand(snd(dest_forall(concl th))))
       then REWRITE_TAC[MATCH_MP th (ASSUME `(cw:num->num)(val(EL 10 (st:int64 list))) < n`)] else failwith "") THEN
    COND_CASES_TAC THEN SIMP_TAC[] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN TRY(COND_CASES_TAC THEN SIMP_TAC[])]);;

let TAB_IMPL_LIVE = prove
 (`!(trow:num->S->num->num list) (tn:num->S->num) (twd:num->num) (tdrop:num->S->num->bool)
    (tapp:num->num->S->num list->S->bool) (tput:num->num->S->num->num->num->S->bool) L inp progs bw ctl nctl budget cfr st jm j c wd.
     progs 5 = live /\ val(EL 0 st) = 5 /\ val(EL 1 st) = c /\ val(EL 2 st) = jm /\
     MEM (RowTab j c wd) L /\ MEM (MarkTab jm j c wd) L /\
     (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\ 6 < val(EL 17 st)
     ==> tab_impl (tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr) (trow,tn,twd,tdrop,tapp,tput) inp
                  progs bw ctl budget cfr st`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TAB_IMPL_RO THEN EXISTS_TAC `live` THEN
  ASM_REWRITE_TAC[LIVE_LEAF_WF; PL_LIVE_STATUS] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_DECLS_RO THEN REWRITE_TAC[LIVE_DECLS; ALL] THEN CONV_TAC NUM_REDUCE_CONV;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN TAB_LEAF_AT_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_rel]) THEN
    TAB_DESC_TAC `RowTab j c wd` THEN TAB_DESC_TAC `MarkTab jm j c wd` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pl_rtab]) THEN
    REWRITE_TAC[tab_live] THEN
    MATCH_MP_TAC TAB_SEM_LIVE THEN
    W(fun (asl,_) ->
      let dc = concl(find (fun th -> is_const_app "drv_child" (concl th)) (map snd asl)) in
      let args = snd(strip_comb dc) in
      MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                            `cfr:int64`; el 5 args; el 6 args; el 7 args; `c:num`; `jm:num`]) THEN
    ASM_REWRITE_TAC[]]);;

(* Every theorem this file states, for the audits. *)
let tables_leaves_theorems =
 ["TAB_DESC_SLOTS", TAB_DESC_SLOTS; "TAB_IMPL_PACK", TAB_IMPL_PACK; "TAB_IMPL_UNPACK", TAB_IMPL_UNPACK;
  "TAB_IMPL_EQW", TAB_IMPL_EQW; "TAB_SEM_ROWW", TAB_SEM_ROWW; "TAB_IMPL_ROWW", TAB_IMPL_ROWW;
  "TAB_SEM_LIVE", TAB_SEM_LIVE; "TAB_IMPL_LIVE", TAB_IMPL_LIVE];;
