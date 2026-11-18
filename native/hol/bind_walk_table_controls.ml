(* The returned-value claim alone does not constrain unused appended rows. *)
needs "native/hol/bind_walk_hbind.ml";;
needs "native/hol/bind_walk_store.ml";;

let BW_RETURNED_VALUE_WITH_INVALID_EXTRA_ROW = prove
 (`bw_final [(0,0,0)] [(0,0,0);(1,0,0);(4,0,1);(3,3,3)] 0 0 0 2 /\
   bw_ctx ["x"] [(0,0,0)] 0 0 (TyVar "x") /\
   fddb ["x"] [(0,0,0)] [(0,0,0)] 0 (hdbVar "x" (TyVar "x")) /\
   ~bw_rows_valid ["x"] [(0,0,0)] [(0,0,0);(1,0,0);(4,0,1);(3,3,3)]`,
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BW_FINAL_ABS THEN EXISTS_TAC `1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC BW_CLAIM_BOUND THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[LENGTH;EL;HD;TL;ARITH];
      REWRITE_TAC[LENGTH;EL;HD;TL;ARITH]];
    REWRITE_TAC[bw_ctx;LENGTH;EL;HD;ARITH] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`0`;`0`;`0`] (CONJUNCT1(ISPECL
        [`["x"]:string list`;`[(0,0,0)]:(num#num#num)list`] fdty_RULES))) THEN
      REWRITE_TAC[LENGTH;EL;HD;ARITH];
      ARITH_TAC;
      GEN_TAC THEN ONCE_REWRITE_TAC[fdty_CASES] THEN
      REWRITE_TAC[LENGTH;ARITH_RULE `b < SUC 0 <=> b = 0`] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]];
    MP_TAC(SPECL [`0`;`0`;`0`;`TyVar "x"`] (el 0 (CONJUNCTS(ISPECL
      [`["x"]:string list`;`[(0,0,0)]:(num#num#num)list`;
       `[(0,0,0)]:(num#num#num)list`] fddb_RULES)))) THEN
    REWRITE_TAC[LENGTH;EL;HD;ARITH] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(SPECL [`0`;`0`;`0`] (CONJUNCT1(ISPECL
      [`["x"]:string list`;`[(0,0,0)]:(num#num#num)list`] fdty_RULES))) THEN
    REWRITE_TAC[LENGTH;EL;HD;ARITH];
    REWRITE_TAC[bw_rows_valid] THEN DISCH_THEN(MP_TAC o SPEC `3` o CONJUNCT1) THEN
    REWRITE_TAC[LENGTH;EL;HD;TL;bw_key_ok;ARITH]] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[bw_key_ok] THEN CONV_TAC NUM_REDUCE_CONV);;

let bind_walk_table_control_theorems =
 ["BW_RETURNED_VALUE_WITH_INVALID_EXTRA_ROW",BW_RETURNED_VALUE_WITH_INVALID_EXTRA_ROW];;
