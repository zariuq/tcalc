(* The native inline interner preserves semantic row validity. *)
needs "native/hol/bind_walk_hbind.ml";;
needs "native/hol/bind_walk_store.ml";;

let BW_AFTER_INTERN_ROWS = prove
 (`!s u. bw_after_intern s u
     ==> bw_rows u (val(bw_w u 0)) = bw_rows s (val(bw_w s 0)) \/
         bw_rows u (val(bw_w u 0)) = APPEND (bw_rows s (val(bw_w s 0)))
           [(val(tregs s 1) MOD 8,val(tregs s 1) DIV 8,val(tregs s 2))]`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o REWRITE_RULE[bw_after_intern]) THEN
  MATCH_MP_TAC BW_LIST_GROW_ONE THEN EXISTS_TAC `val(tregs u 5)` THEN
  REWRITE_TAC[LENGTH_BW_ROWS] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < val(bw_w u 0) /\ 2*i < 2*val(bw_w s 0) /\
                  2*i+1 < 2*val(bw_w s 0)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC[EL_BW_ROWS;bw_row];
    ASM_SIMP_TAC[EL_BW_ROWS;bw_row]]);;

let BW_AFTER_INTERN_ROWS_VALID = prove
 (`!nms tys s u.
     bw_after_intern s u /\ bw_rows_valid nms tys (bw_rows s (val(bw_w s 0))) /\
     bw_row_admissible nms tys (bw_rows s (val(bw_w s 0)))
       (val(tregs s 1) MOD 8,val(tregs s 1) DIV 8,val(tregs s 2))
     ==> bw_rows_valid nms tys (bw_rows u (val(bw_w u 0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BW_AFTER_INTERN_ROWS) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  ASM_SIMP_TAC[BW_ROWS_VALID_APPEND]);;

let bind_walk_intern_rows_theorems =
 ["BW_AFTER_INTERN_ROWS",BW_AFTER_INTERN_ROWS;
  "BW_AFTER_INTERN_ROWS_VALID",BW_AFTER_INTERN_ROWS_VALID];;
