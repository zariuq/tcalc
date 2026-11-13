(* ========================================================================= *)
(* The binding walk's hbind row: the row bind_walk returns is dbAbs(ty, rb), *)
(* and its second word rb is the row of hbind (x, TY) 0 T itself (from the  *)
(* decoding's inversion on the dbAbs row and the uniqueness of ty for TY).  *)
(* ========================================================================= *)

needs "native/hol/bind_walk.ml";;

let BIND_WALK_HBIND = prove
 (`!st st'.
     tisa_entry_ok bind_walk st /\ tisa_run bind_walk st = TStop 1 st'
     ==> !nms tys TY X.
           val(tisa_fword st 22) < LENGTH nms /\
           fdty nms tys (val(tisa_fword st 23)) TY /\
           (!a. a < LENGTH nms /\ EL a nms = EL (val(tisa_fword st 22)) nms
                ==> a = val(tisa_fword st 22)) /\
           (!b. fdty nms tys b TY ==> b = val(tisa_fword st 23)) /\
           fddb nms tys (bw_rows st (val(intern_count st))) (val(tregs st 1)) X
           ==> val(intern_word st' (2 * val(tisa_fword st' 19))) =
               4 + 8 * val(tisa_fword st 23) /\
               fddb nms tys (bw_rows st' (val(intern_count st')))
                    (val(intern_word st' (2 * val(tisa_fword st' 19) + 1)))
                    (hbind (EL (val(tisa_fword st 22)) nms,TY) 0 X)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BIND_WALK_SOUND) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`nms:string list`; `tys:(num#num#num)list`;
                                `TY:holtype`; `X:hdbterm`] o
                check (fun th -> is_forall(concl th) && can (find_term ((=) `fddb`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [fddb_CASES]) THEN
  REWRITE_TAC[hdbterm_DISTINCT; hdbterm_INJ] THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
                check (fun th -> is_eq(concl th) && lhand(concl th) = `TY:holtype`)) THEN
  SUBGOAL_THEN `EL (val(tisa_fword st' 19)) (bw_rows st' (val(intern_count st'))) =
                bw_row st' (val(tisa_fword st' 19))` MP_TAC THENL
   [MATCH_MP_TAC EL_BW_ROWS THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[bw_row; PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (ASSUME_TAC o SYM)) THEN
  SUBGOAL_THEN `a = val(tisa_fword st 23)` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                    can (find_term ((=) `fdty`)) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`val(intern_word st' (2 * val(tisa_fword st' 19)))`; `8`] DIVISION) THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

List.iter (fun (n,th) -> Printf.printf "AUDIT %s: %d hyps\n%!" n (length(hyp th)))
  ["BIND_WALK_HBIND", BIND_WALK_HBIND];;
print_endline ("THEOREM BIND_WALK_HBIND: " ^ string_of_thm BIND_WALK_HBIND);;
let ax = axioms() in Printf.printf "AXIOMS %d\n%!" (length ax);
  List.iter (fun th -> Printf.printf "  %s\n%!" (string_of_term (concl th))) ax;;
