(* The counted reader implements the HOLR plan leaf contract. *)

needs "native/hol/kernel_source_load.ml";;
needs "native/leaves/ids_next/ids_next.ml";;


let IDS_LOADS_HOLR = prove
 (`!st xs rest.
     ids_loads st xs rest <=>
     ids_count_input st = APPEND (holr_ids xs) rest /\
     ALL (\x. x < 2 EXP 62) xs /\ LENGTH xs < 2 EXP 62`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ids_loads] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `tail:num list`
       (STRIP_ASSUME_TAC o REWRITE_RULE[ids_count_good; rd_id_payload]))) THEN
    REWRITE_TAC[holr_ids; holr_flat; GSYM APPEND_ASSOC] THEN ASM_MESON_TAC[];
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
      [`LENGTH(xs:num list)`; `APPEND (holr_flat(MAP leb_enc xs)) rest`] THEN
    SUBGOAL_THEN `rd_id_payload (LENGTH xs) (APPEND (holr_flat(MAP leb_enc xs)) rest) xs rest`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[rd_id_payload; holr_flat]; ALL_TAC] THEN
    ASM_REWRITE_TAC[ids_count_good; APPEND_ASSOC; GSYM holr_ids] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP RD_ID_PAYLOAD_LENGTH) THEN ARITH_TAC]);;

let PL_IDS_CURSOR = prove
 (`!t. pl_cursor t = val(ids_initial_cursor t)`,
  REWRITE_TAC[pl_cursor; pl_w; ids_initial_cursor; MULT_CLAUSES; WORD_ADD_0]);;

let PL_IDS_NEXT_SPEC = prove
 (`pl_ids_next_spec ids_next`,
  REWRITE_TAC[pl_ids_next_spec; pl_leaf_ok; IDS_NEXT_LEAF_WF; IDS_NEXT_DECLS] THEN CONJ_TAC THENL
   [MESON_TAC[TISA_RUN_STATUS; IDS_NEXT_RUN; ids_next_post];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`t:tisa_state`; `k:num`; `u:tisa_state`] IDS_NEXT_RUN) THEN
    ASM_REWRITE_TAC[ids_next_post] THEN
    DISCH_THEN(DISJ_CASES_TAC o CONJUNCT2) THENL
     [DISJ2_TAC THEN REWRITE_TAC[PL_IDS_CURSOR; GSYM ids_count_input] THEN
      ASM_MESON_TAC[IDS_LOADS_HOLR];
      FIRST_X_ASSUM(X_CHOOSE_THEN `xs:num list` (X_CHOOSE_THEN `rest:num list` STRIP_ASSUME_TAC)) THEN
      DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`xs:num list`; `rest:num list`] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IDS_LOADS_HOLR] o
        check (fun th -> concl th = `ids_loads t xs rest`)) THEN
      REWRITE_TAC[PL_IDS_CURSOR; GSYM ids_count_input; pl_w; GSYM ids_slot; GSYM IDS_CURSOR_SLOT] THEN
      ASM_CASES_TAC `8 * LENGTH(xs:num list) <= val(tisa_len t 2)` THEN
      FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
      ASM_REWRITE_TAC[GSYM NOT_LE] THEN
      REWRITE_TAC[holr_ids; LENGTH_APPEND; holr_flat; ADD_ASSOC] THEN
      SIMP_TAC[]]]);;
