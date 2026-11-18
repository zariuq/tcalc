(* ========================================================================= *)
(* HOL's interface obeys the append laws (HOL_TAPP_OK); HOL's full layout   *)
(* (hol_layout: the record plans' tables, the Y and N maps with their      *)
(* marks, the names interner and the input) is well formed (HOL_LAYOUT_WF); *)
(* every table can append a row of its width and the names table any byte  *)
(* string (HOL_TAPP_EXISTS).                                                 *)
(*                                                                           *)
(* Loaded after tables_append.ml.                                            *)
(* ========================================================================= *)

let LIST_EL_SEQ = prove
 (`!l:A list. list_of_seq (\i. EL i l) (LENGTH l) = l`,
  GEN_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN SIMP_TAC[EL_LIST_OF_SEQ]);;

(* A list of known length as its elements. *)
let LIST_OF_LENGTH = prove
 (`!l:A list n. LENGTH l = n ==> l = list_of_seq (\i. EL i l) n`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[LIST_EL_SEQ]);;

(* The obligations of one append, by kind. *)
let HOL_COUNT_TAC = ARITH_TAC;;
let HOL_NEWROW_TAC =
  FIRST_ASSUM(fun th -> if is_eq(concl th) && is_const_app "LENGTH" (lhs(concl th)) then
     GEN_REWRITE_TAC RAND_CONV [MATCH_MP LIST_OF_LENGTH th] else failwith "") THEN
  REWRITE_TAC[NAME_LIST_OF_SEQ_EQ] THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[hol_tw] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SIMP_TAC[EL_APPEND; LT_REFL; SUB_REFL] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[PL_F3_WORDS; pl_f2; pl_f5; ntm_ty; ntm_db; FST; SND] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[];;
let HOL_NAMEROW_TAC =
  SIMP_TAC[EL_APPEND; LT_REFL; SUB_REFL] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN ASM_SIMP_TAC[HNAME_BYTES_NAME];;
let HOL_KEPT_TAC =
  REPEAT STRIP_TAC THEN TRY(AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; hol_tw] THEN GEN_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[EL_APPEND];;
let HOL_FRAME_TAC =
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; hol_tw] THEN ASM_REWRITE_TAC[];;

let HOL_TAPP_OK = prove
 (`tab_app_ok hol_tables`,
  REWRITE_TAC[hol_tables; tab_app_ok; tab_frame] THEN MAP_EVERY X_GEN_TAC [`j:num`; `c:num`] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC (pl_ns_vars @ [`r:num list`] @
                       map (fun v -> let n,ty = dest_var v in mk_var(n ^ "'", ty)) pl_ns_vars) THEN
  REWRITE_TAC[hol_tapp] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_var(lhs(concl th)) && not(lhs(concl th) = `r:num list`)
                                 then SUBST_ALL_TAC th else failwith "")) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_pair(lhs(concl th)))) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_var(lhs(concl th)) && not(lhs(concl th) = `r:num list`)
                                 then SUBST_ALL_TAC th else failwith "")) THEN
  REWRITE_TAC[hol_tn; hol_trow; hol_twd; hol_tdrop; FUN_EQ_THM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD1] THEN
  REPEAT CONJ_TAC THEN
  FIRST (map (fun t -> t THEN NO_TAC)
    [HOL_COUNT_TAC; HOL_NEWROW_TAC; HOL_NAMEROW_TAC; HOL_KEPT_TAC; HOL_FRAME_TAC]));;

(* A word written to the marks of the terms, theorems or Y ids drops the id *)
(* (or makes it live, for 0) and keeps every other view.                    *)
let HOL_TPUT_MARK_OK = prove
 (`tab_put_mark_ok hol_tables 16 14 /\ tab_put_mark_ok hol_tables 22 20 /\ tab_put_mark_ok hol_tables 28 26`,
  REPEAT CONJ_TAC THEN REWRITE_TAC[hol_tables; tab_put_mark_ok; FORALL_PAIR_THM] THEN
  (CONJ_TAC THENL
    [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_PAIR_THM; hol_tput] THEN MESON_TAC[];
     REPEAT GEN_TAC THEN REWRITE_TAC[hol_tput] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
     FIRST_X_ASSUM SUBST_ALL_TAC THEN
     REWRITE_TAC[hol_tdrop;hol_trow;hol_tn;hol_tw;hol_mspace;FUN_EQ_THM] THEN
     CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
     REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM;MEM_FILTER;PAIR_EQ]) THEN
     ASM_REWRITE_TAC[MEM;MEM_FILTER;PAIR_EQ] THEN
     CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
     TRY(AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM;hol_tw])]));;

(* HOL's full layout. *)
let hol_layout = new_definition
 `hol_layout = APPEND hol_layout_old
                 [RowTab 24 26 1; MarkTab 28 24 26 1; RowTab 30 32 1; MarkTab 34 30 32 1; NameTab 44; InTab 54]`;;

let HOL_LAYOUT_WF = prove
 (`tab_wf hol_layout`,
  REWRITE_TAC[tab_wf; hol_layout; hol_layout_old; APPEND] THEN CONJ_TAC THENL
   [REWRITE_TAC[tab_slots; ITLIST; tab_dslots; APPEND; PAIRWISE; ALL] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[MEM; injectivity "tabdesc"; distinctness "tabdesc"] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* Every table can append a row of its width; the names table any bytes. *)
let HOL_TAPP_EXISTS = prove
 (`(!s r. LENGTH r = 2 ==> ?s'. hol_tapp 0 4 s r s') /\
   (!s r. LENGTH r = 2 ==> ?s'. hol_tapp 6 10 s r s') /\
   (!s r. LENGTH r = 5 ==> ?s'. hol_tapp 12 14 s r s') /\
   (!s r. LENGTH r = 2 ==> ?s'. hol_tapp 18 20 s r s') /\
   (!s r. LENGTH r = 1 ==> ?s'. hol_tapp 24 26 s r s') /\
   (!s r. LENGTH r = 1 ==> ?s'. hol_tapp 30 32 s r s') /\
   (!s r. ALL (\b. b < 256) r ==> ?s'. hol_tapp 44 50 s r s')`,
  REWRITE_TAC[FORALL_PAIR_THM; hol_tapp] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* Every theorem this file states, for the audits. *)
let tables_hol_laws_theorems =
 ["LIST_EL_SEQ", LIST_EL_SEQ; "LIST_OF_LENGTH", LIST_OF_LENGTH; "HOL_TAPP_OK", HOL_TAPP_OK;
  "HOL_TPUT_MARK_OK", HOL_TPUT_MARK_OK;
  "HOL_LAYOUT_WF", HOL_LAYOUT_WF; "HOL_TAPP_EXISTS", HOL_TAPP_EXISTS];;
