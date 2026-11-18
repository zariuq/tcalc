(* ========================================================================= *)
(* HOL's tables through the interface: the native state's tables by the     *)
(* host's binding slots (PLANS.txt, section 2):                             *)
(*   rows  0 types (keyed), 6 de Bruijn rows (keyed), 12 terms (5 words),   *)
(*         18 theorems (2 words), 24 the Y map, 30 the N map (1 word),     *)
(*         44 the names (their bytes);                                      *)
(*   counts 4, 10, 14, 20, 26, 32, and 50 (the names' header);              *)
(*   marks 34 N ids, 28 Y ids, 16 terms, 22 theorems (drop spaces 0..3),    *)
(*   one word per id, written by put_word (hol_tput: a drop).               *)
(* A fixed table's row is the list of its words (hol_tw): a keyed row       *)
(* (tag,a,b) is held as the words tag + 8a and b. A name's row is its bytes *)
(* (hname_bytes, the inverse of holr_name on bytes: HNAME_BYTES_NAME,       *)
(* HOLR_NAME_BYTES), and names are appended as bytes. On the steps the      *)
(* record plans already take (pl_old_step), the interface's leaf meaning is *)
(* pl_leaf's for any input (TAB_LEAF_HOL), given the tags below 8 that the  *)
(* keys' canonical form gives and an append's width word 2; so are runs     *)
(* (TAB_RUN_HOL).                                                            *)
(*                                                                           *)
(* Loaded after tables.ml (holr_keys.ml is in the Model world).             *)
(* ========================================================================= *)

(* The byte a character holds; a name's bytes (holr_name's inverse on bytes). *)
let hchar_code = define
 `hchar_code (ASCII b7 b6 b5 b4 b3 b2 b1 b0) =
    (if b7 then 128 else 0) + (if b6 then 64 else 0) + (if b5 then 32 else 0) + (if b4 then 16 else 0) +
    (if b3 then 8 else 0) + (if b2 then 4 else 0) + (if b1 then 2 else 0) + (if b0 then 1 else 0)`;;

let hname_bytes = new_definition
 `hname_bytes (nm:string) = MAP hchar_code nm`;;

(* Word w of row i of a fixed table. *)
let hol_tw = new_definition
 `hol_tw j ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) i w =
    if j = 0 then pl_f3 (EL i tys) w else if j = 6 then pl_f3 (EL i dbs) w
    else if j = 12 then pl_f5 (EL i ntms) w else if j = 18 then pl_f2 (EL i ths) w
    else if j = 24 then EL i ymap else if j = 30 then EL i nmap else 0`;;

(* The widths of the rows, the marks' rows one word (put_word writes them). *)
let hol_twd = new_definition
 `hol_twd j = if j = 0 \/ j = 6 \/ j = 18 then 2 else if j = 12 then 5
              else if j = 24 \/ j = 30 \/ j = 16 \/ j = 22 \/ j = 28 \/ j = 34 then 1 else 0`;;

(* A fixed table's row is the list of its words; a name's row its bytes. *)
let hol_trow = new_definition
 `hol_trow j ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) i =
    if j = 44 then hname_bytes (EL i nms)
    else list_of_seq (hol_tw j (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) i) (hol_twd j)`;;

let hol_tn = new_definition
 `hol_tn c ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) =
    if c = 4 then LENGTH tys else if c = 10 then LENGTH dbs else if c = 14 then LENGTH ntms
    else if c = 20 then LENGTH ths else if c = 26 then LENGTH ymap else if c = 32 then LENGTH nmap
    else if c = 50 then LENGTH nms else 0`;;

let hol_tdrop = new_definition
 `hol_tdrop jm ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) i <=>
    if jm = 34 then MEM (0,i) drops else if jm = 28 then MEM (1,i) drops
    else if jm = 16 then MEM (2,i) drops else if jm = 22 then MEM (3,i) drops else F`;;

(* Names are appended as their bytes. *)
let hol_tapp = new_definition
 `hol_tapp j c ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) (r:num list) (s':nstate) <=>
    j = 0 /\ c = 4 /\ LENGTH r = 2 /\
      s' = (ctx,nms,APPEND tys [(EL 0 r MOD 8,EL 0 r DIV 8,EL 1 r)],ntms,dbs,ths,nmap,ymap,drops,pol) \/
    j = 6 /\ c = 10 /\ LENGTH r = 2 /\
      s' = (ctx,nms,tys,ntms,APPEND dbs [(EL 0 r MOD 8,EL 0 r DIV 8,EL 1 r)],ths,nmap,ymap,drops,pol) \/
    j = 12 /\ c = 14 /\ LENGTH r = 5 /\
      s' = (ctx,nms,tys,APPEND ntms [(EL 0 r,EL 1 r,EL 2 r,EL 3 r,EL 4 r)],dbs,ths,nmap,ymap,drops,pol) \/
    j = 18 /\ c = 20 /\ LENGTH r = 2 /\
      s' = (ctx,nms,tys,ntms,dbs,APPEND ths [(EL 0 r,EL 1 r)],nmap,ymap,drops,pol) \/
    j = 24 /\ c = 26 /\ LENGTH r = 1 /\
      s' = (ctx,nms,tys,ntms,dbs,ths,nmap,APPEND ymap [EL 0 r],drops,pol) \/
    j = 30 /\ c = 32 /\ LENGTH r = 1 /\
      s' = (ctx,nms,tys,ntms,dbs,ths,APPEND nmap [EL 0 r],ymap,drops,pol) \/
    j = 44 /\ c = 50 /\ ALL (\b. b < 256) r /\
      s' = (ctx,APPEND nms [holr_name r],tys,ntms,dbs,ths,nmap,ymap,drops,pol)`;;

(* A word written to the marks of the terms, theorems or Y ids: the id     *)
(* dropped (any word but 0) or live (0). Names are never dropped.           *)
let hol_mspace = new_definition
 `hol_mspace jm = if jm = 28 then 1 else if jm = 16 then 2 else 3`;;

let hol_tput = new_definition
 `hol_tput j c ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) i w v (s':nstate) <=>
    (j = 16 /\ c = 14 \/ j = 22 /\ c = 20 \/ j = 28 /\ c = 26) /\ w = 0 /\
    s' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,
          (if v = 0 then FILTER (\p. ~(p = (hol_mspace j,i))) drops else CONS (hol_mspace j,i) drops),pol)`;;

let hol_tables = new_definition
 `hol_tables = (hol_trow,hol_tn,hol_twd,hol_tdrop,hol_tapp,hol_tput)`;;

(* The keyed tables' tags below 8: the packing tag + 8a is invertible. *)
let tab_canon = new_definition
 `tab_canon ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) <=>
    (!i. i < LENGTH tys ==> FST(EL i tys) < 8) /\ (!i. i < LENGTH dbs ==> FST(EL i dbs) < 8)`;;

(* The steps the record plans of plans_abs.ml take, by leaf and slots. *)
let pl_old_step = new_definition
 `pl_old_step (st:int64 list) <=>
    val(EL 0 st) = 0 /\ (val(EL 1 st) = 0 /\ val(EL 3 st) = 4 \/ val(EL 1 st) = 6 /\ val(EL 3 st) = 10) \/
    val(EL 0 st) = 1 \/ val(EL 0 st) = 2 \/ val(EL 0 st) = 3 \/
    val(EL 0 st) = 4 /\ (val(EL 1 st) = 0 /\ val(EL 2 st) = 4 \/ val(EL 1 st) = 6 /\ val(EL 2 st) = 10 \/
                          val(EL 1 st) = 12 /\ val(EL 2 st) = 14 \/ val(EL 1 st) = 18 /\ val(EL 2 st) = 20) \/
    val(EL 0 st) = 5 /\ (val(EL 1 st) = 14 /\ val(EL 2 st) = 16 \/ val(EL 1 st) = 20 /\ val(EL 2 st) = 22 \/
                          val(EL 1 st) = 26 /\ val(EL 2 st) = 28) \/
    val(EL 0 st) = 6 /\ val(EL 1 st) = 18 /\ val(EL 2 st) = 20`;;

(* ------------------------------------------------------------------------- *)
(* Names: a character's byte, a name's bytes.                               *)
(* ------------------------------------------------------------------------- *)

let HCHAR_CODE_OF = prove
 (`!n. n < 256 ==> hchar_code (hchar_of n) = n`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[hchar_of; hchar_code] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC BITS8 THEN ASM_REWRITE_TAC[]);;

let HCHAR_OF_CODE = prove
 (`!c. hchar_of (hchar_code c) = c`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `c:char` (cases "char")) THEN
  REWRITE_TAC[hchar_code; hchar_of; CHAR_INJ] THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let HCHAR_CODE_LT = prove
 (`!c. hchar_code c < 256`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `c:char` (cases "char")) THEN
  REWRITE_TAC[hchar_code] THEN REPEAT COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV);;

let HOLR_NAME_BYTES = prove
 (`!nm. holr_name (hname_bytes nm) = nm`,
  REWRITE_TAC[holr_name; hname_bytes] THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; HCHAR_OF_CODE]);;

let HNAME_BYTES_NAME = prove
 (`!bs. ALL (\b. b < 256) bs ==> hname_bytes (holr_name bs) = bs`,
  REWRITE_TAC[holr_name; hname_bytes] THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[HCHAR_CODE_OF]);;

let HNAME_BYTES_LT = prove
 (`!nm. ALL (\b. b < 256) (hname_bytes nm)`,
  REWRITE_TAC[hname_bytes; ALL_MAP; o_DEF; HCHAR_CODE_LT; ALL_T]);;

(* ------------------------------------------------------------------------- *)
(* One step: the interface's meaning is pl_leaf's.                           *)
(* ------------------------------------------------------------------------- *)

(* A canonical keyed row matches the two words exactly when it is their key. *)
let PL_F3_KEY = prove
 (`!r k0 k1. FST r < 8 ==> (pl_f3 r 0 = k0 /\ pl_f3 r 1 = k1 <=> r = pl_key k0 k1)`,
  REWRITE_TAC[FORALL_PAIR_THM; pl_f3; pl_key; PAIR_EQ; FST; SND] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) && is_var(rhs(concl th)) &&
      rhs(concl th) = `k0:num`)) THEN
    ASM_SIMP_TAC[PL_TAG_MODDIV];
    ASM_REWRITE_TAC[] THEN MESON_TAC[DIVISION_SIMP; ADD_SYM; MULT_SYM]]);;

(* pl_intern by the two words of the rows, for canonical rows. *)
let PL_INTERN_WORDS = prove
 (`!rows k0 k1 k pay rows'.
     (!i. i < LENGTH rows ==> FST(EL i rows) < 8)
     ==> (pl_intern rows k0 k1 k pay rows' <=>
          (k = 1 /\ pay < 2 EXP 60 /\
           (pay < LENGTH rows /\ pl_f3 (EL pay rows) 0 = k0 /\ pl_f3 (EL pay rows) 1 = k1 /\ rows' = rows \/
            pay = LENGTH rows /\
            (!i. i < LENGTH rows ==> ~(pl_f3 (EL i rows) 0 = k0 /\ pl_f3 (EL i rows) 1 = k1)) /\
            LENGTH rows + 1 < 2 EXP 60 /\ rows' = APPEND rows [(k0 MOD 8,k0 DIV 8,k1)])) \/
          (~(k = 0) /\ ~(k = 1) /\ rows' = rows))`,
  let KEY_WORDS = prove(`!k0 k1. pl_f3 (pl_key k0 k1) 0 = k0 /\ pl_f3 (pl_key k0 k1) 1 = k1`,
    REWRITE_TAC[pl_f3; pl_key; FST; SND] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MESON_TAC[DIVISION_SIMP; ADD_SYM; MULT_SYM]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i < LENGTH (rows:(num#num#num)list)
                    ==> (pl_f3 (EL i rows) 0 = k0 /\ pl_f3 (EL i rows) 1 = k1 <=> EL i rows = pl_key k0 k1)`
    ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_F3_KEY THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pl_intern; pl_interned] THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[KEY_WORDS; APPEND_NIL] THEN
    DISJ2_TAC THEN REWRITE_TAC[pl_key] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `~MEM (pl_key k0 k1) (rows:(num#num#num)list)` THEN
    REWRITE_TAC[MEM_EXISTS_EL] THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `[]:(num#num#num)list` THEN ASM_REWRITE_TAC[APPEND_NIL] THEN ASM_MESON_TAC[];
      EXISTS_TAC `[pl_key k0 k1]` THEN REWRITE_TAC[MEM_EXISTS_EL; NOT_EXISTS_THM] THEN
      CONJ_TAC THENL
       [DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN
        ASM_CASES_TAC `i < LENGTH (rows:(num#num#num)list)` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ASM_REWRITE_TAC[pl_key]]]]);;

(* row_word over rows that are lists of words reads the words. *)
let TAB_ROWW_SEQ = prove
 (`!(f:num->num->num) n wd a0 a1 v1 k pay.
     pl_roww (\i w. EL w (list_of_seq (f i) wd)) n wd a0 a1 v1 k pay <=> pl_roww f n wd a0 a1 v1 k pay`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_roww] THEN
  ASM_CASES_TAC `a0 < n /\ a1 < wd` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

(* The fixed tables' rows as their words. *)
let TAB_TROW_TAC =
  REWRITE_TAC[tab_intern; hol_trow; hol_twd] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[TAB_ROWW_SEQ] THEN CONV_TAC(DEPTH_CONV LIST_OF_SEQ_CONV) THEN REWRITE_TAC[CONS_11];;

let TAB_HOL_UNFOLD_TAC =
  REWRITE_TAC[pl_roww; pl_live; holr_live; tab_live; tab_append; pl_append_th; tab_row;
              hol_tw; hol_tn; hol_twd; hol_tdrop; hol_tapp] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[];;

let TAB_APPEND_HOL_TAC =
  TAB_HOL_UNFOLD_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; LENGTH_LIST_OF_SEQ; ARITH] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[] THEN MESON_TAC[];;

let TAB_INTERN_HOL_TAC =
  REWRITE_TAC[tab_intern; hol_tw; hol_tn; hol_tapp] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  ASSUM_LIST(fun ths -> REWRITE_TAC(mapfilter (MATCH_MP PL_INTERN_WORDS) ths)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];;

let TAB_LEAF_HOL = prove
 (`!inp st cw ctx nms tys ntms dbs ths nmap ymap drops pol stk k pay ns'.
     pl_old_step st /\ tab_canon (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
     (val(EL 0 st) = 6 ==> cw(val(EL 12 st)) = 2)
     ==> (pl_leaf st (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) k pay ns' <=>
          tab_leaf hol_tables inp st (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) k pay ns')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_old_step; tab_canon] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[pl_leaf; tab_leaf; hol_tables; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN TAB_TROW_TAC THEN
  FIRST [TAB_HOL_UNFOLD_TAC THEN NO_TAC; TAB_APPEND_HOL_TAC; TAB_INTERN_HOL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Runs: canonical tags are kept, and the two runs agree.                    *)
(* ------------------------------------------------------------------------- *)

let PL_INTERN_CANON = prove
 (`!rows k0 k1 k pay rows'.
     (!i. i < LENGTH rows ==> FST(EL i rows) < 8) /\ pl_intern rows k0 k1 k pay rows'
     ==> (!i. i < LENGTH rows' ==> FST(EL i rows') < 8)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN ASSUME_TAC(CONJUNCT1 th)) THEN
  ASM_SIMP_TAC[PL_INTERN_WORDS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; EL_APPEND] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `i - LENGTH (rows:(num#num#num)list) = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EL; HD; FST] THEN SIMP_TAC[DIVISION; ARITH_EQ]);;

let TAB_CANON_LEAF = prove
 (`!st cw ctx nms tys ntms dbs ths nmap ymap drops pol stk k pay ns'.
     pl_old_step st /\ tab_canon (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
     pl_leaf st (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) k pay ns'
     ==> tab_canon ns'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_old_step] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[pl_leaf; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tab_canon]) THEN REWRITE_TAC[tab_canon] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_INTERN_CANON THEN ASM_MESON_TAC[]);;

let TAB_RUN_HOL = prove
 (`!inp P i cw ns stk r.
     ALL pl_old_step P /\ tab_canon ns /\ cw 2 = 2 /\
     (!st. MEM st P ==> ~(val(EL 17 st) = 2) /\ (val(EL 0 st) = 6 ==> val(EL 12 st) = 2))
     ==> (pl_run P i (cw,ns,stk) r <=> tab_run hol_tables inp P i (cw,ns,stk) r)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL [REWRITE_TAC[pl_run; tab_run]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN SPEC_TAC(`ns:nstate`,`ns:nstate`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC pl_ns_vars THEN REWRITE_TAC[ALL; MEM] THEN STRIP_TAC THEN
  REWRITE_TAC[pl_run; tab_run; FST; SND] THEN
  SUBGOAL_THEN (mk_forall(`k:num`, mk_forall(`pay:num`, mk_forall(`ns':nstate`,
     mk_iff(list_mk_icomb "pl_leaf" [`h:int64 list`; mk_pair(`cw:num->num`, mk_pair(end_itlist (curry mk_pair) pl_ns_vars, `stk:num list`)); `k:num`; `pay:num`; `ns':nstate`],
            list_mk_icomb "tab_leaf" [`hol_tables`; `inp:num list`; `h:int64 list`; mk_pair(`cw:num->num`, mk_pair(end_itlist (curry mk_pair) pl_ns_vars, `stk:num list`)); `k:num`; `pay:num`; `ns':nstate`])))))
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC TAB_LEAF_HOL THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN SUBGOAL_THEN `val(EL 12 (h:int64 list)) = 2` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `pay:num` (X_CHOOSE_THEN `ns':nstate` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `pay:num`; `ns':nstate`] THEN ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN `tab_canon (ns':nstate)` ASSUME_TAC THENL
    [MP_TAC(SPECL ([`h:int64 list`; `cw:num->num`] @ pl_ns_vars @ [`stk:num list`; `k:num`; `pay:num`; `ns':nstate`])
                  TAB_CANON_LEAF) THEN
     ASM_REWRITE_TAC[tab_canon] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
     ALL_TAC]) THEN
  COND_CASES_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term (is_const_app "tab_run")) (concl th)
     then (MP_TAC(SPECL [`i + 1`; `pl_set cw (val(EL 17 (h:int64 list))) pay`; `ns':nstate`; `stk:num list`;
                         `r:num#num#pstate`] th)) else failwith "") THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[pl_set] THEN BETA_TAC THEN REPEAT CONJ_TAC THEN
     TRY(COND_CASES_TAC THEN ASM_MESON_TAC[]) THEN ASM_MESON_TAC[];
     SIMP_TAC[]]));;

(* Every theorem this file states, for the audits. *)
let tables_hol_theorems =
 ["HCHAR_CODE_OF", HCHAR_CODE_OF; "HCHAR_OF_CODE", HCHAR_OF_CODE; "HCHAR_CODE_LT", HCHAR_CODE_LT;
  "HOLR_NAME_BYTES", HOLR_NAME_BYTES; "HNAME_BYTES_NAME", HNAME_BYTES_NAME; "HNAME_BYTES_LT", HNAME_BYTES_LT;
  "PL_F3_KEY", PL_F3_KEY; "PL_INTERN_WORDS", PL_INTERN_WORDS; "TAB_ROWW_SEQ", TAB_ROWW_SEQ;
  "TAB_LEAF_HOL", TAB_LEAF_HOL; "PL_INTERN_CANON", PL_INTERN_CANON; "TAB_CANON_LEAF", TAB_CANON_LEAF;
  "TAB_RUN_HOL", TAB_RUN_HOL];;
