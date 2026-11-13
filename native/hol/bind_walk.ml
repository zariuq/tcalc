(* ========================================================================= *)
(* The binding walk: the de Bruijn image of an abstraction, as the           *)
(* standalone t-ISA p1 program bind_walk (tcalc/native/walks/bind_walk.metta;*)
(* its text is tcalc/native/walks/bind_walk_prog.txt, its image record      *)
(* bind_walk.hol).                                                           *)
(*                                                                           *)
(* HOLR's ABS record builds TmAbs v body; its image is                       *)
(*   hdbAbs ty (hbind (x,ty) 0 (hdb body)).                                  *)
(* The walk computes it over the hash-consed de Bruijn rows, interning every *)
(* new row with intern16's algorithm and table, and returns the dbAbs row.   *)
(*                                                                           *)
(* Regions (intern16's numbering): 0 rows (16-byte rows k0 = tag + 8a,      *)
(* k1 = b), 1 table (8-byte slots), 2 header (word 0 the published count),  *)
(* 3 work (at least 256 bytes). Inputs: arg0 = x (name id), arg1 = ty (type *)
(* id), entry register v1 = t (the body's image row).                       *)
(*                                                                           *)
(* Main theorems:                                                            *)
(*  BW_RUN: every run from a state entry validation accepts ends with        *)
(*    bw_result: the table invariant intern_ok kept; the rows below the     *)
(*    published count kept (when they lie in the rows region); FIRED        *)
(*    returns a row that decodes, in the rows below the new published count, *)
(*    to hdbAbs TY (hbind (EL x nms,TY) 0 T) whenever t decodes to T in the  *)
(*    rows below the old count (bw_final), for every names list nms and type *)
(*    rows tys in which x is the only id with its name and ty the only id   *)
(*    with its type TY (bw_ctx); every other outcome leaves the published   *)
(*    count.                                                                 *)
(*  BIND_WALK_SOUND, BIND_WALK_CANONICAL: the same, stated directly.         *)
(*  BW_CTX_SATISFIABLE: the hypotheses of soundness can hold.                *)
(*                                                                           *)
(* The walk's memory is untrusted: tasks are checked against their rows and *)
(* the results they combine, memo slots against the log count and the log  *)
(* entry's key; only result entries below vsp and log entries below lc,     *)
(* written by this run, carry claims (bw_mid). New rows are appended at a   *)
(* private count (work word 0); the published count is written once, last,  *)
(* on FIRED.                                                                 *)
(* ========================================================================= *)

needs "native/hol/intern16_complete.ml";;
(* The fibre's row decoders (holfibre.ml's, verbatim; see that file). *)
needs "native/hol/holfibre_rows.ml";;

(* Four regions: decisions use focused arithmetic (tisa_wp.ml's header); the *)
(* setting is restored at the end of this file.                              *)
let bw_saved_arith_focus = !tisa_arith_focus;;
tisa_arith_focus := true;;

(* ------------------------------------------------------------------------- *)
(* The claims of the walk, in the fibre's decoding (fddb, holfibre.ml).      *)
(* ------------------------------------------------------------------------- *)

(* A decoded row lies below the list's length. *)
let FDDB_LT = prove
 (`!nms tys dbs i t. fddb nms tys dbs i t ==> i < LENGTH dbs`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[fddb_CASES] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* D' extends D: the rows of D, then more. *)
let bw_ext = new_definition
 `bw_ext (D:(num#num#num)list) D' <=>
    LENGTH D <= LENGTH D' /\ !i. i < LENGTH D ==> EL i D' = EL i D`;;

let BW_EXT_REFL = prove
 (`!D:(num#num#num)list. bw_ext D D`,
  REWRITE_TAC[bw_ext; LE_REFL]);;

let BW_EXT_TRANS = prove
 (`!D1 D2 D3:(num#num#num)list. bw_ext D1 D2 /\ bw_ext D2 D3 ==> bw_ext D1 D3`,
  REWRITE_TAC[bw_ext] THEN REPEAT STRIP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i < LENGTH(D2:(num#num#num)list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

let BW_FDDB_EXT_BOTH = prove
 (`!nms tys D D'.
     bw_ext D D'
     ==> (!i t. fddb nms tys D i t ==> fddb nms tys D' i t) /\
         (!i l. fddbs nms tys D i l ==> fddbs nms tys D' i l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_ext] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i < LENGTH(D:(num#num#num)list) ==> i < LENGTH(D':(num#num#num)list) /\ EL i D' = EL i D`
   ASSUME_TAC THENL [ASM_MESON_TAC[LTE_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC fddb_INDUCT THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[fddb_RULES]);;

let BW_FDDB_EXT = prove
 (`!nms tys D D' i t. bw_ext D D' /\ fddb nms tys D i t ==> fddb nms tys D' i t`,
  MESON_TAC[BW_FDDB_EXT_BOTH]);;

(* x is the only name id with its string, ty the only type id with its type. *)
let bw_ctx = new_definition
 `bw_ctx nms tys x ty TY <=>
    x < LENGTH nms /\ fdty nms tys ty TY /\
    (!a. a < LENGTH nms /\ EL a nms = EL x nms ==> a = x) /\
    (!b. fdty nms tys b TY ==> b = ty)`;;

(* The claim of a result entry (i, n, r): row r, in the rows D, is hbind at   *)
(* depth n of row i in the rows D0 the walk started from.                     *)
let bw_claim = new_definition
 `bw_claim D0 D x ty i n r <=>
    !nms tys TY X. bw_ctx nms tys x ty TY /\ fddb nms tys D0 i X
                   ==> fddb nms tys D r (hbind (EL x nms,TY) n X)`;;

(* The claim of the whole walk: row r is dbAbs ty over hbind at depth 0 of t. *)
let bw_final = new_definition
 `bw_final D0 D x ty t r <=>
    !nms tys TY T. bw_ctx nms tys x ty TY /\ fddb nms tys D0 t T
                   ==> fddb nms tys D r (hdbAbs TY (hbind (EL x nms,TY) 0 T))`;;

let BW_CLAIM_EXT = prove
 (`!D0 D D' x ty i n r. bw_claim D0 D x ty i n r /\ bw_ext D D' ==> bw_claim D0 D' x ty i n r`,
  REWRITE_TAC[bw_claim] THEN MESON_TAC[BW_FDDB_EXT]);;

let BW_FINAL_EXT = prove
 (`!D0 D D' x ty t r. bw_final D0 D x ty t r /\ bw_ext D D' ==> bw_final D0 D' x ty t r`,
  REWRITE_TAC[bw_final] THEN MESON_TAC[BW_FDDB_EXT]);;

let BW_CLAIM_VACUOUS = prove
 (`!D0 D x ty i n r. ~(i < LENGTH D0) ==> bw_claim D0 D x ty i n r`,
  REWRITE_TAC[bw_claim] THEN MESON_TAC[FDDB_LT]);;

let BW_FINAL_VACUOUS = prove
 (`!D0 D x ty t r. ~(t < LENGTH D0) ==> bw_final D0 D x ty t r`,
  REWRITE_TAC[bw_final] THEN MESON_TAC[FDDB_LT]);;

(* The decoding of a row of each tag. *)
let BW_FDDB_ROW = prove
 (`!nms tys dbs i tag a b X.
     i < LENGTH dbs /\ EL i dbs = (tag,a,b) /\ fddb nms tys dbs i X
     ==> (tag = 0 /\ a < LENGTH nms /\ ?T. fdty nms tys b T /\ X = hdbVar (EL a nms) T) \/
         (tag = 1 /\ X = hdbBound a) \/
         (tag = 2 /\ a < LENGTH nms /\ ?T. fdty nms tys b T /\ X = hdbConst (EL a nms) T) \/
         (tag = 3 /\ ?A B. fddb nms tys dbs a A /\ fddb nms tys dbs b B /\ X = hdbComb A B) \/
         (tag = 4 /\ ?T B. fdty nms tys a T /\ fddb nms tys dbs b B /\ X = hdbAbs T B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[fddb_CASES] o check (fun th -> is_comb(concl th) &&
     can (find_term ((=) `fddb`)) (concl th))) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
                                                       not(type_of(lhand(concl th)) = `:hdbterm`)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ASM_MESON_TAC[]);;

(* Rows of tag 1 and 2, and of tag 0 other than the variable: unchanged. *)
let BW_CLAIM_SELF = prove
 (`!D0 D x ty i n tag a b.
     i < LENGTH D0 /\ EL i D0 = (tag,a,b) /\
     (tag = 1 \/ tag = 2 \/ tag = 0 /\ ~(a = x /\ b = ty)) /\ bw_ext D0 D
     ==> bw_claim D0 D x ty i n i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bw_claim; bw_ctx] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `D0:(num#num#num)list`;
                 `i:num`; `tag:num`; `a:num`; `b:num`; `X:hdbterm`] BW_FDDB_ROW) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `D0:(num#num#num)list`;
                 `D:(num#num#num)list`; `i:num`; `X:hdbterm`] BW_FDDB_EXT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
                                                       is_numeral(rand(concl th))))) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NUM_REDUCE_CONV)) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhand(concl th) = `X:hdbterm`)) THEN
  REWRITE_TAC[hbind] THEN TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_MESON_TAC[]);;

(* The equality of an hdbterm with its hbind image when both decode one row. *)
let BW_HBIND_SAME = prove
 (`!nms tys D a v n X.
     fddb nms tys D a (hbind v n X) /\ fddb nms tys D a X ==> hbind v n X = X`,
  MESON_TAC[FDDB_FUNCTIONAL]);;

(* The variable itself: dbBound n. *)
let BW_CLAIM_BOUND = prove
 (`!D0 D x ty i n r b'.
     i < LENGTH D0 /\ EL i D0 = (0,x,ty) /\ r < LENGTH D /\ EL r D = (1,n,b')
     ==> bw_claim D0 D x ty i n r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bw_claim; bw_ctx] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `D0:(num#num#num)list`;
                 `i:num`; `0`; `x:num`; `ty:num`; `X:hdbterm`] BW_FDDB_ROW) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[hbind; PAIR_EQ] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(SPEC_ALL fddb_RULES))) THEN
    EXISTS_TAC `b':num` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[FDTY_FUNCTIONAL]]);;

(* dbComb(a, b) whose children are unchanged: the row itself. *)
let BW_CLAIM_COMB_SAME = prove
 (`!D0 D x ty i n a b.
     i < LENGTH D0 /\ EL i D0 = (3,a,b) /\ bw_ext D0 D /\
     bw_claim D0 D x ty a n a /\ bw_claim D0 D x ty b n b
     ==> bw_claim D0 D x ty i n i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_claim] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `D0:(num#num#num)list`;
                 `i:num`; `3`; `a:num`; `b:num`; `X:hdbterm`] BW_FDDB_ROW) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `fddb nms tys D a (hbind (EL x nms,TY) n A) /\ fddb nms tys D a A /\
                fddb nms tys D b (hbind (EL x nms,TY) n B) /\ fddb nms tys D b B /\
                fddb nms tys D i X`
   STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[BW_FDDB_EXT]; ALL_TAC] THEN
  SUBGOAL_THEN `hbind (EL x nms,TY) n A = A /\ hbind (EL x nms,TY) n B = B` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[BW_HBIND_SAME]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhand(concl th) = `X:hdbterm`)) THEN
  ASM_REWRITE_TAC[hbind]);;

let BW_CLAIM_ABS_SAME = prove
 (`!D0 D x ty i n A b.
     i < LENGTH D0 /\ EL i D0 = (4,A,b) /\ bw_ext D0 D /\ bw_claim D0 D x ty b (n + 1) b
     ==> bw_claim D0 D x ty i n i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_claim] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `D0:(num#num#num)list`;
                 `i:num`; `4`; `A:num`; `b:num`; `X:hdbterm`] BW_FDDB_ROW) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `fddb nms tys D b (hbind (EL x nms,TY) (n + 1) B) /\ fddb nms tys D b B /\
                fddb nms tys D i X`
   STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[BW_FDDB_EXT]; ALL_TAC] THEN
  SUBGOAL_THEN `hbind (EL x nms,TY) (n + 1) B = B` ASSUME_TAC THENL
   [ASM_MESON_TAC[BW_HBIND_SAME]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhand(concl th) = `X:hdbterm`)) THEN
  ASM_REWRITE_TAC[hbind]);;

(* The end: dbAbs ty over the result for (t, 0). *)
let BW_FINAL_ABS = prove
 (`!D0 D x ty t rt r.
     bw_claim D0 D x ty t 0 rt /\ r < LENGTH D /\ EL r D = (4,ty,rt)
     ==> bw_final D0 D x ty t r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_claim; bw_final] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(SPEC_ALL fddb_RULES)))))) THEN
  MAP_EVERY EXISTS_TAC [`ty:num`; `rt:num`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[bw_ctx]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* dbComb(a, b), its children's results ra and rb, and the row r of the key  *)
(* dbComb(ra, rb). The key's row is needed only when ra lies below the rows  *)
(* (a row id shifted into a key word is exact there).                        *)
let BW_CLAIM_COMB = prove
 (`!D0 D x ty i n a b ra rb r.
     i < LENGTH D0 /\ EL i D0 = (3,a,b) /\
     bw_claim D0 D x ty a n ra /\ bw_claim D0 D x ty b n rb /\
     (ra < LENGTH D ==> r < LENGTH D /\ EL r D = (3,ra,rb))
     ==> bw_claim D0 D x ty i n r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_claim] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `D0:(num#num#num)list`;
                 `i:num`; `3`; `a:num`; `b:num`; `X:hdbterm`] BW_FDDB_ROW) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[hbind] THEN
  SUBGOAL_THEN `fddb nms tys D ra (hbind (EL x nms,TY) n A) /\ fddb nms tys D rb (hbind (EL x nms,TY) n B)`
   STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ra < LENGTH(D:(num#num#num)list)` ASSUME_TAC THENL [ASM_MESON_TAC[FDDB_LT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(SPEC_ALL fddb_RULES))))) THEN
  MAP_EVERY EXISTS_TAC [`ra:num`; `rb:num`] THEN ASM_REWRITE_TAC[]);;

(* dbAbs(A, b), the body's result rb at depth n + 1, and the row r of the    *)
(* key dbAbs(A, rb).                                                         *)
let BW_CLAIM_ABS = prove
 (`!D0 D x ty i n A b rb r.
     i < LENGTH D0 /\ EL i D0 = (4,A,b) /\
     bw_claim D0 D x ty b (n + 1) rb /\ r < LENGTH D /\ EL r D = (4,A,rb)
     ==> bw_claim D0 D x ty i n r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_claim] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `D0:(num#num#num)list`;
                 `i:num`; `4`; `A:num`; `b:num`; `X:hdbterm`] BW_FDDB_ROW) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[hbind] THEN
  MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(SPEC_ALL fddb_RULES)))))) THEN
  MAP_EVERY EXISTS_TAC [`A:num`; `rb:num`] THEN ASM_MESON_TAC[]);;

let bw_abs_expand = new_definition
 `bw_abs_expand = (TSeq (TInstr (TLoad TyU64 8 3 1 2 (&32:int))) (TSeq (TInstr (TImm TyU64 4 (word 2))) (TSeq (TInstr (TBin BinAdd TyU64 4 3 4)) (TSeq (TInstr (TCmp CondUlt TyU64 1 1 (OpReg 4))) (TSeq (TIf 1 (TSeq (TInstr (TImm TyU64 6 (word 10))) (TReturn 2 6)) TSkip) (TSeq (TInstr (TShift ShiftLeft TyU64 4 3 2)) (TSeq (TInstr (TAddr 3 4 2 (SOME 4) 3 (&128:int))) (TSeq (TInstr (TImm TyU64 1 (word 2))) (TSeq (TInstr (TStore 8 3 4 (&0:int) 1)) (TSeq (TInstr (TImm TyU64 1 (word 0))) (TSeq (TInstr (TStore 8 3 4 (&32:int) 1)) (TSeq (TInstr (TStore 8 3 4 (&40:int) 5)) (TSeq (TInstr (TImm TyU64 1 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 1 7 1)) (TSeq (TInstr (TStore 8 3 4 (&48:int) 1)) (TSeq (TInstr (TImm TyU64 1 (word 2))) (TSeq (TInstr (TBin BinAdd TyU64 1 3 1)) (TSeq (TInstr (TStore 8 3 2 (&8:int) 1)) (TSeq (TInstr (TImm TyU64 1 (word 3))) (TSeq (TInstr (TStore 8 3 2 (&64:int) 1)) (TInstr (TImm TyBool 9 (word 0)))))))))))))))))))))))`;;

let bw_comb_expand = new_definition
 `bw_comb_expand = (TSeq (TInstr (TLoad TyU64 8 3 1 2 (&32:int))) (TSeq (TInstr (TImm TyU64 4 (word 3))) (TSeq (TInstr (TBin BinAdd TyU64 4 3 4)) (TSeq (TInstr (TCmp CondUlt TyU64 1 1 (OpReg 4))) (TSeq (TIf 1 (TSeq (TInstr (TImm TyU64 6 (word 10))) (TReturn 2 6)) TSkip) (TSeq (TInstr (TShift ShiftRightU TyU64 6 6 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 4 3 2)) (TSeq (TInstr (TAddr 3 4 2 (SOME 4) 3 (&128:int))) (TSeq (TInstr (TImm TyU64 1 (word 1))) (TSeq (TInstr (TStore 8 3 4 (&0:int) 1)) (TSeq (TInstr (TImm TyU64 1 (word 0))) (TSeq (TInstr (TStore 8 3 4 (&32:int) 1)) (TSeq (TInstr (TStore 8 3 4 (&40:int) 5)) (TSeq (TInstr (TStore 8 3 4 (&48:int) 7)) (TSeq (TInstr (TStore 8 3 4 (&64:int) 1)) (TSeq (TInstr (TStore 8 3 4 (&72:int) 6)) (TSeq (TInstr (TStore 8 3 4 (&80:int) 7)) (TSeq (TInstr (TImm TyU64 1 (word 3))) (TSeq (TInstr (TBin BinAdd TyU64 1 3 1)) (TSeq (TInstr (TStore 8 3 2 (&8:int) 1)) (TSeq (TInstr (TImm TyU64 1 (word 3))) (TSeq (TInstr (TStore 8 3 2 (&64:int) 1)) (TInstr (TImm TyBool 9 (word 0)))))))))))))))))))))))))`;;

let bw_leaf = new_definition
 `bw_leaf = (TSeq (TInstr (TMov TyU64 5 8)) (TSeq (TInstr (TImm TyU64 4 (word 0))) (TSeq (TInstr (TStore 8 3 2 (&64:int) 4)) (TInstr (TImm TyBool 9 (word 0))))))`;;

let bw_bound = new_definition
 `bw_bound = (TSeq (TInstr (TCmp CondUlt TyU64 1 7 (OpImm (word 1152921504606846976)))) (TSeq (TIf 1 TSkip (TSeq (TInstr (TImm TyU64 6 (word 8))) (TReturn 2 6))) (TSeq (TInstr (TShift ShiftLeft TyU64 1 7 3)) (TSeq (TInstr (TImm TyU64 6 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 1 1 6)) (TSeq (TInstr (TImm TyU64 2 (word 0))) (TSeq (TInstr (TLoadFrame TyPtr 6 6)) (TSeq (TInstr (TImm TyU64 4 (word 0))) (TSeq (TInstr (TStore 8 3 6 (&64:int) 4)) (TInstr (TImm TyBool 9 (word 1))))))))))))`;;

let bw_tags = new_definition
 `bw_tags = (TSeq (TInstr (TImm TyU64 1 (word 7))) (TSeq (TInstr (TBin BinAnd TyU64 1 6 1)) (TSeq (TInstr (TCmp CondUlt TyU64 9 1 (OpImm (word 3)))) (TIf 9 bw_leaf (TSeq (TInstr (TCmp CondEq TyU64 9 1 (OpImm (word 3)))) (TIf 9 bw_comb_expand (TSeq (TInstr (TCmp CondEq TyU64 9 1 (OpImm (word 4)))) (TIf 9 bw_abs_expand (TSeq (TInstr (TImm TyU64 6 (word 9))) (TReturn 2 6))))))))))`;;

let bw_miss = new_definition
 `bw_miss = (TSeq (TInstr (TShift ShiftLeft TyU64 1 8 1)) (TSeq (TInstr (TLoadFrame TyPtr 5 0)) (TSeq (TInstr (TAddr 0 5 5 (SOME 1) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 6 5 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 5 5 (&8:int))) (TSeq (TInstr (TLoadFrame TyU64 1 22)) (TSeq (TInstr (TShift ShiftLeft TyU64 1 1 3)) (TSeq (TInstr (TCmp CondEq TyU64 1 6 (OpReg 1))) (TSeq (TInstr (TLoadFrame TyU64 9 23)) (TSeq (TInstr (TCmp CondEq TyU64 9 5 (OpReg 9))) (TSeq (TInstr (TBin BinAnd TyBool 1 1 9)) (TIf 1 bw_bound bw_tags))))))))))))`;;

let bw_append = new_definition
 `bw_append = (TSeq (TInstr (TLoadFrame TyPtr 3 6)) (TSeq (TInstr (TLoad TyU64 8 3 5 3 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 3 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 3 3 4)) (TSeq (TInstr (TCmp CondUlt TyU64 3 5 (OpReg 3))) (TIf 3 (TSeq (TInstr (TShift ShiftLeft TyU64 3 5 1)) (TSeq (TInstr (TLoadFrame TyPtr 6 0)) (TSeq (TInstr (TAddr 0 6 6 (SOME 3) 3 (&0:int))) (TSeq (TInstr (TStore 8 0 6 (&0:int) 1)) (TSeq (TInstr (TStore 8 0 6 (&8:int) 2)) (TSeq (TInstr (TImm TyU64 3 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 3 5 3)) (TSeq (TInstr (TStore 8 1 4 (&0:int) 3)) (TSeq (TInstr (TLoadFrame TyPtr 6 6)) (TSeq (TInstr (TStore 8 3 6 (&0:int) 3)) (TInstr (TImm TyBool 9 (word 0))))))))))))) (TSeq (TInstr (TImm TyU64 3 (word 16))) (TReturn 2 3))))))))`;;

let bw_occupied = new_definition
 `bw_occupied = (TSeq (TInstr (TImm TyU64 3 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 5 5 3)) (TSeq (TInstr (TLoadFrame TyPtr 3 6)) (TSeq (TInstr (TLoad TyU64 8 3 3 3 (&0:int))) (TSeq (TInstr (TCmp CondUlt TyU64 3 5 (OpReg 3))) (TIf 3 (TSeq (TInstr (TShift ShiftLeft TyU64 3 5 1)) (TSeq (TInstr (TLoadFrame TyPtr 4 0)) (TSeq (TInstr (TAddr 0 4 4 (SOME 3) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 3 4 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 3 3 (OpReg 1))) (TIf 3 (TSeq (TInstr (TLoad TyU64 8 0 3 4 (&8:int))) (TSeq (TInstr (TCmp CondEq TyU64 3 3 (OpReg 2))) (TIf 3 (TInstr (TImm TyBool 9 (word 0))) TSkip))) TSkip)))))) TSkip))))))`;;

let bw_memo = new_definition
 `bw_memo = (TSeq (TInstr (TLoad TyU64 8 3 4 2 (&24:int))) (TSeq (TInstr (TLoad TyU64 8 3 6 2 (&32:int))) (TSeq (TInstr (TCmp CondUlt TyU64 3 4 (OpReg 6))) (TIf 3 (TSeq (TInstr (TShift ShiftLeft TyU64 3 6 1)) (TSeq (TInstr (TBin BinAdd TyU64 3 3 4)) (TSeq (TInstr (TShift ShiftLeft TyU64 3 3 2)) (TSeq (TInstr (TAddr 3 3 2 (SOME 3) 3 (&128:int))) (TSeq (TInstr (TStore 8 3 3 (&0:int) 7)) (TSeq (TInstr (TStore 8 3 3 (&8:int) 8)) (TSeq (TInstr (TStore 8 3 3 (&16:int) 5)) (TSeq (TInstr (TShift ShiftLeft TyU64 1 6 2)) (TSeq (TInstr (TImm TyU64 3 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 1 1 3)) (TSeq (TInstr (TImm TyU64 3 (word 11400714819323198485))) (TSeq (TInstr (TBin BinMulLo TyU64 9 8 3)) (TSeq (TInstr (TBin BinAdd TyU64 9 9 7)) (TSeq (TInstr (TBin BinMulLo TyU64 9 9 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 9 9 32)) (TSeq (TInstr (TBin BinAnd TyU64 9 9 1)) (TSeq (TInstr (TShift ShiftLeft TyU64 3 6 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 1 6 2)) (TSeq (TInstr (TBin BinAdd TyU64 1 1 3)) (TSeq (TInstr (TBin BinAdd TyU64 1 1 9)) (TSeq (TInstr (TAddr 3 1 2 (SOME 1) 3 (&128:int))) (TSeq (TInstr (TStore 8 3 1 (&0:int) 4)) (TSeq (TInstr (TImm TyU64 3 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 4 4 3)) (TInstr (TStore 8 3 2 (&24:int) 4)))))))))))))))))))))))))) TSkip))))`;;

let bw_abs = new_definition
 `bw_abs = (TSeq (TInstr (TShift ShiftLeft TyU64 1 8 1)) (TSeq (TInstr (TLoadFrame TyPtr 4 0)) (TSeq (TInstr (TAddr 0 4 4 (SOME 1) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 6 4 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 5 4 (&8:int))) (TSeq (TInstr (TImm TyU64 1 (word 7))) (TSeq (TInstr (TBin BinAnd TyU64 1 6 1)) (TSeq (TInstr (TCmp CondEq TyU64 1 1 (OpImm (word 4)))) (TSeq (TIf 1 TSkip (TSeq (TInstr (TImm TyU64 6 (word 11))) (TReturn 2 6))) (TSeq (TInstr (TCmp CondUlt TyU64 1 7 (OpImm (word 1152921504606846976)))) (TSeq (TIf 1 TSkip (TSeq (TInstr (TImm TyU64 6 (word 8))) (TReturn 2 6))) (TSeq (TInstr (TLoad TyU64 8 3 3 2 (&16:int))) (TSeq (TInstr (TCmp CondEq TyU64 1 3 (OpImm (word 0)))) (TSeq (TIf 1 (TSeq (TInstr (TImm TyU64 6 (word 12))) (TReturn 2 6)) TSkip) (TSeq (TInstr (TImm TyU64 1 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 3 3 1)) (TSeq (TInstr (TStore 8 3 2 (&16:int) 3)) (TSeq (TInstr (TLoad TyU64 8 3 1 2 (&32:int))) (TSeq (TInstr (TBin BinAdd TyU64 1 1 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 1 1 2)) (TSeq (TInstr (TAddr 3 4 2 (SOME 1) 3 (&128:int))) (TSeq (TInstr (TLoad TyU64 8 3 1 4 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 1 1 (OpReg 5))) (TSeq (TInstr (TLoad TyU64 8 3 3 4 (&8:int))) (TSeq (TInstr (TImm TyU64 9 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 9 7 9)) (TSeq (TInstr (TCmp CondEq TyU64 3 3 (OpReg 9))) (TSeq (TInstr (TBin BinAnd TyBool 1 1 3)) (TSeq (TIf 1 TSkip (TSeq (TInstr (TImm TyU64 6 (word 13))) (TReturn 2 6))) (TSeq (TInstr (TLoad TyU64 8 3 3 4 (&16:int))) (TSeq (TInstr (TImm TyU64 1 (word 1))) (TSeq (TInstr (TStore 8 3 2 (&64:int) 1)) (TSeq (TInstr (TCmp CondEq TyU64 1 3 (OpReg 5))) (TIf 1 (TSeq (TInstr (TMov TyU64 5 8)) (TInstr (TImm TyBool 9 (word 0)))) (TSeq (TInstr (TMov TyU64 1 6)) (TSeq (TInstr (TMov TyU64 2 3)) (TInstr (TImm TyBool 9 (word 1)))))))))))))))))))))))))))))))))))))))`;;

let bw_comb = new_definition
 `bw_comb = (TSeq (TInstr (TShift ShiftLeft TyU64 1 8 1)) (TSeq (TInstr (TLoadFrame TyPtr 4 0)) (TSeq (TInstr (TAddr 0 4 4 (SOME 1) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 6 4 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 5 4 (&8:int))) (TSeq (TInstr (TImm TyU64 1 (word 7))) (TSeq (TInstr (TBin BinAnd TyU64 1 6 1)) (TSeq (TInstr (TCmp CondEq TyU64 1 1 (OpImm (word 3)))) (TSeq (TIf 1 TSkip (TSeq (TInstr (TImm TyU64 6 (word 11))) (TReturn 2 6))) (TSeq (TInstr (TShift ShiftRightU TyU64 6 6 3)) (TSeq (TInstr (TLoad TyU64 8 3 3 2 (&16:int))) (TSeq (TInstr (TCmp CondUlt TyU64 1 3 (OpImm (word 2)))) (TSeq (TIf 1 (TSeq (TInstr (TImm TyU64 6 (word 12))) (TReturn 2 6)) TSkip) (TSeq (TInstr (TImm TyU64 1 (word 2))) (TSeq (TInstr (TBin BinSub TyU64 3 3 1)) (TSeq (TInstr (TStore 8 3 2 (&16:int) 3)) (TSeq (TInstr (TLoad TyU64 8 3 1 2 (&32:int))) (TSeq (TInstr (TBin BinAdd TyU64 1 1 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 1 1 2)) (TSeq (TInstr (TAddr 3 4 2 (SOME 1) 3 (&128:int))) (TSeq (TInstr (TLoad TyU64 8 3 1 4 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 1 1 (OpReg 6))) (TSeq (TInstr (TLoad TyU64 8 3 3 4 (&8:int))) (TSeq (TInstr (TCmp CondEq TyU64 3 3 (OpReg 7))) (TSeq (TInstr (TBin BinAnd TyBool 1 1 3)) (TSeq (TInstr (TLoad TyU64 8 3 3 4 (&32:int))) (TSeq (TInstr (TCmp CondEq TyU64 3 3 (OpReg 5))) (TSeq (TInstr (TBin BinAnd TyBool 1 1 3)) (TSeq (TInstr (TLoad TyU64 8 3 3 4 (&40:int))) (TSeq (TInstr (TCmp CondEq TyU64 3 3 (OpReg 7))) (TSeq (TInstr (TBin BinAnd TyBool 1 1 3)) (TSeq (TIf 1 TSkip (TSeq (TInstr (TImm TyU64 6 (word 13))) (TReturn 2 6))) (TSeq (TInstr (TLoad TyU64 8 3 1 4 (&16:int))) (TSeq (TInstr (TLoad TyU64 8 3 3 4 (&48:int))) (TSeq (TInstr (TImm TyU64 4 (word 1))) (TSeq (TInstr (TStore 8 3 2 (&64:int) 4)) (TSeq (TInstr (TCmp CondEq TyU64 4 1 (OpReg 6))) (TSeq (TInstr (TCmp CondEq TyU64 9 3 (OpReg 5))) (TSeq (TInstr (TBin BinAnd TyBool 4 4 9)) (TIf 4 (TSeq (TInstr (TMov TyU64 5 8)) (TInstr (TImm TyBool 9 (word 0)))) (TSeq (TInstr (TShift ShiftLeft TyU64 1 1 3)) (TSeq (TInstr (TImm TyU64 4 (word 3))) (TSeq (TInstr (TBin BinAdd TyU64 1 1 4)) (TSeq (TInstr (TMov TyU64 2 3)) (TInstr (TImm TyBool 9 (word 1)))))))))))))))))))))))))))))))))))))))))))))))`;;

let bw_visit = new_definition
 `bw_visit = (TSeq (TInstr (TLoad TyU64 8 3 1 2 (&32:int))) (TSeq (TInstr (TShift ShiftLeft TyU64 1 1 2)) (TSeq (TInstr (TImm TyU64 5 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 1 1 5)) (TSeq (TInstr (TImm TyU64 5 (word 11400714819323198485))) (TSeq (TInstr (TBin BinMulLo TyU64 6 7 5)) (TSeq (TInstr (TBin BinAdd TyU64 6 6 8)) (TSeq (TInstr (TBin BinMulLo TyU64 6 6 5)) (TSeq (TInstr (TShift ShiftRightU TyU64 6 6 32)) (TSeq (TInstr (TBin BinAnd TyU64 6 6 1)) (TSeq (TInstr (TLoad TyU64 8 3 1 2 (&32:int))) (TSeq (TInstr (TShift ShiftLeft TyU64 5 1 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 1 1 2)) (TSeq (TInstr (TBin BinAdd TyU64 1 1 5)) (TSeq (TInstr (TBin BinAdd TyU64 1 1 6)) (TSeq (TInstr (TAddr 3 1 2 (SOME 1) 3 (&128:int))) (TSeq (TInstr (TLoad TyU64 8 3 1 1 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 3 5 2 (&24:int))) (TSeq (TInstr (TCmp CondUlt TyU64 5 1 (OpReg 5))) (TSeq (TInstr (TImm TyBool 9 (word 0))) (TSeq (TIf 5 (TSeq (TInstr (TLoad TyU64 8 3 5 2 (&32:int))) (TSeq (TInstr (TShift ShiftLeft TyU64 5 5 1)) (TSeq (TInstr (TBin BinAdd TyU64 5 5 1)) (TSeq (TInstr (TShift ShiftLeft TyU64 5 5 2)) (TSeq (TInstr (TAddr 3 5 2 (SOME 5) 3 (&128:int))) (TSeq (TInstr (TLoad TyU64 8 3 6 5 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 6 6 (OpReg 8))) (TSeq (TInstr (TLoad TyU64 8 3 1 5 (&8:int))) (TSeq (TInstr (TCmp CondEq TyU64 1 1 (OpReg 7))) (TSeq (TInstr (TBin BinAnd TyBool 9 6 1)) (TInstr (TLoad TyU64 8 3 5 5 (&16:int))))))))))))) TSkip) (TIf 9 (TSeq (TInstr (TImm TyU64 6 (word 0))) (TSeq (TInstr (TStore 8 3 2 (&64:int) 6)) (TInstr (TImm TyBool 9 (word 0))))) bw_miss))))))))))))))))))))))`;;

let bw_probe = new_definition
 `bw_probe = (TSeq (TInstr (TBin BinAdd TyU64 3 6 7)) (TSeq (TInstr (TLoadFrame TyU64 4 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 4 4 3)) (TSeq (TInstr (TImm TyU64 5 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 4 4 5)) (TSeq (TInstr (TBin BinAnd TyU64 3 3 4)) (TSeq (TInstr (TLoadFrame TyPtr 4 2)) (TSeq (TInstr (TAddr 1 4 4 (SOME 3) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 1 5 4 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 3 5 (OpImm (word 0)))) (TIf 3 bw_append bw_occupied)))))))))))`;;

let bw_push = new_definition
 `bw_push = (TSeq (TInstr (TLoad TyU64 8 3 4 2 (&16:int))) (TSeq (TInstr (TLoad TyU64 8 3 6 2 (&32:int))) (TSeq (TInstr (TCmp CondUlt TyU64 7 4 (OpReg 6))) (TSeq (TIf 7 TSkip (TSeq (TInstr (TImm TyU64 6 (word 15))) (TReturn 2 6))) (TSeq (TInstr (TBin BinAdd TyU64 6 6 4)) (TSeq (TInstr (TShift ShiftLeft TyU64 6 6 2)) (TSeq (TInstr (TAddr 3 6 2 (SOME 6) 3 (&128:int))) (TSeq (TInstr (TLoad TyU64 8 3 7 2 (&48:int))) (TSeq (TInstr (TStore 8 3 6 (&0:int) 7)) (TSeq (TInstr (TLoad TyU64 8 3 8 2 (&56:int))) (TSeq (TInstr (TStore 8 3 6 (&8:int) 8)) (TSeq (TInstr (TStore 8 3 6 (&16:int) 5)) (TSeq (TInstr (TImm TyU64 6 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 4 4 6)) (TSeq (TInstr (TStore 8 3 2 (&16:int) 4)) (TSeq (TInstr (TCmp CondEq TyU64 4 3 (OpImm (word 1)))) (TIf 4 bw_memo TSkip)))))))))))))))))`;;

let bw_publish = new_definition
 `bw_publish = (TSeq (TInstr (TLoad TyU64 8 3 3 2 (&0:int))) (TSeq (TInstr (TLoadFrame TyPtr 4 4)) (TSeq (TInstr (TStore 8 2 4 (&0:int) 3)) (TReturn 1 5))))`;;

let bw_last = new_definition
 `bw_last = (TSeq (TInstr (TLoad TyU64 8 3 3 2 (&16:int))) (TSeq (TInstr (TCmp CondEq TyU64 4 3 (OpImm (word 0)))) (TSeq (TIf 4 (TSeq (TInstr (TImm TyU64 6 (word 5))) (TReturn 2 6)) TSkip) (TSeq (TInstr (TImm TyU64 4 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 3 3 4)) (TSeq (TInstr (TLoad TyU64 8 3 4 2 (&32:int))) (TSeq (TInstr (TBin BinAdd TyU64 4 4 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 4 4 2)) (TSeq (TInstr (TAddr 3 4 2 (SOME 4) 3 (&128:int))) (TSeq (TInstr (TLoad TyU64 8 3 5 4 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 3 6 2 (&40:int))) (TSeq (TInstr (TCmp CondEq TyU64 5 5 (OpReg 6))) (TSeq (TInstr (TLoad TyU64 8 3 6 4 (&8:int))) (TSeq (TInstr (TCmp CondEq TyU64 6 6 (OpImm (word 0)))) (TSeq (TInstr (TBin BinAnd TyBool 5 5 6)) (TSeq (TIf 5 TSkip (TSeq (TInstr (TImm TyU64 6 (word 6))) (TReturn 2 6))) (TSeq (TInstr (TLoad TyU64 8 3 2 4 (&16:int))) (TSeq (TInstr (TLoadFrame TyU64 1 23)) (TSeq (TInstr (TShift ShiftLeft TyU64 1 1 3)) (TSeq (TInstr (TImm TyU64 3 (word 4))) (TSeq (TInstr (TBin BinAdd TyU64 1 1 3)) (TSeq (TInstr (TLoadFrame TyPtr 3 6)) (TSeq (TInstr (TImm TyU64 4 (word 2))) (TSeq (TInstr (TStore 8 3 3 (&64:int) 4)) (TInstr (TImm TyBool 9 (word 1)))))))))))))))))))))))))))`;;

let bw_pop = new_definition
 `bw_pop = (TSeq (TInstr (TImm TyU64 4 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 3 3 4)) (TSeq (TInstr (TStore 8 3 2 (&8:int) 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 4 3 2)) (TSeq (TInstr (TAddr 3 4 2 (SOME 4) 3 (&128:int))) (TSeq (TInstr (TLoad TyU64 8 3 6 4 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 3 8 4 (&8:int))) (TSeq (TInstr (TLoad TyU64 8 3 7 4 (&16:int))) (TSeq (TInstr (TStore 8 3 2 (&48:int) 8)) (TSeq (TInstr (TStore 8 3 2 (&56:int) 7)) (TSeq (TInstr (TCmp CondEq TyU64 5 6 (OpImm (word 0)))) (TIf 5 bw_visit (TSeq (TInstr (TCmp CondEq TyU64 5 6 (OpImm (word 1)))) (TIf 5 bw_comb (TSeq (TInstr (TCmp CondEq TyU64 5 6 (OpImm (word 2)))) (TIf 5 bw_abs (TSeq (TInstr (TImm TyU64 6 (word 7))) (TReturn 2 6))))))))))))))))))`;;

let bw_intern = new_definition
 `bw_intern = (TSeq (TInstr (TBin BinXor TyU64 6 1 2)) (TSeq (TInstr (TImm TyU64 3 (word 11400714819323198485))) (TSeq (TInstr (TBin BinMulLo TyU64 6 6 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 3 6 29)) (TSeq (TInstr (TBin BinXor TyU64 6 6 3)) (TSeq (TInstr (TLoadFrame TyU64 8 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 8 8 3)) (TSeq (TInstr (TImm TyBool 9 (word 1))) (TSeq (TInstr (TImm TyU64 5 (word 0))) (TSeq (TEarlyLoop 7 8 9 4294967295 bw_probe) (TIf 9 (TSeq (TInstr (TImm TyU64 3 (word 14))) (TReturn 2 3)) TSkip)))))))))))`;;

let bw_post = new_definition
 `bw_post = (TSeq (TInstr (TLoadFrame TyPtr 2 6)) (TSeq (TInstr (TLoad TyU64 8 3 3 2 (&64:int))) (TSeq (TInstr (TCmp CondEq TyU64 4 3 (OpImm (word 2)))) (TIf 4 bw_publish (TSeq (TInstr (TCmp CondUlt TyU64 4 3 (OpImm (word 2)))) (TIf 4 bw_push TSkip))))))`;;

let bw_step = new_definition
 `bw_step = (TSeq (TInstr (TLoadFrame TyPtr 2 6)) (TSeq (TInstr (TLoad TyU64 8 3 3 2 (&8:int))) (TSeq (TInstr (TCmp CondEq TyU64 4 3 (OpImm (word 0)))) (TIf 4 bw_last bw_pop))))`;;

let bw_tail = new_definition
 `bw_tail = (TSeq (TIf 9 bw_intern TSkip) bw_post)`;;

let bw_body = new_definition
 `bw_body = (TSeq bw_step bw_tail)`;;

let bw_prologue = new_definition
 `bw_prologue = (TSeq (TInstr (TLoadFrame TyPtr 2 4)) (TSeq (TInstr (TLoad TyU64 8 2 3 2 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 4 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 4 4 4)) (TSeq (TInstr (TCmp CondUlt TyU64 5 4 (OpReg 3))) (TSeq (TIf 5 (TSeq (TInstr (TImm TyU64 6 (word 1))) (TReturn 2 6)) TSkip) (TSeq (TInstr (TCmp CondUlt TyU64 5 1 (OpReg 3))) (TSeq (TIf 5 TSkip (TSeq (TInstr (TImm TyU64 6 (word 2))) (TReturn 2 6))) (TSeq (TInstr (TLoadFrame TyU64 4 22)) (TSeq (TInstr (TCmp CondUlt TyU64 5 4 (OpImm (word 1152921504606846976)))) (TSeq (TInstr (TLoadFrame TyU64 4 23)) (TSeq (TInstr (TCmp CondUlt TyU64 6 4 (OpImm (word 1152921504606846976)))) (TSeq (TInstr (TBin BinAnd TyBool 5 5 6)) (TSeq (TIf 5 TSkip (TSeq (TInstr (TImm TyU64 6 (word 3))) (TReturn 2 6))) (TSeq (TInstr (TLoadFrame TyPtr 2 6)) (TSeq (TInstr (TStore 8 3 2 (&0:int) 3)) (TSeq (TInstr (TLoadFrame TyU64 4 7)) (TSeq (TInstr (TShift ShiftRightU TyU64 4 4 7)) (TSeq (TInstr (TImm TyU64 5 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 4 4 5)) (TSeq (TInstr (TStore 8 3 2 (&32:int) 4)) (TSeq (TInstr (TStore 8 3 2 (&40:int) 1)) (TSeq (TInstr (TImm TyU64 6 (word 0))) (TSeq (TInstr (TStore 8 3 2 (&128:int) 6)) (TSeq (TInstr (TStore 8 3 2 (&136:int) 1)) (TSeq (TInstr (TStore 8 3 2 (&144:int) 6)) (TSeq (TInstr (TStore 8 3 2 (&8:int) 5)) (TSeq (TInstr (TStore 8 3 2 (&16:int) 6)) (TSeq (TInstr (TStore 8 3 2 (&24:int) 6)) (TInstr (TImm TyU64 11 (word 4294967295))))))))))))))))))))))))))))))))`;;

let bind_walk = new_definition
 `bind_walk = TProg [(2,16,8); (2,8,8); (2,8,8); (2,256,8)] [(1,TyU64,0)] (TSeq bw_prologue (TSeq (TCountLoop 10 11 4294967295 bw_body) (TSeq (TInstr (TImm TyU64 6 (word 4))) (TReturn 2 6))))`;;

let BIND_WALK_TERM = prove
 (`bind_walk = (TProg [(2,16,8); (2,8,8); (2,8,8); (2,256,8)] [(1,TyU64,0)] (TSeq (TSeq (TInstr (TLoadFrame TyPtr 2 4)) (TSeq (TInstr (TLoad TyU64 8 2 3 2 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 4 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 4 4 4)) (TSeq (TInstr (TCmp CondUlt TyU64 5 4 (OpReg 3))) (TSeq (TIf 5 (TSeq (TInstr (TImm TyU64 6 (word 1))) (TReturn 2 6)) TSkip) (TSeq (TInstr (TCmp CondUlt TyU64 5 1 (OpReg 3))) (TSeq (TIf 5 TSkip (TSeq (TInstr (TImm TyU64 6 (word 2))) (TReturn 2 6))) (TSeq (TInstr (TLoadFrame TyU64 4 22)) (TSeq (TInstr (TCmp CondUlt TyU64 5 4 (OpImm (word 1152921504606846976)))) (TSeq (TInstr (TLoadFrame TyU64 4 23)) (TSeq (TInstr (TCmp CondUlt TyU64 6 4 (OpImm (word 1152921504606846976)))) (TSeq (TInstr (TBin BinAnd TyBool 5 5 6)) (TSeq (TIf 5 TSkip (TSeq (TInstr (TImm TyU64 6 (word 3))) (TReturn 2 6))) (TSeq (TInstr (TLoadFrame TyPtr 2 6)) (TSeq (TInstr (TStore 8 3 2 (&0:int) 3)) (TSeq (TInstr (TLoadFrame TyU64 4 7)) (TSeq (TInstr (TShift ShiftRightU TyU64 4 4 7)) (TSeq (TInstr (TImm TyU64 5 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 4 4 5)) (TSeq (TInstr (TStore 8 3 2 (&32:int) 4)) (TSeq (TInstr (TStore 8 3 2 (&40:int) 1)) (TSeq (TInstr (TImm TyU64 6 (word 0))) (TSeq (TInstr (TStore 8 3 2 (&128:int) 6)) (TSeq (TInstr (TStore 8 3 2 (&136:int) 1)) (TSeq (TInstr (TStore 8 3 2 (&144:int) 6)) (TSeq (TInstr (TStore 8 3 2 (&8:int) 5)) (TSeq (TInstr (TStore 8 3 2 (&16:int) 6)) (TSeq (TInstr (TStore 8 3 2 (&24:int) 6)) (TInstr (TImm TyU64 11 (word 4294967295)))))))))))))))))))))))))))))))) (TSeq (TCountLoop 10 11 4294967295 (TSeq (TSeq (TInstr (TLoadFrame TyPtr 2 6)) (TSeq (TInstr (TLoad TyU64 8 3 3 2 (&8:int))) (TSeq (TInstr (TCmp CondEq TyU64 4 3 (OpImm (word 0)))) (TIf 4 (TSeq (TInstr (TLoad TyU64 8 3 3 2 (&16:int))) (TSeq (TInstr (TCmp CondEq TyU64 4 3 (OpImm (word 0)))) (TSeq (TIf 4 (TSeq (TInstr (TImm TyU64 6 (word 5))) (TReturn 2 6)) TSkip) (TSeq (TInstr (TImm TyU64 4 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 3 3 4)) (TSeq (TInstr (TLoad TyU64 8 3 4 2 (&32:int))) (TSeq (TInstr (TBin BinAdd TyU64 4 4 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 4 4 2)) (TSeq (TInstr (TAddr 3 4 2 (SOME 4) 3 (&128:int))) (TSeq (TInstr (TLoad TyU64 8 3 5 4 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 3 6 2 (&40:int))) (TSeq (TInstr (TCmp CondEq TyU64 5 5 (OpReg 6))) (TSeq (TInstr (TLoad TyU64 8 3 6 4 (&8:int))) (TSeq (TInstr (TCmp CondEq TyU64 6 6 (OpImm (word 0)))) (TSeq (TInstr (TBin BinAnd TyBool 5 5 6)) (TSeq (TIf 5 TSkip (TSeq (TInstr (TImm TyU64 6 (word 6))) (TReturn 2 6))) (TSeq (TInstr (TLoad TyU64 8 3 2 4 (&16:int))) (TSeq (TInstr (TLoadFrame TyU64 1 23)) (TSeq (TInstr (TShift ShiftLeft TyU64 1 1 3)) (TSeq (TInstr (TImm TyU64 3 (word 4))) (TSeq (TInstr (TBin BinAdd TyU64 1 1 3)) (TSeq (TInstr (TLoadFrame TyPtr 3 6)) (TSeq (TInstr (TImm TyU64 4 (word 2))) (TSeq (TInstr (TStore 8 3 3 (&64:int) 4)) (TInstr (TImm TyBool 9 (word 1))))))))))))))))))))))))))) (TSeq (TInstr (TImm TyU64 4 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 3 3 4)) (TSeq (TInstr (TStore 8 3 2 (&8:int) 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 4 3 2)) (TSeq (TInstr (TAddr 3 4 2 (SOME 4) 3 (&128:int))) (TSeq (TInstr (TLoad TyU64 8 3 6 4 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 3 8 4 (&8:int))) (TSeq (TInstr (TLoad TyU64 8 3 7 4 (&16:int))) (TSeq (TInstr (TStore 8 3 2 (&48:int) 8)) (TSeq (TInstr (TStore 8 3 2 (&56:int) 7)) (TSeq (TInstr (TCmp CondEq TyU64 5 6 (OpImm (word 0)))) (TIf 5 (TSeq (TInstr (TLoad TyU64 8 3 1 2 (&32:int))) (TSeq (TInstr (TShift ShiftLeft TyU64 1 1 2)) (TSeq (TInstr (TImm TyU64 5 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 1 1 5)) (TSeq (TInstr (TImm TyU64 5 (word 11400714819323198485))) (TSeq (TInstr (TBin BinMulLo TyU64 6 7 5)) (TSeq (TInstr (TBin BinAdd TyU64 6 6 8)) (TSeq (TInstr (TBin BinMulLo TyU64 6 6 5)) (TSeq (TInstr (TShift ShiftRightU TyU64 6 6 32)) (TSeq (TInstr (TBin BinAnd TyU64 6 6 1)) (TSeq (TInstr (TLoad TyU64 8 3 1 2 (&32:int))) (TSeq (TInstr (TShift ShiftLeft TyU64 5 1 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 1 1 2)) (TSeq (TInstr (TBin BinAdd TyU64 1 1 5)) (TSeq (TInstr (TBin BinAdd TyU64 1 1 6)) (TSeq (TInstr (TAddr 3 1 2 (SOME 1) 3 (&128:int))) (TSeq (TInstr (TLoad TyU64 8 3 1 1 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 3 5 2 (&24:int))) (TSeq (TInstr (TCmp CondUlt TyU64 5 1 (OpReg 5))) (TSeq (TInstr (TImm TyBool 9 (word 0))) (TSeq (TIf 5 (TSeq (TInstr (TLoad TyU64 8 3 5 2 (&32:int))) (TSeq (TInstr (TShift ShiftLeft TyU64 5 5 1)) (TSeq (TInstr (TBin BinAdd TyU64 5 5 1)) (TSeq (TInstr (TShift ShiftLeft TyU64 5 5 2)) (TSeq (TInstr (TAddr 3 5 2 (SOME 5) 3 (&128:int))) (TSeq (TInstr (TLoad TyU64 8 3 6 5 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 6 6 (OpReg 8))) (TSeq (TInstr (TLoad TyU64 8 3 1 5 (&8:int))) (TSeq (TInstr (TCmp CondEq TyU64 1 1 (OpReg 7))) (TSeq (TInstr (TBin BinAnd TyBool 9 6 1)) (TInstr (TLoad TyU64 8 3 5 5 (&16:int))))))))))))) TSkip) (TIf 9 (TSeq (TInstr (TImm TyU64 6 (word 0))) (TSeq (TInstr (TStore 8 3 2 (&64:int) 6)) (TInstr (TImm TyBool 9 (word 0))))) (TSeq (TInstr (TShift ShiftLeft TyU64 1 8 1)) (TSeq (TInstr (TLoadFrame TyPtr 5 0)) (TSeq (TInstr (TAddr 0 5 5 (SOME 1) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 6 5 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 5 5 (&8:int))) (TSeq (TInstr (TLoadFrame TyU64 1 22)) (TSeq (TInstr (TShift ShiftLeft TyU64 1 1 3)) (TSeq (TInstr (TCmp CondEq TyU64 1 6 (OpReg 1))) (TSeq (TInstr (TLoadFrame TyU64 9 23)) (TSeq (TInstr (TCmp CondEq TyU64 9 5 (OpReg 9))) (TSeq (TInstr (TBin BinAnd TyBool 1 1 9)) (TIf 1 (TSeq (TInstr (TCmp CondUlt TyU64 1 7 (OpImm (word 1152921504606846976)))) (TSeq (TIf 1 TSkip (TSeq (TInstr (TImm TyU64 6 (word 8))) (TReturn 2 6))) (TSeq (TInstr (TShift ShiftLeft TyU64 1 7 3)) (TSeq (TInstr (TImm TyU64 6 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 1 1 6)) (TSeq (TInstr (TImm TyU64 2 (word 0))) (TSeq (TInstr (TLoadFrame TyPtr 6 6)) (TSeq (TInstr (TImm TyU64 4 (word 0))) (TSeq (TInstr (TStore 8 3 6 (&64:int) 4)) (TInstr (TImm TyBool 9 (word 1)))))))))))) (TSeq (TInstr (TImm TyU64 1 (word 7))) (TSeq (TInstr (TBin BinAnd TyU64 1 6 1)) (TSeq (TInstr (TCmp CondUlt TyU64 9 1 (OpImm (word 3)))) (TIf 9 (TSeq (TInstr (TMov TyU64 5 8)) (TSeq (TInstr (TImm TyU64 4 (word 0))) (TSeq (TInstr (TStore 8 3 2 (&64:int) 4)) (TInstr (TImm TyBool 9 (word 0)))))) (TSeq (TInstr (TCmp CondEq TyU64 9 1 (OpImm (word 3)))) (TIf 9 (TSeq (TInstr (TLoad TyU64 8 3 1 2 (&32:int))) (TSeq (TInstr (TImm TyU64 4 (word 3))) (TSeq (TInstr (TBin BinAdd TyU64 4 3 4)) (TSeq (TInstr (TCmp CondUlt TyU64 1 1 (OpReg 4))) (TSeq (TIf 1 (TSeq (TInstr (TImm TyU64 6 (word 10))) (TReturn 2 6)) TSkip) (TSeq (TInstr (TShift ShiftRightU TyU64 6 6 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 4 3 2)) (TSeq (TInstr (TAddr 3 4 2 (SOME 4) 3 (&128:int))) (TSeq (TInstr (TImm TyU64 1 (word 1))) (TSeq (TInstr (TStore 8 3 4 (&0:int) 1)) (TSeq (TInstr (TImm TyU64 1 (word 0))) (TSeq (TInstr (TStore 8 3 4 (&32:int) 1)) (TSeq (TInstr (TStore 8 3 4 (&40:int) 5)) (TSeq (TInstr (TStore 8 3 4 (&48:int) 7)) (TSeq (TInstr (TStore 8 3 4 (&64:int) 1)) (TSeq (TInstr (TStore 8 3 4 (&72:int) 6)) (TSeq (TInstr (TStore 8 3 4 (&80:int) 7)) (TSeq (TInstr (TImm TyU64 1 (word 3))) (TSeq (TInstr (TBin BinAdd TyU64 1 3 1)) (TSeq (TInstr (TStore 8 3 2 (&8:int) 1)) (TSeq (TInstr (TImm TyU64 1 (word 3))) (TSeq (TInstr (TStore 8 3 2 (&64:int) 1)) (TInstr (TImm TyBool 9 (word 0))))))))))))))))))))))))) (TSeq (TInstr (TCmp CondEq TyU64 9 1 (OpImm (word 4)))) (TIf 9 (TSeq (TInstr (TLoad TyU64 8 3 1 2 (&32:int))) (TSeq (TInstr (TImm TyU64 4 (word 2))) (TSeq (TInstr (TBin BinAdd TyU64 4 3 4)) (TSeq (TInstr (TCmp CondUlt TyU64 1 1 (OpReg 4))) (TSeq (TIf 1 (TSeq (TInstr (TImm TyU64 6 (word 10))) (TReturn 2 6)) TSkip) (TSeq (TInstr (TShift ShiftLeft TyU64 4 3 2)) (TSeq (TInstr (TAddr 3 4 2 (SOME 4) 3 (&128:int))) (TSeq (TInstr (TImm TyU64 1 (word 2))) (TSeq (TInstr (TStore 8 3 4 (&0:int) 1)) (TSeq (TInstr (TImm TyU64 1 (word 0))) (TSeq (TInstr (TStore 8 3 4 (&32:int) 1)) (TSeq (TInstr (TStore 8 3 4 (&40:int) 5)) (TSeq (TInstr (TImm TyU64 1 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 1 7 1)) (TSeq (TInstr (TStore 8 3 4 (&48:int) 1)) (TSeq (TInstr (TImm TyU64 1 (word 2))) (TSeq (TInstr (TBin BinAdd TyU64 1 3 1)) (TSeq (TInstr (TStore 8 3 2 (&8:int) 1)) (TSeq (TInstr (TImm TyU64 1 (word 3))) (TSeq (TInstr (TStore 8 3 2 (&64:int) 1)) (TInstr (TImm TyBool 9 (word 0))))))))))))))))))))))) (TSeq (TInstr (TImm TyU64 6 (word 9))) (TReturn 2 6)))))))))))))))))))))))))))))))))))))))))))) (TSeq (TInstr (TCmp CondEq TyU64 5 6 (OpImm (word 1)))) (TIf 5 (TSeq (TInstr (TShift ShiftLeft TyU64 1 8 1)) (TSeq (TInstr (TLoadFrame TyPtr 4 0)) (TSeq (TInstr (TAddr 0 4 4 (SOME 1) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 6 4 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 5 4 (&8:int))) (TSeq (TInstr (TImm TyU64 1 (word 7))) (TSeq (TInstr (TBin BinAnd TyU64 1 6 1)) (TSeq (TInstr (TCmp CondEq TyU64 1 1 (OpImm (word 3)))) (TSeq (TIf 1 TSkip (TSeq (TInstr (TImm TyU64 6 (word 11))) (TReturn 2 6))) (TSeq (TInstr (TShift ShiftRightU TyU64 6 6 3)) (TSeq (TInstr (TLoad TyU64 8 3 3 2 (&16:int))) (TSeq (TInstr (TCmp CondUlt TyU64 1 3 (OpImm (word 2)))) (TSeq (TIf 1 (TSeq (TInstr (TImm TyU64 6 (word 12))) (TReturn 2 6)) TSkip) (TSeq (TInstr (TImm TyU64 1 (word 2))) (TSeq (TInstr (TBin BinSub TyU64 3 3 1)) (TSeq (TInstr (TStore 8 3 2 (&16:int) 3)) (TSeq (TInstr (TLoad TyU64 8 3 1 2 (&32:int))) (TSeq (TInstr (TBin BinAdd TyU64 1 1 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 1 1 2)) (TSeq (TInstr (TAddr 3 4 2 (SOME 1) 3 (&128:int))) (TSeq (TInstr (TLoad TyU64 8 3 1 4 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 1 1 (OpReg 6))) (TSeq (TInstr (TLoad TyU64 8 3 3 4 (&8:int))) (TSeq (TInstr (TCmp CondEq TyU64 3 3 (OpReg 7))) (TSeq (TInstr (TBin BinAnd TyBool 1 1 3)) (TSeq (TInstr (TLoad TyU64 8 3 3 4 (&32:int))) (TSeq (TInstr (TCmp CondEq TyU64 3 3 (OpReg 5))) (TSeq (TInstr (TBin BinAnd TyBool 1 1 3)) (TSeq (TInstr (TLoad TyU64 8 3 3 4 (&40:int))) (TSeq (TInstr (TCmp CondEq TyU64 3 3 (OpReg 7))) (TSeq (TInstr (TBin BinAnd TyBool 1 1 3)) (TSeq (TIf 1 TSkip (TSeq (TInstr (TImm TyU64 6 (word 13))) (TReturn 2 6))) (TSeq (TInstr (TLoad TyU64 8 3 1 4 (&16:int))) (TSeq (TInstr (TLoad TyU64 8 3 3 4 (&48:int))) (TSeq (TInstr (TImm TyU64 4 (word 1))) (TSeq (TInstr (TStore 8 3 2 (&64:int) 4)) (TSeq (TInstr (TCmp CondEq TyU64 4 1 (OpReg 6))) (TSeq (TInstr (TCmp CondEq TyU64 9 3 (OpReg 5))) (TSeq (TInstr (TBin BinAnd TyBool 4 4 9)) (TIf 4 (TSeq (TInstr (TMov TyU64 5 8)) (TInstr (TImm TyBool 9 (word 0)))) (TSeq (TInstr (TShift ShiftLeft TyU64 1 1 3)) (TSeq (TInstr (TImm TyU64 4 (word 3))) (TSeq (TInstr (TBin BinAdd TyU64 1 1 4)) (TSeq (TInstr (TMov TyU64 2 3)) (TInstr (TImm TyBool 9 (word 1))))))))))))))))))))))))))))))))))))))))))))))) (TSeq (TInstr (TCmp CondEq TyU64 5 6 (OpImm (word 2)))) (TIf 5 (TSeq (TInstr (TShift ShiftLeft TyU64 1 8 1)) (TSeq (TInstr (TLoadFrame TyPtr 4 0)) (TSeq (TInstr (TAddr 0 4 4 (SOME 1) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 6 4 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 5 4 (&8:int))) (TSeq (TInstr (TImm TyU64 1 (word 7))) (TSeq (TInstr (TBin BinAnd TyU64 1 6 1)) (TSeq (TInstr (TCmp CondEq TyU64 1 1 (OpImm (word 4)))) (TSeq (TIf 1 TSkip (TSeq (TInstr (TImm TyU64 6 (word 11))) (TReturn 2 6))) (TSeq (TInstr (TCmp CondUlt TyU64 1 7 (OpImm (word 1152921504606846976)))) (TSeq (TIf 1 TSkip (TSeq (TInstr (TImm TyU64 6 (word 8))) (TReturn 2 6))) (TSeq (TInstr (TLoad TyU64 8 3 3 2 (&16:int))) (TSeq (TInstr (TCmp CondEq TyU64 1 3 (OpImm (word 0)))) (TSeq (TIf 1 (TSeq (TInstr (TImm TyU64 6 (word 12))) (TReturn 2 6)) TSkip) (TSeq (TInstr (TImm TyU64 1 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 3 3 1)) (TSeq (TInstr (TStore 8 3 2 (&16:int) 3)) (TSeq (TInstr (TLoad TyU64 8 3 1 2 (&32:int))) (TSeq (TInstr (TBin BinAdd TyU64 1 1 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 1 1 2)) (TSeq (TInstr (TAddr 3 4 2 (SOME 1) 3 (&128:int))) (TSeq (TInstr (TLoad TyU64 8 3 1 4 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 1 1 (OpReg 5))) (TSeq (TInstr (TLoad TyU64 8 3 3 4 (&8:int))) (TSeq (TInstr (TImm TyU64 9 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 9 7 9)) (TSeq (TInstr (TCmp CondEq TyU64 3 3 (OpReg 9))) (TSeq (TInstr (TBin BinAnd TyBool 1 1 3)) (TSeq (TIf 1 TSkip (TSeq (TInstr (TImm TyU64 6 (word 13))) (TReturn 2 6))) (TSeq (TInstr (TLoad TyU64 8 3 3 4 (&16:int))) (TSeq (TInstr (TImm TyU64 1 (word 1))) (TSeq (TInstr (TStore 8 3 2 (&64:int) 1)) (TSeq (TInstr (TCmp CondEq TyU64 1 3 (OpReg 5))) (TIf 1 (TSeq (TInstr (TMov TyU64 5 8)) (TInstr (TImm TyBool 9 (word 0)))) (TSeq (TInstr (TMov TyU64 1 6)) (TSeq (TInstr (TMov TyU64 2 3)) (TInstr (TImm TyBool 9 (word 1))))))))))))))))))))))))))))))))))))))) (TSeq (TInstr (TImm TyU64 6 (word 7))) (TReturn 2 6)))))))))))))))))))))) (TSeq (TIf 9 (TSeq (TInstr (TBin BinXor TyU64 6 1 2)) (TSeq (TInstr (TImm TyU64 3 (word 11400714819323198485))) (TSeq (TInstr (TBin BinMulLo TyU64 6 6 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 3 6 29)) (TSeq (TInstr (TBin BinXor TyU64 6 6 3)) (TSeq (TInstr (TLoadFrame TyU64 8 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 8 8 3)) (TSeq (TInstr (TImm TyBool 9 (word 1))) (TSeq (TInstr (TImm TyU64 5 (word 0))) (TSeq (TEarlyLoop 7 8 9 4294967295 (TSeq (TInstr (TBin BinAdd TyU64 3 6 7)) (TSeq (TInstr (TLoadFrame TyU64 4 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 4 4 3)) (TSeq (TInstr (TImm TyU64 5 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 4 4 5)) (TSeq (TInstr (TBin BinAnd TyU64 3 3 4)) (TSeq (TInstr (TLoadFrame TyPtr 4 2)) (TSeq (TInstr (TAddr 1 4 4 (SOME 3) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 1 5 4 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 3 5 (OpImm (word 0)))) (TIf 3 (TSeq (TInstr (TLoadFrame TyPtr 3 6)) (TSeq (TInstr (TLoad TyU64 8 3 5 3 (&0:int))) (TSeq (TInstr (TLoadFrame TyU64 3 1)) (TSeq (TInstr (TShift ShiftRightU TyU64 3 3 4)) (TSeq (TInstr (TCmp CondUlt TyU64 3 5 (OpReg 3))) (TIf 3 (TSeq (TInstr (TShift ShiftLeft TyU64 3 5 1)) (TSeq (TInstr (TLoadFrame TyPtr 6 0)) (TSeq (TInstr (TAddr 0 6 6 (SOME 3) 3 (&0:int))) (TSeq (TInstr (TStore 8 0 6 (&0:int) 1)) (TSeq (TInstr (TStore 8 0 6 (&8:int) 2)) (TSeq (TInstr (TImm TyU64 3 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 3 5 3)) (TSeq (TInstr (TStore 8 1 4 (&0:int) 3)) (TSeq (TInstr (TLoadFrame TyPtr 6 6)) (TSeq (TInstr (TStore 8 3 6 (&0:int) 3)) (TInstr (TImm TyBool 9 (word 0))))))))))))) (TSeq (TInstr (TImm TyU64 3 (word 16))) (TReturn 2 3)))))))) (TSeq (TInstr (TImm TyU64 3 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 5 5 3)) (TSeq (TInstr (TLoadFrame TyPtr 3 6)) (TSeq (TInstr (TLoad TyU64 8 3 3 3 (&0:int))) (TSeq (TInstr (TCmp CondUlt TyU64 3 5 (OpReg 3))) (TIf 3 (TSeq (TInstr (TShift ShiftLeft TyU64 3 5 1)) (TSeq (TInstr (TLoadFrame TyPtr 4 0)) (TSeq (TInstr (TAddr 0 4 4 (SOME 3) 3 (&0:int))) (TSeq (TInstr (TLoad TyU64 8 0 3 4 (&0:int))) (TSeq (TInstr (TCmp CondEq TyU64 3 3 (OpReg 1))) (TIf 3 (TSeq (TInstr (TLoad TyU64 8 0 3 4 (&8:int))) (TSeq (TInstr (TCmp CondEq TyU64 3 3 (OpReg 2))) (TIf 3 (TInstr (TImm TyBool 9 (word 0))) TSkip))) TSkip)))))) TSkip)))))))))))))))))) (TIf 9 (TSeq (TInstr (TImm TyU64 3 (word 14))) (TReturn 2 3)) TSkip))))))))))) TSkip) (TSeq (TInstr (TLoadFrame TyPtr 2 6)) (TSeq (TInstr (TLoad TyU64 8 3 3 2 (&64:int))) (TSeq (TInstr (TCmp CondEq TyU64 4 3 (OpImm (word 2)))) (TIf 4 (TSeq (TInstr (TLoad TyU64 8 3 3 2 (&0:int))) (TSeq (TInstr (TLoadFrame TyPtr 4 4)) (TSeq (TInstr (TStore 8 2 4 (&0:int) 3)) (TReturn 1 5)))) (TSeq (TInstr (TCmp CondUlt TyU64 4 3 (OpImm (word 2)))) (TIf 4 (TSeq (TInstr (TLoad TyU64 8 3 4 2 (&16:int))) (TSeq (TInstr (TLoad TyU64 8 3 6 2 (&32:int))) (TSeq (TInstr (TCmp CondUlt TyU64 7 4 (OpReg 6))) (TSeq (TIf 7 TSkip (TSeq (TInstr (TImm TyU64 6 (word 15))) (TReturn 2 6))) (TSeq (TInstr (TBin BinAdd TyU64 6 6 4)) (TSeq (TInstr (TShift ShiftLeft TyU64 6 6 2)) (TSeq (TInstr (TAddr 3 6 2 (SOME 6) 3 (&128:int))) (TSeq (TInstr (TLoad TyU64 8 3 7 2 (&48:int))) (TSeq (TInstr (TStore 8 3 6 (&0:int) 7)) (TSeq (TInstr (TLoad TyU64 8 3 8 2 (&56:int))) (TSeq (TInstr (TStore 8 3 6 (&8:int) 8)) (TSeq (TInstr (TStore 8 3 6 (&16:int) 5)) (TSeq (TInstr (TImm TyU64 6 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 4 4 6)) (TSeq (TInstr (TStore 8 3 2 (&16:int) 4)) (TSeq (TInstr (TCmp CondEq TyU64 4 3 (OpImm (word 1)))) (TIf 4 (TSeq (TInstr (TLoad TyU64 8 3 4 2 (&24:int))) (TSeq (TInstr (TLoad TyU64 8 3 6 2 (&32:int))) (TSeq (TInstr (TCmp CondUlt TyU64 3 4 (OpReg 6))) (TIf 3 (TSeq (TInstr (TShift ShiftLeft TyU64 3 6 1)) (TSeq (TInstr (TBin BinAdd TyU64 3 3 4)) (TSeq (TInstr (TShift ShiftLeft TyU64 3 3 2)) (TSeq (TInstr (TAddr 3 3 2 (SOME 3) 3 (&128:int))) (TSeq (TInstr (TStore 8 3 3 (&0:int) 7)) (TSeq (TInstr (TStore 8 3 3 (&8:int) 8)) (TSeq (TInstr (TStore 8 3 3 (&16:int) 5)) (TSeq (TInstr (TShift ShiftLeft TyU64 1 6 2)) (TSeq (TInstr (TImm TyU64 3 (word 1))) (TSeq (TInstr (TBin BinSub TyU64 1 1 3)) (TSeq (TInstr (TImm TyU64 3 (word 11400714819323198485))) (TSeq (TInstr (TBin BinMulLo TyU64 9 8 3)) (TSeq (TInstr (TBin BinAdd TyU64 9 9 7)) (TSeq (TInstr (TBin BinMulLo TyU64 9 9 3)) (TSeq (TInstr (TShift ShiftRightU TyU64 9 9 32)) (TSeq (TInstr (TBin BinAnd TyU64 9 9 1)) (TSeq (TInstr (TShift ShiftLeft TyU64 3 6 3)) (TSeq (TInstr (TShift ShiftLeft TyU64 1 6 2)) (TSeq (TInstr (TBin BinAdd TyU64 1 1 3)) (TSeq (TInstr (TBin BinAdd TyU64 1 1 9)) (TSeq (TInstr (TAddr 3 1 2 (SOME 1) 3 (&128:int))) (TSeq (TInstr (TStore 8 3 1 (&0:int) 4)) (TSeq (TInstr (TImm TyU64 3 (word 1))) (TSeq (TInstr (TBin BinAdd TyU64 4 4 3)) (TInstr (TStore 8 3 2 (&24:int) 4)))))))))))))))))))))))))) TSkip)))) TSkip))))))))))))))))) TSkip))))))))) (TSeq (TInstr (TImm TyU64 6 (word 4))) (TReturn 2 6)))))`,
  REWRITE_TAC[bind_walk; bw_prologue; bw_body; bw_step; bw_last; bw_pop; bw_visit; bw_miss; bw_bound; bw_tags; bw_leaf; bw_comb_expand; bw_abs_expand; bw_comb; bw_abs; bw_tail; bw_intern; bw_probe; bw_append; bw_occupied; bw_post; bw_publish; bw_push; bw_memo]);;

(* ------------------------------------------------------------------------- *)
(* The walk's view of a state: work words, rows as triples, entries.         *)
(* ------------------------------------------------------------------------- *)

(* Work word k: region 3's base plus 8k. *)
let bw_w = new_definition
 `bw_w st k = tisa_read st (word_add (tisa_base st 3) (word (8 * k))) 8`;;

(* Field f of entry e of area a (0 tasks, 1 results, 2 memo log); K is work  *)
(* word 4.                                                                    *)
let bw_ent = new_definition
 `bw_ent st a e f = bw_w st (16 + 4 * (a * val(bw_w st 4) + e) + f)`;;

(* Row j as a triple (tag, a, b): k0 = tag + 8a, k1 = b. *)
let bw_row = new_definition
 `bw_row st j = (val(intern_word st (2 * j)) MOD 8, val(intern_word st (2 * j)) DIV 8,
                 val(intern_word st (2 * j + 1)))`;;

let bw_rows = new_definition
 `bw_rows st c = list_of_seq (bw_row st) c`;;

let LENGTH_BW_ROWS = prove
 (`!st c. LENGTH(bw_rows st c) = c`,
  REWRITE_TAC[bw_rows; LENGTH_LIST_OF_SEQ]);;

let EL_BW_ROWS = prove
 (`!st c i. i < c ==> EL i (bw_rows st c) = bw_row st i`,
  SIMP_TAC[bw_rows; EL_LIST_OF_SEQ]);;

let BW_ROWS_EXT = prove
 (`!s s' c c'. c <= c' /\ (!i. i < 2 * c ==> intern_word s' i = intern_word s i)
               ==> bw_ext (bw_rows s c) (bw_rows s' c')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bw_ext; LENGTH_BW_ROWS] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i < c':num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_BW_ROWS; bw_row] THEN
  SUBGOAL_THEN `2 * i < 2 * c /\ 2 * i + 1 < 2 * c` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The table with an explicit count (intern16_complete.ml's intern_ok is it  *)
(* at the published count).                                                  *)
(* ------------------------------------------------------------------------- *)

let bw_complete = new_definition
 `bw_complete st c <=>
    !i. i < c
        ==> ?d. d < val(intern_slots st) /\
                intern_slot st (intern_pos st (intern_hash (intern_word st (2 * i))
                                                           (intern_word st (2 * i + 1))) d) =
                word(i + 1) /\
                !e. e < d
                    ==> ~(intern_slot st (intern_pos st (intern_hash (intern_word st (2 * i))
                                                                     (intern_word st (2 * i + 1))) e) =
                          word 0)`;;

let bw_distinct = new_definition
 `bw_distinct st c <=>
    !i j. i < c /\ j < c /\ intern_has st i (intern_word st (2 * j)) (intern_word st (2 * j + 1))
          ==> i = j`;;

let bw_iok = new_definition
 `bw_iok st c <=> c <= val(tisa_len st 0) DIV 16 /\ bw_complete st c /\ bw_distinct st c`;;

let INTERN_OK_BW = prove
 (`!st. intern_ok st <=> bw_iok st (val(intern_count st))`,
  REWRITE_TAC[intern_ok; bw_iok; intern_complete; bw_complete; intern_distinct; bw_distinct]);;

let BW_IOK_DOWN = prove
 (`!st c c'. bw_iok st c /\ c' <= c ==> bw_iok st c'`,
  REWRITE_TAC[bw_iok; bw_complete; bw_distinct] THEN REPEAT STRIP_TAC THENL
   [ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* A state that shows the rows below c, the slots and the rows region's     *)
(* length of a well-formed one keeps the table well formed at c.            *)
let BW_IOK_TRANSFER = prove
 (`!s t c. bw_iok s c /\ intern_slots t = intern_slots s /\ tisa_len t 0 = tisa_len s 0 /\
           (!i. i < 2 * c ==> intern_word t i = intern_word s i) /\
           (!p. val p < val(intern_slots s) ==> intern_slot t p = intern_slot s p)
           ==> bw_iok t c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_iok] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!h x. intern_pos t h x = intern_pos s h x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[intern_pos]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < c ==> intern_word t (2 * i) = intern_word s (2 * i) /\
                              intern_word t (2 * i + 1) = intern_word s (2 * i + 1)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!h d. d < val(intern_slots s)
                      ==> intern_slot t (intern_pos s h d) = intern_slot s (intern_pos s h d)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC INTERN_POS_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `bw_complete s c`)) THEN
    REWRITE_TAC[bw_complete] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `intern_word`)) (concl th) &&
      not (can (find_term ((=) `intern_slot`)) (concl th)) &&
      can (find_term ((=) `2 * i + 1`)) (concl(SPEC `i:num` th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `e:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `e < val(intern_slots s)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `bw_distinct s c`)) THEN
    REWRITE_TAC[bw_distinct; intern_has] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Entry validation: four read-write regions, their bounds, their distance   *)
(* from the frame and from each other, their minimum lengths.                *)
(* ------------------------------------------------------------------------- *)

let bw_regions = new_definition
 `bw_regions st <=>
    val(tregs st 0) + 192 <= 2 EXP 64 /\
    val(tisa_base st 0) + val(tisa_len st 0) < 2 EXP 64 /\
    val(tisa_base st 1) + val(tisa_len st 1) < 2 EXP 64 /\
    val(tisa_base st 2) + val(tisa_len st 2) < 2 EXP 64 /\
    val(tisa_base st 3) + val(tisa_len st 3) < 2 EXP 64 /\
    (val(tisa_base st 0) + val(tisa_len st 0) <= val(tregs st 0) \/
     val(tregs st 0) + 192 <= val(tisa_base st 0)) /\
    (val(tisa_base st 1) + val(tisa_len st 1) <= val(tregs st 0) \/
     val(tregs st 0) + 192 <= val(tisa_base st 1)) /\
    (val(tisa_base st 2) + val(tisa_len st 2) <= val(tregs st 0) \/
     val(tregs st 0) + 192 <= val(tisa_base st 2)) /\
    (val(tisa_base st 3) + val(tisa_len st 3) <= val(tregs st 0) \/
     val(tregs st 0) + 192 <= val(tisa_base st 3)) /\
    16 <= val(tisa_len st 0) /\ 8 <= val(tisa_len st 1) /\
    8 <= val(tisa_len st 2) /\ 256 <= val(tisa_len st 3) /\
    (val(tisa_base st 0) + val(tisa_len st 0) <= val(tisa_base st 1) \/
     val(tisa_base st 1) + val(tisa_len st 1) <= val(tisa_base st 0)) /\
    (val(tisa_base st 0) + val(tisa_len st 0) <= val(tisa_base st 2) \/
     val(tisa_base st 2) + val(tisa_len st 2) <= val(tisa_base st 0)) /\
    (val(tisa_base st 0) + val(tisa_len st 0) <= val(tisa_base st 3) \/
     val(tisa_base st 3) + val(tisa_len st 3) <= val(tisa_base st 0)) /\
    (val(tisa_base st 1) + val(tisa_len st 1) <= val(tisa_base st 2) \/
     val(tisa_base st 2) + val(tisa_len st 2) <= val(tisa_base st 1)) /\
    (val(tisa_base st 1) + val(tisa_len st 1) <= val(tisa_base st 3) \/
     val(tisa_base st 3) + val(tisa_len st 3) <= val(tisa_base st 1)) /\
    (val(tisa_base st 2) + val(tisa_len st 2) <= val(tisa_base st 3) \/
     val(tisa_base st 3) + val(tisa_len st 3) <= val(tisa_base st 2))`;;

(* The region facts as separate assumptions (the disjunctions kept whole). *)
let BW_REGIONS_TAC =
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o GEN_REWRITE_RULE I [bw_regions] o
              check (fun th -> concl th = `bw_regions st`));;

let BW_CLOSE_TAC =
  FIRST_ASSUM ACCEPT_TAC ORELSE (ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE TISA_WP_ARITH_TAC;;

let BW_ENTRY = prove
 (`!st. tisa_entry_ok bind_walk st ==> bw_regions st`,
  GEN_TAC THEN
  REWRITE_TAC[bind_walk; tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok;
              tisa_region_ok; tisa_pair_ok; tisa_frame; tisa_base; tisa_len; bw_regions] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(val(tisa_fword st 1) = 0) /\ ~(val(tisa_fword st 3) = 0) /\
                ~(val(tisa_fword st 5) = 0) /\ ~(val(tisa_fword st 7) = 0)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TISA_WP_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(val(tisa_fword st 1) = 0)`;
                              ASSUME `~(val(tisa_fword st 3) = 0)`;
                              ASSUME `~(val(tisa_fword st 5) = 0)`;
                              ASSUME `~(val(tisa_fword st 7) = 0)`]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT CONJ_TAC THEN BW_CLOSE_TAC);;

(* What the prologue checked. *)
let bw_entered = new_definition
 `bw_entered st <=>
    val(intern_count st) <= val(tisa_len st 0) DIV 16 /\
    val(tregs st 1) < val(intern_count st) /\
    val(tisa_fword st 22) < 2 EXP 60 /\ val(tisa_fword st 23) < 2 EXP 60`;;

(* ------------------------------------------------------------------------- *)
(* The walk's invariant at a step: the frame, the published header and the  *)
(* rows below it as on entry; the private count c (work word 0) between the  *)
(* published count and the rows' capacity; K, t; the stack and log counts   *)
(* within K; every result entry below vsp and every log entry below lc      *)
(* claims what it should; and the table well formed at c when it was at     *)
(* the published count on entry.                                             *)
(* ------------------------------------------------------------------------- *)

(* The claim of entry e of area a of state s. *)
let bw_eclaim = new_definition
 `bw_eclaim st s a e <=>
    bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
             (val(tisa_fword st 22)) (val(tisa_fword st 23))
             (val(bw_ent s a e 0)) (val(bw_ent s a e 1)) (val(bw_ent s a e 2))`;;

let bw_mid = new_definition
 `bw_mid st s <=>
    tregs s 0 = tregs st 0 /\
    (!i. i < 24 ==> tisa_fword s i = tisa_fword st i) /\
    intern_count s = intern_count st /\
    val(intern_count st) <= val(bw_w s 0) /\ val(bw_w s 0) <= val(tisa_len st 0) DIV 16 /\
    (!i. i < 2 * val(intern_count st) ==> intern_word s i = intern_word st i) /\
    val(bw_w s 4) = val(tisa_len st 3) DIV 128 - 1 /\
    bw_w s 5 = tregs st 1 /\
    val(bw_w s 1) <= val(bw_w s 4) /\ val(bw_w s 2) <= val(bw_w s 4) /\
    val(bw_w s 3) <= val(bw_w s 4) /\
    (!v. v < val(bw_w s 2) ==> bw_eclaim st s 1 v) /\
    (!p. p < val(bw_w s 3) ==> bw_eclaim st s 2 p) /\
    (intern_ok st ==> bw_iok s (val(bw_w s 0)))`;;

let bw_inv = new_definition
 `bw_inv st (N:num) (j:num) s <=> bw_mid st s`;;

(* Every outcome: the table kept well formed; the rows below the published  *)
(* count kept when they lie in the rows region (past it they can alias the  *)
(* frame's status and return words, which every stop writes); FIRED, whose  *)
(* published count lay in the rows region, returns dbAbs ty over hbind at   *)
(* depth 0 of t, in the rows below the new published count; any other       *)
(* outcome leaves the published count.                                       *)
let bw_result = new_definition
 `bw_result st k s <=>
    (intern_ok st ==> intern_ok s) /\
    (val(intern_count st) <= val(tisa_len st 0) DIV 16
     ==> !i. i < 2 * val(intern_count st) ==> intern_word s i = intern_word st i) /\
    (k = 1 ==> val(intern_count st) <= val(tisa_len st 0) DIV 16 /\
               val(intern_count st) <= val(intern_count s) /\
               val(tisa_fword s 19) < val(intern_count s) /\
               bw_final (bw_rows st (val(intern_count st))) (bw_rows s (val(intern_count s)))
                        (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val(tregs st 1))
                        (val(tisa_fword s 19))) /\
    (~(k = 1) ==> intern_count s = intern_count st)`;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic over the assumptions, in widening rings: first the arithmetic *)
(* assumptions sharing an atom (a numeric leaf: val x, a variable, LENGTH l, *)
(* ...) with the goal, then those sharing one with that set, and so on; at  *)
(* each ring also each disjunctive assumption that touches the ring, one at *)
(* a time. The invariant carries many facts with DIV and subtraction;       *)
(* handing ARITH_TAC all of them at once is slow. A goal without atoms (F)  *)
(* starts from the atoms of the latest arithmetic assumption.                *)
(* ------------------------------------------------------------------------- *)

let bw_arith_ops = ["+"; "*"; "-"; "DIV"; "MOD"; "EXP"; "<"; "<="; ">"; ">="; "=";
                    "/\\"; "\\/"; "==>"];;

let rec bw_arith_leaves t acc =
  if is_numeral t then acc else
  match t with
    Comb(Comb(Const(op,_),a),b) when mem op bw_arith_ops ->
      bw_arith_leaves a (bw_arith_leaves b acc)
  | Comb(Const(("SUC" | "~"),_),a) -> bw_arith_leaves a acc
  | _ -> if type_of t = `:num` then insert t acc else acc;;

let BW_ARITH_TAC : tactic =
  let atoms tm = bw_arith_leaves tm [] in
  let atoms_of ths a = itlist (fun th acc -> union (atoms (concl th)) acc) ths a in
  fun (asl,w) ->
    let ok th = let c = concl th in
      not (is_forall c) && tisa_focus_arith_fm c && atoms c <> [] in
    let cands = map snd (filter (fun (_,th) -> ok th) asl) in
    let plain = filter (fun th -> not (can (find_term is_disj) (concl th))) cands
    and disj = filter (fun th -> can (find_term is_disj) (concl th)) cands in
    let attempt ths = (MAP_EVERY MP_TAC ths THEN ARITH_TAC) (asl,w) in
    let rec rings seen ats acc =
      let nw = filter (fun th -> not (mem th seen) && intersect (atoms (concl th)) ats <> []) plain in
      if nw = [] then rev acc
      else let seen' = seen @ nw in rings seen' (atoms_of nw ats) ((seen',atoms_of nw ats)::acc) in
    let seed = if atoms w <> [] then atoms w
               else match cands with th::_ -> atoms (concl th) | [] -> [] in
    let rs = (([], seed) :: rings [] seed []) in
    let tries = flat (map (fun (ths,ats) ->
                  ths :: map (fun d -> ths @ [d])
                             (filter (fun d -> intersect (atoms (concl d)) ats <> []) disj)) rs) in
    tryfind attempt tries;;

(* ------------------------------------------------------------------------- *)
(* Steps of the invariant: a state that shows the same rows, slots, header   *)
(* and frame, a private count kept, and live entries that each claim what    *)
(* they should, keeps it.                                                    *)
(* ------------------------------------------------------------------------- *)

let BW_ROWS_EQ = prove
 (`!s s' c. (!i. i < 2 * c ==> intern_word s' i = intern_word s i)
            ==> bw_rows s' c = bw_rows s c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_BW_ROWS] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_BW_ROWS; bw_row] THEN
  SUBGOAL_THEN `2 * j < 2 * c /\ 2 * j + 1 < 2 * c` STRIP_ASSUME_TAC THENL
   [BW_ARITH_TAC; ASM_SIMP_TAC[]]);;

(* The general step: every live entry of s' claims its result over the rows *)
(* of s (which s' shows), the counts within K, the rest kept.               *)
let BW_MID_STEP = prove
 (`!st s s'.
     bw_mid st s /\
     tregs s' 0 = tregs st 0 /\ (!i. i < 24 ==> tisa_fword s' i = tisa_fword st i) /\
     intern_count s' = intern_count st /\
     bw_w s' 0 = bw_w s 0 /\ bw_w s' 4 = bw_w s 4 /\ bw_w s' 5 = bw_w s 5 /\
     val(bw_w s' 1) <= val(bw_w s 4) /\ val(bw_w s' 2) <= val(bw_w s 4) /\
     val(bw_w s' 3) <= val(bw_w s 4) /\
     (!i. i < 2 * val(bw_w s 0) ==> intern_word s' i = intern_word s i) /\
     (!p. val p < val(intern_slots st) ==> intern_slot s' p = intern_slot s p) /\
     (!v. v < val(bw_w s' 2)
          ==> bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
                       (val(tisa_fword st 22)) (val(tisa_fword st 23))
                       (val(bw_ent s' 1 v 0)) (val(bw_ent s' 1 v 1)) (val(bw_ent s' 1 v 2))) /\
     (!p. p < val(bw_w s' 3)
          ==> bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
                       (val(tisa_fword st 22)) (val(tisa_fword st 23))
                       (val(bw_ent s' 2 p 0)) (val(bw_ent s' 2 p 1)) (val(bw_ent s' 2 p 2)))
     ==> bw_mid st s'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_mid] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bw_rows s' (val(bw_w s 0)) = bw_rows s (val(bw_w s 0))` ASSUME_TAC THENL
   [MATCH_MP_TAC BW_ROWS_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[bw_eclaim] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(BW_ARITH_TAC THEN NO_TAC) THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < 2 * val(bw_w s 0)` (fun th -> ASM_SIMP_TAC[th]) THEN BW_ARITH_TAC;
    DISCH_TAC THEN MATCH_MP_TAC BW_IOK_TRANSFER THEN EXISTS_TAC `s:tisa_state` THEN
    SUBGOAL_THEN `intern_slots s' = intern_slots st /\ intern_slots s = intern_slots st /\
                  tisa_len s' 0 = tisa_len st 0 /\ tisa_len s 0 = tisa_len st 0`
     STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[tisa_len; intern_slots] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[ARITH_RULE `1 < 24 /\ 3 < 24`];
      ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* After interning: the key's row, the private count c or c + 1, every other *)
(* work word, the rows below c, the header and the frame kept.               *)
(* ------------------------------------------------------------------------- *)

let bw_after_intern = new_definition
 `bw_after_intern s u <=>
    tregs u 0 = tregs s 0 /\ tregs u 1 = tregs s 1 /\ tregs u 2 = tregs s 2 /\
    tregs u 10 = tregs s 10 /\ tregs u 11 = tregs s 11 /\
    (!i. i < 24 ==> tisa_fword u i = tisa_fword s i) /\
    intern_count u = intern_count s /\
    (val(bw_w u 0) = val(bw_w s 0) \/ val(bw_w u 0) = val(bw_w s 0) + 1) /\
    val(bw_w u 0) <= val(tisa_len s 0) DIV 16 /\
    (!k. 0 < k /\ 8 * k + 8 <= val(tisa_len s 3) ==> bw_w u k = bw_w s k) /\
    (!i. i < 2 * val(bw_w s 0) ==> intern_word u i = intern_word s i) /\
    val(tregs u 5) < val(bw_w u 0) /\
    intern_word u (2 * val(tregs u 5)) = tregs s 1 /\
    intern_word u (2 * val(tregs u 5) + 1) = tregs s 2 /\
    (bw_iok s (val(bw_w s 0)) ==> bw_iok u (val(bw_w u 0)))`;;

let BW_MID_INTERNED = prove
 (`!st s u. bw_regions st /\ bw_mid st s /\ bw_after_intern s u ==> bw_mid st u`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o REWRITE_RULE[bw_mid])
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o REWRITE_RULE[bw_after_intern]))) THEN
  BW_REGIONS_TAC THEN REWRITE_TAC[bw_mid] THEN
  SUBGOAL_THEN `val(intern_count st) <= val(bw_w s 0) /\ val(bw_w s 0) <= val(bw_w u 0)`
   STRIP_ASSUME_TAC THENL [BW_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!k. 0 < k /\ k < 16 + 4 * (3 * val(bw_w s 4)) ==> bw_w u k = bw_w s k`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `tisa_len s 3 = tisa_len st 3` SUBST1_TAC THENL
     [REWRITE_TAC[tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[ARITH_RULE `7 < 24`];
      BW_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `bw_w u 1 = bw_w s 1 /\ bw_w u 2 = bw_w s 2 /\ bw_w u 3 = bw_w s 3 /\
                bw_w u 4 = bw_w s 4 /\ bw_w u 5 = bw_w s 5`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN BW_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!a e f. a < 3 /\ e < val(bw_w s 4) /\ f < 3 ==> bw_ent u a e f = bw_ent s a e f`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[bw_ent] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th = `bw_w u 4 = bw_w s 4`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `a * val(bw_w s 4) <= 2 * val(bw_w s 4)` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN BW_ARITH_TAC; BW_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `bw_ext (bw_rows s (val(bw_w s 0))) (bw_rows u (val(bw_w u 0)))` ASSUME_TAC THENL
   [MATCH_MP_TAC BW_ROWS_EXT THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[bw_eclaim] THEN REPEAT CONJ_TAC THENL
   [(* the frame *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `tisa_fword u`)) (concl th)
                          then SUBST1_TAC(MP (SPEC `i:num` th) (ASSUME `i < 24`)) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `tisa_fword s`)) (concl th) &&
                             can (find_term ((=) `tisa_fword st`)) (concl th)
                          then ACCEPT_TAC(MP (SPEC `i:num` th) (ASSUME `i < 24`)) else NO_TAC);
    BW_ARITH_TAC;
    (* the private count within the rows region *)
    SUBGOAL_THEN `tisa_len s 0 = tisa_len st 0` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `tisa_fword s`)) (concl th) &&
                               can (find_term ((=) `tisa_fword st`)) (concl th)
                            then MATCH_MP_TAC th else NO_TAC) THEN CONV_TAC NUM_REDUCE_CONV;
      BW_ARITH_TAC];
    (* the rows below the published count *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < 2 * val(bw_w s 0)` (fun th -> ASM_SIMP_TAC[th]) THEN BW_ARITH_TAC;
    BW_ARITH_TAC;
    BW_ARITH_TAC;
    BW_ARITH_TAC;
    (* results and log: the entries read as in s, the rows extended *)
    X_GEN_TAC `v:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `v < val(bw_w s 4)` ASSUME_TAC THENL [BW_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `bw_ent u`)) (concl th)
                          then REWRITE_TAC(map (fun f -> MATCH_MP th (CONJ (ARITH_RULE `1 < 3`)
                                 (CONJ (ASSUME `v < val(bw_w s 4)`)
                                       (ARITH_RULE (mk_binop `(<):num->num->bool` (mk_small_numeral f) `3`)))))
                                 [0;1;2])
                          else NO_TAC) THEN
    MATCH_MP_TAC BW_CLAIM_EXT THEN EXISTS_TAC `bw_rows s (val(bw_w s 0))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `bw_eclaim st s 1`)) (concl th))) THEN
    ASM_REWRITE_TAC[bw_eclaim];
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `p < val(bw_w s 4)` ASSUME_TAC THENL [BW_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `bw_ent u`)) (concl th)
                          then REWRITE_TAC(map (fun f -> MATCH_MP th (CONJ (ARITH_RULE `2 < 3`)
                                 (CONJ (ASSUME `p < val(bw_w s 4)`)
                                       (ARITH_RULE (mk_binop `(<):num->num->bool` (mk_small_numeral f) `3`)))))
                                 [0;1;2])
                          else NO_TAC) THEN
    MATCH_MP_TAC BW_CLAIM_EXT THEN EXISTS_TAC `bw_rows s (val(bw_w s 0))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `bw_eclaim st s 2`)) (concl th))) THEN
    ASM_REWRITE_TAC[bw_eclaim];
    (* the table *)
    DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_imp(concl th) && can (find_term ((=) `bw_iok u`)) (concl th)
                          then MATCH_MP_TAC th else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `intern_ok st`
                          then MATCH_MP_TAC th else NO_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* What a step leaves for the tail, and the tail for the result.             *)
(* ------------------------------------------------------------------------- *)

(* The result r in the rows D, for mode m: modes 0 and 1 claim (si, sn, r); *)
(* mode 2 is the whole walk's claim.                                          *)
let bw_resok = new_definition
 `bw_resok st m mi mn D r <=>
    (m < 2 ==> bw_claim (bw_rows st (val(intern_count st))) D
                        (val(tisa_fword st 22)) (val(tisa_fword st 23)) mi mn r) /\
    (m = 2 ==> r < LENGTH D /\
               bw_final (bw_rows st (val(intern_count st))) D
                        (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val(tregs st 1)) r)`;;

let bw_post_pre = new_definition
 `bw_post_pre st s <=>
    bw_mid st s /\
    bw_resok st (val(bw_w s 8)) (val(bw_w s 6)) (val(bw_w s 7)) (bw_rows s (val(bw_w s 0)))
             (val(tregs s 5))`;;

let bw_tail_pre = new_definition
 `bw_tail_pre st s <=>
    bw_mid st s /\ tisa_bool (tregs s 9) /\
    (tregs s 9 = word 0
     ==> bw_resok st (val(bw_w s 8)) (val(bw_w s 6)) (val(bw_w s 7)) (bw_rows s (val(bw_w s 0)))
                  (val(tregs s 5))) /\
    (~(tregs s 9 = word 0)
     ==> !D r. bw_ext (bw_rows s (val(bw_w s 0))) D /\
               LENGTH D <= val(tisa_len st 0) DIV 16 /\ r < LENGTH D /\
               EL r D = (val(tregs s 1) MOD 8, val(tregs s 1) DIV 8, val(tregs s 2))
               ==> bw_resok st (val(bw_w s 8)) (val(bw_w s 6)) (val(bw_w s 7)) D r)`;;

(* After interning, the tail's promise for the key gives the post block's   *)
(* precondition.                                                              *)
let BW_POST_PRE_INTERNED = prove
 (`!st s u. bw_regions st /\ bw_tail_pre st s /\ ~(tregs s 9 = word 0) /\ bw_after_intern s u
            ==> bw_post_pre st u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [bw_tail_pre] o
              check (fun th -> can (find_term ((=) `bw_tail_pre`)) (concl th))) THEN
  REWRITE_TAC[bw_post_pre] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BW_MID_INTERNED THEN EXISTS_TAC `s:tisa_state` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_neg(lhand(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o GEN_REWRITE_RULE I [bw_after_intern] o
              check (fun th -> can (find_term ((=) `bw_after_intern`)) (concl th))) THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o GEN_REWRITE_RULE I [bw_mid] o
              check (fun th -> concl th = `bw_mid st s`)) THEN
  BW_REGIONS_TAC THEN
  SUBGOAL_THEN `tisa_len s 3 = tisa_len st 3 /\ tisa_len s 0 = tisa_len st 0` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `tisa_fword s`)) (concl th) &&
                             can (find_term ((=) `tisa_fword st`)) (concl th)
                          then CONJ_TAC THEN MATCH_MP_TAC th THEN CONV_TAC NUM_REDUCE_CONV else NO_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN `bw_w u 6 = bw_w s 6 /\ bw_w u 7 = bw_w s 7 /\ bw_w u 8 = bw_w s 8`
   (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `bw_w u`)) (concl th) &&
                             can (find_term ((=) `tisa_len s 3`)) (concl th)
                          then MATCH_MP_TAC th else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if concl th = `tisa_len s 3 = tisa_len st 3` then REWRITE_TAC[th] else NO_TAC) THEN
    BW_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[LENGTH_BW_ROWS] THEN
  SUBGOAL_THEN `EL (val(tregs u 5)) (bw_rows u (val(bw_w u 0))) = bw_row u (val(tregs u 5))`
   SUBST1_TAC THENL [MATCH_MP_TAC EL_BW_ROWS THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[bw_row] THEN
  FIRST_ASSUM(fun th -> if concl th = `intern_word u (2 * val (tregs u 5)) = tregs s 1`
                        then REWRITE_TAC[th] else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if concl th = `intern_word u (2 * val (tregs u 5) + 1) = tregs s 2`
                        then REWRITE_TAC[th] else NO_TAC) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BW_ROWS_EXT THEN CONJ_TAC THENL [BW_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
    FIRST_ASSUM(fun th -> if concl th = `tisa_len s 0 = tisa_len st 0` then
                            RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
    BW_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The finish (status and return words) of a state with the entry state's    *)
(* frame keeps the rows, the slots and the header.                          *)
(* ------------------------------------------------------------------------- *)

let BW_FINST_KEEP = prove
 (`!st X k (v:int64).
     bw_regions st /\ tregs X 0 = tregs st 0 /\ (!i. i < 24 ==> tisa_fword X i = tisa_fword st i)
     ==> tregs (tisa_finst k v X) 0 = tregs st 0 /\
         intern_count (tisa_finst k v X) = intern_count X /\
         (!i. i < 2 * (val(tisa_len st 0) DIV 16)
              ==> intern_word (tisa_finst k v X) i = intern_word X i) /\
         (!p. val p < val(intern_slots st) ==> intern_slot (tisa_finst k v X) p = intern_slot X p) /\
         tisa_len (tisa_finst k v X) 0 = tisa_len st 0 /\
         intern_slots (tisa_finst k v X) = intern_slots st /\
         tisa_fword (tisa_finst k v X) 19 = v /\
         (!i. i < 24 /\ ~(i = 18) /\ ~(i = 19) ==> tisa_fword (tisa_finst k v X) i = tisa_fword st i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_REGIONS_TAC THEN
  MP_TAC(ISPECL [`k:num`; `v:int64`; `X:tisa_state`] TISA_FINST_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)] THEN
  SUBGOAL_THEN `!r. r < 4 ==> tisa_base X r = tisa_base st r /\ tisa_len X r = tisa_len st r`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_base; tisa_len] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    BW_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r < 4 ==> tisa_base (tisa_finst k v X) r = tisa_base st r /\
                              tisa_len (tisa_finst k v X) r = tisa_len st r`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE `r < 4 ==> r < 9`]; ALL_TAC] THEN
  REWRITE_TAC[TISA_TREGS_FINST; intern_count; intern_word; intern_slot; intern_slots] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4 /\ 19 < 24`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_read`)) (concl th))) THEN
    REWRITE_TAC[ASSUME `tregs X 0 = tregs st 0`] THEN BW_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 0) (word (8 * i)):int64) = val(tisa_base st 0) + 8 * i`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_read`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN BW_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `tisa_len st 1` VAL_BOUND_64) THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_USHR]) THEN RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NUM_REDUCE_CONV)) THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 1) (word (8 * val(p:int64))):int64) =
                  val(tisa_base st 1) + 8 * val p`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_read`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN BW_ARITH_TAC]);;

(* A stop (not FIRED) whose state shows the rows below the private count, the *)
(* slots, the header and the frame of a state where the invariant held.     *)
let BW_RESULT_STOP = prove
 (`!st s X k (v:int64).
     bw_regions st /\ bw_mid st s /\ ~(k = 1) /\
     tregs X 0 = tregs st 0 /\ (!i. i < 24 ==> tisa_fword X i = tisa_fword st i) /\
     intern_count X = intern_count st /\
     (!i. i < 2 * val(bw_w s 0) ==> intern_word X i = intern_word s i) /\
     (!p. val p < val(intern_slots st) ==> intern_slot X p = intern_slot s p)
     ==> bw_result st k (tisa_finst k v X)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `X:tisa_state`; `k:num`; `v:int64`] BW_FINST_KEEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_mid] o check (fun th -> concl th = `bw_mid st s`)) THEN
  SUBGOAL_THEN `!i. i < 2 * val(bw_w s 0) ==> intern_word (tisa_finst k v X) i = intern_word s i`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i < 2 * (val(tisa_len st 0) DIV 16)` (fun th -> ASM_SIMP_TAC[th]) THEN
    BW_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[bw_result] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[INTERN_OK_BW] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BW_IOK_DOWN THEN EXISTS_TAC `val(bw_w s 0)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BW_IOK_TRANSFER THEN EXISTS_TAC `s:tisa_state` THEN
    SUBGOAL_THEN `intern_slots s = intern_slots st /\ tisa_len s 0 = tisa_len st 0` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[intern_slots; tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[ARITH_RULE `1 < 24 /\ 3 < 24`];
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i < 2 * val(bw_w s 0)` (fun th -> ASM_SIMP_TAC[th]) THEN BW_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A stop from a state where the invariant held.                             *)
(* ------------------------------------------------------------------------- *)

let BW_RESULT_STOP_MID = prove
 (`!st X k (v:int64). bw_regions st /\ bw_mid st X /\ ~(k = 1)
                      ==> bw_result st k (tisa_finst k v X)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BW_RESULT_STOP THEN EXISTS_TAC `X:tisa_state` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o GEN_REWRITE_RULE I [bw_mid] o
              check (fun th -> concl th = `bw_mid st X`)) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* An 8-byte store at work word k: work word k' reads the value at k' = k,   *)
(* the old word elsewhere; the frame, the header, the rows and the slots are *)
(* kept (the work region lies apart from all of them).                       *)
(* ------------------------------------------------------------------------- *)

let BW_WORK_STORE = prove
 (`!st s k (v:int64).
     bw_regions st /\ tregs s 0 = tregs st 0 /\ (!i. i < 24 ==> tisa_fword s i = tisa_fword st i) /\
     8 * k + 8 <= val(tisa_len st 3)
     ==> tregs (tisa_store (word_add (tisa_base st 3) (word (8 * k))) 8 v s) 0 = tregs st 0 /\
         (!i. i < 24 ==> tisa_fword (tisa_store (word_add (tisa_base st 3) (word (8 * k))) 8 v s) i =
                         tisa_fword st i) /\
         intern_count (tisa_store (word_add (tisa_base st 3) (word (8 * k))) 8 v s) = intern_count s /\
         (!i. 8 * i + 8 <= val(tisa_len st 0)
              ==> intern_word (tisa_store (word_add (tisa_base st 3) (word (8 * k))) 8 v s) i =
                  intern_word s i) /\
         (!p. val p < val(intern_slots st)
              ==> intern_slot (tisa_store (word_add (tisa_base st 3) (word (8 * k))) 8 v s) p =
                  intern_slot s p) /\
         (!k'. 8 * k' + 8 <= val(tisa_len st 3)
               ==> bw_w (tisa_store (word_add (tisa_base st 3) (word (8 * k))) 8 v s) k' =
                   if k' = k then v else bw_w s k')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_REGIONS_TAC THEN
  ABBREV_TAC `a = word_add (tisa_base st 3) (word (8 * k)):int64` THEN
  SUBGOAL_THEN `val(a:int64) = val(tisa_base st 3) + 8 * k` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:int64`; `8`; `v:int64`; `s:tisa_state`] TISA_STORE_KEEPS_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN BW_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `!r. r < 4 ==> tisa_base s r = tisa_base st r /\ tisa_len s r = tisa_len st r`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_base; tisa_len] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    BW_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[TISA_TREGS_STORE] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 12 /\ 1 < 12 /\ 2 < 12 /\ 3 < 12`;
               ARITH_RULE `0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4`] THEN
  REWRITE_TAC[intern_count; intern_word; intern_slot; intern_slots; bw_w] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 12 /\ 1 < 12 /\ 2 < 12 /\ 3 < 12`;
               ARITH_RULE `0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 0) (word (8 * i)):int64) = val(tisa_base st 0) + 8 * i`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_USHR]) THEN RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NUM_REDUCE_CONV)) THEN
    MP_TAC(ISPEC `tisa_len st 1` VAL_BOUND_64) THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 1) (word (8 * val(p:int64))):int64) =
                  val(tisa_base st 1) + 8 * val p`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 3) (word (8 * k')):int64) = val(tisa_base st 3) + 8 * k'`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC TISA_READ_STORE_SAME THEN
      ASM_REWRITE_TAC[] THEN BW_ARITH_TAC;
      MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC]]);;

(* The invariant depends on a state only through its frame register and its *)
(* memory.                                                                    *)
let BW_MID_SAME = prove
 (`!st s s'. tregs s' 0 = tregs s 0 /\ tmem s' = tmem s ==> (bw_mid st s' <=> bw_mid st s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TISA_SAME_VIEW) THEN
  SUBGOAL_THEN `bw_w s' = bw_w s /\ intern_word s' = intern_word s /\
                intern_count s' = intern_count s /\ tisa_fword s' = tisa_fword s /\
                intern_slot s' = intern_slot s /\ intern_slots s' = intern_slots s /\
                intern_pos s' = intern_pos s /\ tisa_len s' = tisa_len s`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; bw_w; intern_word; intern_count; intern_slot; intern_slots;
                intern_pos] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bw_ent s' = bw_ent s /\ bw_row s' = bw_row s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; bw_ent; bw_row] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `bw_rows s' = bw_rows s` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; bw_rows] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `bw_eclaim st s' = bw_eclaim st s /\ bw_iok s' = bw_iok s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; bw_eclaim; bw_iok; bw_complete; bw_distinct; intern_has] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[bw_mid] THEN ASM_REWRITE_TAC[]);;

(* A register write keeps the invariant. *)
let BW_MID_SETREG = prove
 (`!st s d (v:int64). ~(d = 0) /\ bw_mid st s ==> bw_mid st (tisa_setreg d v s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`st:tisa_state`; `s:tisa_state`; `tisa_setreg d v s`] BW_MID_SAME) THEN
  ASM_REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 = d <=> d = 0`]);;

(* The claim of the would-be entry e of area a of s, over s's rows. *)
let bw_nclaim = new_definition
 `bw_nclaim st s a e <=>
    bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
             (val(tisa_fword st 22)) (val(tisa_fword st 23))
             (val(bw_ent s a e 0)) (val(bw_ent s a e 1)) (val(bw_ent s a e 2))`;;


(* ------------------------------------------------------------------------- *)
(* A store at a work word the invariant does not read, at tsp within K, at   *)
(* vsp popping, or pushing a result or a log entry that claims what it      *)
(* should, keeps the invariant.                                               *)
(* ------------------------------------------------------------------------- *)

let bw_wfree = new_definition
 `bw_wfree s k <=>
    k = 6 \/ k = 7 \/ k = 8 \/
    (16 <= k /\ k < 16 + 4 * val(bw_w s 4)) \/
    (16 + 4 * (val(bw_w s 4) + val(bw_w s 2)) <= k /\ k < 16 + 4 * (2 * val(bw_w s 4))) \/
    (16 + 4 * (2 * val(bw_w s 4) + val(bw_w s 3)) <= k /\ k < 16 + 4 * (3 * val(bw_w s 4))) \/
    16 + 12 * val(bw_w s 4) <= k`;;

let BW_ECLAIM_NCLAIM = prove
 (`!st s a e. bw_eclaim st s a e <=> bw_nclaim st s a e`,
  REWRITE_TAC[bw_eclaim; bw_nclaim]);;

(* The invariant's facts as assumptions, K's defining equation turned so   *)
(* that rewriting with the assumptions leaves val(bw_w s 4) in place.       *)
let BW_MID_FACTS_TAC s =
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o GEN_REWRITE_RULE I [bw_mid] o
              check (fun th -> concl th = mk_comb(`bw_mid st`, s))) THEN
  RULE_ASSUM_TAC(fun th -> if concl th = subst [s,`s:tisa_state`]
                                           `val(bw_w s 4) = val(tisa_len st 3) DIV 128 - 1`
                           then SYM th else th);;

(* Arithmetic, on arithmetic goals only. *)
let BW_ARITH_GOAL_TAC : tactic = fun (asl,w) ->
  if tisa_focus_arith_fm w then BW_ARITH_TAC (asl,w) else failwith "BW_ARITH_GOAL_TAC";;

(* The core: a store at k, away from words 0, 4 and 5, that keeps the three *)
(* counts within K and leaves the words of every live entry, each claiming  *)
(* what it claimed over s.                                                   *)
let BW_MID_STORE_CORE = prove
 (`!st s k (v:int64).
     bw_regions st /\ bw_mid st s /\ 8 * k + 8 <= val(tisa_len st 3) /\
     ~(k = 0) /\ ~(k = 4) /\ ~(k = 5) /\
     val(if k = 1 then v else bw_w s 1) <= val(bw_w s 4) /\
     val(if k = 2 then v else bw_w s 2) <= val(bw_w s 4) /\
     val(if k = 3 then v else bw_w s 3) <= val(bw_w s 4) /\
     (!e. e < val(if k = 2 then v else bw_w s 2)
          ==> (!f. f < 3 ==> ~(16 + 4 * (val(bw_w s 4) + e) + f = k)) /\ bw_nclaim st s 1 e) /\
     (!e. e < val(if k = 3 then v else bw_w s 3)
          ==> (!f. f < 3 ==> ~(16 + 4 * (2 * val(bw_w s 4) + e) + f = k)) /\ bw_nclaim st s 2 e)
     ==> bw_mid st (tisa_store (word_add (tisa_base st 3) (word (8 * k))) 8 v s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_MID_FACTS_TAC `s:tisa_state` THEN BW_REGIONS_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `s:tisa_state`; `k:num`; `v:int64`] BW_WORK_STORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `s' = tisa_store (word_add (tisa_base st 3) (word (8 * k))) 8 v s` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `128 * val(bw_w s 4) + 128 <= val(tisa_len st 3)` ASSUME_TAC THENL
   [BW_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!k'. k' < 16 + 4 * (3 * val(bw_w s 4))
                     ==> bw_w s' k' = if k' = k then v else bw_w s k'`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `bw_w s'`)) (concl th)
                          then MATCH_MP_TAC th else NO_TAC) THEN
    BW_ARITH_TAC;
    ALL_TAC] THEN
  (* words 0 to 5 *)
  SUBGOAL_THEN `bw_w s' 0 = bw_w s 0 /\ bw_w s' 4 = bw_w s 4 /\ bw_w s' 5 = bw_w s 5 /\
                bw_w s' 1 = (if k = 1 then v else bw_w s 1) /\
                bw_w s' 2 = (if k = 2 then v else bw_w s 2) /\
                bw_w s' 3 = (if k = 3 then v else bw_w s 3)`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    W(fun (asl,w) ->
      let a = rand(lhand w) in
      FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `bw_w s'`)) (concl th) &&
                               can (find_term is_cond) (concl th) &&
                               not (can (find_term ((=) `tisa_len st 3`)) (concl th))
                            then MP_TAC(SPEC a th) else NO_TAC) THEN
      ANTS_TAC THENL [BW_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN BW_ARITH_TAC);
    ALL_TAC] THEN
  MATCH_MP_TAC BW_MID_STEP THEN EXISTS_TAC `s:tisa_state` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* the rows: below 2c words, inside the rows region *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `intern_word s'`)) (concl th) &&
                             can (find_term ((=) `tisa_len st 0`)) (concl th)
                          then MATCH_MP_TAC th else NO_TAC) THEN
    BW_ARITH_TAC;
    (* results *)
    X_GEN_TAC `e:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `bw_nclaim st s 1`)) (concl th)
                          then MP_TAC(SPEC `e:num` th) else NO_TAC) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `e < val(bw_w s 4)` ASSUME_TAC THENL [BW_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `!f. f < 3 ==> bw_ent s' 1 e f = bw_ent s 1 e f` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[bw_ent; MULT_CLAUSES] THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `bw_w s'`)) (concl th) &&
                               not (can (find_term ((=) `tisa_len st 3`)) (concl th))
                            then W(fun (asl,w) -> MP_TAC(SPEC (rand(lhand w)) th)) else NO_TAC) THEN
      ANTS_TAC THENL [BW_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `f:num` o check (fun th -> is_forall(concl th) &&
                      can (find_term ((=) `4 * (val(bw_w s 4) + e)`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < 3 /\ 1 < 3 /\ 2 < 3`] THEN
    FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[bw_nclaim] o
                check (fun th -> concl th = `bw_nclaim st s 1 e`));
    (* log *)
    X_GEN_TAC `e:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `bw_nclaim st s 2`)) (concl th)
                          then MP_TAC(SPEC `e:num` th) else NO_TAC) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `e < val(bw_w s 4)` ASSUME_TAC THENL [BW_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `!f. f < 3 ==> bw_ent s' 2 e f = bw_ent s 2 e f` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[bw_ent] THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `bw_w s'`)) (concl th) &&
                               not (can (find_term ((=) `tisa_len st 3`)) (concl th))
                            then W(fun (asl,w) -> MP_TAC(SPEC (rand(lhand w)) th)) else NO_TAC) THEN
      ANTS_TAC THENL [BW_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `f:num` o check (fun th -> is_forall(concl th) &&
                      can (find_term ((=) `4 * (2 * val(bw_w s 4) + e)`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < 3 /\ 1 < 3 /\ 2 < 3`] THEN
    FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[bw_nclaim] o
                check (fun th -> concl th = `bw_nclaim st s 2 e`))]);;

(* An entry of area a below the new count: an old entry (its claim from the *)
(* invariant) or the pushed one (its claim given).                           *)
let BW_ENTRY_CLAIM_TAC a =
  let cnt = mk_comb(`val:int64->num`,
                    mk_comb(mk_comb(`bw_w`, `s:tisa_state`), mk_small_numeral (a + 1))) in
  let ecl = list_mk_comb(`bw_eclaim`, [`st:tisa_state`; `s:tisa_state`; mk_small_numeral a]) in
  X_GEN_TAC `e:num` THEN DISCH_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `f:num` THEN DISCH_TAC THEN BW_ARITH_TAC;
    ASM_CASES_TAC (mk_binop `(<):num->num->bool` `e:num` cnt) THENL
     [REWRITE_TAC[GSYM BW_ECLAIM_NCLAIM] THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) ecl)) (concl th)
                            then MATCH_MP_TAC th else NO_TAC) THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST
       [SUBGOAL_THEN (mk_eq(`e:num`, cnt)) SUBST1_TAC THENL
         [BW_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
        MATCH_MP_TAC(TAUT `F ==> p`) THEN BW_ARITH_TAC]]];;

let BW_MID_STORE_W = prove
 (`!st s k (v:int64).
     bw_regions st /\ bw_mid st s /\ 8 * k + 8 <= val(tisa_len st 3) /\
     (bw_wfree s k \/
      (k = 1 /\ val v <= val(bw_w s 4)) \/
      (k = 2 /\ val v <= val(bw_w s 2)) \/
      (k = 2 /\ val v = val(bw_w s 2) + 1 /\ val(bw_w s 2) < val(bw_w s 4) /\
       bw_nclaim st s 1 (val(bw_w s 2))) \/
      (k = 3 /\ val v = val(bw_w s 3) + 1 /\ val(bw_w s 3) < val(bw_w s 4) /\
       bw_nclaim st s 2 (val(bw_w s 3))))
     ==> bw_mid st (tisa_store (word_add (tisa_base st 3) (word (8 * k))) 8 v s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  BW_MID_FACTS_TAC `s:tisa_state` THEN BW_REGIONS_TAC THEN
  SUBGOAL_THEN `128 * val(bw_w s 4) + 128 <= val(tisa_len st 3)` ASSUME_TAC THENL
   [BW_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (ASSUME_TAC o GEN_REWRITE_RULE I [bw_wfree])
              (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
                (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
                  (DISJ_CASES_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC)))) THENL
   [(* a free word *)
    SUBGOAL_THEN `~(k = 0) /\ ~(k = 1) /\ ~(k = 2) /\ ~(k = 3) /\ ~(k = 4) /\ ~(k = 5)`
     STRIP_ASSUME_TAC THENL [BW_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC BW_MID_STORE_CORE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [BW_ENTRY_CLAIM_TAC 1; BW_ENTRY_CLAIM_TAC 2];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  (MATCH_MP_TAC BW_MID_STORE_CORE THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
   TRY(BW_ARITH_GOAL_TAC THEN NO_TAC) THENL
    [BW_ENTRY_CLAIM_TAC 1; BW_ENTRY_CLAIM_TAC 2]));;

(* ------------------------------------------------------------------------- *)
(* An early-exit loop, by an invariant Inv N j over the iteration index: the *)
(* check of k before and after each body, as tisa_early_iter runs it.        *)
(* ------------------------------------------------------------------------- *)

(* Weakening the continuation's postcondition. *)
let TISA_RWP_MONO_Q = prove
 (`!r Q Q' R. (!s. Q s ==> Q' s) ==> tisa_rwp r Q R ==> tisa_rwp r Q' R`,
  REWRITE_TAC[tisa_rwp] THEN MESON_TAC[]);;

let TISA_WP_EARLY_LOOP = prove
 (`!(Inv:num->num->tisa_state->bool) x n k cap body Q R st.
     (cap < val(tregs st n) ==> R 2 (tisa_failst 2 st)) /\
     (~(cap < val(tregs st n)) ==> Inv (val(tregs st n)) 0 st) /\
     (!N j s0. j < N /\ Inv N j s0
               ==> (~tisa_bool (tregs (tisa_setreg x (word j) s0) k)
                    ==> R 3 (tisa_failst 3 (tisa_setreg x (word j) s0))) /\
                   (tisa_bool (tregs (tisa_setreg x (word j) s0) k) /\
                    tregs (tisa_setreg x (word j) s0) k = word 0
                    ==> Q (tisa_setreg x (word j) s0)) /\
                   (tisa_bool (tregs (tisa_setreg x (word j) s0) k) /\
                    ~(tregs (tisa_setreg x (word j) s0) k = word 0)
                    ==> tisa_wp body
                          (\s2. (~tisa_bool (tregs s2 k) ==> R 3 (tisa_failst 3 s2)) /\
                                (tisa_bool (tregs s2 k) /\ tregs s2 k = word 0 ==> Q s2) /\
                                (tisa_bool (tregs s2 k) /\ ~(tregs s2 k = word 0)
                                 ==> Inv N (j + 1) s2))
                          R (tisa_setreg x (word j) s0))) /\
     (!N s. Inv N N s ==> Q (tisa_setreg x (word N) s))
     ==> tisa_wp (TEarlyLoop x n k cap body) Q R st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tisa_wp; tisa_exec] THEN
  COND_CASES_TAC THENL [ASM_SIMP_TAC[TISA_FAIL_STOP; TISA_RWP_STOP]; ALL_TAC] THEN
  SUBGOAL_THEN `(Inv:num->num->tisa_state->bool) (val(tregs st n)) 0 st` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `N = val(tregs st n)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!m j s0. j + m = N /\ (Inv:num->num->tisa_state->bool) N j s0
             ==> tisa_rwp (tisa_early_iter m (\st'. tisa_exec body st') x k j s0) Q R`
   (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[ADD_CLAUSES]) THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tisa_early_iter] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `j:num = N`)) THEN
    REWRITE_TAC[TISA_RWP_CONT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `j:num`; `s0:tisa_state`] o
    check (fun th -> can (find_term ((=) `tisa_wp`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN BW_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `s1 = tisa_setreg x (word j) s0` THEN STRIP_TAC THEN
  REWRITE_TAC[tisa_early_check] THEN
  ASM_CASES_TAC `tisa_bool (tregs s1 k)` THEN
  ASM_REWRITE_TAC[TISA_FAIL_STOP; TISA_RWP_STOP] THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  ASM_CASES_TAC `tregs s1 k = word 0` THEN ASM_REWRITE_TAC[TISA_RWP_CONT] THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[TISA_RWP_THEN] THEN BETA_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `tisa_wp`)) (concl th))) THEN
  ASM_REWRITE_TAC[tisa_wp] THEN MATCH_MP_TAC TISA_RWP_MONO_Q THEN
  X_GEN_TAC `s2:tisa_state` THEN BETA_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `tisa_bool (tregs s2 k)` THEN
  ASM_REWRITE_TAC[TISA_FAIL_STOP; TISA_RWP_STOP] THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  ASM_CASES_TAC `tregs s2 k = word 0` THEN ASM_REWRITE_TAC[TISA_RWP_CONT] THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term ((=) `tisa_early_iter`)) (concl th) && is_forall (concl th))) THEN
  CONJ_TAC THENL [BW_ARITH_TAC; ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The table with an explicit count c and key (k0, k1): a probe that went on *)
(* found a used slot whose row, if below c, is not the key; appending the    *)
(* key at c through the first empty slot of its probe sequence keeps the     *)
(* table well formed (intern16_complete.ml's INTERN_OK_APPEND, with the      *)
(* count and the key as parameters).                                          *)
(* ------------------------------------------------------------------------- *)

let bw_probed = new_definition
 `bw_probed s c (k0:int64) (k1:int64) x <=>
    ~(intern_slot s (intern_pos s (intern_hash k0 k1) x) = word 0) /\
    (val(word_sub (intern_slot s (intern_pos s (intern_hash k0 k1) x)) (word 1)) < c
     ==> ~intern_has s (val(word_sub (intern_slot s (intern_pos s (intern_hash k0 k1) x)) (word 1)))
                       k0 k1)`;;

let BW_IOK_APPEND =
  let rows_x = `!x. x < c
                    ==> intern_word t (2 * x) = intern_word s (2 * x) /\
                        intern_word t (2 * x + 1) = intern_word s (2 * x + 1)`
  and no_old = `!i. i < c ==> ~(intern_word s (2 * i) = k0 /\ intern_word s (2 * i + 1) = k1)` in
  prove
 (`!s t c j (k0:int64) (k1:int64).
     bw_iok s c /\ c < val(tisa_len s 0) DIV 16 /\
     j < val(intern_slots s) /\
     (!x. x < j ==> bw_probed s c k0 k1 x) /\
     intern_slot s (intern_pos s (intern_hash k0 k1) j) = word 0 /\
     intern_slots t = intern_slots s /\ tisa_len t 0 = tisa_len s 0 /\
     (!i. i < 2 * c ==> intern_word t i = intern_word s i) /\
     intern_word t (2 * c) = k0 /\ intern_word t (2 * c + 1) = k1 /\
     (!p. val p < val(intern_slots s)
          ==> intern_slot t p =
              if p = intern_pos s (intern_hash k0 k1) j then word(c + 1) else intern_slot s p)
     ==> bw_iok t (c + 1) /\ (!i. i < c ==> ~intern_has s i k0 k1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_iok] o
                check (fun th -> concl th = `bw_iok s c`)) THEN
  SUBGOAL_THEN `c + 1 < 2 EXP 64 /\ 0 < val(intern_slots s)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `tisa_len s 0` VAL_BOUND_64) THEN BW_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!h x. intern_pos t h x = intern_pos s h x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[intern_pos]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!h d. d < val(intern_slots s)
          ==> intern_slot t (intern_pos s h d) =
              if intern_pos s h d = intern_pos s (intern_hash k0 k1) j
              then word(c + 1) else intern_slot s (intern_pos s h d)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC INTERN_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(word(c + 1):int64 = word 0)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTERN_WORD_SUC_NZ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* No row below c holds the key: its probe chain would have passed the    *)
  (* key's probe j, met the empty slot, or been seen by a probe.           *)
  SUBGOAL_THEN no_old ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL [BW_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[bw_complete] o
                check (fun th -> concl th = `bw_complete s c`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (ARITH_RULE `d < j \/ d = j \/ j < d`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `d:num` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `bw_probed`)) (concl th))) THEN
      ASM_REWRITE_TAC[bw_probed] THEN
      ASM_SIMP_TAC[INTERN_WORD_SUC_PRED; intern_has];
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `d:num = j`)) THEN
      SUBGOAL_THEN `word(i + 1):int64 = word 0` MP_TAC THENL
       [ASM_MESON_TAC[]; ASM_SIMP_TAC[INTERN_WORD_SUC_NZ]];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[intern_has] THEN ASM_MESON_TAC[]] THEN
  REWRITE_TAC[bw_iok; bw_complete; bw_distinct; intern_has] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [BW_ARITH_TAC;
    (* every row is found by probing: old rows at their old distance, the  *)
    (* new row at the key's probe j                                          *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < c \/ i = c` STRIP_ASSUME_TAC THENL
     [BW_ARITH_TAC;
      SUBGOAL_THEN `intern_word t (2 * i) = intern_word s (2 * i) /\
                    intern_word t (2 * i + 1) = intern_word s (2 * i + 1)`
       (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN BW_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL [BW_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[bw_complete] o
                  check (fun th -> concl th = `bw_complete s c`)) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `d:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [COND_CASES_TAC THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `word(i + 1):int64 = word 0` MP_TAC THENL
         [FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
                                     can (find_term ((=) `d:num`)) (lhand(concl th)) &&
                                     not(is_forall(concl th)) &&
                                     type_of(lhand(concl th)) = `:int64`
                                  then SUBST_ALL_TAC th else NO_TAC) THEN
          ASM_MESON_TAC[];
          ASM_SIMP_TAC[INTERN_WORD_SUC_NZ]];
        X_GEN_TAC `e:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `e < val(intern_slots s)` ASSUME_TAC THENL
         [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]];
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `i:num = c`)) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `j:num` THEN ASM_SIMP_TAC[] THEN
      X_GEN_TAC `e:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `e < val(intern_slots s)` ASSUME_TAC THENL
       [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:num` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `bw_probed`)) (concl th))) THEN
      ASM_SIMP_TAC[bw_probed]];
    (* no two rows hold one key *)
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN rows_x ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN BW_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(a < c \/ a = c) /\ (b < c \/ b = c)` MP_TAC THENL
     [CONJ_TAC THEN BW_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC DISJ_CASES_TAC) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      is_var(lhand(concl th)) && rand(concl th) = `c:num`))) THEN
    REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[bw_distinct; intern_has] o
                    check (fun th -> concl th = `bw_distinct s c`)) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(MP (SPEC `a:num` (ASSUME rows_x)) (ASSUME `a < c`)) THEN
      MP_TAC(MP (SPEC `b:num` (ASSUME rows_x)) (ASSUME `b < c`)) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN (fun th -> REWRITE_TAC[GSYM th]))) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPEC `a:num` (ASSUME rows_x)) THEN MP_TAC(SPEC `a:num` (ASSUME no_old)) THEN
      MP_TAC(ASSUME `intern_word t (2 * a) = intern_word t (2 * c)`) THEN
      MP_TAC(ASSUME `intern_word t (2 * a + 1) = intern_word t (2 * c + 1)`) THEN
      MP_TAC(ASSUME `intern_word t (2 * c) = k0`) THEN
      MP_TAC(ASSUME `intern_word t (2 * c + 1) = k1`) THEN
      MP_TAC(ASSUME `a < c`) THEN MESON_TAC[];
      MP_TAC(SPEC `b:num` (ASSUME rows_x)) THEN MP_TAC(SPEC `b:num` (ASSUME no_old)) THEN
      MP_TAC(ASSUME `intern_word t (2 * c) = intern_word t (2 * b)`) THEN
      MP_TAC(ASSUME `intern_word t (2 * c + 1) = intern_word t (2 * b + 1)`) THEN
      MP_TAC(ASSUME `intern_word t (2 * c) = k0`) THEN
      MP_TAC(ASSUME `intern_word t (2 * c + 1) = k1`) THEN
      MP_TAC(ASSUME `b < c`) THEN MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Glue between the generator's reads and the invariant's views.             *)
(* ------------------------------------------------------------------------- *)

(* A read of 8 bytes of a variable state s at W + E (E a sum the generator  *)
(* wrote) is entry field bw_ent s a e f when E = 8 * (16 + 4 * (a * K + e) + f), *)
(* K the value of work word 4 of s.                                          *)
let BW_ENT_AS_READ = prove
 (`!st s a e f E.
     tisa_base s 3 = tisa_base st 3 /\
     E = 8 * (16 + 4 * (a * val(bw_w s 4) + e) + f)
     ==> bw_ent s a e f = tisa_read s (word_add (tisa_base st 3) (word E)) 8`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[bw_ent; bw_w]);;

(* The low three bits and the rest of a word. *)
let BW_VAL_AND7 = prove
 (`!x:int64. val(word_and x (word 7)) = val x MOD 8`,
  GEN_TAC THEN
  SUBGOAL_THEN `word 7:int64 = word(2 EXP 3 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* A key word tag + 8a, exactly when 8a + tag does not wrap. *)
let BW_KEY_FIELDS = prove
 (`!(x:int64) tag. tag < 8 /\ 8 * val x + tag < 2 EXP 64
                   ==> val(word_add (word_shl x 3) (word tag)) MOD 8 = tag /\
                       val(word_add (word_shl x 3) (word tag)) DIV 8 = val x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add (word_shl x 3) (word tag):int64) = 8 * val x + tag` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `(8 * val(x:int64)) MOD 18446744073709551616 = 8 * val x /\
                  tag MOD 18446744073709551616 = tag` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN BW_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOD_LT THEN BW_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(8 = 0)`; DIV_LT] THEN ARITH_TAC]);;

let TISA_BOOL_01 = prove
 (`tisa_bool (word 0:int64) /\ tisa_bool (word 1:int64)`,
  REWRITE_TAC[tisa_bool; VAL_WORD_0; VAL_WORD_1] THEN ARITH_TAC);;

let WORD_1_NE_0 = prove
 (`~(word 1:int64 = word 0)`,
  CONV_TAC WORD_REDUCE_CONV);;

(* Two states with one frame register and one memory show one view. *)
let BW_SAME_VIEWS = prove
 (`!s t. tregs s 0 = tregs t 0 /\ tmem s = tmem t
         ==> intern_count s = intern_count t /\ (!i. intern_word s i = intern_word t i) /\
             (!p. intern_slot s p = intern_slot t p) /\ (!k. bw_w s k = bw_w t k) /\
             (!i. tisa_fword s i = tisa_fword t i) /\ intern_slots s = intern_slots t /\
             (!r. tisa_len s r = tisa_len t r) /\ (!r. tisa_base s r = tisa_base t r) /\
             (!c. bw_iok s c <=> bw_iok t c) /\ (!c. bw_rows s c = bw_rows t c)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TISA_SAME_VIEW) THEN
  SUBGOAL_THEN `bw_w s = bw_w t /\ intern_word s = intern_word t /\
                intern_count s = intern_count t /\ tisa_fword s = tisa_fword t /\
                intern_slot s = intern_slot t /\ intern_slots s = intern_slots t /\
                intern_pos s = intern_pos t /\ tisa_len s = tisa_len t /\
                tisa_base s = tisa_base t`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; bw_w; intern_word; intern_count; intern_slot; intern_slots;
                intern_pos] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bw_row s = bw_row t` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; bw_row] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[bw_rows; bw_iok; bw_complete; bw_distinct; intern_has]);;

(* A path whose condition is word 1 = word 0 (a register known to be 1     *)
(* compared with 0) is impossible.                                          *)
let BW_CONTRA_TAC : tactic =
  FIRST_ASSUM(fun th -> let c = concl th in
    if c = `word 1:int64 = word 0` then CONTR_TAC(REWRITE_RULE[WORD_1_NE_0] th)
    else if c = `word 0:int64 = word 1` then CONTR_TAC(REWRITE_RULE[GSYM WORD_1_NE_0] th)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The claims of each step, from word-level facts.                           *)
(* ------------------------------------------------------------------------- *)

(* A row's words as the generator reads them (row index shifted, then scaled). *)
let BW_ROW_READ = prove
 (`!st s (i:int64).
     tisa_base s 0 = tisa_base st 0 /\ val i < 2 EXP 62
     ==> intern_word s (2 * val i) =
         tisa_read s (word_add (tisa_base st 0) (word (8 * val(word_shl i 1)))) 8 /\
         intern_word s (2 * val i + 1) =
         tisa_read s (word_add (tisa_base st 0) (word (8 * val(word_shl i 1) + 8))) 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_shl (i:int64) 1) = 2 * val i` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_SHL1 THEN BW_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[intern_word; ARITH_RULE `8 * (2 * x + 1) = 8 * (2 * x) + 8`]);;

(* Row i of the rows the walk started from, from its words in s. *)
let BW_ROW_TRIPLE = prove
 (`!st s (i:int64) (k0:int64) (k1:int64).
     bw_mid st s /\ val i < val(intern_count st) /\
     intern_word s (2 * val i) = k0 /\ intern_word s (2 * val i + 1) = k1
     ==> val i < LENGTH(bw_rows st (val(intern_count st))) /\
         EL (val i) (bw_rows st (val(intern_count st))) = (val k0 MOD 8, val k0 DIV 8, val k1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_mid] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LENGTH_BW_ROWS; EL_BW_ROWS; bw_row] THEN
  SUBGOAL_THEN `2 * val(i:int64) < 2 * val(intern_count st) /\ 2 * val i + 1 < 2 * val(intern_count st)`
   STRIP_ASSUME_TAC THENL [BW_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let BW_EXT_MID = prove
 (`!st s. bw_mid st s
          ==> bw_ext (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_mid] THEN STRIP_TAC THEN
  MATCH_MP_TAC BW_ROWS_EXT THEN ASM_SIMP_TAC[]);;

(* A word equals x << 3 exactly when its tag is 0 and its rest is x. *)
let BW_SHL3_EQ = prove
 (`!(k0:int64) (x:int64). val x < 2 EXP 60
                          ==> (k0 = word_shl x 3 <=> val k0 MOD 8 = 0 /\ val k0 DIV 8 = val x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `val(word_shl (x:int64) 3) = 8 * val x` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_SHL; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC MOD_LT THEN BW_ARITH_TAC;
    EQ_TAC THENL
     [DISCH_THEN SUBST1_TAC THEN SIMP_TAC[MOD_MULT; DIV_MULT; ARITH_EQ];
      STRIP_TAC THEN MP_TAC(SPECL [`val(k0:int64)`; `8`] DIVISION) THEN
      ASM_REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC]]);;

(* The claim of a row of tag 0, 1 or 2 other than the variable: itself. *)
let BW_RES_LEAF = prove
 (`!st s (i:int64) (n:int64) (k0:int64) (k1:int64).
     bw_mid st s /\ bw_entered st /\
     (val i < val(intern_count st)
      ==> intern_word s (2 * val i) = k0 /\ intern_word s (2 * val i + 1) = k1) /\
     val k0 MOD 8 < 3 /\ ~(k0 = word_shl (tisa_fword st 22) 3 /\ k1 = tisa_fword st 23)
     ==> bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
                  (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val i) (val n) (val i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `val(i:int64) < val(intern_count st)` THENL
   [ALL_TAC; MATCH_MP_TAC BW_CLAIM_VACUOUS THEN ASM_REWRITE_TAC[LENGTH_BW_ROWS]] THEN
  MP_TAC(SPECL [`st:tisa_state`; `s:tisa_state`; `i:int64`; `k0:int64`; `k1:int64`] BW_ROW_TRIPLE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC BW_CLAIM_SELF THEN
  MAP_EVERY EXISTS_TAC [`val(k0:int64) MOD 8`; `val(k0:int64) DIV 8`; `val(k1:int64)`] THEN
  ASM_SIMP_TAC[BW_EXT_MID] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_entered] o
              check (fun th -> concl th = `bw_entered st`)) THEN
  ASM_SIMP_TAC[BW_SHL3_EQ; GSYM VAL_EQ] THEN BW_ARITH_TAC);;

(* The variable itself: any row r of the key (1 + 8n, 0) claims hbind. *)
let BW_RES_BOUND = prove
 (`!st s (i:int64) (n:int64) D r.
     bw_mid st s /\ bw_entered st /\
     (val i < val(intern_count st)
      ==> intern_word s (2 * val i) = word_shl (tisa_fword st 22) 3 /\
          intern_word s (2 * val i + 1) = tisa_fword st 23) /\
     val n < 2 EXP 60 /\
     r < LENGTH D /\
     EL r D = (val(word_add (word_shl n 3) (word 1)) MOD 8,
               val(word_add (word_shl n 3) (word 1)) DIV 8, val(word 0:int64))
     ==> bw_claim (bw_rows st (val(intern_count st))) D
                  (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val i) (val n) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `val(i:int64) < val(intern_count st)` THENL
   [ALL_TAC; MATCH_MP_TAC BW_CLAIM_VACUOUS THEN ASM_REWRITE_TAC[LENGTH_BW_ROWS]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_entered] o
              check (fun th -> concl th = `bw_entered st`)) THEN
  MP_TAC(SPECL [`st:tisa_state`; `s:tisa_state`; `i:int64`;
                `word_shl (tisa_fword st 22) 3`; `tisa_fword st 23`] BW_ROW_TRIPLE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`n:int64`; `1`] BW_KEY_FIELDS) THEN
  ANTS_TAC THENL [BW_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC BW_CLAIM_BOUND THEN EXISTS_TAC `0` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can (find_term ((=) `EL (val(i:int64)):(num#num#num)list->num#num#num`)) (concl th)
                          then REWRITE_TAC[th] else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_0]) THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
  MP_TAC(SPECL [`word_shl (tisa_fword st 22) 3`; `tisa_fword st 22`] BW_SHL3_EQ) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* dbComb(a, b) with both results unchanged: the row itself. *)
let BW_RES_COMB_SAME = prove
 (`!st s (i:int64) (n:int64) (k0:int64) (b:int64) (ia:int64) (na:int64) (ra:int64)
    (ib:int64) (nb:int64) (rb:int64).
     bw_mid st s /\
     (val i < val(intern_count st)
      ==> intern_word s (2 * val i) = k0 /\ intern_word s (2 * val i + 1) = b) /\
     val k0 MOD 8 = 3 /\
     bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
              (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val ia) (val na) (val ra) /\
     bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
              (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val ib) (val nb) (val rb) /\
     ia = word_ushr k0 3 /\ na = n /\ ib = b /\ nb = n /\ ra = word_ushr k0 3 /\ rb = b
     ==> bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
                  (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val i) (val n) (val i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `val(i:int64) < val(intern_count st)` THENL
   [ALL_TAC; MATCH_MP_TAC BW_CLAIM_VACUOUS THEN ASM_REWRITE_TAC[LENGTH_BW_ROWS]] THEN
  MP_TAC(SPECL [`st:tisa_state`; `s:tisa_state`; `i:int64`; `k0:int64`; `b:int64`] BW_ROW_TRIPLE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC BW_CLAIM_COMB_SAME THEN
  MAP_EVERY EXISTS_TAC [`val(k0:int64) DIV 8`; `val(b:int64)`] THEN
  ASM_SIMP_TAC[BW_EXT_MID] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
                                                       type_of(lhand(concl th)) = `:int64`))) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(REWRITE_CONV[VAL_WORD_USHR] THENC NUM_REDUCE_CONV))) THEN
  ASM_REWRITE_TAC[]);;

(* dbComb(a, b): any row r of the key dbComb(ra, rb) claims hbind. *)
let BW_RES_COMB_KEY = prove
 (`!st s (i:int64) (n:int64) (k0:int64) (b:int64) (ia:int64) (na:int64) (ra:int64)
    (ib:int64) (nb:int64) (rb:int64) D r.
     bw_mid st s /\
     (val i < val(intern_count st)
      ==> intern_word s (2 * val i) = k0 /\ intern_word s (2 * val i + 1) = b) /\
     val k0 MOD 8 = 3 /\
     bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
              (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val ia) (val na) (val ra) /\
     bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
              (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val ib) (val nb) (val rb) /\
     ia = word_ushr k0 3 /\ na = n /\ ib = b /\ nb = n /\
     bw_ext (bw_rows s (val(bw_w s 0))) D /\ LENGTH D <= val(tisa_len st 0) DIV 16 /\
     r < LENGTH D /\
     EL r D = (val(word_add (word_shl ra 3) (word 3)) MOD 8,
               val(word_add (word_shl ra 3) (word 3)) DIV 8, val rb)
     ==> bw_claim (bw_rows st (val(intern_count st))) D
                  (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val i) (val n) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `val(i:int64) < val(intern_count st)` THENL
   [ALL_TAC; MATCH_MP_TAC BW_CLAIM_VACUOUS THEN ASM_REWRITE_TAC[LENGTH_BW_ROWS]] THEN
  MP_TAC(SPECL [`st:tisa_state`; `s:tisa_state`; `i:int64`; `k0:int64`; `b:int64`] BW_ROW_TRIPLE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC BW_CLAIM_COMB THEN
  MAP_EVERY EXISTS_TAC [`val(k0:int64) DIV 8`; `val(b:int64)`; `val(ra:int64)`; `val(rb:int64)`] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
                                                       type_of(lhand(concl th)) = `:int64`))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BW_CLAIM_EXT THEN EXISTS_TAC `bw_rows s (val(bw_w s 0))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `word_ushr (k0:int64) 3`)) (concl th) &&
                                            can (find_term ((=) `bw_claim`)) (concl th))) THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    MATCH_MP_TAC BW_CLAIM_EXT THEN EXISTS_TAC `bw_rows s (val(bw_w s 0))` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`ra:int64`; `3`] BW_KEY_FIELDS) THEN
    ANTS_TAC THENL [MP_TAC(ISPEC `tisa_len st 0` VAL_BOUND_64) THEN BW_ARITH_TAC; SIMP_TAC[]]]);;

(* dbAbs(A, b) with the body's result unchanged: the row itself. *)
let BW_RES_ABS_SAME = prove
 (`!st s (i:int64) (n:int64) (k0:int64) (b:int64) (ib:int64) (nb:int64) (rb:int64).
     bw_mid st s /\
     (val i < val(intern_count st)
      ==> intern_word s (2 * val i) = k0 /\ intern_word s (2 * val i + 1) = b) /\
     val k0 MOD 8 = 4 /\ val n < 2 EXP 60 /\
     bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
              (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val ib) (val nb) (val rb) /\
     ib = b /\ nb = word_add n (word 1) /\ rb = b
     ==> bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
                  (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val i) (val n) (val i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `val(i:int64) < val(intern_count st)` THENL
   [ALL_TAC; MATCH_MP_TAC BW_CLAIM_VACUOUS THEN ASM_REWRITE_TAC[LENGTH_BW_ROWS]] THEN
  MP_TAC(SPECL [`st:tisa_state`; `s:tisa_state`; `i:int64`; `k0:int64`; `b:int64`] BW_ROW_TRIPLE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC BW_CLAIM_ABS_SAME THEN
  MAP_EVERY EXISTS_TAC [`val(k0:int64) DIV 8`; `val(b:int64)`] THEN
  ASM_SIMP_TAC[BW_EXT_MID] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
                                                       type_of(lhand(concl th)) = `:int64`))) THEN
  SUBGOAL_THEN `val(word_add (n:int64) (word 1)) = val n + 1` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(* dbAbs(A, b): any row r of the key dbAbs(A, rb), whose first word is row  *)
(* i's, claims hbind.                                                         *)
let BW_RES_ABS_KEY = prove
 (`!st s (i:int64) (n:int64) (k0:int64) (b:int64) (ib:int64) (nb:int64) (rb:int64) D r.
     bw_mid st s /\
     (val i < val(intern_count st)
      ==> intern_word s (2 * val i) = k0 /\ intern_word s (2 * val i + 1) = b) /\
     val k0 MOD 8 = 4 /\ val n < 2 EXP 60 /\
     bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
              (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val ib) (val nb) (val rb) /\
     ib = b /\ nb = word_add n (word 1) /\
     bw_ext (bw_rows s (val(bw_w s 0))) D /\ r < LENGTH D /\
     EL r D = (val k0 MOD 8, val k0 DIV 8, val rb)
     ==> bw_claim (bw_rows st (val(intern_count st))) D
                  (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val i) (val n) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `val(i:int64) < val(intern_count st)` THENL
   [ALL_TAC; MATCH_MP_TAC BW_CLAIM_VACUOUS THEN ASM_REWRITE_TAC[LENGTH_BW_ROWS]] THEN
  MP_TAC(SPECL [`st:tisa_state`; `s:tisa_state`; `i:int64`; `k0:int64`; `b:int64`] BW_ROW_TRIPLE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC BW_CLAIM_ABS THEN
  MAP_EVERY EXISTS_TAC [`val(k0:int64) DIV 8`; `val(b:int64)`; `val(rb:int64)`] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
                                                       type_of(lhand(concl th)) = `:int64`))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word_add (n:int64) (word 1)) = val n + 1` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC BW_CLAIM_EXT THEN EXISTS_TAC `bw_rows s (val(bw_w s 0))` THEN ASM_REWRITE_TAC[]);;

(* The end: any row r of the key dbAbs(ty, rt), rt the result for (t, 0),   *)
(* is the walk's whole claim.                                                *)
let BW_RES_LAST_KEY = prove
 (`!st s (it:int64) (nt:int64) (rt:int64) D r.
     bw_mid st s /\ bw_entered st /\
     bw_claim (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
              (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val it) (val nt) (val rt) /\
     it = tregs st 1 /\ nt = word 0 /\
     bw_ext (bw_rows s (val(bw_w s 0))) D /\ r < LENGTH D /\
     EL r D = (val(word_add (word_shl (tisa_fword st 23) 3) (word 4)) MOD 8,
               val(word_add (word_shl (tisa_fword st 23) 3) (word 4)) DIV 8, val rt)
     ==> bw_final (bw_rows st (val(intern_count st))) D
                  (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val(tregs st 1)) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_entered] o
              check (fun th -> concl th = `bw_entered st`)) THEN
  MP_TAC(SPECL [`tisa_fword st 23`; `4`] BW_KEY_FIELDS) THEN
  ANTS_TAC THENL [BW_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC BW_FINAL_ABS THEN EXISTS_TAC `val(rt:int64)` THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
                                                       type_of(lhand(concl th)) = `:int64`))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_0]) THEN
  MATCH_MP_TAC BW_CLAIM_EXT THEN EXISTS_TAC `bw_rows s (val(bw_w s 0))` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The invariant after the prologue: a state that shows the entry state's    *)
(* frame, header, rows and slots, with the work header initialised (c the   *)
(* published count, K, t, one task, no results, an empty log).               *)
(* ------------------------------------------------------------------------- *)

let BW_MID_INIT = prove
 (`!st s.
     bw_regions st /\ bw_entered st /\
     tregs s 0 = tregs st 0 /\ (!i. i < 24 ==> tisa_fword s i = tisa_fword st i) /\
     intern_count s = intern_count st /\
     (!i. i < 2 * val(intern_count st) ==> intern_word s i = intern_word st i) /\
     (!p. val p < val(intern_slots st) ==> intern_slot s p = intern_slot st p) /\
     bw_w s 0 = intern_count st /\
     val(bw_w s 4) = val(tisa_len st 3) DIV 128 - 1 /\ bw_w s 5 = tregs st 1 /\
     val(bw_w s 1) <= val(bw_w s 4) /\ val(bw_w s 2) = 0 /\ val(bw_w s 3) = 0
     ==> bw_mid st s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_entered] o
              check (fun th -> concl th = `bw_entered st`)) THEN
  REWRITE_TAC[bw_mid] THEN ASM_REWRITE_TAC[LT; LE_0; LE_REFL] THEN
  DISCH_TAC THEN MATCH_MP_TAC BW_IOK_TRANSFER THEN EXISTS_TAC `st:tisa_state` THEN
  ASM_REWRITE_TAC[GSYM INTERN_OK_BW] THEN
  SUBGOAL_THEN `intern_slots s = intern_slots st /\ tisa_len s 0 = tisa_len st 0`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[intern_slots; tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH_RULE `1 < 24 /\ 3 < 24`]);;

(* A stop of the prologue: the entry state's memory with status and return  *)
(* words written.                                                            *)
let BW_RESULT_STOP_ENTRY = prove
 (`!st X k (v:int64).
     bw_regions st /\ tregs X 0 = tregs st 0 /\ tmem X = tmem st /\ ~(k = 1)
     ==> bw_result st k (tisa_finst k v X)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X:tisa_state`; `st:tisa_state`] BW_SAME_VIEWS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `X:tisa_state`; `k:num`; `v:int64`] BW_FINST_KEEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `intern_count (tisa_finst k v X) = intern_count st /\
                (!i. i < 2 * (val(tisa_len st 0) DIV 16)
                     ==> intern_word (tisa_finst k v X) i = intern_word st i) /\
                (!p. val p < val(intern_slots st)
                     ==> intern_slot (tisa_finst k v X) p = intern_slot st p)`
   STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[bw_result] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[INTERN_OK_BW] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC BW_IOK_TRANSFER THEN EXISTS_TAC `st:tisa_state` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[bw_iok] o
                  check (fun th -> can (find_term ((=) `bw_iok`)) (concl th))) THEN
    BW_ARITH_TAC;
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN BW_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The views of a later state (not a variable), unfolded so the generator's  *)
(* memory normal form can read them through the stores and the finish.      *)
(* ------------------------------------------------------------------------- *)

let BW_VIEW_DEFS =
  [`bw_w`, bw_w; `bw_ent`, bw_ent; `intern_count`, intern_count; `intern_slots`, intern_slots;
   `intern_word`, intern_word; `intern_slot`, intern_slot; `tisa_fword`, tisa_fword;
   `tisa_base`, tisa_base; `tisa_len`, tisa_len; `tisa_frame`, tisa_frame];;

let BW_UNFOLD_LATER_CONV =
  fun t -> let h,args = strip_comb t in
    match args with
      s::_ when not(is_var s) && can (assoc h) BW_VIEW_DEFS -> REWR_CONV (assoc h BW_VIEW_DEFS) t
    | _ -> failwith "BW_UNFOLD_LATER_CONV";;

(* Unfold every view, of later states and of variable ones. *)
let BW_UNFOLD_ALL_CONV =
  fun t -> let h,args = strip_comb t in
    match args with
      _::_ when can (assoc h) BW_VIEW_DEFS -> REWR_CONV (assoc h BW_VIEW_DEFS) t
    | _ -> failwith "BW_UNFOLD_ALL_CONV";;

(* A view equality of a later state with a variable one: unfold the later    *)
(* state's views, read through the writes, then unfold the rest and compare. *)
let BW_VIEW_TAC =
  CONV_TAC(TOP_DEPTH_CONV BW_UNFOLD_LATER_CONV) THEN CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN
  TISA_STATE_NORM_TAC THEN
  TRY(CONV_TAC(TOP_DEPTH_CONV BW_UNFOLD_ALL_CONV) THEN CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN
      TISA_STATE_NORM_TAC THEN NO_TAC) THEN
  TRY(TISA_ARITH_DECIDE_TAC);;

(* ------------------------------------------------------------------------- *)
(* The probe loop: from the interning block's entry state s (key in v1, v2,  *)
(* the private count in work word 0), before probe j.                        *)
(* ------------------------------------------------------------------------- *)

let bw_probing = new_definition
 `bw_probing s (N:num) j u <=>
    tregs u 0 = tregs s 0 /\ tmem u = tmem s /\
    tregs u 1 = tregs s 1 /\ tregs u 2 = tregs s 2 /\
    tregs u 10 = tregs s 10 /\ tregs u 11 = tregs s 11 /\
    tregs u 6 = intern_hash (tregs s 1) (tregs s 2) /\
    tregs u 8 = intern_slots s /\ tregs u 9 = word 1 /\
    N = val(intern_slots s) /\
    (!x. x < j ==> bw_probed s (val(bw_w s 0)) (tregs s 1) (tregs s 2) x)`;;

let BW_PROBED_STEP = prove
 (`!s c k0 k1 j. (!x. x < j ==> bw_probed s c k0 k1 x) /\ bw_probed s c k0 k1 j
                 ==> !x. x < j + 1 ==> bw_probed s c k0 k1 x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:num = j` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN BW_ARITH_TAC);;

(* The facts about s the probe proofs use, as the generator states them. *)
let bw_s_facts = new_definition
 `bw_s_facts st s <=>
    bw_regions st /\ tregs s 0 = tregs st 0 /\
    (!i. i < 24 ==> tisa_fword s i = tisa_fword st i) /\
    val(bw_w s 0) <= val(tisa_len st 0) DIV 16`;;

let BW_MID_S_FACTS = prove
 (`!st s. bw_regions st /\ bw_mid st s ==> bw_s_facts st s`,
  SIMP_TAC[bw_mid; bw_s_facts]);;

(* The frame words of s as unconditional rewrites for the generator, and the *)
(* region facts as arithmetic.                                               *)
let BW_S_SETUP_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_s_facts] o
              check (fun th -> can (find_term ((=) `bw_s_facts`)) (concl th))) THEN
  FIRST_ASSUM((REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o GEN_REWRITE_RULE I [bw_regions] o
              check (fun th -> concl th = `bw_regions st`)) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `tisa_fword s`)) (concl th) &&
       can (find_term ((=) `tisa_fword st`)) (concl th)
    then MAP_EVERY (fun i -> ASSUME_TAC(MP (SPEC (mk_small_numeral i) th)
                                           (EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool`
                                              (mk_small_numeral i) `24`)))))
                   [0;1;2;3;4;5;6;7;22;23]
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Addresses of work stores as word_add W (word (8 * k)).                    *)
(* ------------------------------------------------------------------------- *)

let bw_add_tm = `(+):num->num->num` and bw_mul_tm = `( * ):num->num->num`;;

let rec bw_sum_terms t =
  if is_binop bw_add_tm t then bw_sum_terms (lhand t) @ bw_sum_terms (rand t) else [t];;

(* k with e = 8 * k, for e a sum of numerals divisible by 8 and 8 * X terms. *)
let bw_k_of e =
  let k_of p =
    if is_numeral p then
      let n = dest_small_numeral p in
      if n mod 8 = 0 then mk_small_numeral(n / 8)
      else failwith "bw_k_of: unaligned"
    else if is_binop bw_mul_tm p && lhand p = `8` then rand p
    else failwith "bw_k_of" in
  end_itlist (fun a b -> mk_binop bw_add_tm a b) (map k_of (bw_sum_terms e));;

let bw_w3_tm = `tisa_base st 3`;;

(* The address of a store into the work region, as word_add W (word(8 * k)). *)
let BW_WADDR_CONV a =
  if a = bw_w3_tm then
    SYM(REWRITE_CONV[MULT_CLAUSES; WORD_ADD_0] (mk_comb(mk_comb(`word_add:int64->int64->int64`, a),
                                                        `word(8 * 0):int64`)))
  else
    let e = rand(rand a) in
    let k = bw_k_of e in
    let target = mk_comb(mk_comb(`word_add:int64->int64->int64`, lhand a),
                         mk_comb(`word:num->int64`, mk_binop bw_mul_tm `8` k)) in
    prove(mk_eq(a, target), AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Folding the generator's reads of entries of the entry state s into        *)
(* bw_ent s a e f, for given candidates (a, e): a read at W + E is field f   *)
(* of entry e of area a when E = 8 * (16 + 4 * (a * K + e) + f).             *)
(* ------------------------------------------------------------------------- *)

let bw_entry_reads s tm =
  find_terms (fun t ->
    let h,args = strip_comb t in
    h = `tisa_read` && length args = 3 && hd args = s && el 2 args = `8` &&
    (let a = el 1 args in
     is_comb a && is_comb(rator a) && rator(rator a) = `word_add:int64->int64->int64` &&
     lhand a = `tisa_base st 3` &&
     (let w = rand a in is_comb w && rator w = `word:num->int64` && not(is_numeral(rand w))))) tm;;

(* Path conditions ~(x = word 0) as arithmetic: ~(val x = 0). *)
let BW_NZ_VAL_TAC : tactic =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_neg c && is_eq(dest_neg c) && rand(dest_neg c) = `word 0:int64`
    then REWRITE_RULE[GSYM VAL_EQ_0] th else th);;

(* Prove read = bw_ent s a e f for one read, trying the candidates. *)
let BW_FOLD_ONE s cands r (asl,w) =
  let try_cand (a,e,f) =
    let target = list_mk_comb(`bw_ent`, [s; a; e; f]) in
    let goal = mk_eq(target, r) in
    let tac = MATCH_MP_TAC BW_ENT_AS_READ THEN CONJ_TAC THENL
               [FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REWRITE_TAC[];
                BW_NZ_VAL_TAC THEN TISA_WP_VAL_FACTS_TAC THEN BW_ARITH_TAC] in
    let (_,gl,just) = tac (asl,goal) in
    if gl <> [] then failwith "BW_FOLD_ONE: unsolved" else just null_inst [] in
  let cands3 = flat (map (fun (a,e) -> map (fun f -> (a,e,mk_small_numeral f)) [0;1;2]) cands) in
  tryfind (fun c -> try_cand c) cands3;;

(* Rewrite every entry read with its bw_ent form, in the goal and assumptions. *)
let BW_FOLD_ENTS_TAC s cands : tactic = fun (asl,w) ->
  let reads = setify (bw_entry_reads s (list_mk_conj(w :: map (concl o snd) asl))) in
  let eqs = mapfilter (fun r -> GSYM(BW_FOLD_ONE s cands r (asl,w))) reads in
  (RULE_ASSUM_TAC(REWRITE_RULE eqs) THEN REWRITE_TAC eqs) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Reading work words, entries and rows of a later state: a chain of        *)
(* register writes and 8-byte stores into the work region over a state     *)
(* whose frame is st's. Each store's word is compared with the word read   *)
(* by arithmetic over the assumptions; the frame of every state on the     *)
(* chain is st's (bw_frame).                                                *)
(* ------------------------------------------------------------------------- *)

let bw_frame = new_definition
 `bw_frame st X <=> tregs X 0 = tregs st 0 /\ (!i. i < 24 ==> tisa_fword X i = tisa_fword st i)`;;

let BW_FRAME_SETREG = prove
 (`!st X d (v:int64). bw_frame st X /\ ~(d = 0) ==> bw_frame st (tisa_setreg d v X)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_frame] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tisa_setreg d v X`; `X:tisa_state`] TISA_SAME_VIEW) THEN
  ASM_REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG; ARITH_RULE `0 = d <=> d = 0`] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

let BW_FRAME_WSTORE = prove
 (`!st X k (v:int64). bw_regions st /\ bw_frame st X /\ 8 * k + 8 <= val(tisa_len st 3)
                      ==> bw_frame st (tisa_store (word_add (tisa_base st 3) (word (8 * k))) 8 v X)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_frame] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `X:tisa_state`; `k:num`; `v:int64`] BW_WORK_STORE) THEN
  ASM_SIMP_TAC[]);;

let BW_W_SETREG = prove
 (`!X d (v:int64) k. ~(d = 0) ==> bw_w (tisa_setreg d v X) k = bw_w X k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tisa_setreg d v X`; `X:tisa_state`] BW_SAME_VIEWS) THEN
  ASM_REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG; ARITH_RULE `0 = d <=> d = 0`] THEN
  SIMP_TAC[]);;

let BW_W_WSTORE = prove
 (`!st X k (v:int64) k'.
     bw_regions st /\ bw_frame st X /\ 8 * k + 8 <= val(tisa_len st 3) /\
     8 * k' + 8 <= val(tisa_len st 3)
     ==> bw_w (tisa_store (word_add (tisa_base st 3) (word (8 * k))) 8 v X) k' =
         if k' = k then v else bw_w X k'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_frame] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `X:tisa_state`; `k:num`; `v:int64`] BW_WORK_STORE) THEN
  ASM_SIMP_TAC[]);;

let BW_ROWS_SETREG = prove
 (`!X d (v:int64) c. ~(d = 0) ==> bw_rows (tisa_setreg d v X) c = bw_rows X c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tisa_setreg d v X`; `X:tisa_state`] BW_SAME_VIEWS) THEN
  ASM_REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG; ARITH_RULE `0 = d <=> d = 0`] THEN
  SIMP_TAC[]);;

let BW_ROWS_WSTORE = prove
 (`!st X k (v:int64) c.
     bw_regions st /\ bw_frame st X /\ 8 * k + 8 <= val(tisa_len st 3) /\
     c <= val(tisa_len st 0) DIV 16
     ==> bw_rows (tisa_store (word_add (tisa_base st 3) (word (8 * k))) 8 v X) c = bw_rows X c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_frame] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `X:tisa_state`; `k:num`; `v:int64`] BW_WORK_STORE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC BW_ROWS_EQ THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN BW_ARITH_TAC);;

(* Value facts of the goal's word terms (tisa_wp.ml's TISA_VAL_FACTS_TAC,    *)
(* their side conditions by focused arithmetic), then arithmetic.           *)
let BW_COND_FACT_TAC th =
  let ante = lhand(concl th) in
  TRY(SUBGOAL_THEN ante (fun a -> ASSUME_TAC(MP th a)) THENL [BW_ARITH_TAC; ALL_TAC]);;

let BW_VAL_FACT_TAC t =
  let u = rand t in
  let h,args = strip_comb u in
  match tisa_const_name h, args with
    "word_and", [x;y] ->
      ASSUME_TAC(ISPECL [x;y] (CONJUNCT1 VAL_WORD_AND_LE)) THEN
      ASSUME_TAC(ISPECL [x;y] (CONJUNCT2 VAL_WORD_AND_LE))
  | "word_ushr", [x;n] when is_numeral n ->
      ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV (ISPECL [x;n] VAL_WORD_USHR))
  | "word", [n] when is_numeral n ->
      ASSUME_TAC((REWRITE_CONV[VAL_WORD; DIMINDEX_64] THENC NUM_REDUCE_CONV) t)
  | "word_add", [x;y] -> BW_COND_FACT_TAC(ISPECL [x;y] TISA_VAL_ADD_EXACT)
  | "word_sub", [x;y] -> BW_COND_FACT_TAC(ISPECL [x;y] TISA_VAL_SUB_EXACT)
  | "word_shl", [x;n] when is_numeral n ->
      BW_COND_FACT_TAC(CONV_RULE NUM_REDUCE_CONV (ISPECL [x;n] TISA_VAL_SHL_EXACT))
  | "word", [n] -> BW_COND_FACT_TAC(ISPEC n TISA_VAL_WORD_EXACT)
  | _ -> ASSUME_TAC(ISPEC u VAL_BOUND_64);;

let BW_VAL_FACTS_TAC : tactic = fun (asl,w) ->
  let seen = ref [] and order = ref [] in
  let rec visit t =
    if mem t !seen then () else
    (seen := t :: !seen; List.iter visit (tisa_val_children t); order := t :: !order) in
  let wordop t = mem (tisa_const_name (fst(strip_comb(rand t))))
                   ["word_and"; "word_add"; "word_sub"; "word_ushr"; "word_shl"; "word"] in
  (* the arithmetic assumptions' word terms first: a goal fact can need them *)
  List.iter (fun (_,th) -> let c = concl th in
               if not (is_forall c) && tisa_focus_arith_fm c
               then List.iter visit (filter wordop (find_terms tisa_is_val64 c)))
            asl;
  List.iter visit (find_terms tisa_is_val64 w);
  MAP_EVERY BW_VAL_FACT_TAC (rev !order) (asl,w);;

(* val(word n) for a numeral n, as a number. *)
let BW_VAL_NUM_CONV t =
  match t with
    Comb(Const("val",_),Comb(Const("word",_),n)) when is_numeral n ->
      (REWRITE_CONV[VAL_WORD; DIMINDEX_64] THENC NUM_REDUCE_CONV) t
  | _ -> failwith "BW_VAL_NUM_CONV";;

let BW_SIDE_ARITH_TAC : tactic =
  BW_NZ_VAL_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV BW_VAL_NUM_CONV))) THEN
  CONV_TAC(TRY_CONV(DEPTH_CONV BW_VAL_NUM_CONV)) THEN
  BW_VAL_FACTS_TAC THEN BW_ARITH_TAC;;

(* Side conditions and frames, remembered within one use of BW_EVAL_TAC (the *)
(* theorems' hypotheses are that goal's assumptions).                        *)
let bw_side_cache = ref ([]:(term*thm)list);;
let bw_frame_cache = ref ([]:(term*thm)list);;

let bw_prove_side (asl:(string*thm)list) tm =
  try assoc tm !bw_side_cache with Failure _ ->
  let nz (n,th) = let c = concl th in
    if is_neg c && is_eq(dest_neg c) && rand(dest_neg c) = `word 0:int64`
    then (n, REWRITE_RULE[GSYM VAL_EQ_0] th) else (n,th) in
  let arith = filter (fun (_,th) -> let c = concl th in
                        not (is_forall c) && tisa_focus_arith_fm c) (map nz asl) in
  let th = TAC_PROOF((arith,tm), BW_SIDE_ARITH_TAC) in
  bw_side_cache := (tm,th) :: !bw_side_cache; th;;

(* The address of a work store, as word_add W (word (8 * k)). *)
let bw_waddr_eq a =
  if a = bw_w3_tm then BW_WADDR_CONV a
  else BW_WADDR_CONV a;;

(* bw_frame st X for a chain over a state with assumptions tregs s 0 and its *)
(* frame words equal to st's.                                                *)
let rec bw_frame_thm asl x =
  try assoc x !bw_frame_cache with Failure _ ->
  let th = bw_frame_thm0 asl x in
  bw_frame_cache := (x,th) :: !bw_frame_cache; th

and bw_frame_thm0 asl x =
  if is_var x then
    TAC_PROOF((asl, mk_comb(`bw_frame st`, x)),
              REWRITE_TAC[bw_frame] THEN ASM_REWRITE_TAC[] THEN
              FIRST_ASSUM(fun th -> if is_forall(concl th) &&
                                       can (find_term ((=) (mk_comb(`tisa_fword`, x)))) (concl th) &&
                                       can (find_term ((=) `tisa_fword st`)) (concl th)
                                    then ACCEPT_TAC th else NO_TAC))
  else
    let h,args = strip_comb x in
    match fst(dest_const h) with
      "tisa_setreg" ->
        let d = el 0 args and v = el 1 args and y = el 2 args in
        let fy = bw_frame_thm asl y in
        let nz = EQT_ELIM(NUM_REDUCE_CONV(mk_neg(mk_eq(d, `0`)))) in
        MATCH_MP (ISPECL [`st:tisa_state`; y; d; v] BW_FRAME_SETREG) (CONJ fy nz)
    | "tisa_store" ->
        let a = el 0 args and v = el 2 args and y = el 3 args in
        let aeq = bw_waddr_eq a in
        let k = rand(rand(rand(rhs(concl aeq)))) in
        let fy = bw_frame_thm asl y in
        let kb = bw_prove_side asl (mk_binop `(<=):num->num->bool`
                   (mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `8` k) `8`)
                   `val(tisa_len st 3)`) in
        let reg = snd(find (fun (_,th) -> concl th = `bw_regions st`) asl) in
        let th = MATCH_MP (ISPECL [`st:tisa_state`; y; k; v] BW_FRAME_WSTORE) (CONJ reg (CONJ fy kb)) in
        GEN_REWRITE_RULE (RAND_CONV o funpow 3 RATOR_CONV o RAND_CONV) [SYM aeq] th
    | _ -> failwith "bw_frame_thm";;

(* |- bw_w X k' = R, R in terms of the base state's work words. *)
let rec bw_w_eval asl t =
  let x = lhand t and k' = rand t in
  if is_var x then REFL t else
  let h,args = strip_comb x in
  match fst(dest_const h) with
    "tisa_setreg" ->
      let d = el 0 args and v = el 1 args and y = el 2 args in
      let nz = EQT_ELIM(NUM_REDUCE_CONV(mk_neg(mk_eq(d, `0`)))) in
      let th1 = MP (ISPECL [y; d; v; k'] BW_W_SETREG) nz in
      TRANS th1 (bw_w_eval asl (rhs(concl th1)))
  | "tisa_store" ->
      let a = el 0 args and v = el 2 args and y = el 3 args in
      let aeq = bw_waddr_eq a in
      let k = rand(rand(rand(rhs(concl aeq)))) in
      let fy = bw_frame_thm asl y in
      let kb = bw_prove_side asl (mk_binop `(<=):num->num->bool`
                 (mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `8` k) `8`)
                 `val(tisa_len st 3)`) in
      let kb' = bw_prove_side asl (mk_binop `(<=):num->num->bool`
                 (mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `8` k') `8`)
                 `val(tisa_len st 3)`) in
      let reg = snd(find (fun (_,th) -> concl th = `bw_regions st`) asl) in
      let th = MATCH_MP (ISPECL [`st:tisa_state`; y; k; v; k'] BW_W_WSTORE)
                        (CONJ reg (CONJ fy (CONJ kb kb'))) in
      let th = GEN_REWRITE_RULE (LAND_CONV o LAND_CONV o funpow 3 RATOR_CONV o RAND_CONV) [SYM aeq] th in
      let c = mk_eq(k',k) in
      (try let no = ARITH_RULE (mk_neg c) in
           let th2 = TRANS th (REWRITE_CONV[no] (rhs(concl th))) in
           TRANS th2 (bw_w_eval asl (rhs(concl th2)))
       with Failure _ ->
       try let yes = bw_prove_side asl c in
           TRANS th (REWRITE_CONV[yes] (rhs(concl th)))
       with Failure _ ->
       try let no = bw_prove_side asl (mk_neg c) in
           let th2 = TRANS th (REWRITE_CONV[no] (rhs(concl th))) in
           TRANS th2 (bw_w_eval asl (rhs(concl th2)))
       with Failure _ ->
           let r = bw_w_eval asl (mk_comb(mk_comb(`bw_w`, y), k')) in
           TRANS th (AP_TERM (mk_comb(mk_comb(`COND:bool->int64->int64->int64`, c), v)) r))
  | _ -> failwith "bw_w_eval";;

(* |- bw_rows X c = bw_rows s c for the chain's base s. *)
let rec bw_rows_eval asl t =
  let x = lhand t and c = rand t in
  if is_var x then REFL t else
  let h,args = strip_comb x in
  match fst(dest_const h) with
    "tisa_setreg" ->
      let d = el 0 args and v = el 1 args and y = el 2 args in
      let nz = EQT_ELIM(NUM_REDUCE_CONV(mk_neg(mk_eq(d, `0`)))) in
      let th1 = MP (ISPECL [y; d; v; c] BW_ROWS_SETREG) nz in
      TRANS th1 (bw_rows_eval asl (rhs(concl th1)))
  | "tisa_store" ->
      let a = el 0 args and v = el 2 args and y = el 3 args in
      let aeq = bw_waddr_eq a in
      let k = rand(rand(rand(rhs(concl aeq)))) in
      let fy = bw_frame_thm asl y in
      let kb = bw_prove_side asl (mk_binop `(<=):num->num->bool`
                 (mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `8` k) `8`)
                 `val(tisa_len st 3)`) in
      let cb = bw_prove_side asl (mk_binop `(<=):num->num->bool` c `val(tisa_len st 0) DIV 16`) in
      let reg = snd(find (fun (_,th) -> concl th = `bw_regions st`) asl) in
      let th = MATCH_MP (ISPECL [`st:tisa_state`; y; k; v; c] BW_ROWS_WSTORE)
                        (CONJ reg (CONJ fy (CONJ kb cb))) in
      let th = GEN_REWRITE_RULE (LAND_CONV o LAND_CONV o funpow 3 RATOR_CONV o RAND_CONV) [SYM aeq] th in
      TRANS th (bw_rows_eval asl (rhs(concl th)))
  | _ -> failwith "bw_rows_eval";;

(* Rewrite every work word, entry and row list of a later state in the goal: *)
(* entries become work words; innermost work words first (an entry's index  *)
(* reads K and the count of the same later state); then the row lists.      *)
let BW_EVAL_TAC : tactic = fun (asl,w) ->
  bw_side_cache := []; bw_frame_cache := [];
  let is_later_w t = let h,args = strip_comb t in
                     h = `bw_w` && length args = 2 && not(is_var(hd args)) in
  let tac1 = CONV_TAC(TOP_DEPTH_CONV(fun t -> let h,args = strip_comb t in
                if h = `bw_ent` && length args = 4 && not(is_var(hd args)) then REWR_CONV bw_ent t
                else failwith "")) in
  let rec words : tactic = fun (asl,w) ->
    let ws = setify(find_terms (fun t -> is_later_w t &&
                                  not (can (find_term is_later_w) (rand t))) w) in
    if ws = [] then ALL_TAC (asl,w)
    else (REWRITE_TAC (map (bw_w_eval asl) ws) THEN words) (asl,w) in
  let rows : tactic = fun (asl,w) ->
    let rs = setify(find_terms (fun t -> let h,args = strip_comb t in
                                 h = `bw_rows` && length args = 2 && not(is_var(hd args))) w) in
    REWRITE_TAC (map (bw_rows_eval asl) rs) (asl,w) in
  (TRY tac1 THEN words THEN rows) (asl,w);;

(* A read of the work region of a later state as its work word. *)
let BW_READ_AS_W = prove
 (`!st X k. bw_frame st X
            ==> tisa_read X (word_add (tisa_base st 3) (word (8 * k))) 8 = bw_w X k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_frame; bw_w] THEN STRIP_TAC THEN
  SUBGOAL_THEN `tisa_base X 3 = tisa_base st 3` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[tisa_base] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[ARITH_RULE `6 < 24`]);;

(* Reads of the work region of later states, in the goal, as work words. *)
let BW_READS_AS_W_TAC : tactic = fun (asl,w) ->
  bw_side_cache := []; bw_frame_cache := [];
  let rd t = let h,args = strip_comb t in
    h = `tisa_read` && length args = 3 && el 2 args = `8` && not(is_var(hd args)) &&
    (let a = el 1 args in
     is_comb a && is_comb(rator a) && rator(rator a) = `word_add:int64->int64->int64` &&
     lhand a = `tisa_base st 3` && can bw_k_of (rand(rand a))) in
  let rs = setify(find_terms rd w) in
  let eq t =
    let x = hd(snd(strip_comb t)) and a = el 1 (snd(strip_comb t)) in
    let aeq = BW_WADDR_CONV a in
    let k = rand(rand(rand(rhs(concl aeq)))) in
    let th = MP (ISPECL [`st:tisa_state`; x; k] BW_READ_AS_W) (bw_frame_thm asl x) in
    GEN_REWRITE_RULE (LAND_CONV o RATOR_CONV o RAND_CONV) [SYM aeq] th in
  REWRITE_TAC (map eq rs) (asl,w);;

(* The evaluation in the goal and in the assumptions: later reads of the    *)
(* work region as work words, then the words and rows evaluated.            *)
let BW_EVAL_ALL_TAC : tactic = fun (asl,w) ->
  bw_side_cache := []; bw_frame_cache := [];
  let all () = list_mk_conj(w :: map (concl o snd) asl) in
  let rd t = let h,args = strip_comb t in
    h = `tisa_read` && length args = 3 && el 2 args = `8` && not(is_var(hd args)) &&
    (let a = el 1 args in
     is_comb a && is_comb(rator a) && rator(rator a) = `word_add:int64->int64->int64` &&
     lhand a = `tisa_base st 3` && can bw_k_of (rand(rand a))) in
  let read_eq asl t =
    let x = hd(snd(strip_comb t)) and a = el 1 (snd(strip_comb t)) in
    let aeq = BW_WADDR_CONV a in
    let k = rand(rand(rand(rhs(concl aeq)))) in
    let th = MP (ISPECL [`st:tisa_state`; x; k] BW_READ_AS_W) (bw_frame_thm asl x) in
    GEN_REWRITE_RULE (LAND_CONV o RATOR_CONV o RAND_CONV) [SYM aeq] th in
  let is_later_w t = let h,args = strip_comb t in
                     h = `bw_w` && length args = 2 && not(is_var(hd args)) in
  let rw eqs = if eqs = [] then ALL_TAC
               else RULE_ASSUM_TAC(REWRITE_RULE eqs) THEN REWRITE_TAC eqs in
  let reads : tactic = fun (asl,w) ->
    let tm = list_mk_conj(w :: map (concl o snd) asl) in
    rw (map (read_eq asl) (setify(find_terms rd tm))) (asl,w) in
  let rec words : tactic = fun (asl,w) ->
    let tm = list_mk_conj(w :: map (concl o snd) asl) in
    let ws = setify(find_terms (fun t -> is_later_w t && not (can (find_term is_later_w) (rand t))) tm) in
    if ws = [] then ALL_TAC (asl,w)
    else (rw (map (bw_w_eval asl) ws) THEN words) (asl,w) in
  let rows : tactic = fun (asl,w) ->
    let tm = list_mk_conj(w :: map (concl o snd) asl) in
    let rs = setify(find_terms (fun t -> let h,args = strip_comb t in
                                 h = `bw_rows` && length args = 2 && not(is_var(hd args))) tm) in
    rw (map (bw_rows_eval asl) rs) (asl,w) in
  ignore (all ());
  (reads THEN words THEN rows) (asl,w);;

(* Work words of s at an entry's field, as bw_ent s a e f, in the goal and *)
(* the assumptions, for the candidate entries (a, e).                       *)
let BW_FOLD_W_TAC s cands : tactic = fun (asl,w) ->
  bw_side_cache := [];
  let tm = list_mk_conj(w :: map (concl o snd) asl) in
  let ws = setify(find_terms (fun t -> let h,args = strip_comb t in
                    h = `bw_w` && length args = 2 && hd args = s && not(is_numeral(el 1 args))) tm) in
  let fold t =
    let k = el 1 (snd(strip_comb t)) in
    tryfind (fun (a,e,f) ->
      let target = list_mk_comb(`bw_ent`, [s; a; e; f]) in
      let th = REWRITE_CONV[bw_ent] target in       (* bw_ent s a e f = bw_w s idx *)
      let idx = rand(rhs(concl th)) in
      let keq = bw_prove_side asl (mk_eq(k, idx)) in
      TRANS (AP_TERM (rator t) keq) (SYM th))
      (flat (map (fun (a,e) -> map (fun f -> (a,e,mk_small_numeral f)) [0;1;2]) cands)) in
  let eqs = mapfilter fold ws in
  (if eqs = [] then ALL_TAC else RULE_ASSUM_TAC(REWRITE_RULE eqs) THEN REWRITE_TAC eqs) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the walk's blocks.                                            *)
(* ------------------------------------------------------------------------- *)

(* The normalized form of work word k (a numeral) of a variable state s. *)
let BW_W_NORM_TAC =
  REWRITE_TAC[bw_w] THEN CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[WORD_ADD_0];;

(* Peel the writes of a later state X off down to the variable state whose   *)
(* invariant holds: register writes, and stores into the work region by     *)
(* BW_MID_STORE_W, its side conditions by reading the work words through the *)
(* writes (BW_EVAL_TAC) and arithmetic.                                      *)
let BW_SIDE_TAC =
  REWRITE_TAC[bw_wfree] THEN BW_EVAL_TAC THEN CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN
  BW_SIDE_ARITH_TAC;;

(* claim_tac proves the claim of a pushed result or log entry (bw_nclaim). *)
let rec BW_PEEL_MID_GEN_TAC claim_tac : tactic = fun (asl,w) ->
  let x = rand w in
  if is_var x then FIRST_ASSUM ACCEPT_TAC (asl,w) else
  let h,args = strip_comb x in
  match fst(dest_const h) with
    "tisa_setreg" ->
      (MATCH_MP_TAC BW_MID_SETREG THEN CONJ_TAC THENL
        [CONV_TAC NUM_REDUCE_CONV; BW_PEEL_MID_GEN_TAC claim_tac]) (asl,w)
  | "tisa_store" ->
      (CONV_TAC(RAND_CONV(RATOR_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV BW_WADDR_CONV))))) THEN
       MATCH_MP_TAC BW_MID_STORE_W THEN
       CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
       CONJ_TAC THENL [BW_PEEL_MID_GEN_TAC claim_tac; ALL_TAC] THEN
       CONJ_TAC THENL [BW_SIDE_ARITH_TAC; ALL_TAC] THEN
       BW_STORE_CASE_TAC claim_tac) (asl,w)
  | _ -> failwith "BW_PEEL_MID_TAC"

(* The case of a store, by its word k: tsp (1), vsp (2: a pop, or a push of *)
(* a result whose claim claim_tac proves), lc (3: a push of a log entry), or *)
(* a free word.                                                               *)
and BW_STORE_CASE_TAC claim_tac : tactic = fun (asl,w) ->
  let side = BW_SIDE_TAC in
  let push = REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; side; side; claim_tac] in
  let k = rand(lhand w) in
  (if k = `1` then DISJ2_TAC THEN DISJ1_TAC THEN CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; side]
   else if k = `2` then
     FIRST [DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; side];
            DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN push]
   else if k = `3` then DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN push
   else DISJ1_TAC THEN side) (asl,w);;

let BW_PEEL_MID_TAC = BW_PEEL_MID_GEN_TAC NO_TAC;;

(* ------------------------------------------------------------------------- *)
(* Leaves of the step blocks.                                                 *)
(* ------------------------------------------------------------------------- *)

(* A stop whose state is a chain of register writes and work stores over a  *)
(* state where the invariant held.                                           *)
let BW_STOP_LEAF_TAC =
  REWRITE_TAC[TISA_FAILST_FINST] THEN MATCH_MP_TAC BW_RESULT_STOP_MID THEN
  REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; BW_PEEL_MID_TAC; CONV_TAC NUM_REDUCE_CONV];;

(* Work words of later states, read through the writes and folded back into  *)
(* the entry state's work words.                                              *)
let BW_W_LATER_TAC =
  CONV_TAC(TOP_DEPTH_CONV(fun t -> let h,args = strip_comb t in
    match args with
      [x;k] when h = `bw_w` && not(is_var x) && is_numeral k -> REWR_CONV bw_w t
    | _ -> failwith "")) THEN
  CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN TISA_STATE_NORM_TAC;;

(* bw_rows X c = bw_rows s c for a later state X that wrote no row below c: *)
(* its row words read through the writes (the region base left folded, so  *)
(* the normal form names it tisa_base st 0).                                 *)
let BW_ROWS_LATER_TAC s : tactic = fun (asl,w) ->
  let rs = find_terms (fun t -> let h,args = strip_comb t in
                         h = `bw_rows` && length args = 2 && not(is_var(hd args))) w in
  MAP_EVERY (fun t ->
    let x = hd(snd(strip_comb t)) and c = el 1 (snd(strip_comb t)) in
    SUBGOAL_THEN (mk_eq(t, list_mk_comb(`bw_rows`, [s; c]))) SUBST1_TAC THENL
     [MATCH_MP_TAC BW_ROWS_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      CONV_TAC(LAND_CONV(REWR_CONV intern_word)) THEN
      TISA_STATE_NORM_TAC THEN REWRITE_TAC[intern_word] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) (setify rs) (asl,w);;

(* A continuing leaf: Q X from the tail's precondition, its invariant by     *)
(* peeling, v9 Boolean, and the step's claim by claim_tac.                   *)
let BW_CONT_LEAF_TAC claim_tac =
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                                     can (find_term ((=) `bw_tail_pre`)) (concl th))) THEN
  REWRITE_TAC[bw_tail_pre] THEN
  CONJ_TAC THENL [BW_PEEL_MID_TAC; ALL_TAC] THEN
  TISA_STATE_NORM_TAC THEN REWRITE_TAC[TISA_BOOL_01; WORD_1_NE_0] THEN claim_tac;;

(* ------------------------------------------------------------------------- *)
(* Block setup: the invariant's facts, and the header reads of the entry     *)
(* state folded into work words, so the generator writes bw_w s k for them. *)
(* ------------------------------------------------------------------------- *)

let BW_HDR_READ = prove
 (`!st s k. tisa_base s 3 = tisa_base st 3
            ==> tisa_read s (word_add (tisa_base st 3) (word (8 * k))) 8 = bw_w s k`,
  SIMP_TAC[bw_w]);;

(* The reads of header words 0..8 of s, as the generator writes them. *)
let bw_hdr_reads s =
  let th0 = SPECL [`st:tisa_state`; s] BW_HDR_READ in
  map (fun k -> CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV THENC REWRITE_CONV[WORD_ADD_0] THENC
                          ONCE_DEPTH_CONV NUM_REDUCE_CONV)
                  (SPEC (mk_small_numeral k) th0)) [0;1;2;3;4;5;6;7;8];;

let BW_BLOCK_SETUP_TAC s =
  BW_REGIONS_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_mid] o
              check (fun th -> concl th = mk_comb(`bw_mid st`, s))) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) (mk_comb(`tisa_fword`, s)))) (concl th) &&
       can (find_term ((=) `tisa_fword st`)) (concl th)
    then MAP_EVERY (fun i -> ASSUME_TAC(MP (SPEC (mk_small_numeral i) th)
                                           (EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool`
                                              (mk_small_numeral i) `24`)))))
                   [0;1;2;3;4;5;6;7;22;23]
    else NO_TAC) THEN
  SUBGOAL_THEN (subst [s,`s:tisa_state`] `tisa_base s 3 = tisa_base st 3`) ASSUME_TAC THENL
   [REWRITE_TAC[tisa_base] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (subst [s,`s:tisa_state`]
                 `tisa_base s 0 = tisa_base st 0 /\ tisa_base s 1 = tisa_base st 1 /\
                  tisa_base s 2 = tisa_base st 2 /\ tisa_len s 0 = tisa_len st 0 /\
                  tisa_len s 1 = tisa_len st 1 /\ tisa_len s 2 = tisa_len st 2 /\
                  tisa_len s 3 = tisa_len st 3`) STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[tisa_base; tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (fun g -> MAP_EVERY (fun th -> ASSUME_TAC(MP th (ASSUME(subst [s,`s:tisa_state`]
                                    `tisa_base s 3 = tisa_base st 3`))))
                      (bw_hdr_reads s) g) THEN
  SUBGOAL_THEN (subst [s,`s:tisa_state`]
                 `128 * val(bw_w s 4) + 128 <= val(tisa_len st 3) /\ 1 <= val(bw_w s 4)`)
   STRIP_ASSUME_TAC THENL [BW_ARITH_TAC; ALL_TAC];;

(* bw_last: no task left. *)
let BW_LAST_GOAL =
 `!st s Q. bw_regions st /\ bw_entered st /\ bw_mid st s /\
           tregs s 2 = tisa_base st 3 /\ val(bw_w s 1) = 0 /\
           (!s'. bw_tail_pre st s' ==> Q s')
           ==> tisa_wp bw_last Q (bw_result st) s`;;

(* ------------------------------------------------------------------------- *)
(* One probe. Its continuing paths keep the invariant one probe further; its *)
(* exits (found, appended) leave the interned state; its stop (rows full)    *)
(* writes only the status and return words.                                  *)
(* ------------------------------------------------------------------------- *)

(* The body's goal with the invariant unfolded, s's facts and u's view as s's. *)
let BW_PROBE_SETUP_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [bw_probing] o
                check (fun th -> can (find_term ((=) `bw_probing`)) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = val(intern_slots s)`)) THEN
  MP_TAC(ISPECL [`u:tisa_state`; `s:tisa_state`] TISA_SAME_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  BW_S_SETUP_TAC THEN
  ASSUME_TAC(SPEC `s:tisa_state` INTERN_SLOTS_VAL) THEN
  SUBGOAL_THEN `tisa_len s 1 = tisa_len st 1 /\ tisa_len s 0 = tisa_len st 0 /\
                tisa_base s 0 = tisa_base st 0 /\ tisa_base s 1 = tisa_base st 1 /\
                tisa_base s 3 = tisa_base st 3`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[tisa_len; tisa_base] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_WORD_EXACT THEN MP_TAC(ISPEC `intern_slots s` VAL_BOUND_64) THEN
    BW_ARITH_TAC; ALL_TAC] THEN
  (* the private count, as the generator reads it *)
  SUBGOAL_THEN `bw_w s 0 = tisa_read s (tisa_base st 3) 8` ASSUME_TAC THENL
   [REWRITE_TAC[bw_w; MULT_CLAUSES; WORD_ADD_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (let eq = `bw_w s 0 = tisa_read s (tisa_base st 3) 8` in
   RULE_ASSUM_TAC(fun th -> if concl th = eq then th else REWRITE_RULE[ASSUME eq] th));;

let BW_PROBE_BODY_GOAL =
 `!st s N j u.
    bw_regions st /\ bw_mid st s /\ j < N /\ bw_probing s N j u
    ==> tisa_wp bw_probe
          (\s2. (~tisa_bool (tregs s2 9) ==> bw_result st 3 (tisa_failst 3 s2)) /\
                (tisa_bool (tregs s2 9) /\ tregs s2 9 = word 0 ==> bw_after_intern s s2) /\
                (tisa_bool (tregs s2 9) /\ ~(tregs s2 9 = word 0)
                 ==> bw_probing s N (j + 1) s2))
          (bw_result st) (tisa_setreg 7 (word j) u)`;;

(* Leaf tactics of the probe body. *)

(* Unfold the views of later states, read through the writes, and compare. *)
let BW_LATER_VIEW_TAC =
  CONV_TAC(TOP_DEPTH_CONV BW_UNFOLD_LATER_CONV) THEN CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN
  TISA_STATE_NORM_TAC THEN
  TRY(REWRITE_TAC[bw_w; intern_count; intern_slots; intern_word; intern_slot; tisa_fword; tisa_frame;
                  tisa_base; tisa_len; MULT_CLAUSES; WORD_ADD_0] THEN
      CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(TISA_ARITH_DECIDE_TAC);;

(* val(word_shl x 1) = 2 * val x for the shifts in the goal and assumptions *)
(* (intern16_complete.ml's INTERN16_SHL_TAC, its bound by focused arithmetic). *)
let BW_SHL_TAC : tactic = fun (asl,w) ->
  let shl_tm = `word_shl:int64->num->int64` in
  let is_shl1 t = is_comb t && is_comb(rator t) && rator(rator t) = shl_tm && rand t = `1` in
  let ts = setify (itlist (fun (_,th) acc -> find_terms is_shl1 (concl th) @ acc) asl
                          (find_terms is_shl1 w)) in
  MAP_EVERY (fun t ->
    let x = rand(rator t) in
    TRY(SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,t),
                            mk_binop `( * ):num->num->num` `2` (mk_comb(`val:int64->num`,x))))
          (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
         [MATCH_MP_TAC TISA_VAL_SHL1 THEN BW_ARITH_TAC; ALL_TAC])) ts (asl,w);;

(* A continuing probe: the invariant one probe further. *)
let BW_PROBE_CONT_TAC =
  REWRITE_TAC[bw_probing] THEN TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC BW_PROBED_STEP THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[bw_probed; intern_slot; intern_pos; intern_has; intern_word; intern_slots] THEN
  ASM_REWRITE_TAC[] THEN BW_SHL_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * (2 * x + 1) = 8 * (2 * x) + 8`] THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* 8-byte stores into the rows region and into the table: the row word or   *)
(* the slot at the store's index reads the value, every other row word,     *)
(* slot and work word, the header and the frame are kept.                   *)
(* ------------------------------------------------------------------------- *)

let BW_ROWS_STORE = prove
 (`!st s m (v:int64).
     bw_regions st /\ tregs s 0 = tregs st 0 /\ (!i. i < 24 ==> tisa_fword s i = tisa_fword st i) /\
     8 * m + 8 <= val(tisa_len st 0)
     ==> tregs (tisa_store (word_add (tisa_base st 0) (word (8 * m))) 8 v s) 0 = tregs st 0 /\
         (!i. i < 24 ==> tisa_fword (tisa_store (word_add (tisa_base st 0) (word (8 * m))) 8 v s) i =
                         tisa_fword st i) /\
         intern_count (tisa_store (word_add (tisa_base st 0) (word (8 * m))) 8 v s) = intern_count s /\
         (!i. 8 * i + 8 <= val(tisa_len st 0)
              ==> intern_word (tisa_store (word_add (tisa_base st 0) (word (8 * m))) 8 v s) i =
                  if i = m then v else intern_word s i) /\
         (!p. val p < val(intern_slots st)
              ==> intern_slot (tisa_store (word_add (tisa_base st 0) (word (8 * m))) 8 v s) p =
                  intern_slot s p) /\
         (!k. 8 * k + 8 <= val(tisa_len st 3)
              ==> bw_w (tisa_store (word_add (tisa_base st 0) (word (8 * m))) 8 v s) k = bw_w s k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_REGIONS_TAC THEN
  ABBREV_TAC `a = word_add (tisa_base st 0) (word (8 * m)):int64` THEN
  SUBGOAL_THEN `val(a:int64) = val(tisa_base st 0) + 8 * m` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:int64`; `8`; `v:int64`; `s:tisa_state`] TISA_STORE_KEEPS_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN BW_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `!r. r < 4 ==> tisa_base s r = tisa_base st r /\ tisa_len s r = tisa_len st r`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_base; tisa_len] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    BW_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[TISA_TREGS_STORE] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 12 /\ 1 < 12 /\ 2 < 12 /\ 3 < 12`;
               ARITH_RULE `0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4`] THEN
  REWRITE_TAC[intern_count; intern_word; intern_slot; intern_slots; bw_w] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 12 /\ 1 < 12 /\ 2 < 12 /\ 3 < 12`;
               ARITH_RULE `0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 0) (word (8 * i)):int64) = val(tisa_base st 0) + 8 * i`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC TISA_READ_STORE_SAME THEN
      ASM_REWRITE_TAC[] THEN BW_ARITH_TAC;
      MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC];
    REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_USHR]) THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NUM_REDUCE_CONV)) THEN
    MP_TAC(ISPEC `tisa_len st 1` VAL_BOUND_64) THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 1) (word (8 * val(p:int64))):int64) =
                  val(tisa_base st 1) + 8 * val p`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 3) (word (8 * k)):int64) = val(tisa_base st 3) + 8 * k`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC]);;

let BW_SLOT_STORE = prove
 (`!st s (q:int64) (v:int64).
     bw_regions st /\ tregs s 0 = tregs st 0 /\ (!i. i < 24 ==> tisa_fword s i = tisa_fword st i) /\
     val q < val(intern_slots st)
     ==> tregs (tisa_store (word_add (tisa_base st 1) (word (8 * val q))) 8 v s) 0 = tregs st 0 /\
         (!i. i < 24 ==> tisa_fword (tisa_store (word_add (tisa_base st 1) (word (8 * val q))) 8 v s) i =
                         tisa_fword st i) /\
         intern_count (tisa_store (word_add (tisa_base st 1) (word (8 * val q))) 8 v s) = intern_count s /\
         (!i. 8 * i + 8 <= val(tisa_len st 0)
              ==> intern_word (tisa_store (word_add (tisa_base st 1) (word (8 * val q))) 8 v s) i =
                  intern_word s i) /\
         (!p. val p < val(intern_slots st)
              ==> intern_slot (tisa_store (word_add (tisa_base st 1) (word (8 * val q))) 8 v s) p =
                  if p = q then v else intern_slot s p) /\
         (!k. 8 * k + 8 <= val(tisa_len st 3)
              ==> bw_w (tisa_store (word_add (tisa_base st 1) (word (8 * val q))) 8 v s) k = bw_w s k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_REGIONS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[intern_slots; VAL_WORD_USHR]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[intern_slots; VAL_WORD_USHR] THEN CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN
  MP_TAC(ISPEC `tisa_len st 1` VAL_BOUND_64) THEN DISCH_TAC THEN
  ABBREV_TAC `a = word_add (tisa_base st 1) (word (8 * val(q:int64))):int64` THEN
  SUBGOAL_THEN `val(a:int64) = val(tisa_base st 1) + 8 * val(q:int64)` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:int64`; `8`; `v:int64`; `s:tisa_state`] TISA_STORE_KEEPS_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN BW_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `!r. r < 4 ==> tisa_base s r = tisa_base st r /\ tisa_len s r = tisa_len st r`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_base; tisa_len] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    BW_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[TISA_TREGS_STORE] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 12 /\ 1 < 12 /\ 2 < 12 /\ 3 < 12`;
               ARITH_RULE `0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4`] THEN
  REWRITE_TAC[intern_count; intern_word; intern_slot; bw_w] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 12 /\ 1 < 12 /\ 2 < 12 /\ 3 < 12`;
               ARITH_RULE `0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 0) (word (8 * i)):int64) = val(tisa_base st 0) + 8 * i`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 1) (word (8 * val(p:int64))):int64) =
                  val(tisa_base st 1) + 8 * val p`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC TISA_READ_STORE_SAME THEN
      ASM_REWRITE_TAC[] THEN BW_ARITH_TAC;
      FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM VAL_EQ] o
                    check (fun th -> is_neg(concl th))) THEN
      MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 3) (word (8 * k)):int64) = val(tisa_base st 3) + 8 * k`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC]);;

(* The store of the published count into the header. *)
let BW_HDR_STORE = prove
 (`!st s (v:int64).
     bw_regions st /\ tregs s 0 = tregs st 0 /\ (!i. i < 24 ==> tisa_fword s i = tisa_fword st i)
     ==> tregs (tisa_store (tisa_base st 2) 8 v s) 0 = tregs st 0 /\
         (!i. i < 24 ==> tisa_fword (tisa_store (tisa_base st 2) 8 v s) i = tisa_fword st i) /\
         intern_count (tisa_store (tisa_base st 2) 8 v s) = v /\
         (!i. 8 * i + 8 <= val(tisa_len st 0)
              ==> intern_word (tisa_store (tisa_base st 2) 8 v s) i = intern_word s i) /\
         (!p. val p < val(intern_slots st)
              ==> intern_slot (tisa_store (tisa_base st 2) 8 v s) p = intern_slot s p) /\
         (!k. 8 * k + 8 <= val(tisa_len st 3)
              ==> bw_w (tisa_store (tisa_base st 2) 8 v s) k = bw_w s k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_REGIONS_TAC THEN
  MP_TAC(ISPECL [`tisa_base st 2`; `8`; `v:int64`; `s:tisa_state`] TISA_STORE_KEEPS_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN BW_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `!r. r < 4 ==> tisa_base s r = tisa_base st r /\ tisa_len s r = tisa_len st r`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_base; tisa_len] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    BW_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[TISA_TREGS_STORE] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 12 /\ 1 < 12 /\ 2 < 12 /\ 3 < 12`;
               ARITH_RULE `0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4`] THEN
  REWRITE_TAC[intern_count; intern_word; intern_slot; intern_slots; bw_w] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 12 /\ 1 < 12 /\ 2 < 12 /\ 3 < 12`;
               ARITH_RULE `0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC TISA_READ_STORE_SAME THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 0) (word (8 * i)):int64) = val(tisa_base st 0) + 8 * i`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_USHR]) THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NUM_REDUCE_CONV)) THEN
    MP_TAC(ISPEC `tisa_len st 1` VAL_BOUND_64) THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 1) (word (8 * val(p:int64))):int64) =
                  val(tisa_base st 1) + 8 * val p`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `val(word_add (tisa_base st 3) (word (8 * k)):int64) = val(tisa_base st 3) + 8 * k`
     ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN BW_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC TISA_READ_STORE_APART THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The append of interning: rows m and m + 1 := k0, k1, slot q := v, work   *)
(* word 0 := v'; the states between the stores differ from the stores'      *)
(* results only in registers other than the frame register.                 *)
(* ------------------------------------------------------------------------- *)

let BW_APPEND_VIEWS = prove
 (`!st s Y0 Y2 Y3 m (k0:int64) (k1:int64) (q:int64) (v:int64) (v':int64).
     bw_regions st /\ tregs s 0 = tregs st 0 /\
     (!i. i < 24 ==> tisa_fword s i = tisa_fword st i) /\
     tregs Y0 0 = tregs st 0 /\ tmem Y0 = tmem s /\
     8 * m + 16 <= val(tisa_len st 0) /\ val q < val(intern_slots st) /\
     tregs Y2 0 = tregs st 0 /\
     tmem Y2 = tmem (tisa_store (word_add (tisa_base st 0) (word (8 * m + 8))) 8 k1
                      (tisa_store (word_add (tisa_base st 0) (word (8 * m))) 8 k0 Y0)) /\
     tregs Y3 0 = tregs st 0 /\
     tmem Y3 = tmem (tisa_store (word_add (tisa_base st 1) (word (8 * val q))) 8 v Y2)
     ==> tregs (tisa_store (tisa_base st 3) 8 v' Y3) 0 = tregs st 0 /\
         (!i. i < 24 ==> tisa_fword (tisa_store (tisa_base st 3) 8 v' Y3) i = tisa_fword st i) /\
         intern_count (tisa_store (tisa_base st 3) 8 v' Y3) = intern_count s /\
         (!i. 8 * i + 8 <= val(tisa_len st 0)
              ==> intern_word (tisa_store (tisa_base st 3) 8 v' Y3) i =
                  if i = m + 1 then k1 else if i = m then k0 else intern_word s i) /\
         (!p. val p < val(intern_slots st)
              ==> intern_slot (tisa_store (tisa_base st 3) 8 v' Y3) p =
                  if p = q then v else intern_slot s p) /\
         (!k. 8 * k + 8 <= val(tisa_len st 3)
              ==> bw_w (tisa_store (tisa_base st 3) 8 v' Y3) k = if k = 0 then v' else bw_w s k) /\
         intern_slots (tisa_store (tisa_base st 3) 8 v' Y3) = intern_slots st /\
         tisa_len (tisa_store (tisa_base st 3) 8 v' Y3) 0 = tisa_len st 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Y0 shows s *)
  MP_TAC(ISPECL [`Y0:tisa_state`; `s:tisa_state`] BW_SAME_VIEWS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* row m *)
  MP_TAC(SPECL [`st:tisa_state`; `Y0:tisa_state`; `m:num`; `k0:int64`] BW_ROWS_STORE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN BW_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Y1 = tisa_store (word_add (tisa_base st 0) (word (8 * m))) 8 k0 Y0` THEN STRIP_TAC THEN
  (* row m + 1 *)
  MP_TAC(SPECL [`st:tisa_state`; `Y1:tisa_state`; `m + 1`; `k1:int64`] BW_ROWS_STORE) THEN
  REWRITE_TAC[ARITH_RULE `8 * (m + 1) = 8 * m + 8`] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN BW_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Z1 = tisa_store (word_add (tisa_base st 0) (word (8 * m + 8))) 8 k1 Y1` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Y2:tisa_state`; `Z1:tisa_state`] BW_SAME_VIEWS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* slot q *)
  MP_TAC(SPECL [`st:tisa_state`; `Y2:tisa_state`; `q:int64`; `v:int64`] BW_SLOT_STORE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Z2 = tisa_store (word_add (tisa_base st 1) (word (8 * val(q:int64)))) 8 v Y2` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`Y3:tisa_state`; `Z2:tisa_state`] BW_SAME_VIEWS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* work word 0 *)
  MP_TAC(SPECL [`st:tisa_state`; `Y3:tisa_state`; `0`; `v':int64`] BW_WORK_STORE) THEN
  REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN BW_REGIONS_TAC THEN BW_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Z3 = tisa_store (tisa_base st 3) 8 v' Y3` THEN STRIP_TAC THEN
  (* the views of Z3 *)
  SUBGOAL_THEN `!r. r < 4 ==> tisa_len Z3 r = tisa_len st r` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_len] THEN FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && can (find_term ((=) `tisa_fword Z3`)) (concl th)
      then MATCH_MP_TAC th else NO_TAC) THEN BW_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[intern_slots; ARITH_RULE `0 < 4 /\ 1 < 4`]);;

(* ------------------------------------------------------------------------- *)
(* The appended leaf of the probe body: the key's rows at m = 2c, the slot   *)
(* of probe j := c + 1, the private count c + 1 (BW_APPEND_VIEWS), and the  *)
(* table well formed at c + 1 (BW_IOK_APPEND).                               *)
(* ------------------------------------------------------------------------- *)

let bw_append_parts x =
  let y4 = rand x in
  let (_,args4) = strip_comb y4 in
  let v' = el 2 args4 and y3 = el 3 args4 in
  let z2 = el 2 (snd(strip_comb y3)) in
  let (_,args2) = strip_comb z2 in
  let slot = el 0 args2 and v = el 2 args2 and y2 = el 3 args2 in
  let q = rand(rand(rand(rand slot))) in
  let z1 = el 2 (snd(strip_comb y2)) in
  let (_,args1) = strip_comb z1 in
  let k1 = el 2 args1 and y1 = el 3 args1 in
  let (_,args0) = strip_comb y1 in
  let row0 = el 0 args0 and k0 = el 2 args0 and y0 = el 3 args0 in
  let m = rand(rand(rand row0)) in
  (y4,y0,y2,y3,m,k0,k1,q,v,v');;

let BW_APPEND_SIDE_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[TISA_TMEM_SETREG] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         REWRITE_TAC[intern_slots] THEN TISA_WP_VAL_FACTS_TAC THEN BW_ARITH_TAC];;

(* A view fact of y (a conditional, as BW_APPEND_VIEWS states it) at idx. *)
let BW_VIEW_AT_TAC y tm idx =
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) (mk_comb(tm, y)))) (concl th) &&
                           can (find_term is_cond) (concl th)
                        then MP_TAC(SPEC idx th) else NO_TAC);;

(* The table well formed at c + 1 (BW_IOK_APPEND): the probes before j saw *)
(* used slots not holding the key, the slot of probe j was empty and now    *)
(* holds c + 1, the key's rows are 2c and 2c + 1.                            *)
let BW_APPEND_IOK_TAC y4 m q v v' : tactic =
  let c0 = `tisa_read s (tisa_base st 3) 8` in
  let vc = mk_comb(`val:int64->num`, c0) in
  DISCH_TAC THEN
  SUBGOAL_THEN (mk_eq(`intern_pos s (intern_hash (tregs s 1) (tregs s 2)) j`, q)) ASSUME_TAC THENL
   [REWRITE_TAC[intern_pos; intern_slots] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`word:num->int64`, mk_binop `(+):num->num->num` vc `1`), v)) ASSUME_TAC THENL
   [REWRITE_TAC[WORD_ADD; WORD_VAL]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = mk_eq(mk_binop `(+):num->num->num` vc `1`, mk_comb(`val:int64->num`, v'))
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
  MP_TAC(ISPECL [`s:tisa_state`; y4; vc; `j:num`; `tregs s 1`; `tregs s 2`] BW_IOK_APPEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (fun (asl,w) ->
      let has t = can (find_term ((=) t)) w in
      (if has `intern_slot s` && not (is_forall w) then
         REWRITE_TAC[intern_slot] THEN ASM_REWRITE_TAC[]
       else if is_forall w && has `intern_slot` then
         X_GEN_TAC `p:int64` THEN DISCH_TAC THEN
         BW_VIEW_AT_TAC y4 `intern_slot` `p:int64` THEN
         ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC[]
       else if is_forall w && has `intern_word` then
         X_GEN_TAC `i:num` THEN DISCH_TAC THEN
         BW_VIEW_AT_TAC y4 `intern_word` `i:num` THEN ANTS_TAC THENL [BW_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
         SUBGOAL_THEN (mk_conj(mk_neg(mk_eq(`i:num`, mk_binop `(+):num->num->num` m `1`)),
                               mk_neg(mk_eq(`i:num`, m))))
          (fun th -> REWRITE_TAC[th]) THEN BW_ARITH_TAC
       else if has `intern_word` then
         FIRST [BW_VIEW_AT_TAC y4 `intern_word` m THEN ANTS_TAC THENL [BW_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
                REWRITE_TAC[ARITH_RULE `~(m = m + 1)`] THEN NO_TAC;
                BW_VIEW_AT_TAC y4 `intern_word` (mk_binop `(+):num->num->num` m `1`) THEN
                ANTS_TAC THENL [BW_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC[] THEN NO_TAC]
       else ASM_REWRITE_TAC[intern_slots] THEN TRY BW_ARITH_GOAL_TAC) (asl,w));
    SIMP_TAC[]];;

let BW_APPEND_LEAF_TAC : tactic = fun (asl,w) ->
  let x = rand w in
  let (y4,y0,y2,y3,m,k0,k1,q,v,v') = bw_append_parts x in
  let c0 = `tisa_read s (tisa_base st 3) 8` in
  let vc = mk_comb(`val:int64->num`, c0) in
  let twoc = mk_binop `( * ):num->num->num` `2` vc in
  (MP_TAC(SPECL [`st:tisa_state`; `s:tisa_state`; y0; y2; y3; m; k0; k1; q; v; v'] BW_APPEND_VIEWS) THEN
   ANTS_TAC THENL [REPEAT CONJ_TAC THEN BW_APPEND_SIDE_TAC; STRIP_TAC] THEN
   MP_TAC(ISPECL [x; y4] BW_SAME_VIEWS) THEN
   ANTS_TAC THENL [REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG] THEN CONV_TAC NUM_REDUCE_CONV;
                   STRIP_TAC] THEN
   SUBGOAL_THEN (mk_eq(`bw_w s 0`, c0)) ASSUME_TAC THENL
    [REWRITE_TAC[bw_w; MULT_CLAUSES; WORD_ADD_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   BW_VIEW_AT_TAC y4 `bw_w` `0` THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
   ANTS_TAC THENL [BW_ARITH_TAC; REWRITE_TAC[] THEN DISCH_TAC] THEN
   REWRITE_TAC[bw_after_intern] THEN ASM_REWRITE_TAC[] THEN
   (* arithmetic facts, oriented so that rewriting leaves the stores' addresses *)
   MP_TAC(ISPEC `tisa_len st 0` VAL_BOUND_64) THEN DISCH_TAC THEN
   SUBGOAL_THEN (mk_conj(mk_eq(twoc, m),
                         mk_eq(mk_binop `(+):num->num->num` vc `1`, mk_comb(`val:int64->num`, v'))))
    STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN CONV_TAC SYM_CONV THENL
      [REWRITE_TAC[VAL_WORD_SHL; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
       MATCH_MP_TAC MOD_LT THEN BW_ARITH_TAC;
       REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
       MATCH_MP_TAC MOD_LT THEN BW_ARITH_TAC];
     ALL_TAC] THEN
   REPEAT CONJ_TAC THEN
   (fun (asl,w) ->
     let has t = can (find_term ((=) t)) w in
     let fa = is_forall w in
     (if fa && has `tisa_fword` then
        (* the frame *)
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        FIRST_ASSUM(fun th -> if is_forall(concl th) &&
                                 can (find_term ((=) (mk_comb(`tisa_fword`, y4)))) (concl th) &&
                                 is_imp(snd(strip_forall(concl th)))
                              then REWRITE_TAC[MP (SPEC `i:num` th) (ASSUME `i < 24`)] else NO_TAC) THEN
        CONV_TAC SYM_CONV THEN FIRST_ASSUM(fun th ->
          if is_forall(concl th) && can (find_term ((=) `tisa_fword s`)) (concl th) &&
             can (find_term ((=) `tisa_fword st`)) (concl th)
          then ACCEPT_TAC(MP (SPEC `i:num` th) (ASSUME `i < 24`)) else NO_TAC)
      else if fa && has `bw_w` then
        (* the work words other than 0 *)
        X_GEN_TAC `k:num` THEN STRIP_TAC THEN
        SUBGOAL_THEN `tisa_len s 3 = tisa_len st 3` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [REWRITE_TAC[tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
          FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `tisa_fword s`)) (concl th) &&
                                   can (find_term ((=) `tisa_fword st`)) (concl th)
                                then MATCH_MP_TAC th else NO_TAC) THEN CONV_TAC NUM_REDUCE_CONV;
          ALL_TAC] THEN
        BW_VIEW_AT_TAC y4 `bw_w` `k:num` THEN ANTS_TAC THENL [BW_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        COND_CASES_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN BW_ARITH_TAC
      else if fa && has `intern_word` then
        (* the rows below 2c *)
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        BW_VIEW_AT_TAC y4 `intern_word` `i:num` THEN ANTS_TAC THENL [BW_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        SUBGOAL_THEN (mk_conj(mk_neg(mk_eq(`i:num`, mk_binop `(+):num->num->num` m `1`)),
                              mk_neg(mk_eq(`i:num`, m))))
         (fun th -> REWRITE_TAC[th]) THEN BW_ARITH_TAC
      else if has `bw_iok` then
        (* the table *)
        BW_APPEND_IOK_TAC y4 m q v v'
      else if has `intern_word` then
        (* the key's two row words *)
        TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST [BW_VIEW_AT_TAC y4 `intern_word` m THEN ANTS_TAC THENL [BW_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
               REWRITE_TAC[ARITH_RULE `~(m = m + 1)`] THEN NO_TAC;
               BW_VIEW_AT_TAC y4 `intern_word` (mk_binop `(+):num->num->num` m `1`) THEN
               ANTS_TAC THENL [BW_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC[] THEN NO_TAC]
      else if has `tregs` && is_eq w && type_of(lhand w) = `:int64` then
        TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[]
      else
        TISA_STATE_NORM_TAC THEN BW_ARITH_TAC) (asl,w))) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The probe body: leaves.                                                   *)
(* ------------------------------------------------------------------------- *)

(* A stop inside the probe (rows full): its state has s's memory. *)
let BW_PROBE_STOP_TAC =
  REWRITE_TAC[TISA_FAILST_FINST] THEN MATCH_MP_TAC BW_RESULT_STOP_MID THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC NUM_REDUCE_CONV] THEN BW_PEEL_MID_TAC;;

(* The found leaf: memory unchanged, the slot's id below the count, its row  *)
(* the key.                                                                   *)
let BW_FOUND_LEAF_TAC =
  W(fun (asl,w) ->
    let x = rand w in
    MP_TAC(ISPECL [x; `s:tisa_state`] BW_SAME_VIEWS)) THEN
  ANTS_TAC THENL [TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[bw_after_intern] THEN ASM_REWRITE_TAC[] THEN
  TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_mid] o check (fun th -> concl th = `bw_mid st s`)) THEN
  ASM_REWRITE_TAC[] THEN
  W(fun (asl,w) ->
     let id = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "word_sub" &&
                                      type_of t = `:int64` with Failure _ -> false) w in
     MP_TAC(ISPECL [`st:tisa_state`; `s:tisa_state`; id] BW_ROW_READ)) THEN
  ANTS_TAC THENL [CONJ_TAC THEN ASM_REWRITE_TAC[] THEN BW_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];;

(* The probe body's leaves. *)
let BW_PROBE_LEAF_TAC : tactic = fun (asl,w) ->
  if can (find_term ((=) `bw_result`)) w && not (is_conj w) then BW_PROBE_STOP_TAC (asl,w)
  else (BETA_TAC THEN TISA_STATE_NORM_TAC THEN REWRITE_TAC[TISA_BOOL_01; WORD_1_NE_0] THEN
        (fun (asl,w) ->
           if fst(strip_comb w) = `bw_probing` then BW_PROBE_CONT_TAC (asl,w)
           else if can (find_term ((=) `tisa_store`)) w then BW_APPEND_LEAF_TAC (asl,w)
           else BW_FOUND_LEAF_TAC (asl,w))) (asl,w);;

let BW_PROBE_BODY_WP = prove
 (BW_PROBE_BODY_GOAL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BW_MID_S_FACTS o CONJ (ASSUME `bw_regions st`)) THEN
  BW_PROBE_SETUP_TAC THEN
  SUBGOAL_THEN `bw_mid st u` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`st:tisa_state`; `s:tisa_state`; `u:tisa_state`] BW_MID_SAME) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[bw_probe; bw_append; bw_occupied] THEN TISA_VCG_TAC THEN
  BW_PROBE_LEAF_TAC);;

(* ------------------------------------------------------------------------- *)
(* The interning block: the hash, the slot count, the probe loop; every     *)
(* slot probed is UNSUPPORTED 14.                                             *)
(* ------------------------------------------------------------------------- *)

let BW_INTERN_WP = prove
 (`!st s Q. bw_regions st /\ bw_mid st s /\ (!u. bw_after_intern s u ==> Q u)
            ==> tisa_wp bw_intern Q (bw_result st) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_BLOCK_SETUP_TAC `s:tisa_state` THEN
  REWRITE_TAC[bw_intern] THEN TISA_VCG_TAC THEN
  MATCH_MP_TAC TISA_WP_EARLY_LOOP THEN EXISTS_TAC `bw_probing s` THEN
  REPEAT CONJ_TAC THENL
   [(* more slots than the loop's cap *)
    DISCH_TAC THEN BW_STOP_LEAF_TAC;
    (* the invariant before the first probe *)
    DISCH_TAC THEN REWRITE_TAC[bw_probing; intern_hash; intern_slots; LT] THEN
    TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[];
    (* one probe *)
    MAP_EVERY X_GEN_TAC [`N:num`; `j:num`; `u:tisa_state`] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [bw_probing] o
                check (fun th -> can (find_term ((=) `bw_probing`)) (concl th))) THEN
    REWRITE_TAC[TISA_TREGS_SETREG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[TISA_BOOL_01; WORD_1_NE_0] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = val(intern_slots s)`)) THEN
    MATCH_MP_TAC TISA_WP_MONO THEN
    EXISTS_TAC `\s2. (~tisa_bool (tregs s2 9) ==> bw_result st 3 (tisa_failst 3 s2)) /\
                     (tisa_bool (tregs s2 9) /\ tregs s2 9 = word 0 ==> bw_after_intern s s2) /\
                     (tisa_bool (tregs s2 9) /\ ~(tregs s2 9 = word 0)
                      ==> bw_probing s (val(intern_slots s)) (j + 1) s2)` THEN
    EXISTS_TAC `bw_result st` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s2:tisa_state` THEN BETA_TAC THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[TISA_WP_IF; TISA_WP_SKIP] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                                       can (find_term ((=) `bw_after_intern`)) (concl th))) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
                                       can (find_term ((=) `bw_after_intern s s2`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC BW_PROBE_BODY_WP THEN ASM_REWRITE_TAC[]];
    (* every slot probed: UNSUPPORTED 14 *)
    MAP_EVERY X_GEN_TAC [`N:num`; `u:tisa_state`] THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [bw_probing]) THEN
    SUBGOAL_THEN `bw_mid st u` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`st:tisa_state`; `s:tisa_state`; `u:tisa_state`] BW_MID_SAME) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    BETA_TAC THEN TISA_VCG_TAC THEN (BW_CONTRA_TAC ORELSE BW_STOP_LEAF_TAC)]);;

(* ------------------------------------------------------------------------- *)
(* Publication: the private count written to the header, last, then FIRED.  *)
(* ------------------------------------------------------------------------- *)

let BW_PUBLISH_RESULT = prove
 (`!st s X (c:int64) (r:int64).
     bw_regions st /\ bw_mid st s /\ tregs X 0 = tregs st 0 /\ tmem X = tmem s /\
     c = bw_w s 0 /\ val r < val(bw_w s 0) /\
     bw_final (bw_rows st (val(intern_count st))) (bw_rows s (val(bw_w s 0)))
              (val(tisa_fword st 22)) (val(tisa_fword st 23)) (val(tregs st 1)) (val r)
     ==> bw_result st 1 (tisa_finst 1 r (tisa_store (tisa_base st 2) 8 c X))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `c:int64 = bw_w s 0`)) THEN
  BW_MID_FACTS_TAC `s:tisa_state` THEN BW_REGIONS_TAC THEN
  MP_TAC(ISPECL [`X:tisa_state`; `s:tisa_state`] BW_SAME_VIEWS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`st:tisa_state`; `X:tisa_state`; `bw_w s 0`] BW_HDR_STORE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Y = tisa_store (tisa_base st 2) 8 (bw_w s 0) X` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `Y:tisa_state`; `1`; `r:int64`] BW_FINST_KEEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Z = tisa_finst 1 r Y` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i < 2 * val(bw_w s 0) ==> intern_word Z i = intern_word s i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i < 2 * (val(tisa_len st 0) DIV 16) /\ 8 * i + 8 <= val(tisa_len st 0)`
     STRIP_ASSUME_TAC THENL [BW_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `bw_rows Z (val(bw_w s 0)) = bw_rows s (val(bw_w s 0))` ASSUME_TAC THENL
   [MATCH_MP_TAC BW_ROWS_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[bw_result] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the table *)
    REWRITE_TAC[INTERN_OK_BW] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BW_IOK_TRANSFER THEN EXISTS_TAC `s:tisa_state` THEN
    SUBGOAL_THEN `intern_slots s = intern_slots st /\ tisa_len s 0 = tisa_len st 0` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[intern_slots; tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[ARITH_RULE `1 < 24 /\ 3 < 24`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
                                         lhand(concl th) = `intern_ok st`)) THEN
      ASM_REWRITE_TAC[INTERN_OK_BW];
      X_GEN_TAC `p:int64` THEN DISCH_TAC THEN ASM_SIMP_TAC[]];
    (* the old rows *)
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < 2 * val(bw_w s 0)` (fun th -> ASM_SIMP_TAC[th]) THEN BW_ARITH_TAC;
    BW_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Setup for a block whose entry state s satisfies the invariant: the region *)
(* facts and the invariant's numeric facts in the generator's normal form.   *)
(* ------------------------------------------------------------------------- *)

let BW_MID_SETUP_TAC s =
  BW_REGIONS_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_mid] o
              check (fun th -> concl th = mk_comb(`bw_mid st`, s))) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) (mk_comb(`tisa_fword`, s)))) (concl th) &&
       can (find_term ((=) `tisa_fword st`)) (concl th)
    then MAP_EVERY (fun i -> ASSUME_TAC(MP (SPEC (mk_small_numeral i) th)
                                           (EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool`
                                              (mk_small_numeral i) `24`)))))
                   [0;1;2;3;4;5;6;7;22;23]
    else NO_TAC) THEN
  SUBGOAL_THEN (subst [s,`s:tisa_state`] `tisa_base s 3 = tisa_base st 3 /\ tisa_base s 0 = tisa_base st 0 /\
                tisa_base s 1 = tisa_base st 1 /\ tisa_base s 2 = tisa_base st 2 /\
                tisa_len s 0 = tisa_len st 0 /\ tisa_len s 1 = tisa_len st 1 /\
                tisa_len s 3 = tisa_len st 3`)
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[tisa_base; tisa_len] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> if can (find_term ((=) `bw_w`)) (concl th) &&
                              not (is_forall(concl th))
                           then CONV_RULE(TRY_CONV(REWRITE_CONV[bw_w] THENC TRY_CONV NUM_REDUCE_CONV THENC
                                         REWRITE_CONV[WORD_ADD_0])) th
                           else th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME(subst [s,`s:tisa_state`] `tisa_base s 3 = tisa_base st 3`)]);;

let BW_POST_GOAL =
 `!st N j s. bw_regions st /\ bw_entered st /\ bw_post_pre st s
             ==> tisa_wp bw_post (bw_inv st N (j + 1)) (bw_result st) s`;;

(* The claim of a pushed result or log entry: (si, sn, r) read back through  *)
(* the stores, the claim the step left for the tail.                        *)
let BW_PUSH_CLAIM_TAC =
  REWRITE_TAC[bw_nclaim] THEN BW_EVAL_TAC THEN CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN
  FIRST_ASSUM(fun th -> if is_imp(concl th) && can (find_term ((=) `bw_claim`)) (concl th)
                        then MP_TAC th else NO_TAC) THEN
  ANTS_TAC THENL [BW_SIDE_ARITH_TAC; DISCH_THEN ACCEPT_TAC];;

(* The mode-2 facts of the result promise: the walk's final claim for v5.   *)
let BW_MODE2_TAC =
  SUBGOAL_THEN `val(bw_w s 8) = 2` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `bw_w s 8 = word 2` then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && lhand(concl th) = `val(bw_w s 8) = 2`)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[LENGTH_BW_ROWS] THEN STRIP_TAC];;

let BW_POST_LEAF_TAC : tactic = fun (asl,w) ->
  if can (find_term ((=) `tisa_store (tisa_base st 2)`)) w then
    (MATCH_MP_TAC BW_PUBLISH_RESULT THEN EXISTS_TAC `s:tisa_state` THEN
     BW_MODE2_TAC THEN REPEAT CONJ_TAC THEN TISA_STATE_NORM_TAC THEN
     REWRITE_TAC[TISA_TMEM_SETREG] THEN ASM_REWRITE_TAC[]) (asl,w)
  else if can (find_term ((=) `bw_result`)) w then BW_STOP_LEAF_TAC (asl,w)
  else (REWRITE_TAC[bw_inv] THEN BW_PEEL_MID_GEN_TAC BW_PUSH_CLAIM_TAC) (asl,w);;

let BW_POST_WP = prove
 (BW_POST_GOAL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_post_pre] o
              check (fun th -> can (find_term ((=) `bw_post_pre`)) (concl th))) THEN
  BW_BLOCK_SETUP_TAC `s:tisa_state` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_resok] o
                check (fun th -> can (find_term ((=) `bw_resok`)) (concl th))) THEN
  REWRITE_TAC[bw_post; bw_publish; bw_push; bw_memo] THEN TISA_VCG_TAC THEN
  BW_POST_LEAF_TAC);;

(* ------------------------------------------------------------------------- *)
(* The tail of every step: intern the key when v9 says so, then the result.  *)
(* ------------------------------------------------------------------------- *)

let BW_TAIL_WP = prove
 (`!st N j s. bw_regions st /\ bw_entered st /\ bw_tail_pre st s
              ==> tisa_wp bw_tail (bw_inv st N (j + 1)) (bw_result st) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bw_tail; TISA_WP_SEQ; TISA_WP_IF] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bw_tail_pre] o
              check (fun th -> can (find_term ((=) `bw_tail_pre`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[TISA_WP_SKIP] THEN MATCH_MP_TAC BW_POST_WP THEN
    ASM_REWRITE_TAC[bw_post_pre] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC BW_INTERN_WP THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `u:tisa_state` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC BW_POST_WP THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BW_POST_PRE_INTERNED THEN EXISTS_TAC `s:tisa_state` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* bw_last: no task left; the result for (t, 0) on top; dbAbs ty over it.    *)
(* ------------------------------------------------------------------------- *)

let BW_LAST_CLAIM_TAC =
  (* the key: (4 + 8 ty, rt); the claim of the walk *)
  BW_W_LATER_TAC THEN BW_ROWS_LATER_TAC `s:tisa_state` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bw_resok] THEN CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  BW_FOLD_ENTS_TAC `s:tisa_state` [`1`, `val(bw_w s 2) - 1`] THEN
  MATCH_MP_TAC BW_RES_LAST_KEY THEN
  MAP_EVERY EXISTS_TAC
     [`s:tisa_state`; `bw_ent s 1 (val(bw_w s 2) - 1) 0`; `bw_ent s 1 (val(bw_w s 2) - 1) 1`;
      `bw_ent s 1 (val(bw_w s 2) - 1) 2`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `val(bw_w s 2) - 1` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `bw_eclaim st s 1`)) (concl th))) THEN
  ANTS_TAC THENL [BW_NZ_VAL_TAC THEN BW_ARITH_TAC; REWRITE_TAC[bw_eclaim] THEN ASM_REWRITE_TAC[]];;

let BW_LAST_LEAF_TAC : tactic = fun (asl,w) ->
  if can (find_term ((=) `bw_result`)) w then BW_STOP_LEAF_TAC (asl,w)
  else BW_CONT_LEAF_TAC BW_LAST_CLAIM_TAC (asl,w);;

let BW_LAST_WP = prove
 (`!st s Q. bw_regions st /\ bw_entered st /\ bw_mid st s /\
            tregs s 2 = tisa_base st 3 /\ val(bw_w s 1) = 0 /\
            (!s'. bw_tail_pre st s' ==> Q s')
            ==> tisa_wp bw_last Q (bw_result st) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_BLOCK_SETUP_TAC `s:tisa_state` THEN
  REWRITE_TAC[bw_last] THEN TISA_VCG_TAC THEN BW_LAST_LEAF_TAC);;

(* ------------------------------------------------------------------------- *)
(* Claims of the step blocks: the result's (i, n) is (si, sn) = (work words  *)
(* 6, 7), from row i and the entries the block read.                         *)
(* ------------------------------------------------------------------------- *)

(* The two words of row i as the generator reads them. *)
let bw_rowrd i off =
  let e = mk_binop `( * ):num->num->num` `8`
            (mk_comb(`val:int64->num`, mk_comb(mk_comb(`word_shl:int64->num->int64`, i), `1`))) in
  let e = if off then mk_binop `(+):num->num->num` e `8` else e in
  mk_comb(mk_comb(mk_comb(`tisa_read`, `s:tisa_state`),
          mk_comb(mk_comb(`word_add:int64->int64->int64`, `tisa_base st 0`),
                  mk_comb(`word:num->int64`, e))), `8`);;

let bw_entt a e f = list_mk_comb(`bw_ent`, [`s:tisa_state`; a; e; mk_small_numeral f]);;

(* Under val i < count, row i's words are the generator's reads (and what *)
(* the path conditions say of them).                                         *)
let BW_ROW_FACT_TAC i =
  DISCH_TAC THEN MP_TAC(ISPECL [`st:tisa_state`; `s:tisa_state`; i] BW_ROW_READ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN BW_SIDE_ARITH_TAC;
                  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]];;

(* The claim of entry e of area a, its fields rewritten by the path facts. *)
let BW_ECLAIM_AT_TAC a e =
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
                           can (find_term ((=) (list_mk_comb(`bw_eclaim`, [`st:tisa_state`; `s:tisa_state`; a]))))
                               (concl th)
                        then MP_TAC(SPEC e th) else NO_TAC) THEN
  ANTS_TAC THENL [BW_SIDE_ARITH_TAC; REWRITE_TAC[bw_eclaim] THEN ASM_REWRITE_TAC[] THEN NO_TAC];;

(* A tag test: val k0 MOD 8 from word_and k0 (word 7). *)
let BW_TAG_TAC =
  REWRITE_TAC[GSYM BW_VAL_AND7] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV BW_VAL_NUM_CONV) THEN REWRITE_TAC[] THEN NO_TAC;;

(* A hypothesis of a claim lemma: row facts, a tag, an entry's claim, or    *)
(* arithmetic.                                                               *)
let BW_CLAIM_HYP_TAC i ents : tactic = fun (asl,w) ->
  (if is_imp w && can (find_term ((=) `intern_word`)) w then BW_ROW_FACT_TAC i
   else if can (find_term ((=) `(MOD):num->num->num`)) w then
     FIRST [BW_TAG_TAC; REWRITE_TAC[GSYM BW_VAL_AND7] THEN BW_SIDE_ARITH_TAC]
   else if can (find_term ((=) `bw_claim`)) w then
     FIRST (map (fun (a,e) -> BW_ECLAIM_AT_TAC a e) ents)
   else FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; BW_SIDE_ARITH_TAC]) (asl,w);;

(* The result promise: work words and rows read, the mode decided. *)
let BW_RESOK_PREP_TAC =
  BW_EVAL_ALL_TAC THEN TRY(REPEAT GEN_TAC THEN STRIP_TAC) THEN
  REWRITE_TAC[bw_resok] THEN CONV_TAC(TRY_CONV(DEPTH_CONV BW_VAL_NUM_CONV)) THEN
  CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[];;

(* Entry reads and entry words of s as bw_ent s a e f. *)
let BW_FOLD_ALL_TAC ents =
  BW_FOLD_ENTS_TAC `s:tisa_state` ents THEN BW_FOLD_W_TAC `s:tisa_state` ents;;

(* A continuing leaf with claim tactic claim_tac (tactics.ml's            *)
(* BW_CONT_LEAF_TAC); a stop leaf.                                          *)
let BW_STEP_LEAF_TAC claim_tac : tactic = fun (asl,w) ->
  if can (find_term ((=) `bw_result`)) w then (BW_CONTRA_TAC ORELSE BW_STOP_LEAF_TAC) (asl,w)
  else (BW_CONTRA_TAC ORELSE BW_CONT_LEAF_TAC claim_tac) (asl,w);;

(* The entry conditions of a block at a later state: its invariant by peeling, *)
(* register facts by normalization, work words by reading them.              *)
let BW_TASK_PRE_TAC : tactic =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         BW_PEEL_MID_TAC;
         TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         TISA_STATE_NORM_TAC THEN BW_EVAL_ALL_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC];;

let BW_SUB_GOAL blk =
  subst [blk, `bw_comb:tisa_stmt`]
   `!st s Q. bw_regions st /\ bw_entered st /\ bw_mid st s /\
             tregs s 2 = tisa_base st 3 /\ tregs s 8 = bw_w s 6 /\ tregs s 7 = bw_w s 7 /\
             (!s'. bw_tail_pre st s' ==> Q s')
             ==> tisa_wp bw_comb Q (bw_result st) s`;;

(* ------------------------------------------------------------------------- *)
(* COMB(i, n): row i is dbComb(a, b); the two results on top are for (a, n) *)
(* and (b, n).                                                                *)
(* ------------------------------------------------------------------------- *)

let BW_COMB_CLAIM_TAC =
  let i = `bw_w s 6` and e2 = `val(bw_w s 2) - 2` and e1 = `val(bw_w s 2) - 1` in
  let ents = [`1`, e2; `1`, e1] in
  let wits = [bw_rowrd i false; bw_rowrd i true;
              bw_entt `1` e2 0; bw_entt `1` e2 1; bw_entt `1` e2 2;
              bw_entt `1` e1 0; bw_entt `1` e1 1; bw_entt `1` e1 2] in
  BW_RESOK_PREP_TAC THEN BW_FOLD_ALL_TAC ents THEN
  FIRST
   [MATCH_MP_TAC BW_RES_COMB_SAME THEN MAP_EVERY EXISTS_TAC wits THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN BW_CLAIM_HYP_TAC i ents;
    MATCH_MP_TAC BW_RES_COMB_KEY THEN MAP_EVERY EXISTS_TAC (`s:tisa_state` :: wits) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN BW_CLAIM_HYP_TAC i ents];;

let BW_COMB_WP = prove
 (BW_SUB_GOAL `bw_comb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_BLOCK_SETUP_TAC `s:tisa_state` THEN
  REWRITE_TAC[bw_comb] THEN TISA_VCG_TAC THEN BW_STEP_LEAF_TAC BW_COMB_CLAIM_TAC);;

(* ------------------------------------------------------------------------- *)
(* ABS(i, n): row i is dbAbs(A, b); the result on top is for (b, n + 1).    *)
(* ------------------------------------------------------------------------- *)

let BW_ABS_CLAIM_TAC =
  let i = `bw_w s 6` and e1 = `val(bw_w s 2) - 1` in
  let ents = [`1`, e1] in
  let wits = [bw_rowrd i false; bw_rowrd i true;
              bw_entt `1` e1 0; bw_entt `1` e1 1; bw_entt `1` e1 2] in
  BW_RESOK_PREP_TAC THEN BW_FOLD_ALL_TAC ents THEN
  FIRST
   [MATCH_MP_TAC BW_RES_ABS_SAME THEN MAP_EVERY EXISTS_TAC wits THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN BW_CLAIM_HYP_TAC i ents;
    MATCH_MP_TAC BW_RES_ABS_KEY THEN MAP_EVERY EXISTS_TAC (`s:tisa_state` :: wits) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN BW_CLAIM_HYP_TAC i ents];;

let BW_ABS_WP = prove
 (BW_SUB_GOAL `bw_abs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_BLOCK_SETUP_TAC `s:tisa_state` THEN
  REWRITE_TAC[bw_abs] THEN TISA_VCG_TAC THEN BW_STEP_LEAF_TAC BW_ABS_CLAIM_TAC);;

(* ------------------------------------------------------------------------- *)
(* The expansions of dbComb and dbAbs into tasks (no result: mode 3).       *)
(* ------------------------------------------------------------------------- *)

let BW_EXPAND_GOAL blk =
  subst [blk, `bw_comb_expand:tisa_stmt`]
   `!st s Q. bw_regions st /\ bw_entered st /\ bw_mid st s /\
             tregs s 2 = tisa_base st 3 /\ tregs s 3 = bw_w s 1 /\
             (!s'. bw_tail_pre st s' ==> Q s')
             ==> tisa_wp bw_comb_expand Q (bw_result st) s`;;

let BW_COMB_EXPAND_WP = prove
 (BW_EXPAND_GOAL `bw_comb_expand`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_BLOCK_SETUP_TAC `s:tisa_state` THEN
  REWRITE_TAC[bw_comb_expand] THEN TISA_VCG_TAC THEN BW_STEP_LEAF_TAC BW_RESOK_PREP_TAC);;

let BW_ABS_EXPAND_WP = prove
 (BW_EXPAND_GOAL `bw_abs_expand`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_BLOCK_SETUP_TAC `s:tisa_state` THEN
  REWRITE_TAC[bw_abs_expand] THEN TISA_VCG_TAC THEN BW_STEP_LEAF_TAC BW_RESOK_PREP_TAC);;

(* ------------------------------------------------------------------------- *)
(* VISIT(i, n): the memo (a hit is the log entry's result); a miss reads    *)
(* row i: the variable itself (dbBound n), a row of tag 0, 1, 2 (itself),   *)
(* or a dbComb/dbAbs expanded into tasks (no result).                       *)
(* ------------------------------------------------------------------------- *)

(* The memo's log position p, from the path condition val p < lc. *)
let bw_memo_pos (asl:(string*thm)list) =
  let c = find (fun t -> try let l,r = dest_binop `(<):num->num->bool` t in
                            r = `val(bw_w s 3)` && not(is_numeral l) &&
                            fst(dest_const(rator l)) = "val"
                         with Failure _ -> false)
               (map (concl o snd) asl) in
  lhand c;;

let BW_VISIT_CLAIM_TAC : tactic = fun g ->
  let i = `bw_w s 6` in
  (BW_RESOK_PREP_TAC THEN
   (fun (asl,w) ->
     let ents = try [`2`, bw_memo_pos asl] with Failure _ -> [] in
     ((if ents = [] then ALL_TAC else BW_FOLD_ALL_TAC ents) THEN
      FIRST
       [(* a memo hit *)
        FIRST (map (fun (a,e) -> BW_ECLAIM_AT_TAC a e) ents);
        (* a row of tag 0, 1, 2 *)
        MATCH_MP_TAC BW_RES_LEAF THEN MAP_EVERY EXISTS_TAC [bw_rowrd i false; bw_rowrd i true] THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN BW_CLAIM_HYP_TAC i [];
        (* the variable *)
        MATCH_MP_TAC BW_RES_BOUND THEN EXISTS_TAC `s:tisa_state` THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN BW_CLAIM_HYP_TAC i []]) (asl,w))) g;;

let BW_VISIT_PRE =
 `bw_regions st /\ bw_entered st /\ bw_mid st s /\
  tregs s 2 = tisa_base st 3 /\ tregs s 8 = bw_w s 6 /\ tregs s 7 = bw_w s 7 /\
  tregs s 3 = bw_w s 1 /\
  (!s'. bw_tail_pre st s' ==> Q s')`;;

let BW_MISS_GOAL = list_mk_forall([`st:tisa_state`; `s:tisa_state`; `Q:tisa_state->bool`],
  mk_imp(BW_VISIT_PRE, `tisa_wp bw_miss Q (bw_result st) s`));;

let BW_VISIT_GOAL = list_mk_forall([`st:tisa_state`; `s:tisa_state`; `Q:tisa_state->bool`],
  mk_imp(BW_VISIT_PRE, `tisa_wp bw_visit Q (bw_result st) s`));;

(* The leaves of the miss: stops, the expansions (their lemmas), the        *)
(* variable and the rows of tag 0, 1, 2.                                     *)
let BW_MISS_LEAF_TAC : tactic = fun (asl,w) ->
  let blk = try rand(rator(rator(rator w))) with Failure _ -> `T` in
  if blk = `bw_comb_expand` then (MATCH_MP_TAC BW_COMB_EXPAND_WP THEN BW_TASK_PRE_TAC) (asl,w)
  else if blk = `bw_abs_expand` then (MATCH_MP_TAC BW_ABS_EXPAND_WP THEN BW_TASK_PRE_TAC) (asl,w)
  else BW_STEP_LEAF_TAC BW_VISIT_CLAIM_TAC (asl,w);;

let BW_MISS_WP = prove
 (BW_MISS_GOAL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_BLOCK_SETUP_TAC `s:tisa_state` THEN
  REWRITE_TAC[bw_miss; bw_bound; bw_tags; bw_leaf] THEN TISA_VCG_TAC THEN BW_MISS_LEAF_TAC);;

let BW_VISIT_LEAF_TAC : tactic = fun (asl,w) ->
  let blk = try rand(rator(rator(rator w))) with Failure _ -> `T` in
  if blk = `bw_miss` then (MATCH_MP_TAC BW_MISS_WP THEN BW_TASK_PRE_TAC) (asl,w)
  else BW_STEP_LEAF_TAC BW_VISIT_CLAIM_TAC (asl,w);;

let BW_VISIT_WP = prove
 (BW_VISIT_GOAL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_BLOCK_SETUP_TAC `s:tisa_state` THEN
  REWRITE_TAC[bw_visit] THEN TISA_VCG_TAC THEN BW_VISIT_LEAF_TAC);;

(* ------------------------------------------------------------------------- *)
(* bw_pop: pop the top task (kind, i, n); si, sn := i, n; dispatch to the   *)
(* VISIT, COMB and ABS blocks.                                               *)
(* ------------------------------------------------------------------------- *)

let BW_POP_GOAL =
 `!st s Q. bw_regions st /\ bw_entered st /\ bw_mid st s /\
           tregs s 2 = tisa_base st 3 /\ tregs s 3 = bw_w s 1 /\ ~(val(bw_w s 1) = 0) /\
           (!s'. bw_tail_pre st s' ==> Q s')
           ==> tisa_wp bw_pop Q (bw_result st) s`;;

let BW_POP_LEAF_TAC : tactic = fun (asl,w) ->
  let blk = try rand(rator(rator(rator w))) with Failure _ -> `T` in
  if blk = `bw_visit` then (MATCH_MP_TAC BW_VISIT_WP THEN BW_TASK_PRE_TAC) (asl,w)
  else if blk = `bw_comb` then (MATCH_MP_TAC BW_COMB_WP THEN BW_TASK_PRE_TAC) (asl,w)
  else if blk = `bw_abs` then (MATCH_MP_TAC BW_ABS_WP THEN BW_TASK_PRE_TAC) (asl,w)
  else (BW_CONTRA_TAC ORELSE BW_STOP_LEAF_TAC) (asl,w);;

let BW_POP_WP = prove
 (BW_POP_GOAL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_BLOCK_SETUP_TAC `s:tisa_state` THEN
  REWRITE_TAC[bw_pop] THEN TISA_VCG_TAC THEN BW_POP_LEAF_TAC);;

(* ------------------------------------------------------------------------- *)
(* bw_step: no task left (bw_last), or pop the top task (bw_pop).            *)
(* ------------------------------------------------------------------------- *)

let BW_STEP_PRE_TAC : tactic =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         BW_PEEL_MID_TAC;
         TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         RULE_ASSUM_TAC(REWRITE_RULE[GSYM VAL_EQ_0]) THEN
         TISA_STATE_NORM_TAC THEN BW_EVAL_ALL_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC];;

let BW_STEP_WP = prove
 (`!st s Q. bw_regions st /\ bw_entered st /\ bw_mid st s /\
            (!s'. bw_tail_pre st s' ==> Q s')
            ==> tisa_wp bw_step Q (bw_result st) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN BW_BLOCK_SETUP_TAC `s:tisa_state` THEN
  REWRITE_TAC[bw_step] THEN TISA_VCG_TAC THEN
  (fun (asl,w) ->
     let blk = try rand(rator(rator(rator w))) with Failure _ -> `T` in
     if blk = `bw_last` then (MATCH_MP_TAC BW_LAST_WP THEN BW_STEP_PRE_TAC) (asl,w)
     else if blk = `bw_pop` then (MATCH_MP_TAC BW_POP_WP THEN BW_STEP_PRE_TAC) (asl,w)
     else (BW_CONTRA_TAC ORELSE BW_STOP_LEAF_TAC) (asl,w)));;

(* ------------------------------------------------------------------------- *)
(* The prologue: the published count within the rows region, t below it,   *)
(* x and ty below 2^60, else UNSUPPORTED 1, 2, 3 with the entry memory; then *)
(* the work header (c, K, t, one task VISIT(t, 0), no results, empty log).  *)
(* ------------------------------------------------------------------------- *)

(* The views outside the work region of a chain of register writes and work *)
(* stores over s.                                                            *)
let bw_keep = new_definition
 `bw_keep st s X <=>
    tregs X 0 = tregs st 0 /\ (!i. i < 24 ==> tisa_fword X i = tisa_fword st i) /\
    intern_count X = intern_count s /\
    (!i. 8 * i + 8 <= val(tisa_len st 0) ==> intern_word X i = intern_word s i) /\
    (!p. val p < val(intern_slots st) ==> intern_slot X p = intern_slot s p)`;;

let BW_KEEP_BASE = prove
 (`!st s. tregs s 0 = tregs st 0 /\ (!i. i < 24 ==> tisa_fword s i = tisa_fword st i)
          ==> bw_keep st s s`,
  SIMP_TAC[bw_keep]);;

let BW_KEEP_SETREG = prove
 (`!st s X d (v:int64). bw_keep st s X /\ ~(d = 0) ==> bw_keep st s (tisa_setreg d v X)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tisa_setreg d v X`; `X:tisa_state`] BW_SAME_VIEWS) THEN
  ASM_REWRITE_TAC[TISA_TREGS_SETREG; TISA_TMEM_SETREG; ARITH_RULE `0 = d <=> d = 0`] THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[bw_keep]) THEN
  ASM_REWRITE_TAC[bw_keep; TISA_TREGS_SETREG; ARITH_RULE `0 = d <=> d = 0`]);;

let BW_KEEP_WSTORE = prove
 (`!st s X k (v:int64).
     bw_regions st /\ bw_keep st s X /\ 8 * k + 8 <= val(tisa_len st 3)
     ==> bw_keep st s (tisa_store (word_add (tisa_base st 3) (word (8 * k))) 8 v X)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bw_keep] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `X:tisa_state`; `k:num`; `v:int64`] BW_WORK_STORE) THEN
  ASM_SIMP_TAC[]);;

(* |- bw_keep st s x for a chain x over the variable s. *)
let rec bw_keep_thm asl s x =
  if x = s then
    TAC_PROOF((asl, list_mk_comb(`bw_keep`, [`st:tisa_state`; s; s])),
              MATCH_MP_TAC BW_KEEP_BASE THEN ASM_REWRITE_TAC[] THEN
              TRY(FIRST_ASSUM ACCEPT_TAC))
  else
    let h,args = strip_comb x in
    match fst(dest_const h) with
      "tisa_setreg" ->
        let d = el 0 args and v = el 1 args and y = el 2 args in
        let nz = EQT_ELIM(NUM_REDUCE_CONV(mk_neg(mk_eq(d, `0`)))) in
        MATCH_MP (ISPECL [`st:tisa_state`; s; y; d; v] BW_KEEP_SETREG) (CONJ (bw_keep_thm asl s y) nz)
    | "tisa_store" ->
        let a = el 0 args and v = el 2 args and y = el 3 args in
        let aeq = bw_waddr_eq a in
        let k = rand(rand(rand(rhs(concl aeq)))) in
        let kb = bw_prove_side asl (mk_binop `(<=):num->num->bool`
                   (mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `8` k) `8`)
                   `val(tisa_len st 3)`) in
        let reg = snd(find (fun (_,th) -> concl th = `bw_regions st`) asl) in
        let th = MATCH_MP (ISPECL [`st:tisa_state`; s; y; k; v] BW_KEEP_WSTORE)
                          (CONJ reg (CONJ (bw_keep_thm asl s y) kb)) in
        GEN_REWRITE_RULE (RAND_CONV o funpow 3 RATOR_CONV o RAND_CONV) [SYM aeq] th
    | _ -> failwith "bw_keep_thm";;

let BW_KEEP_TAC s : tactic = fun (asl,w) ->
  bw_side_cache := [];
  let x = rand w in
  ACCEPT_TAC (bw_keep_thm asl s x) (asl,w);;

(* A stop of the prologue: registers written over the entry state. *)
let BW_PROLOGUE_STOP_TAC =
  REWRITE_TAC[TISA_FAILST_FINST] THEN MATCH_MP_TAC BW_RESULT_STOP_ENTRY THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(TISA_STATE_NORM_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[TISA_TMEM_SETREG] THEN NO_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV;;

(* The continuing end of the prologue: the entry checks hold, the work      *)
(* header is the invariant's start (BW_MID_INIT), the budget register set.  *)
let BW_PROLOGUE_CONT_TAC : tactic =
  BETA_TAC THEN
  SUBGOAL_THEN `bw_entered st` ASSUME_TAC THENL
   [REWRITE_TAC[bw_entered; intern_count] THEN BW_SIDE_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(TISA_STATE_NORM_TAC THEN NO_TAC) THEN
  W(fun (asl,w) ->
     bw_side_cache := [];
     MP_TAC(REWRITE_RULE[bw_keep] (bw_keep_thm asl `st:tisa_state` (rand w)))) THEN
  STRIP_TAC THEN MATCH_MP_TAC BW_MID_INIT THEN ASM_REWRITE_TAC[] THEN
  BW_EVAL_TAC THEN REWRITE_TAC[intern_count] THEN
  REPEAT CONJ_TAC THEN
  TRY(X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `intern_word`)) (concl th)
                            then MATCH_MP_TAC th else NO_TAC) THEN
      BW_SIDE_ARITH_TAC THEN NO_TAC) THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  BW_SIDE_ARITH_TAC;;

let BW_PROLOGUE_WP = prove
 (`!st. tisa_entry_ok bind_walk st
        ==> tisa_wp bw_prologue
              (\s. bw_entered st /\ bw_mid st s /\ tregs s 11 = word 4294967295)
              (bw_result st) st`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BW_ENTRY) THEN BW_REGIONS_TAC THEN
  REWRITE_TAC[bw_prologue] THEN TISA_VCG_TAC THEN
  (fun (asl,w) ->
    if can (find_term ((=) `bw_result`)) w then BW_PROLOGUE_STOP_TAC (asl,w)
    else BW_PROLOGUE_CONT_TAC (asl,w)));;

(* ------------------------------------------------------------------------- *)
(* One step of the walk, and the body: the step, then the tail.              *)
(* ------------------------------------------------------------------------- *)

let BW_BODY_WP = prove
 (`!st N j s0.
     bw_regions st /\ bw_entered st /\ j < N /\ bw_inv st N j s0
     ==> tisa_wp bw_body (bw_inv st N (j + 1)) (bw_result st) (tisa_setreg 10 (word j) s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bw_body; TISA_WP_SEQ] THEN
  MATCH_MP_TAC BW_STEP_WP THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BW_MID_SETREG THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM(ACCEPT_TAC o REWRITE_RULE[bw_inv] o
                  check (fun th -> can (find_term ((=) `bw_inv`)) (concl th)));
    X_GEN_TAC `s':tisa_state` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC BW_TAIL_WP THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The whole program.                                                        *)
(* ------------------------------------------------------------------------- *)

let BW_ROOT_WP = prove
 (`!st. tisa_entry_ok bind_walk st
        ==> tisa_wp (tisa_root bind_walk) (\s. F) (bw_result st) st`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BW_ENTRY) THEN
  REWRITE_TAC[bind_walk; tisa_root; TISA_WP_SEQ] THEN
  MATCH_MP_TAC TISA_WP_MONO THEN
  EXISTS_TAC `\s. bw_entered st /\ bw_mid st s /\ tregs s 11 = word 4294967295` THEN
  EXISTS_TAC `bw_result st` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC BW_PROLOGUE_WP THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `s:tisa_state` THEN BETA_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC TISA_WP_COUNT_LOOP THEN EXISTS_TAC `bw_inv st` THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[bw_inv] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC BW_BODY_WP THEN ASM_REWRITE_TAC[bw_inv];
    MAP_EVERY X_GEN_TAC [`N:num`; `s1:tisa_state`] THEN DISCH_TAC THEN
    TISA_VCG_TAC THEN MATCH_MP_TAC BW_RESULT_STOP_MID THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    REPEAT(MATCH_MP_TAC BW_MID_SETREG THEN CONV_TAC NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The whole program: every run that stops ends with bw_result; no run      *)
(* continues past the final RETURN.                                          *)
(* ------------------------------------------------------------------------- *)

let BW_RUN = prove
 (`!st k st'. tisa_entry_ok bind_walk st /\ tisa_run bind_walk st = TStop k st'
              ==> bw_result st k st'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `st:tisa_state` BW_ROOT_WP) THEN ASM_REWRITE_TAC[tisa_wp] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> tisa_has_tm `tisa_run` th)) THEN
  ASM_REWRITE_TAC[tisa_run] THEN
  MP_TAC(ISPEC `tisa_exec (tisa_root bind_walk) st` TISA_RESULT_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC)
     (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `a:tisa_state` SUBST1_TAC))) THEN
  REWRITE_TAC[tisa_then; TISA_RWP_CONT; TISA_RWP_STOP; TISA_RESULT_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN REWRITE_TAC[]);;

(* Soundness: a FIRED run returns the row of dbAbs ty over hbind (x,ty) at   *)
(* depth 0 of t's decoding, in the rows below the new published count; the *)
(* rows below the old count are unchanged, and the count only grows.        *)
let BIND_WALK_SOUND = prove
 (`!st st'.
     tisa_entry_ok bind_walk st /\ tisa_run bind_walk st = TStop 1 st'
     ==> val(intern_count st) <= val(intern_count st') /\
         val(tisa_fword st' 19) < val(intern_count st') /\
         (!i. i < 2 * val(intern_count st) ==> intern_word st' i = intern_word st i) /\
         (!nms tys TY T.
            val(tisa_fword st 22) < LENGTH nms /\
            fdty nms tys (val(tisa_fword st 23)) TY /\
            (!a. a < LENGTH nms /\ EL a nms = EL (val(tisa_fword st 22)) nms
                 ==> a = val(tisa_fword st 22)) /\
            (!b. fdty nms tys b TY ==> b = val(tisa_fword st 23)) /\
            fddb nms tys (bw_rows st (val(intern_count st))) (val(tregs st 1)) T
            ==> fddb nms tys (bw_rows st' (val(intern_count st'))) (val(tisa_fword st' 19))
                     (hdbAbs TY (hbind (EL (val(tisa_fword st 22)) nms,TY) 0 T)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `1`; `st':tisa_state`] BW_RUN) THEN
  ASM_REWRITE_TAC[bw_result] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
                    can (find_term ((=) `intern_word`)) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[bw_final; bw_ctx] o
                  check (fun th -> can (find_term ((=) `bw_final`)) (concl th))) THEN
    REWRITE_TAC[GSYM CONJ_ASSOC]]);;

(* Canonicity: every outcome keeps intern16's table invariant, so no row is *)
(* ever duplicated; the rows below the old count are kept; every outcome    *)
(* but FIRED leaves the published count.                                    *)
let BIND_WALK_CANONICAL = prove
 (`!st k st'.
     tisa_entry_ok bind_walk st /\ intern_ok st /\ tisa_run bind_walk st = TStop k st'
     ==> intern_ok st' /\
         (!i. i < 2 * val(intern_count st) ==> intern_word st' i = intern_word st i) /\
         (~(k = 1) ==> intern_count st' = intern_count st)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:tisa_state`; `k:num`; `st':tisa_state`] BW_RUN) THEN
  ASM_REWRITE_TAC[bw_result] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(intern_count st) <= val(tisa_len st 0) DIV 16` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[INTERN_OK_BW; bw_iok] o
                check (fun th -> concl th = `intern_ok st`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
                    can (find_term ((=) `intern_word`)) (concl th))) THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

(* The hypotheses of soundness can hold: a context with one name and one     *)
(* type variable.                                                            *)
let BW_CTX_SATISFIABLE = prove
 (`?nms tys TY. bw_ctx nms tys 0 0 TY`,
  MAP_EVERY EXISTS_TAC [`["x"]:string list`; `[(0,0,0)]:(num#num#num)list`; `TyVar "x"`] THEN
  REWRITE_TAC[bw_ctx; LENGTH; ARITH] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`0`; `0`; `0`] (CONJUNCT1 (ISPECL [`["x"]:string list`;
                                                     `[(0,0,0)]:(num#num#num)list`] fdty_RULES))) THEN
    REWRITE_TAC[LENGTH; EL; HD; ARITH];
    ARITH_TAC;
    GEN_TAC THEN ONCE_REWRITE_TAC[fdty_CASES] THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `b < SUC 0 <=> b = 0`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Every theorem this file states, for the audits. *)
let bw_theorems = ref [
  "FDDB_LT", FDDB_LT;
  "BW_EXT_REFL", BW_EXT_REFL;
  "BW_EXT_TRANS", BW_EXT_TRANS;
  "BW_FDDB_EXT_BOTH", BW_FDDB_EXT_BOTH;
  "BW_FDDB_EXT", BW_FDDB_EXT;
  "BW_CLAIM_EXT", BW_CLAIM_EXT;
  "BW_FINAL_EXT", BW_FINAL_EXT;
  "BW_CLAIM_VACUOUS", BW_CLAIM_VACUOUS;
  "BW_FINAL_VACUOUS", BW_FINAL_VACUOUS;
  "BW_FDDB_ROW", BW_FDDB_ROW;
  "BW_CLAIM_SELF", BW_CLAIM_SELF;
  "BW_HBIND_SAME", BW_HBIND_SAME;
  "BW_CLAIM_BOUND", BW_CLAIM_BOUND;
  "BW_CLAIM_COMB_SAME", BW_CLAIM_COMB_SAME;
  "BW_CLAIM_ABS_SAME", BW_CLAIM_ABS_SAME;
  "BW_FINAL_ABS", BW_FINAL_ABS;
  "BW_CLAIM_COMB", BW_CLAIM_COMB;
  "BW_CLAIM_ABS", BW_CLAIM_ABS;
  "BIND_WALK_TERM", BIND_WALK_TERM;
  "LENGTH_BW_ROWS", LENGTH_BW_ROWS;
  "EL_BW_ROWS", EL_BW_ROWS;
  "BW_ROWS_EXT", BW_ROWS_EXT;
  "INTERN_OK_BW", INTERN_OK_BW;
  "BW_IOK_DOWN", BW_IOK_DOWN;
  "BW_IOK_TRANSFER", BW_IOK_TRANSFER;
  "BW_ENTRY", BW_ENTRY;
  "BW_ROWS_EQ", BW_ROWS_EQ;
  "BW_MID_STEP", BW_MID_STEP;
  "BW_MID_INTERNED", BW_MID_INTERNED;
  "BW_POST_PRE_INTERNED", BW_POST_PRE_INTERNED;
  "BW_FINST_KEEP", BW_FINST_KEEP;
  "BW_RESULT_STOP", BW_RESULT_STOP;
  "BW_RESULT_STOP_MID", BW_RESULT_STOP_MID;
  "BW_WORK_STORE", BW_WORK_STORE;
  "BW_MID_SAME", BW_MID_SAME;
  "BW_MID_SETREG", BW_MID_SETREG;
  "BW_ECLAIM_NCLAIM", BW_ECLAIM_NCLAIM;
  "BW_MID_STORE_CORE", BW_MID_STORE_CORE;
  "BW_MID_STORE_W", BW_MID_STORE_W;
  "TISA_RWP_MONO_Q", TISA_RWP_MONO_Q;
  "TISA_WP_EARLY_LOOP", TISA_WP_EARLY_LOOP;
  "BW_IOK_APPEND", BW_IOK_APPEND;
  "BW_ENT_AS_READ", BW_ENT_AS_READ;
  "BW_VAL_AND7", BW_VAL_AND7;
  "BW_KEY_FIELDS", BW_KEY_FIELDS;
  "TISA_BOOL_01", TISA_BOOL_01;
  "WORD_1_NE_0", WORD_1_NE_0;
  "BW_SAME_VIEWS", BW_SAME_VIEWS;
  "BW_ROW_READ", BW_ROW_READ;
  "BW_ROW_TRIPLE", BW_ROW_TRIPLE;
  "BW_EXT_MID", BW_EXT_MID;
  "BW_SHL3_EQ", BW_SHL3_EQ;
  "BW_RES_LEAF", BW_RES_LEAF;
  "BW_RES_BOUND", BW_RES_BOUND;
  "BW_RES_COMB_SAME", BW_RES_COMB_SAME;
  "BW_RES_COMB_KEY", BW_RES_COMB_KEY;
  "BW_RES_ABS_SAME", BW_RES_ABS_SAME;
  "BW_RES_ABS_KEY", BW_RES_ABS_KEY;
  "BW_RES_LAST_KEY", BW_RES_LAST_KEY;
  "BW_MID_INIT", BW_MID_INIT;
  "BW_RESULT_STOP_ENTRY", BW_RESULT_STOP_ENTRY;
  "BW_PROBED_STEP", BW_PROBED_STEP;
  "BW_MID_S_FACTS", BW_MID_S_FACTS;
  "BW_FRAME_SETREG", BW_FRAME_SETREG;
  "BW_FRAME_WSTORE", BW_FRAME_WSTORE;
  "BW_W_SETREG", BW_W_SETREG;
  "BW_W_WSTORE", BW_W_WSTORE;
  "BW_ROWS_SETREG", BW_ROWS_SETREG;
  "BW_ROWS_WSTORE", BW_ROWS_WSTORE;
  "BW_READ_AS_W", BW_READ_AS_W;
  "BW_HDR_READ", BW_HDR_READ;
  "BW_ROWS_STORE", BW_ROWS_STORE;
  "BW_SLOT_STORE", BW_SLOT_STORE;
  "BW_HDR_STORE", BW_HDR_STORE;
  "BW_APPEND_VIEWS", BW_APPEND_VIEWS;
  "BW_PROBE_BODY_WP", BW_PROBE_BODY_WP;
  "BW_INTERN_WP", BW_INTERN_WP;
  "BW_PUBLISH_RESULT", BW_PUBLISH_RESULT;
  "BW_POST_WP", BW_POST_WP;
  "BW_TAIL_WP", BW_TAIL_WP;
  "BW_LAST_WP", BW_LAST_WP;
  "BW_COMB_WP", BW_COMB_WP;
  "BW_ABS_WP", BW_ABS_WP;
  "BW_COMB_EXPAND_WP", BW_COMB_EXPAND_WP;
  "BW_ABS_EXPAND_WP", BW_ABS_EXPAND_WP;
  "BW_MISS_WP", BW_MISS_WP;
  "BW_VISIT_WP", BW_VISIT_WP;
  "BW_POP_WP", BW_POP_WP;
  "BW_STEP_WP", BW_STEP_WP;
  "BW_KEEP_BASE", BW_KEEP_BASE;
  "BW_KEEP_SETREG", BW_KEEP_SETREG;
  "BW_KEEP_WSTORE", BW_KEEP_WSTORE;
  "BW_PROLOGUE_WP", BW_PROLOGUE_WP;
  "BW_BODY_WP", BW_BODY_WP;
  "BW_ROOT_WP", BW_ROOT_WP;
  "BW_RUN", BW_RUN;
  "BIND_WALK_SOUND", BIND_WALK_SOUND;
  "BIND_WALK_CANONICAL", BIND_WALK_CANONICAL;
  "BW_CTX_SATISFIABLE", BW_CTX_SATISFIABLE;
];;

tisa_arith_focus := bw_saved_arith_focus;;
