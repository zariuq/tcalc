(* ========================================================================= *)
(* Negative controls for the fibre's guards. Each control takes a step       *)
(* lemma with one guard removed and refutes it: concrete rows satisfy every  *)
(* remaining premise, yet the new theorem row is not derivable. The rows    *)
(* decode, in HOL's initial context, to the sequents [] |- x = x and        *)
(* [] |- y = y, and the bad row to [] |- x = y, which is unprovable because *)
(* its image in the core context is (HCORE_DISTINCT_EQ_UNPROVABLE).          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Evaluating decoders on explicit row lists.                                *)
(* ------------------------------------------------------------------------- *)

let FIBRE_EVAL_CONV =
  REPEATC(CHANGED_CONV(REWRITE_CONV[EL_CONS; LENGTH; PAIR_EQ] THENC NUM_REDUCE_CONV));;

let fibre_row lst i =
  let r = el i (dest_list lst) in
  let tag,rest = dest_pair r in
  let a,b = dest_pair rest in
  dest_small_numeral tag,a,b;;

let fibre_mp rule ants =
  let ant = lhand(concl rule) in
  let ant_th = prove(ant, CONV_TAC FIBRE_EVAL_CONV THEN REWRITE_TAC ants) in
  CONV_RULE (RAND_CONV FIBRE_EVAL_CONV) (MP rule ant_th);;

let rec fdty_thm nms tys i =
  let rules = CONJUNCTS(SPECL [nms; tys] fdty_RULES) in
  let tag,a,b = fibre_row tys i in
  let n = mk_small_numeral i in
  if tag = 0 then fibre_mp (SPECL [n; a; b] (el 0 rules)) []
  else if tag = 1 then
    let lth = fdtys_thm nms tys (dest_small_numeral b) in
    fibre_mp (SPECL [n; a; b; rand(concl lth)] (el 1 rules)) [lth]
  else failwith "fdty_thm"
and fdtys_thm nms tys i =
  let rules = CONJUNCTS(SPECL [nms; tys] fdty_RULES) in
  let tag,a,b = fibre_row tys i in
  let n = mk_small_numeral i in
  if tag = 2 then fibre_mp (SPECL [n; a; b] (el 2 rules)) []
  else if tag = 3 then
    let tth = fdty_thm nms tys (dest_small_numeral a)
    and lth = fdtys_thm nms tys (dest_small_numeral b) in
    fibre_mp (SPECL [n; a; b; rand(concl tth); rand(concl lth)] (el 3 rules)) [tth; lth]
  else failwith "fdtys_thm";;

let rec fddb_thm nms tys dbs i =
  let rules = CONJUNCTS(SPECL [nms; tys; dbs] fddb_RULES) in
  let tag,a,b = fibre_row dbs i in
  let n = mk_small_numeral i in
  if tag = 0 || tag = 2 then
    let tth = fdty_thm nms tys (dest_small_numeral b) in
    fibre_mp (SPECL [n; a; b; rand(concl tth)] (el tag rules)) [tth]
  else if tag = 1 then fibre_mp (SPECL [n; a; b] (el 1 rules)) []
  else if tag = 3 then
    let s = fddb_thm nms tys dbs (dest_small_numeral a)
    and t = fddb_thm nms tys dbs (dest_small_numeral b) in
    fibre_mp (SPECL [n; a; b; rand(concl s); rand(concl t)] (el 3 rules)) [s; t]
  else if tag = 4 then
    let tth = fdty_thm nms tys (dest_small_numeral a)
    and t = fddb_thm nms tys dbs (dest_small_numeral b) in
    fibre_mp (SPECL [n; a; b; rand(concl tth); rand(concl t)] (el 4 rules)) [tth; t]
  else failwith "fddb_thm"
and fddbs_thm nms tys dbs i =
  let rules = CONJUNCTS(SPECL [nms; tys; dbs] fddb_RULES) in
  let tag,a,b = fibre_row dbs i in
  let n = mk_small_numeral i in
  if tag = 5 then fibre_mp (SPECL [n; a; b] (el 5 rules)) []
  else if tag = 6 then
    let t = fddb_thm nms tys dbs (dest_small_numeral a)
    and l = fddbs_thm nms tys dbs (dest_small_numeral b) in
    fibre_mp (SPECL [n; a; b; rand(concl t); rand(concl l)] (el 6 rules)) [t; l]
  else failwith "fddbs_thm";;

(* ------------------------------------------------------------------------- *)
(* The witness rows.                                                         *)
(*   names 0 x, 1 y, 2 =, 3 bool, 4 fun                                      *)
(*   types 1 bool, 4 bool->bool, 7 bool->bool->bool (2,3,5,6 list cells)     *)
(*   db    0 x, 1 y, 2 "=", 4 x = x, 6 y = y, 7 x = y, 8 the empty list,     *)
(*         10 (x = y) = (x = y)                                              *)
(* ------------------------------------------------------------------------- *)

let ctl_nms = `["x"; "y"; "="; "bool"; "fun"]`;;
let ctl_tys = `[(2,0,0); (1,3,0); (3,1,0); (3,1,2); (1,4,3); (3,4,0); (3,1,5); (1,4,6)]
                :(num#num#num)list`;;
let ctl_dbs = `[(0,0,1); (0,1,1); (2,2,7); (3,2,0); (3,3,0); (3,2,1); (3,5,1); (3,3,1); (5,0,0);
                 (3,2,7); (3,9,7)]
                :(num#num#num)list`;;

let CTL_DB = map (fddb_thm ctl_nms ctl_tys ctl_dbs) [0;1;2;3;4;5;6;7;9;10];;
let CTL_NIL = fddbs_thm ctl_nms ctl_tys ctl_dbs 8;;

(* x:bool is ok in the initial signature, and the initial theory is ok. *)
let CTL_VAR_OK = prove
 (`!x. hterm_ok (hsigof hinit_ctxt) (TmVar x HBool)`,
  REWRITE_TAC[hterm_ok; hsigof; HBool; HTYPE_OK; LENGTH; ALL] THEN
  REWRITE_TAC[hinit_ctxt; htype_list; hflat; MAP; htypes_of_upd; APPEND; hlookup] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[]);;

(* The bad sequent: no row can stand for [] |- x = y in the initial context. *)
let CTL_XY_NOT_OK = prove
 (mk_neg(list_mk_comb(`fibre_thm_ok`,[`hinit_ctxt`; ctl_nms; ctl_tys; ctl_dbs; `(8,7)`])),
  REWRITE_TAC[fibre_thm_ok; FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `hs:hdbterm list` (X_CHOOSE_THEN `cd:hdbterm`
    (X_CHOOSE_THEN `hyps:holterm list` (X_CHOOSE_THEN `tm:holterm` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `hs:hdbterm list = []` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[CTL_NIL; FDDB_FUNCTIONAL]; ALL_TAC] THEN
  SUBGOAL_THEN `hyps:holterm list = []` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[MEM; list_CASES]; ALL_TAC] THEN
  SUBGOAL_THEN `cd = hdb (TmVar "x" HBool =:= TmVar "y" HBool)` SUBST_ALL_TAC THENL
   [REWRITE_TAC[HDB_EQUATION; htypeof; hdb; HFun; HBool] THEN
    ASM_MESON_TAC[el 7 CTL_DB; FDDB_FUNCTIONAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `tm = (TmVar "x" HBool =:= TmVar "y" HBool)` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`hthyof hinit_ctxt`; `[]:holterm list`; `tm:holterm`] FIBRE_PROVES_WELLTYPED) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `hwelltyped (TmVar "x" HBool =:= TmVar "y" HBool)` ASSUME_TAC THENL
     [REWRITE_TAC[HWELLTYPED_EQUATION; HEQUATION_HAS_TYPE_BOOL; HWELLTYPED_CLAUSES; htypeof];
      ALL_TAC] THEN
    UNDISCH_TAC `hdb tm = hdb (TmVar "x" HBool =:= TmVar "y" HBool)` THEN
    REWRITE_TAC[HDB_EQUATION; htypeof; hdb; HDB_EQ_INV; HDB_VAR] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[hequation; HEqual; htypeof];
    ALL_TAC] THEN
  MP_TAC HCORE_DISTINCT_EQ_UNPROVABLE THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC HEXTENDS_PROVES THEN EXISTS_TAC `hinit_ctxt` THEN
  ASM_REWRITE_TAC[HCORE_EXTENDS_INIT]);;

(* ------------------------------------------------------------------------- *)
(* Rows that are ok: [] |- x = x, [] |- y = y and [] |- (x = y) = (x = y).   *)
(* ------------------------------------------------------------------------- *)

let CTL_BOOL = prove
 (`HBool = TyApp "bool" [] /\
   HFun HBool (HFun HBool HBool) =
   TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]]`,
  REWRITE_TAC[HFun; HBool]);;

let CTL_EQ_OK = prove
 (`hterm_ok (hsigof hinit_ctxt) (TmVar "x" HBool =:= TmVar "y" HBool)`,
  SUBGOAL_THEN `his_std_sig (hsigof hinit_ctxt)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP HTHEORY_OK_STD_SIG HINIT_THEORY_OK) THEN REWRITE_TAC[hthyof; FST];
    ASM_SIMP_TAC[HTERM_OK_EQUATION; CTL_VAR_OK; htypeof]]);;

let CTL_REFL_TAC t =
  MATCH_MP_TAC FIBRE_REFL THEN EXISTS_TAC t THEN
  REWRITE_TAC[HINIT_THEORY_OK; CTL_VAR_OK; CTL_EQ_OK; CTL_NIL] THEN
  REWRITE_TAC[HDB_EQUATION; HTYPEOF_EQUATION; htypeof; hdb; HFun; HBool] THEN
  REWRITE_TAC CTL_DB;;

let CTL_XX_OK = prove
 (list_mk_comb(`fibre_thm_ok`,[`hinit_ctxt`; ctl_nms; ctl_tys; ctl_dbs; `(8,4)`]),
  CTL_REFL_TAC `TmVar "x" HBool`);;

let CTL_YY_OK = prove
 (list_mk_comb(`fibre_thm_ok`,[`hinit_ctxt`; ctl_nms; ctl_tys; ctl_dbs; `(8,6)`]),
  CTL_REFL_TAC `TmVar "y" HBool`);;

let CTL_XYXY_OK = prove
 (list_mk_comb(`fibre_thm_ok`,[`hinit_ctxt`; ctl_nms; ctl_tys; ctl_dbs; `(8,10)`]),
  CTL_REFL_TAC `TmVar "x" HBool =:= TmVar "y" HBool`);;

let ctl_ty = `TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]]`;;
let ctl_x = `hdbVar "x" (TyApp "bool" [])` and ctl_y = `hdbVar "y" (TyApp "bool" [])`;;
let ctl_xy = `hdbComb (hdbComb (hdbConst "=" (TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]])) (hdbVar "x" (TyApp "bool" []))) (hdbVar "y" (TyApp "bool" []))`;;

(* ------------------------------------------------------------------------- *)
(* TRANS without "the middle terms are one": from x = x and y = y it would  *)
(* append x = y.                                                             *)
(* ------------------------------------------------------------------------- *)

let FIBRE_TRANS_UNGUARDED_REFUTED = prove
 (`~(!ctx nms tys dbs h1 c1 h2 c2 hk k ty1 ty2 l m1 m2 r hs1 hs2 hs.
       fibre_thm_ok ctx nms tys dbs (h1,c1) /\ fibre_thm_ok ctx nms tys dbs (h2,c2) /\
       fddbs nms tys dbs h1 hs1 /\ fddbs nms tys dbs h2 hs2 /\
       fddb nms tys dbs c1 (hdbComb (hdbComb (hdbConst "=" ty1) l) m1) /\
       fddb nms tys dbs c2 (hdbComb (hdbComb (hdbConst "=" ty2) m2) r) /\
       fddb nms tys dbs k (hdbComb (hdbComb (hdbConst "=" ty1) l) r) /\
       fddbs nms tys dbs hk hs /\ (!x. MEM x hs1 \/ MEM x hs2 ==> MEM x hs)
       ==> fibre_thm_ok ctx nms tys dbs (hk,k))`,
  DISCH_THEN(MP_TAC o SPECL [`hinit_ctxt`; ctl_nms; ctl_tys; ctl_dbs; `8`; `4`; `8`; `6`;
                              `8`; `7`; ctl_ty; ctl_ty; ctl_x; ctl_x; ctl_y; ctl_y;
                              `[]:hdbterm list`; `[]:hdbterm list`; `[]:hdbterm list`]) THEN
  REWRITE_TAC([CTL_XY_NOT_OK; CTL_XX_OK; CTL_YY_OK; CTL_NIL; MEM] @ CTL_DB));;

(* ------------------------------------------------------------------------- *)
(* EQ_MP without "the second theorem is the left side": from                 *)
(* (x = y) = (x = y) and x = x it would append x = y.                        *)
(* ------------------------------------------------------------------------- *)

let FIBRE_EQ_MP_UNGUARDED_REFUTED = prove
 (`~(!ctx nms tys dbs h1 c1 h2 c2 hk k ty p q hs1 hs2 hs.
       fibre_thm_ok ctx nms tys dbs (h1,c1) /\ fibre_thm_ok ctx nms tys dbs (h2,c2) /\
       fddbs nms tys dbs h1 hs1 /\ fddbs nms tys dbs h2 hs2 /\
       fddb nms tys dbs c1 (hdbComb (hdbComb (hdbConst "=" ty) p) q) /\
       fddb nms tys dbs k q /\
       fddbs nms tys dbs hk hs /\ (!x. MEM x hs1 \/ MEM x hs2 ==> MEM x hs)
       ==> fibre_thm_ok ctx nms tys dbs (hk,k))`,
  DISCH_THEN(MP_TAC o SPECL [`hinit_ctxt`; ctl_nms; ctl_tys; ctl_dbs; `8`; `10`; `8`; `4`;
                              `8`; `7`;
                              `TyApp "fun" [TyApp "bool" []; TyApp "fun" [TyApp "bool" []; TyApp "bool" []]]`;
                              ctl_xy; ctl_xy;
                              `[]:hdbterm list`; `[]:hdbterm list`; `[]:hdbterm list`]) THEN
  REWRITE_TAC([CTL_XY_NOT_OK; CTL_XYXY_OK; CTL_XX_OK; CTL_NIL; MEM] @ CTL_DB));;
