(* ========================================================================= *)
(* HOL in tcalc: the native fibre of HOL Light's kernel.                     *)
(*                                                                           *)
(* A state is a family of append-only regions of rows of numbers; an id is  *)
(* a row index. Names are a list of strings. Type rows (tag,a,b):            *)
(*   0 TyVar(name a)        1 TyApp(name a, argument list b)                 *)
(*   2 empty list           3 list cell (type a, rest b)                     *)
(* Named term rows (tag,a,b,c,d), built by the construction records; c is *)
(* the term's type and d its de Bruijn image:                                *)
(*   0 TmVar(name a, type b)   1 TmConst(name a, type b)                     *)
(*   2 TmComb(a, b)            3 TmAbs(variable row a, body b)               *)
(* De Bruijn rows (tag,a,b), the canonical form theorems are stated in:     *)
(*   0 dbVar(name a, type b)   1 dbBound(index a)   2 dbConst(name a, type b)*)
(*   3 dbComb(a, b)            4 dbAbs(type a, body b)                       *)
(*   5 empty list              6 list cell (term a, rest b)                  *)
(* Theorem rows: (hypothesis list id, conclusion id), both de Bruijn.        *)
(*                                                                           *)
(* Decoding is relational, so a row that decodes to nothing supports no      *)
(* theorem. Alpha-equivalent terms have one de Bruijn image, so equality of  *)
(* de Bruijn ids decides alpha-equivalence; an equation's side types are     *)
(* read off the type of its equality constant.                               *)
(*                                                                           *)
(* The theorem region's predicate (fibre_thm_ok): a sequent provable in the  *)
(* context's theory has the row's conclusion as its de Bruijn image, and     *)
(* each of its hypotheses is, by de Bruijn image, among the row's            *)
(* hypotheses. Each predicate depends only on rows written before, so        *)
(* appending rows preserves it.                                              *)
(* ========================================================================= *)

(* Load after HolInHol/make.ml (the port of Candle's syntax and proves).    *)

(* ------------------------------------------------------------------------- *)
(* Decoding types and type lists.                                            *)
(* ------------------------------------------------------------------------- *)

let fdty_RULES,fdty_INDUCT,fdty_CASES = new_inductive_definition
 `(!i a b. i < LENGTH tys /\ EL i tys = (0,a,b) /\ a < LENGTH nms
           ==> fdty (nms:string list) (tys:(num#num#num)list) i (TyVar (EL a nms))) /\
  (!i a b args. i < LENGTH tys /\ EL i tys = (1,a,b) /\ a < LENGTH nms /\
                fdtys nms tys b args
           ==> fdty nms tys i (TyApp (EL a nms) args)) /\
  (!i a b. i < LENGTH tys /\ EL i tys = (2,a,b) ==> fdtys nms tys i []) /\
  (!i a b ty rest. i < LENGTH tys /\ EL i tys = (3,a,b) /\
                   fdty nms tys a ty /\ fdtys nms tys b rest
           ==> fdtys nms tys i (CONS ty rest))`;;

(* ------------------------------------------------------------------------- *)
(* Decoding de Bruijn terms and term lists.                                  *)
(* ------------------------------------------------------------------------- *)

let fddb_RULES,fddb_INDUCT,fddb_CASES = new_inductive_definition
 `(!i a b ty. i < LENGTH dbs /\ EL i dbs = (0,a,b) /\ a < LENGTH nms /\
              fdty nms tys b ty
           ==> fddb (nms:string list) (tys:(num#num#num)list)
                    (dbs:(num#num#num)list) i (hdbVar (EL a nms) ty)) /\
  (!i a b. i < LENGTH dbs /\ EL i dbs = (1,a,b)
           ==> fddb nms tys dbs i (hdbBound a)) /\
  (!i a b ty. i < LENGTH dbs /\ EL i dbs = (2,a,b) /\ a < LENGTH nms /\
              fdty nms tys b ty
           ==> fddb nms tys dbs i (hdbConst (EL a nms) ty)) /\
  (!i a b s t. i < LENGTH dbs /\ EL i dbs = (3,a,b) /\
               fddb nms tys dbs a s /\ fddb nms tys dbs b t
           ==> fddb nms tys dbs i (hdbComb s t)) /\
  (!i a b ty t. i < LENGTH dbs /\ EL i dbs = (4,a,b) /\
                fdty nms tys a ty /\ fddb nms tys dbs b t
           ==> fddb nms tys dbs i (hdbAbs ty t)) /\
  (!i a b. i < LENGTH dbs /\ EL i dbs = (5,a,b)
           ==> fddbs nms tys dbs i []) /\
  (!i a b t rest. i < LENGTH dbs /\ EL i dbs = (6,a,b) /\
                  fddb nms tys dbs a t /\ fddbs nms tys dbs b rest
           ==> fddbs nms tys dbs i (CONS t rest))`;;

(* ------------------------------------------------------------------------- *)
(* Decoding named terms.                                                     *)
(* ------------------------------------------------------------------------- *)

let fdtm_RULES,fdtm_INDUCT,fdtm_CASES = new_inductive_definition
 `(!i a b c d ty. i < LENGTH ntms /\ EL i ntms = (0,a,b,c,d) /\ a < LENGTH nms /\
                  fdty nms tys b ty
           ==> fdtm (nms:string list) (tys:(num#num#num)list)
                    (ntms:(num#num#num#num#num)list) i (TmVar (EL a nms) ty)) /\
  (!i a b c d ty. i < LENGTH ntms /\ EL i ntms = (1,a,b,c,d) /\ a < LENGTH nms /\
                  fdty nms tys b ty
           ==> fdtm nms tys ntms i (TmConst (EL a nms) ty)) /\
  (!i a b c d s t. i < LENGTH ntms /\ EL i ntms = (2,a,b,c,d) /\
                   fdtm nms tys ntms a s /\ fdtm nms tys ntms b t
           ==> fdtm nms tys ntms i (TmComb s t)) /\
  (!i a b c d v t. i < LENGTH ntms /\ EL i ntms = (3,a,b,c,d) /\
                   fdtm nms tys ntms a v /\ fdtm nms tys ntms b t
           ==> fdtm nms tys ntms i (TmAbs v t))`;;

let ntm_ty = new_definition
 `ntm_ty (r:num#num#num#num#num) = FST(SND(SND(SND r)))`;;

let ntm_db = new_definition
 `ntm_db (r:num#num#num#num#num) = SND(SND(SND(SND r)))`;;

(* ------------------------------------------------------------------------- *)
(* The theorem region's predicate, relative to a theory context.             *)
(* ------------------------------------------------------------------------- *)

let fibre_thm_ok = new_definition
 `fibre_thm_ok ctx nms tys dbs (th:num#num) <=>
    ?hs cd hyps tm. fddbs nms tys dbs (FST th) hs /\ fddb nms tys dbs (SND th) cd /\
                    hproves (hthyof ctx) hyps tm /\ hdb tm = cd /\
                    (!x. MEM x hyps ==> MEM (hdb x) hs)`;;

(* A type row is ok when it decodes to a type, or a list of types, that is *)
(* ok in the context's signature.                                           *)
let fibre_ty_ok = new_definition
 `fibre_ty_ok ctx nms tys i <=>
    (?ty. fdty nms tys i ty /\ htype_ok (FST(hsigof ctx)) ty) \/
    (?l. fdtys nms tys i l /\ ALL (htype_ok (FST(hsigof ctx))) l)`;;

(* A named term row is ok when its term is ok in the signature, and its type *)
(* and de Bruijn image fields decode to the term's type and image.          *)
let fibre_tm_ok = new_definition
 `fibre_tm_ok ctx nms tys dbs ntms i <=>
    ?t. fdtm nms tys ntms i t /\ hterm_ok (hsigof ctx) t /\
        fdty nms tys (ntm_ty (EL i ntms)) (htypeof t) /\
        fddb nms tys dbs (ntm_db (EL i ntms)) (hdb t)`;;

(* ------------------------------------------------------------------------- *)
(* Growth: appending rows preserves every decoding and the predicate.        *)
(* ------------------------------------------------------------------------- *)

let FIBRE_EL_APPEND = prove
 (`!(l:A list) m i. i < LENGTH l
      ==> i < LENGTH (APPEND l m) /\ EL i (APPEND l m) = EL i l`,
  SIMP_TAC[LENGTH_APPEND; EL_APPEND] THEN ARITH_TAC);;

let FIBRE_EL_APPEND_NAMES = prove
 (`!(l:A list) m i. i < LENGTH l ==> i < LENGTH (APPEND l m) /\ EL i (APPEND l m) = EL i l`,
  REWRITE_TAC[FIBRE_EL_APPEND]);;

let FDTY_EXTEND = prove
 (`!nms tys nm ty.
      (!i t. fdty nms tys i t ==> fdty (APPEND nms nm) (APPEND tys ty) i t) /\
      (!i l. fdtys nms tys i l ==> fdtys (APPEND nms nm) (APPEND tys ty) i l)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC fdty_INDUCT THEN
  MESON_TAC[fdty_RULES; FIBRE_EL_APPEND]);;

let FDDB_EXTEND = prove
 (`!nms tys dbs nm ty db.
      (!i t. fddb nms tys dbs i t
             ==> fddb (APPEND nms nm) (APPEND tys ty) (APPEND dbs db) i t) /\
      (!i l. fddbs nms tys dbs i l
             ==> fddbs (APPEND nms nm) (APPEND tys ty) (APPEND dbs db) i l)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC fddb_INDUCT THEN
  MESON_TAC[fddb_RULES; FIBRE_EL_APPEND; FDTY_EXTEND]);;

(* ------------------------------------------------------------------------- *)
(* Decoding is a function: equal ids decode to equal objects, so a guard    *)
(* comparing ids is sound.                                                   *)
(* ------------------------------------------------------------------------- *)

let FDTY_FUNCTIONAL = prove
 (`!nms tys.
      (!i t. fdty nms tys i t ==> !u. fdty nms tys i u ==> t = u) /\
      (!i l. fdtys nms tys i l ==> !m. fdtys nms tys i m ==> l = m)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC fdty_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[fdty_CASES] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[holtype_INJ; CONS_11]);;

let FDDB_FUNCTIONAL = prove
 (`!nms tys dbs.
      (!i t. fddb nms tys dbs i t ==> !u. fddb nms tys dbs i u ==> t = u) /\
      (!i l. fddbs nms tys dbs i l ==> !m. fddbs nms tys dbs i m ==> l = m)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC fddb_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[fddb_CASES] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[hdbterm_INJ; CONS_11; FDTY_FUNCTIONAL]);;

let FDTM_EXTEND = prove
 (`!nms tys ntms nm ty nt i t.
      fdtm nms tys ntms i t ==> fdtm (APPEND nms nm) (APPEND tys ty) (APPEND ntms nt) i t`,
  REPLICATE_TAC 6 GEN_TAC THEN MATCH_MP_TAC fdtm_INDUCT THEN
  MESON_TAC[fdtm_RULES; FIBRE_EL_APPEND; FDTY_EXTEND]);;

let FDTM_FUNCTIONAL = prove
 (`!nms tys ntms.
      !i t. fdtm nms tys ntms i t ==> !u. fdtm nms tys ntms i u ==> t = u`,
  REPLICATE_TAC 3 GEN_TAC THEN MATCH_MP_TAC fdtm_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[fdtm_CASES] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[holterm_INJ; FDTY_FUNCTIONAL]);;

(* ------------------------------------------------------------------------- *)
(* Reading a theorem row back as a provable sequent.                         *)
(* ------------------------------------------------------------------------- *)

let FIBRE_THM_GET = prove
 (`!ctx nms tys dbs h c hs C.
      fibre_thm_ok ctx nms tys dbs (h,c) /\
      fddbs nms tys dbs h hs /\ fddb nms tys dbs c C
      ==> ?hyps tm. hproves (hthyof ctx) hyps tm /\ hdb tm = C /\
                    (!x. MEM x hyps ==> MEM (hdb x) hs)`,
  REWRITE_TAC[fibre_thm_ok; FST; SND] THEN MESON_TAC[FDDB_FUNCTIONAL]);;

let FIBRE_THM_INTRO = prove
 (`!ctx nms tys dbs h c hs hyps tm.
      fddbs nms tys dbs h hs /\ fddb nms tys dbs c (hdb tm) /\
      hproves (hthyof ctx) hyps tm /\ (!x. MEM x hyps ==> MEM (hdb x) hs)
      ==> fibre_thm_ok ctx nms tys dbs (h,c)`,
  REWRITE_TAC[fibre_thm_ok; FST; SND] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Inverting the de Bruijn translation, and equations.                       *)
(* ------------------------------------------------------------------------- *)

let HDB_COMB_INV = prove
 (`!t a b. hdb t = hdbComb a b <=>
           ?t1 t2. t = TmComb t1 t2 /\ hdb t1 = a /\ hdb t2 = b`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `t:holterm` (cases "holterm")) THEN
  REWRITE_TAC[hdb; hdbterm_DISTINCT; hdbterm_INJ; holterm_DISTINCT; holterm_INJ] THEN
  MESON_TAC[]);;

let HDB_EQ_INV = prove
 (`!t ty l r. hdb t = hdbComb (hdbComb (hdbConst "=" ty) l) r <=>
              ?a b. t = TmComb (TmComb (TmConst "=" ty) a) b /\
                    hdb a = l /\ hdb b = r`,
  REWRITE_TAC[HDB_COMB_INV; HDB_CONST] THEN MESON_TAC[]);;

let HDB_EQUATION = prove
 (`!s t. hdb (s =:= t) =
         hdbComb (hdbComb (hdbConst "=" (HFun (htypeof s) (HFun (htypeof s) HBool)))
                          (hdb s)) (hdb t)`,
  REWRITE_TAC[hequation; HEqual; hdb]);;

(* In a standard signature, an ok term headed by the constant "=" is an      *)
(* equation in the sense of =:=, so the type of "=" names the sides' type.  *)
let FIBRE_EQUATION_SHAPE = prove
 (`!sig ty l r.
      his_std_sig sig /\ hterm_ok sig (TmComb (TmComb (TmConst "=" ty) l) r)
      ==> TmComb (TmComb (TmConst "=" ty) l) r = (l =:= r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[his_std_sig] THEN STRIP_TAC THEN
  UNDISCH_TAC `hterm_ok sig (TmComb (TmComb (TmConst "=" ty) l) r)` THEN
  ASM_REWRITE_TAC[hterm_ok; option_INJ; UNWIND_THM1; HWELLTYPED_CLAUSES; htypeof;
                  HTYPE_SUBST_HFUN; HBool; HTYPE_SUBST; MAP] THEN
  REWRITE_TAC[hequation; HEqual; HBool; holterm_INJ] THEN
  MESON_TAC[HFUN_INJ]);;

let FIBRE_THM_EQ = prove
 (`!ctx nms tys dbs h c hs ty l r.
      fibre_thm_ok ctx nms tys dbs (h,c) /\ fddbs nms tys dbs h hs /\
      fddb nms tys dbs c (hdbComb (hdbComb (hdbConst "=" ty) l) r)
      ==> ?hyps a b. hproves (hthyof ctx) hyps (a =:= b) /\
                     hdb a = l /\ hdb b = r /\
                     ty = HFun (htypeof a) (HFun (htypeof a) HBool) /\
                     (!x. MEM x hyps ==> MEM (hdb x) hs)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP FIBRE_THM_GET) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`hyps:holterm list`; `tm:holterm`] THEN
  REWRITE_TAC[HDB_EQ_INV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:holterm`; `b:holterm`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `TmComb (TmComb (TmConst "=" ty) a) b = (a =:= b)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIBRE_EQUATION_SHAPE THEN EXISTS_TAC `FST(hthyof ctx)` THEN
    ASM_MESON_TAC[HPROVES_TERM_OK; HTHEORY_OK_STD_SIG]; ALL_TAC] THEN
  SUBGOAL_THEN `ty = HFun (htypeof a) (HFun (htypeof a) HBool)` ASSUME_TAC THENL
   [UNDISCH_TAC `TmComb (TmComb (TmConst "=" ty) a) b = (a =:= b)` THEN
    REWRITE_TAC[hequation; HEqual; holterm_INJ]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`hyps:holterm list`; `a:holterm`; `b:holterm`] THEN
  ASM_MESON_TAC[]);;

(* Terms in provable sequents are welltyped. *)
let FIBRE_PROVES_WELLTYPED = prove
 (`!thy hyps tm. hproves thy hyps tm
      ==> hwelltyped tm /\ !x. MEM x hyps ==> hwelltyped x`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP HPROVES_TERM_OK) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[hwelltyped]);;

let FIBRE_PROVES_EQ_WELLTYPED = prove
 (`!thy hyps a b. hproves thy hyps (a =:= b) ==> hwelltyped a /\ hwelltyped b`,
  MESON_TAC[HPROVES_TERM_OK; HEQUATION_HAS_TYPE_BOOL]);;

(* ------------------------------------------------------------------------- *)
(* The rules as row steps. Each lemma takes the rows the step appends, as    *)
(* decoded objects, and shows the new theorem row satisfies the predicate.   *)
(* Hypothesis lists only need to contain the images of the derivation's     *)
(* hypotheses, so a row may list more hypotheses than it needs.             *)
(* ------------------------------------------------------------------------- *)

let FIBRE_HYPS_UNION = prove
 (`!h1 h2 (hs1:hdbterm list) hs2 hs.
      (!x. MEM x h1 ==> MEM (hdb x) hs1) /\ (!x. MEM x h2 ==> MEM (hdb x) hs2) /\
      (!x. MEM x hs1 \/ MEM x hs2 ==> MEM x hs)
      ==> !x. MEM x (HTERM_UNION h1 h2) ==> MEM (hdb x) hs`,
  MESON_TAC[HTERM_UNION_NONEW]);;

let FIBRE_TRANS = prove
 (`!ctx nms tys dbs h1 c1 h2 c2 hk k ty1 ty2 l m r hs1 hs2 hs.
      fibre_thm_ok ctx nms tys dbs (h1,c1) /\ fibre_thm_ok ctx nms tys dbs (h2,c2) /\
      fddbs nms tys dbs h1 hs1 /\ fddbs nms tys dbs h2 hs2 /\
      fddb nms tys dbs c1 (hdbComb (hdbComb (hdbConst "=" ty1) l) m) /\
      fddb nms tys dbs c2 (hdbComb (hdbComb (hdbConst "=" ty2) m) r) /\
      fddb nms tys dbs k (hdbComb (hdbComb (hdbConst "=" ty1) l) r) /\
      fddbs nms tys dbs hk hs /\ (!x. MEM x hs1 \/ MEM x hs2 ==> MEM x hs)
      ==> fibre_thm_ok ctx nms tys dbs (hk,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `dbs:(num#num#num)list`; `h1:num`; `c1:num`; `hs1:hdbterm list`;
                `ty1:holtype`; `l:hdbterm`; `m:hdbterm`] FIBRE_THM_EQ) THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `dbs:(num#num#num)list`; `h2:num`; `c2:num`; `hs2:hdbterm list`;
                `ty2:holtype`; `m:hdbterm`; `r:hdbterm`] FIBRE_THM_EQ) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`hb:holterm list`; `a2:holterm`; `b2:holterm`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`ha:holterm list`; `a1:holterm`; `b1:holterm`] THEN STRIP_TAC THEN
  MATCH_MP_TAC FIBRE_THM_INTRO THEN
  MAP_EVERY EXISTS_TAC [`hs:hdbterm list`; `HTERM_UNION ha hb`; `a1 =:= b2`] THEN
  SUBGOAL_THEN `hdb (a1 =:= b2) = hdbComb (hdbComb (hdbConst "=" ty1) l) r`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[HDB_EQUATION]; ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HPROVES_TRANS THEN
    MAP_EVERY EXISTS_TAC [`b1:holterm`; `a2:holterm`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `hwelltyped b1 /\ hwelltyped a2` ASSUME_TAC THENL
     [ASM_MESON_TAC[FIBRE_PROVES_EQ_WELLTYPED]; ASM_SIMP_TAC[HACONV_DB]];
    MATCH_MP_TAC FIBRE_HYPS_UNION THEN
    MAP_EVERY EXISTS_TAC [`hs1:hdbterm list`; `hs2:hdbterm list`] THEN
    ASM_REWRITE_TAC[]]);;

let FIBRE_THM_EQT = prove
 (`!ctx nms tys dbs h c hs A l r.
      fibre_thm_ok ctx nms tys dbs (h,c) /\ fddbs nms tys dbs h hs /\
      fddb nms tys dbs c (hdbComb (hdbComb (hdbConst "=" (HFun A (HFun A HBool))) l) r)
      ==> ?hyps a b. hproves (hthyof ctx) hyps (a =:= b) /\
                     hdb a = l /\ hdb b = r /\ htypeof a = A /\
                     (!x. MEM x hyps ==> MEM (hdb x) hs)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP FIBRE_THM_EQ) THEN
  REWRITE_TAC[HFUN_INJ] THEN MESON_TAC[]);;

let FIBRE_EQ_MP = prove
 (`!ctx nms tys dbs h1 c1 h2 c2 hk k ty p q hs1 hs2 hs.
      fibre_thm_ok ctx nms tys dbs (h1,c1) /\ fibre_thm_ok ctx nms tys dbs (h2,c2) /\
      fddbs nms tys dbs h1 hs1 /\ fddbs nms tys dbs h2 hs2 /\
      fddb nms tys dbs c1 (hdbComb (hdbComb (hdbConst "=" ty) p) q) /\
      fddb nms tys dbs c2 p /\ fddb nms tys dbs k q /\
      fddbs nms tys dbs hk hs /\ (!x. MEM x hs1 \/ MEM x hs2 ==> MEM x hs)
      ==> fibre_thm_ok ctx nms tys dbs (hk,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `dbs:(num#num#num)list`; `h1:num`; `c1:num`; `hs1:hdbterm list`;
                `ty:holtype`; `p:hdbterm`; `q:hdbterm`] FIBRE_THM_EQ) THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `dbs:(num#num#num)list`; `h2:num`; `c2:num`; `hs2:hdbterm list`;
                `p:hdbterm`] FIBRE_THM_GET) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`hb:holterm list`; `t2:holterm`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`ha:holterm list`; `a:holterm`; `b:holterm`] THEN STRIP_TAC THEN
  MATCH_MP_TAC FIBRE_THM_INTRO THEN
  MAP_EVERY EXISTS_TAC [`hs:hdbterm list`; `HTERM_UNION ha hb`; `b:holterm`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HPROVES_EQ_MP THEN
    MAP_EVERY EXISTS_TAC [`a:holterm`; `t2:holterm`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `hwelltyped a /\ hwelltyped t2` ASSUME_TAC THENL
     [ASM_MESON_TAC[FIBRE_PROVES_EQ_WELLTYPED; FIBRE_PROVES_WELLTYPED];
      ASM_SIMP_TAC[HACONV_DB]];
    MATCH_MP_TAC FIBRE_HYPS_UNION THEN
    MAP_EVERY EXISTS_TAC [`hs1:hdbterm list`; `hs2:hdbterm list`] THEN
    ASM_REWRITE_TAC[]]);;

let FIBRE_MK_COMB = prove
 (`!ctx nms tys dbs h1 c1 h2 c2 hk k f g x y tx ty hs1 hs2 hs.
      fibre_thm_ok ctx nms tys dbs (h1,c1) /\ fibre_thm_ok ctx nms tys dbs (h2,c2) /\
      fddbs nms tys dbs h1 hs1 /\ fddbs nms tys dbs h2 hs2 /\
      fddb nms tys dbs c1
        (hdbComb (hdbComb (hdbConst "=" (HFun (HFun tx ty) (HFun (HFun tx ty) HBool))) f) g) /\
      fddb nms tys dbs c2 (hdbComb (hdbComb (hdbConst "=" (HFun tx (HFun tx HBool))) x) y) /\
      fddb nms tys dbs k (hdbComb (hdbComb (hdbConst "=" (HFun ty (HFun ty HBool)))
                                           (hdbComb f x)) (hdbComb g y)) /\
      fddbs nms tys dbs hk hs /\ (!z. MEM z hs1 \/ MEM z hs2 ==> MEM z hs)
      ==> fibre_thm_ok ctx nms tys dbs (hk,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `dbs:(num#num#num)list`; `h1:num`; `c1:num`; `hs1:hdbterm list`;
                `HFun tx ty`; `f:hdbterm`; `g:hdbterm`] FIBRE_THM_EQT) THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `dbs:(num#num#num)list`; `h2:num`; `c2:num`; `hs2:hdbterm list`;
                `tx:holtype`; `x:hdbterm`; `y:hdbterm`] FIBRE_THM_EQT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`hb:holterm list`; `a2:holterm`; `b2:holterm`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`ha:holterm list`; `a1:holterm`; `b1:holterm`] THEN STRIP_TAC THEN
  MATCH_MP_TAC FIBRE_THM_INTRO THEN
  MAP_EVERY EXISTS_TAC [`hs:hdbterm list`; `HTERM_UNION ha hb`;
                        `TmComb a1 a2 =:= TmComb b1 b2`] THEN
  SUBGOAL_THEN
   `hdb (TmComb a1 a2 =:= TmComb b1 b2) =
    hdbComb (hdbComb (hdbConst "=" (HFun ty (HFun ty HBool))) (hdbComb f x)) (hdbComb g y)`
    SUBST1_TAC THENL
   [ASM_REWRITE_TAC[HDB_EQUATION; hdb; htypeof; HCODOMAIN_HFUN]; ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HPROVES_MK_COMB THEN ASM_REWRITE_TAC[HWELLTYPED_CLAUSES] THEN
    ASM_MESON_TAC[FIBRE_PROVES_EQ_WELLTYPED];
    MATCH_MP_TAC FIBRE_HYPS_UNION THEN
    MAP_EVERY EXISTS_TAC [`hs1:hdbterm list`; `hs2:hdbterm list`] THEN
    ASM_REWRITE_TAC[]]);;

let FIBRE_REFL = prove
 (`!ctx nms tys dbs e k t.
      htheory_ok (hthyof ctx) /\ hterm_ok (hsigof ctx) t /\
      fddbs nms tys dbs e [] /\ fddb nms tys dbs k (hdb (t =:= t))
      ==> fibre_thm_ok ctx nms tys dbs (e,k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIBRE_THM_INTRO THEN
  MAP_EVERY EXISTS_TAC [`[]:hdbterm list`; `[]:holterm list`; `t =:= t`] THEN
  ASM_REWRITE_TAC[MEM] THEN MATCH_MP_TAC HPROVES_REFL THEN
  ASM_REWRITE_TAC[hthyof; FST]);;

let FIBRE_ASSUME = prove
 (`!ctx nms tys dbs hk k p hs.
      htheory_ok (hthyof ctx) /\ hterm_ok (hsigof ctx) p /\ p hhas_type HBool /\
      fddb nms tys dbs k (hdb p) /\ fddbs nms tys dbs hk hs /\ MEM (hdb p) hs
      ==> fibre_thm_ok ctx nms tys dbs (hk,k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIBRE_THM_INTRO THEN
  MAP_EVERY EXISTS_TAC [`hs:hdbterm list`; `[p]:holterm list`; `p:holterm`] THEN
  ASM_REWRITE_TAC[MEM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HPROVES_ASSUME THEN ASM_REWRITE_TAC[hthyof; FST];
    ASM_MESON_TAC[]]);;

let FIBRE_BETA = prove
 (`!ctx nms tys dbs e k x ty t.
      htheory_ok (hthyof ctx) /\ htype_ok (FST(hsigof ctx)) ty /\
      hterm_ok (hsigof ctx) t /\ fddbs nms tys dbs e [] /\
      fddb nms tys dbs k (hdb (TmComb (TmAbs (TmVar x ty) t) (TmVar x ty) =:= t))
      ==> fibre_thm_ok ctx nms tys dbs (e,k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIBRE_THM_INTRO THEN
  MAP_EVERY EXISTS_TAC [`[]:hdbterm list`; `[]:holterm list`;
                        `TmComb (TmAbs (TmVar x ty) t) (TmVar x ty) =:= t`] THEN
  ASM_REWRITE_TAC[MEM] THEN MATCH_MP_TAC HPROVES_BETA THEN
  ASM_REWRITE_TAC[hthyof; FST]);;

let FIBRE_ABS = prove
 (`!ctx nms tys dbs h c hk k x ty A l r hs.
      fibre_thm_ok ctx nms tys dbs (h,c) /\ fddbs nms tys dbs h hs /\
      fddb nms tys dbs c (hdbComb (hdbComb (hdbConst "=" (HFun A (HFun A HBool))) l) r) /\
      htype_ok (FST(hsigof ctx)) ty /\
      (!p. MEM p hs ==> ~hdbVFREE_IN (hdbVar x ty) p) /\
      fddb nms tys dbs k
        (hdbComb (hdbComb (hdbConst "=" (HFun (HFun ty A) (HFun (HFun ty A) HBool)))
                          (hdbAbs ty (hbind (x,ty) 0 l))) (hdbAbs ty (hbind (x,ty) 0 r))) /\
      fddbs nms tys dbs hk hs
      ==> fibre_thm_ok ctx nms tys dbs (hk,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `dbs:(num#num#num)list`; `h:num`; `c:num`; `hs:hdbterm list`;
                `A:holtype`; `l:hdbterm`; `r:hdbterm`] FIBRE_THM_EQT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`hyps:holterm list`; `a:holterm`; `b:holterm`] THEN STRIP_TAC THEN
  MATCH_MP_TAC FIBRE_THM_INTRO THEN
  MAP_EVERY EXISTS_TAC [`hs:hdbterm list`; `hyps:holterm list`;
                        `TmAbs (TmVar x ty) a =:= TmAbs (TmVar x ty) b`] THEN
  SUBGOAL_THEN
   `hdb (TmAbs (TmVar x ty) a =:= TmAbs (TmVar x ty) b) =
    hdbComb (hdbComb (hdbConst "=" (HFun (HFun ty A) (HFun (HFun ty A) HBool)))
                     (hdbAbs ty (hbind (x,ty) 0 l))) (hdbAbs ty (hbind (x,ty) 0 r))`
    SUBST1_TAC THENL
   [ASM_REWRITE_TAC[HDB_EQUATION; hdb; htypeof; hdest_var]; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC HPROVES_ABS THEN ASM_REWRITE_TAC[hthyof; FST] THEN
  REWRITE_TAC[NOT_EX; GSYM ALL_MEM] THEN X_GEN_TAC `p:holterm` THEN DISCH_TAC THEN
  SUBGOAL_THEN `hwelltyped p` ASSUME_TAC THENL
   [ASM_MESON_TAC[FIBRE_PROVES_WELLTYPED]; ALL_TAC] THEN
  MP_TAC(SPEC `p:holterm` HDBVFREE_IN_VFREE_IN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; hdb]) THEN ASM_MESON_TAC[]);;

let FIBRE_DEDUCT = prove
 (`!ctx nms tys dbs h1 c1 h2 c2 hk k p q hs1 hs2 hs.
      fibre_thm_ok ctx nms tys dbs (h1,c1) /\ fibre_thm_ok ctx nms tys dbs (h2,c2) /\
      fddbs nms tys dbs h1 hs1 /\ fddbs nms tys dbs h2 hs2 /\
      fddb nms tys dbs c1 p /\ fddb nms tys dbs c2 q /\
      fddb nms tys dbs k
        (hdbComb (hdbComb (hdbConst "=" (HFun HBool (HFun HBool HBool))) p) q) /\
      fddbs nms tys dbs hk hs /\
      (!z. (MEM z hs1 /\ ~(z = q)) \/ (MEM z hs2 /\ ~(z = p)) ==> MEM z hs)
      ==> fibre_thm_ok ctx nms tys dbs (hk,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `dbs:(num#num#num)list`; `h1:num`; `c1:num`; `hs1:hdbterm list`;
                `p:hdbterm`] FIBRE_THM_GET) THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `dbs:(num#num#num)list`; `h2:num`; `c2:num`; `hs2:hdbterm list`;
                `q:hdbterm`] FIBRE_THM_GET) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`hb:holterm list`; `t2:holterm`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`ha:holterm list`; `t1:holterm`] THEN STRIP_TAC THEN
  MATCH_MP_TAC FIBRE_THM_INTRO THEN
  MAP_EVERY EXISTS_TAC
   [`hs:hdbterm list`;
    `HTERM_UNION (FILTER ((~) o HACONV t2) ha) (FILTER ((~) o HACONV t1) hb)`;
    `t1 =:= t2`] THEN
  SUBGOAL_THEN `htypeof t1 = HBool` ASSUME_TAC THENL
   [ASM_MESON_TAC[HPROVES_TERM_OK; HWELLTYPED_LEMMA]; ALL_TAC] THEN
  SUBGOAL_THEN
   `hdb (t1 =:= t2) =
    hdbComb (hdbComb (hdbConst "=" (HFun HBool (HFun HBool HBool))) p) q`
    SUBST1_TAC THENL
   [ASM_REWRITE_TAC[HDB_EQUATION]; ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HPROVES_DEDUCT_ANTISYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hwelltyped t1 /\ hwelltyped t2 /\
                (!z. MEM z ha ==> hwelltyped z) /\ (!z. MEM z hb ==> hwelltyped z)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FIBRE_PROVES_WELLTYPED]; ALL_TAC] THEN
  X_GEN_TAC `z:holterm` THEN DISCH_THEN(MP_TAC o MATCH_MP HTERM_UNION_NONEW) THEN
  REWRITE_TAC[MEM_FILTER; o_THM] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
   [DISJ1_TAC; DISJ2_TAC] THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[HACONV_DB]);;

let FIBRE_INST_TYPE = prove
 (`!ctx nms tys dbs h c hk k C tyin hs1 hs.
      fibre_thm_ok ctx nms tys dbs (h,c) /\ fddbs nms tys dbs h hs1 /\
      fddb nms tys dbs c C /\
      ALL (htype_ok (FST(hsigof ctx))) (MAP FST tyin) /\
      fddb nms tys dbs k (hdbINST tyin C) /\ fddbs nms tys dbs hk hs /\
      (!z. MEM z hs1 ==> MEM (hdbINST tyin z) hs)
      ==> fibre_thm_ok ctx nms tys dbs (hk,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `dbs:(num#num#num)list`; `h:num`; `c:num`; `hs1:hdbterm list`;
                `C:hdbterm`] FIBRE_THM_GET) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`hyps:holterm list`; `tm:holterm`] THEN STRIP_TAC THEN
  MATCH_MP_TAC FIBRE_THM_INTRO THEN
  MAP_EVERY EXISTS_TAC [`hs:hdbterm list`; `MAP (HINST tyin) hyps`; `HINST tyin tm`] THEN
  SUBGOAL_THEN `hwelltyped tm /\ !x. MEM x hyps ==> hwelltyped x` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FIBRE_PROVES_WELLTYPED]; ALL_TAC] THEN
  ASM_SIMP_TAC[HINST_DBINST] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HPROVES_INST_TYPE THEN ASM_REWRITE_TAC[hthyof; FST];
    REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[HINST_DBINST]]);;

let FIBRE_INST = prove
 (`!ctx nms tys dbs h c hk k C ilist hs1 hs.
      fibre_thm_ok ctx nms tys dbs (h,c) /\ fddbs nms tys dbs h hs1 /\
      fddb nms tys dbs c C /\
      (!s s'. MEM (s',s) ilist
              ==> ?x ty. s = TmVar x ty /\ s' hhas_type ty /\ hterm_ok (hsigof ctx) s') /\
      fddb nms tys dbs k (hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) ilist) C) /\
      fddbs nms tys dbs hk hs /\
      (!z. MEM z hs1 ==> MEM (hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) ilist) z) hs)
      ==> fibre_thm_ok ctx nms tys dbs (hk,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `dbs:(num#num#num)list`; `h:num`; `c:num`; `hs1:hdbterm list`;
                `C:hdbterm`] FIBRE_THM_GET) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`hyps:holterm list`; `tm:holterm`] THEN STRIP_TAC THEN
  MATCH_MP_TAC FIBRE_THM_INTRO THEN
  MAP_EVERY EXISTS_TAC [`hs:hdbterm list`; `MAP (HVSUBST ilist) hyps`; `HVSUBST ilist tm`] THEN
  SUBGOAL_THEN `hwelltyped tm /\ !x. MEM x hyps ==> hwelltyped x` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FIBRE_PROVES_WELLTYPED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. hwelltyped t
        ==> hdb (HVSUBST ilist t) = hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) ilist) (hdb t)`
    ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPEC `t:holterm` HVSUBST_DBVSUBST) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[hwelltyped];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HPROVES_INST THEN ASM_REWRITE_TAC[hthyof; FST];
    REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Growth preserves every region's predicate.                                *)
(* ------------------------------------------------------------------------- *)

let FIBRE_TY_OK_EXTEND = prove
 (`!ctx nms tys nm ty i.
      fibre_ty_ok ctx nms tys i ==> fibre_ty_ok ctx (APPEND nms nm) (APPEND tys ty) i`,
  REWRITE_TAC[fibre_ty_ok] THEN MESON_TAC[FDTY_EXTEND]);;

let FIBRE_TM_OK_EXTEND = prove
 (`!ctx nms tys dbs ntms nm ty db nt i.
      i < LENGTH ntms /\ fibre_tm_ok ctx nms tys dbs ntms i
      ==> fibre_tm_ok ctx (APPEND nms nm) (APPEND tys ty) (APPEND dbs db)
                      (APPEND ntms nt) i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fibre_tm_ok] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[FIBRE_EL_APPEND] THEN
  ASM_MESON_TAC[FDTM_EXTEND; FDTY_EXTEND; FDDB_EXTEND]);;

let FIBRE_THM_OK_EXTEND = prove
 (`!ctx nms tys dbs nm ty db th.
      fibre_thm_ok ctx nms tys dbs th
      ==> fibre_thm_ok ctx (APPEND nms nm) (APPEND tys ty) (APPEND dbs db) th`,
  REWRITE_TAC[fibre_thm_ok] THEN MESON_TAC[FDDB_EXTEND]);;

(* ------------------------------------------------------------------------- *)
(* Reading row predicates back.                                              *)
(* ------------------------------------------------------------------------- *)

let FDTY_TAG = prove
 (`!nms tys.
      (!i ty. fdty nms tys i ty ==> FST(EL i tys) = 0 \/ FST(EL i tys) = 1) /\
      (!i l. fdtys nms tys i l ==> FST(EL i tys) = 2 \/ FST(EL i tys) = 3)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[fdty_CASES] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let FIBRE_TY_OK_GET = prove
 (`!ctx nms tys i ty.
      fibre_ty_ok ctx nms tys i /\ fdty nms tys i ty ==> htype_ok (FST(hsigof ctx)) ty`,
  REWRITE_TAC[fibre_ty_ok] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[FDTY_FUNCTIONAL]; ALL_TAC] THEN
  SUBGOAL_THEN `F` CONTR_TAC THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`] FDTY_TAG) THEN
  DISCH_THEN(fun th -> MP_TAC(SPECL [`i:num`; `ty:holtype`] (CONJUNCT1 th)) THEN
                       MP_TAC(SPECL [`i:num`; `l:holtype list`] (CONJUNCT2 th))) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let FIBRE_TYS_OK_GET = prove
 (`!ctx nms tys i l.
      fibre_ty_ok ctx nms tys i /\ fdtys nms tys i l
      ==> ALL (htype_ok (FST(hsigof ctx))) l`,
  REWRITE_TAC[fibre_ty_ok] THEN REPEAT STRIP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[FDTY_FUNCTIONAL]] THEN
  SUBGOAL_THEN `F` CONTR_TAC THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`] FDTY_TAG) THEN
  DISCH_THEN(fun th -> MP_TAC(SPECL [`i:num`; `ty:holtype`] (CONJUNCT1 th)) THEN
                       MP_TAC(SPECL [`i:num`; `l:holtype list`] (CONJUNCT2 th))) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let FIBRE_TM_OK_GET = prove
 (`!ctx nms tys dbs ntms i t.
      fibre_tm_ok ctx nms tys dbs ntms i /\ fdtm nms tys ntms i t
      ==> hterm_ok (hsigof ctx) t /\
          fdty nms tys (ntm_ty (EL i ntms)) (htypeof t) /\
          fddb nms tys dbs (ntm_db (EL i ntms)) (hdb t)`,
  REWRITE_TAC[fibre_tm_ok] THEN MESON_TAC[FDTM_FUNCTIONAL]);;

(* ------------------------------------------------------------------------- *)
(* The construction records as row steps.                                    *)
(* ------------------------------------------------------------------------- *)

let FIBRE_TYVAR = prove
 (`!ctx nms tys i n b.
      i < LENGTH tys /\ EL i tys = (0,n,b) /\ n < LENGTH nms
      ==> fibre_ty_ok ctx nms tys i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fibre_ty_ok] THEN DISJ1_TAC THEN
  EXISTS_TAC `TyVar (EL n nms)` THEN REWRITE_TAC[HTYPE_OK] THEN
  ASM_MESON_TAC[fdty_RULES]);;

let FIBRE_TYAPP = prove
 (`!ctx nms tys i n l args.
      i < LENGTH tys /\ EL i tys = (1,n,l) /\ n < LENGTH nms /\
      fdtys nms tys l args /\ ALL (htype_ok (FST(hsigof ctx))) args /\
      hlookup (FST(hsigof ctx)) (EL n nms) = SOME (LENGTH args)
      ==> fibre_ty_ok ctx nms tys i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fibre_ty_ok] THEN DISJ1_TAC THEN
  EXISTS_TAC `TyApp (EL n nms) args` THEN ASM_REWRITE_TAC[HTYPE_OK] THEN
  ASM_MESON_TAC[fdty_RULES]);;

let FIBRE_TYNIL = prove
 (`!ctx nms tys i a b.
      i < LENGTH tys /\ EL i tys = (2,a,b) ==> fibre_ty_ok ctx nms tys i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fibre_ty_ok] THEN DISJ2_TAC THEN
  EXISTS_TAC `[]:holtype list` THEN REWRITE_TAC[ALL] THEN
  ASM_MESON_TAC[fdty_RULES]);;

let FIBRE_TYCONS = prove
 (`!ctx nms tys i a b ty rest.
      i < LENGTH tys /\ EL i tys = (3,a,b) /\
      fdty nms tys a ty /\ htype_ok (FST(hsigof ctx)) ty /\
      fdtys nms tys b rest /\ ALL (htype_ok (FST(hsigof ctx))) rest
      ==> fibre_ty_ok ctx nms tys i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fibre_ty_ok] THEN DISJ2_TAC THEN
  EXISTS_TAC `CONS (ty:holtype) rest` THEN ASM_REWRITE_TAC[ALL] THEN
  ASM_MESON_TAC[fdty_RULES]);;

let FIBRE_VAR = prove
 (`!ctx nms tys dbs ntms i n y d ty.
      i < LENGTH ntms /\ EL i ntms = (0,n,y,y,d) /\ n < LENGTH nms /\
      fdty nms tys y ty /\ fibre_ty_ok ctx nms tys y /\
      fddb nms tys dbs d (hdbVar (EL n nms) ty)
      ==> fibre_tm_ok ctx nms tys dbs ntms i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fibre_tm_ok] THEN
  EXISTS_TAC `TmVar (EL n nms) ty` THEN
  ASM_REWRITE_TAC[ntm_ty; ntm_db; hterm_ok; htypeof; hdb; FST; SND] THEN
  ASM_MESON_TAC[fdtm_RULES; FIBRE_TY_OK_GET]);;

let FIBRE_CONST = prove
 (`!ctx nms tys dbs ntms i n y d ty ty0 tyin.
      i < LENGTH ntms /\ EL i ntms = (1,n,y,y,d) /\ n < LENGTH nms /\
      fdty nms tys y ty /\ fibre_ty_ok ctx nms tys y /\
      hlookup (SND(hsigof ctx)) (EL n nms) = SOME ty0 /\
      HTYPE_SUBST tyin ty0 = ty /\
      fddb nms tys dbs d (hdbConst (EL n nms) ty)
      ==> fibre_tm_ok ctx nms tys dbs ntms i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fibre_tm_ok] THEN
  EXISTS_TAC `TmConst (EL n nms) ty` THEN
  ASM_REWRITE_TAC[ntm_ty; ntm_db; hterm_ok; htypeof; hdb; FST; SND] THEN
  ASM_MESON_TAC[fdtm_RULES; FIBRE_TY_OK_GET]);;

let FIBRE_COMB = prove
 (`!ctx nms tys dbs ntms i s t y d ts tt B.
      i < LENGTH ntms /\ EL i ntms = (2,s,t,y,d) /\
      fibre_tm_ok ctx nms tys dbs ntms s /\ fibre_tm_ok ctx nms tys dbs ntms t /\
      fdtm nms tys ntms s ts /\ fdtm nms tys ntms t tt /\
      htypeof ts = HFun (htypeof tt) B /\ fdty nms tys y B /\
      fddb nms tys dbs d (hdbComb (hdb ts) (hdb tt))
      ==> fibre_tm_ok ctx nms tys dbs ntms i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fibre_tm_ok] THEN
  EXISTS_TAC `TmComb ts tt` THEN
  ASM_REWRITE_TAC[ntm_ty; ntm_db; hterm_ok; htypeof; hdb; FST; SND;
                  HCODOMAIN_HFUN; HWELLTYPED_CLAUSES] THEN
  ASM_MESON_TAC[fdtm_RULES; FIBRE_TM_OK_GET; HTERM_OK_WELLTYPED]);;

let FIBRE_ABSN = prove
 (`!ctx nms tys dbs ntms i v b y d x ty tb.
      i < LENGTH ntms /\ EL i ntms = (3,v,b,y,d) /\
      fibre_tm_ok ctx nms tys dbs ntms v /\ fibre_tm_ok ctx nms tys dbs ntms b /\
      fdtm nms tys ntms v (TmVar x ty) /\ fdtm nms tys ntms b tb /\
      fdty nms tys y (HFun ty (htypeof tb)) /\
      fddb nms tys dbs d (hdbAbs ty (hbind (x,ty) 0 (hdb tb)))
      ==> fibre_tm_ok ctx nms tys dbs ntms i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fibre_tm_ok] THEN
  EXISTS_TAC `TmAbs (TmVar x ty) tb` THEN
  ASM_REWRITE_TAC[ntm_ty; ntm_db; htypeof; hdb; hdest_var; FST; SND] THEN
  REWRITE_TAC[hterm_ok; holterm_INJ] THEN
  SUBGOAL_THEN `hterm_ok (hsigof ctx) (TmVar x ty) /\ hterm_ok (hsigof ctx) tb`
    MP_TAC THENL [ASM_MESON_TAC[FIBRE_TM_OK_GET]; REWRITE_TAC[hterm_ok]] THEN
  STRIP_TAC THEN ASM_MESON_TAC[fdtm_RULES]);;

(* ------------------------------------------------------------------------- *)
(* Theory records. Extending the context keeps every row's predicate, and   *)
(* each record's theorems are provable in the extended context.             *)
(* ------------------------------------------------------------------------- *)

let FIBRE_HUPDATES_EXTENDS = prove
 (`!upd ctx. upd hupdates ctx ==> (CONS upd ctx) hextends ctx`,
  MESON_TAC[hextends_RULES]);;

let FIBRE_CTX_EXTEND = prove
 (`!c1 c2 nms tys dbs ntms i th.
      c2 hextends c1
      ==> (fibre_ty_ok c1 nms tys i ==> fibre_ty_ok c2 nms tys i) /\
          (fibre_tm_ok c1 nms tys dbs ntms i ==> fibre_tm_ok c2 nms tys dbs ntms i) /\
          (fibre_thm_ok c1 nms tys dbs th ==> fibre_thm_ok c2 nms tys dbs th)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[fibre_ty_ok; fibre_tm_ok; fibre_thm_ok] THEN REPEAT CONJ_TAC THENL
   [STRIP_TAC THENL
     [DISJ1_TAC THEN ASM_MESON_TAC[HEXTENDS_TYPE_OK];
      DISJ2_TAC THEN EXISTS_TAC `l:holtype list` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `htype_ok (FST(hsigof c1))` THEN
      ASM_MESON_TAC[HEXTENDS_TYPE_OK]];
    ASM_MESON_TAC[HEXTENDS_TERM_OK];
    ASM_MESON_TAC[HEXTENDS_PROVES]]);;

(* A closed theorem of the context, as a theorem row with no hypotheses. *)
let FIBRE_THM_OF_PROVES = prove
 (`!ctx nms tys dbs e k t.
      hproves (hthyof ctx) [] t /\ fddbs nms tys dbs e [] /\ fddb nms tys dbs k (hdb t)
      ==> fibre_thm_ok ctx nms tys dbs (e,k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIBRE_THM_INTRO THEN
  MAP_EVERY EXISTS_TAC [`[]:hdbterm list`; `[]:holterm list`; `t:holterm`] THEN
  ASM_REWRITE_TAC[MEM]);;

let FIBRE_NEW_TYPE = prove
 (`!ctx name arity.
      hlookup (htype_list ctx) name = NONE
      ==> (CONS (HNewType name arity) ctx) hextends ctx`,
  MESON_TAC[HOL_NEW_TYPE; FIBRE_HUPDATES_EXTENDS]);;

let FIBRE_NEW_CONSTANT = prove
 (`!ctx name ty.
      hlookup (hconst_list ctx) name = NONE /\ htype_ok (htype_list ctx) ty
      ==> (CONS (HNewConst name ty) ctx) hextends ctx`,
  MESON_TAC[HOL_NEW_CONSTANT; FIBRE_HUPDATES_EXTENDS]);;

let FIBRE_NEW_AXIOM = prove
 (`!ctx nms tys dbs e k tm.
      htheory_ok (hthyof ctx) /\ hterm_ok (hsigof ctx) tm /\ tm hhas_type HBool /\
      fddbs nms tys dbs e [] /\ fddb nms tys dbs k (hdb tm)
      ==> (CONS (HNewAxiom tm) ctx) hextends ctx /\
          fibre_thm_ok (CONS (HNewAxiom tm) ctx) nms tys dbs (e,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `tm:holterm`] HOL_NEW_AXIOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[FIBRE_HUPDATES_EXTENDS] THEN
  MATCH_MP_TAC FIBRE_THM_OF_PROVES THEN EXISTS_TAC `tm:holterm` THEN
  ASM_REWRITE_TAC[]);;

let FIBRE_NEW_DEFINITION = prove
 (`!ctx nms tys dbs e k c ty r.
      htheory_ok (hthyof ctx) /\ hterm_ok (hsigof ctx) (TmVar c ty =:= r) /\
      hlookup (hconst_list ctx) c = NONE /\ HCLOSED r /\
      (!v. MEM v (htvars r) ==> MEM v (htyvars ty)) /\
      fddbs nms tys dbs e [] /\ fddb nms tys dbs k (hdb (TmConst c ty =:= r))
      ==> (CONS (HConstSpec [c,r] (TmVar c ty =:= r)) ctx) hextends ctx /\
          fibre_thm_ok (CONS (HConstSpec [c,r] (TmVar c ty =:= r)) ctx) nms tys dbs (e,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `c:string`; `ty:holtype`; `r:holterm`]
               HOL_NEW_BASIC_DEFINITION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[FIBRE_HUPDATES_EXTENDS] THEN
  MATCH_MP_TAC FIBRE_THM_OF_PROVES THEN EXISTS_TAC `TmConst c ty =:= r` THEN
  ASM_REWRITE_TAC[]);;

(* The two theorems of a type definition, in HOL Light's shapes, are taken  *)
(* from HOL_NEW_BASIC_TYPE_DEFINITION rather than transcribed.               *)
let FIBRE_NEW_TYPEDEF =
  let th = SPEC_ALL HOL_NEW_BASIC_TYPE_DEFINITION in
  let ant,cncl = dest_imp(concl th) in
  let rest = rand cncl in
  let p1,p2 = dest_conj rest in
  let t1 = rand p1 and t2 = rand p2 in
  let ctx' = rand(rand(rator(rator p1))) and ctx = `ctxt:hupdate list` in
  let nms = `nms:string list` and tys = `tys:(num#num#num)list`
  and dbs = `dbs:(num#num#num)list` and e = `e:num`
  and k1 = `k1:num` and k2 = `k2:num` in
  let fd k t = list_mk_comb(`fddb`,[nms;tys;dbs;k;mk_comb(`hdb`,t)]) in
  let ok k = list_mk_comb(`fibre_thm_ok`,[ctx';nms;tys;dbs;mk_pair(e,k)]) in
  let goal = mk_imp(list_mk_conj[ant; list_mk_comb(`fddbs`,[nms;tys;dbs;e;`[]:hdbterm list`]);
                                 fd k1 t1; fd k2 t2],
                    list_mk_conj[mk_comb(mk_comb(`(hextends)`,ctx'),ctx); ok k1; ok k2]) in
  prove(goal,
    STRIP_TAC THEN MP_TAC th THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[FIBRE_HUPDATES_EXTENDS] THEN
    CONJ_TAC THEN MATCH_MP_TAC FIBRE_THM_OF_PROVES THEN ASM_MESON_TAC[]);;
