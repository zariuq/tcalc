(* ========================================================================= *)
(* The native checker's record steps over decoded rows, and their           *)
(* simulation of what a HOLR stream means (holr_step, holr_spec.ml).        *)
(*                                                                           *)
(* A native state holds the context; the decoded names; the type, named     *)
(* term, de Bruijn and theorem rows of the fibre (holfibre.ml); the N map   *)
(* (HOLR name id to name row) and the Y map (HOLR type id to type row); the *)
(* dropped ids; and the axiom policy. HOLR term ids are named-row indices   *)
(* and HOLR theorem ids are theorem-row indices.                            *)
(*                                                                           *)
(* nat_step states what each record handler does, on decoded rows: rows     *)
(* are appended; every appended type row is ok in the context; the new map  *)
(* entry, named row or theorem row decodes to what the record makes. The   *)
(* guards are stated on decoded objects, as holr_step states its own. A    *)
(* theorem row's decoding is what the record's fibre lemma needs, so the   *)
(* lemma gives the row's derivation.                                        *)
(*                                                                           *)
(* nat_sim ns hs: the HOLR state hs is the decoding of the native state ns: *)
(* the same context, drops and policy; the names of the N map; the types   *)
(* of the Y map; the terms of the named rows; and, for each theorem row, a *)
(* derivable sequent whose conclusion has the row's conclusion as its de   *)
(* Bruijn image and whose hypotheses have images among the row's.          *)
(*                                                                           *)
(* The invariant nat_ok: the row predicates and the maps (nat_rows_ok), and *)
(* canonicity (nat_canon): no two name rows hold one name, and no two type *)
(* or de Bruijn rows decode to one object. Steps append only new rows, so  *)
(* canonicity is kept (NAT_STEP_CANON).                                     *)
(*                                                                           *)
(* NAT_STEP_SIM: a native step from an ok state is matched by a holr_step,  *)
(* and keeps the invariant and the simulation; one lemma per record kind   *)
(* (NAT_SIM_NAME_REC, NAT_SIM_TYVAR, ...) gives it. NAT_RUN_SIM lifts it   *)
(* to runs. NAT_ACCEPTS: a stream whose records the native steps run from  *)
(* a canonical bootstrap state with empty maps, at the larger of the       *)
(* host's policy floor and the header's policy, is accepted in HOLR's      *)
(* meaning; NAT_ACCEPTS_SOUND adds that the final context meets the policy,*)
(* every theorem row of the final state is derivable and its rows are     *)
(* canonical, and NAT_ACCEPTS_BOOT states it from the first native slice's *)
(* bootstrap rows. NAT_TYS_OK_ONE and NAT_TYS_OK_APPEND compose the type   *)
(* rows a handler appends. NAT_CONTROL_ACCEPTS is a positive control: a    *)
(* stream of the slice's record kinds, ending in a claim, runs natively     *)
(* and is accepted under every host floor.                                  *)
(*                                                                           *)
(* Loaded after holfibre_all.ml.                                            *)
(* ========================================================================= *)

new_type_abbrev("nstate",
  `:hupdate list # string list # (num#num#num)list # (num#num#num#num#num)list #
    (num#num#num)list # (num#num)list # num list # num list # (num#num)list # num`);;

(* ------------------------------------------------------------------------- *)
(* The invariant: the row regions satisfy the fibre's invariant (the        *)
(* context extends HOL's initial context, and every type, named and theorem *)
(* row satisfies its predicate), the N map points at names and the Y map at *)
(* rows that decode to types.                                               *)
(* ------------------------------------------------------------------------- *)

let nat_rows_ok = new_definition
 `nat_rows_ok ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) <=>
    fibre_inv (ctx,nms,tys,ntms,dbs,ths) /\
    ALL (\i. i < LENGTH nms) nmap /\ ALL (\y. ?ty. fdty nms tys y ty) ymap`;;

(* ------------------------------------------------------------------------- *)
(* Canonicity. Two type rows are the same object when they decode to one    *)
(* type or to one list of types; two de Bruijn rows, when they decode to   *)
(* one term or one list of terms. The rows are canonical when no two name  *)
(* rows hold one name, every de Bruijn row decodes, and rows that are the   *)
(* same object are one row. (Every type row decodes already: fibre_inv.)   *)
(* ------------------------------------------------------------------------- *)

let fdty_same = new_definition
 `fdty_same nms tys i j <=>
    (?t. fdty nms tys i t /\ fdty nms tys j t) \/
    (?l. fdtys nms tys i l /\ fdtys nms tys j l)`;;

let fddb_same = new_definition
 `fddb_same nms tys dbs i j <=>
    (?t. fddb nms tys dbs i t /\ fddb nms tys dbs j t) \/
    (?l. fddbs nms tys dbs i l /\ fddbs nms tys dbs j l)`;;

let nat_canon = new_definition
 `nat_canon (nms:string list) (tys:(num#num#num)list) (dbs:(num#num#num)list) <=>
    (!i j. i < LENGTH nms /\ j < LENGTH nms /\ EL i nms = EL j nms ==> i = j) /\
    (!i. i < LENGTH dbs ==> (?t. fddb nms tys dbs i t) \/ (?l. fddbs nms tys dbs i l)) /\
    (!i j. fdty_same nms tys i j ==> i = j) /\
    (!i j. fddb_same nms tys dbs i j ==> i = j)`;;

(* The invariant: the row predicates and the maps, and canonicity. *)
let nat_ok = new_definition
 `nat_ok ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) <=>
    nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\ nat_canon nms tys dbs`;;

(* A step appends a name, a type row or a de Bruijn row only when it is     *)
(* new: no row before it is the same object. An appended de Bruijn row      *)
(* decodes (an appended type row does: nat_tys_ok). This is what interning *)
(* gives: a lookup that finds every existing row, and an append only when   *)
(* none was found.                                                          *)
let nat_new_names = new_definition
 `nat_new_names (nms:string list) mn <=>
    !k j. k < LENGTH nms + LENGTH mn /\ LENGTH nms <= k /\ j < k
          ==> ~(EL j (APPEND nms mn) = EL k (APPEND nms mn))`;;

let nat_new_rows = new_definition
 `nat_new_rows nms tys dbs (mt:(num#num#num)list) (md:(num#num#num)list) <=>
    (!k j. k < LENGTH tys + LENGTH mt /\ LENGTH tys <= k /\ j < k
           ==> ~fdty_same nms (APPEND tys mt) j k) /\
    (!k. k < LENGTH dbs + LENGTH md /\ LENGTH dbs <= k
         ==> (?t. fddb nms (APPEND tys mt) (APPEND dbs md) k t) \/
             (?l. fddbs nms (APPEND tys mt) (APPEND dbs md) k l)) /\
    (!k j. k < LENGTH dbs + LENGTH md /\ LENGTH dbs <= k /\ j < k
           ==> ~fddb_same nms (APPEND tys mt) (APPEND dbs md) j k)`;;

(* A theorem row together with a derivable sequent it stands for. *)
let fibre_thm_wit = new_definition
 `fibre_thm_wit ctx nms tys dbs (th:num#num) ((hyps,tm):holterm list#holterm) <=>
    ?hs. fddbs nms tys dbs (FST th) hs /\ fddb nms tys dbs (SND th) (hdb tm) /\
         hproves (hthyof ctx) hyps tm /\ (!x. MEM x hyps ==> MEM (hdb x) hs)`;;

let FIBRE_THM_OK_WIT = prove
 (`!ctx nms tys dbs th.
      fibre_thm_ok ctx nms tys dbs th <=> ?hyps tm. fibre_thm_wit ctx nms tys dbs th (hyps,tm)`,
  REWRITE_TAC[fibre_thm_ok; fibre_thm_wit] THEN MESON_TAC[]);;

(* The HOLR state is the decoding of the native one. *)
let nat_sim = new_definition
 `nat_sim ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate)
          ((hctx,hnms,htys,htms,hths,hdrops,hpol):hrstate) <=>
    hctx = ctx /\ hnms = MAP (\i. EL i nms) nmap /\
    LENGTH htys = LENGTH ymap /\
    (!j. j < LENGTH ymap ==> fdty nms tys (EL j ymap) (EL j htys)) /\
    LENGTH htms = LENGTH ntms /\
    (!j. j < LENGTH ntms ==> fdtm nms tys ntms j (EL j htms)) /\
    LENGTH hths = LENGTH ths /\
    (!j. j < LENGTH ths ==> fibre_thm_wit ctx nms tys dbs (EL j ths) (EL j hths)) /\
    hdrops = drops /\ hpol = pol`;;

(* Every type, term and theorem operand is a live id: below its space's     *)
(* count and not dropped. The counts are the Y map's, the named rows' and  *)
(* the theorem rows'.                                                       *)
let nat_ops_live = new_definition
 `nat_ops_live ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) r <=>
    ALL (\y. holr_live 1 y (LENGTH ymap) drops) (FST(holr_operands r)) /\
    ALL (\t. holr_live 2 t (LENGTH ntms) drops) (FST(SND(holr_operands r))) /\
    ALL (\h. holr_live 3 h (LENGTH ths) drops) (SND(SND(holr_operands r)))`;;

(* The type rows a step appends are ok in the context. *)
let nat_tys_ok = new_definition
 `nat_tys_ok ctx nms tys (mt:(num#num#num)list) <=>
    !i. LENGTH tys <= i /\ i < LENGTH tys + LENGTH mt
        ==> fibre_ty_ok ctx nms (APPEND tys mt) i`;;

(* The two theorems HOL Light's new_basic_type_definition returns, as       *)
(* functions of the type's name, the constants' names, P, x and the sorted *)
(* type variables of P (HOL_NEW_BASIC_TYPE_DEFINITION states them).        *)
let htydef_abs = new_definition
 `htydef_abs tyname absname repname (x:holterm) params =
    TmComb (TmConst absname (HFun (htypeof x) (TyApp tyname (MAP TyVar params))))
           (TmComb (TmConst repname (HFun (TyApp tyname (MAP TyVar params)) (htypeof x)))
                   (TmVar "a" (TyApp tyname (MAP TyVar params)))) =:=
    TmVar "a" (TyApp tyname (MAP TyVar params))`;;

let htydef_rep = new_definition
 `htydef_rep tyname absname repname P (x:holterm) params =
    TmComb P (TmVar "r" (htypeof x)) =:=
    (TmComb (TmConst repname (HFun (TyApp tyname (MAP TyVar params)) (htypeof x)))
            (TmComb (TmConst absname (HFun (htypeof x) (TyApp tyname (MAP TyVar params))))
                    (TmVar "r" (htypeof x))) =:=
     TmVar "r" (htypeof x))`;;

(* ------------------------------------------------------------------------- *)
(* The record steps. In each clause the state before is                     *)
(* (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol); a step may append type   *)
(* rows mt (each ok) and de Bruijn rows md, all new (nat_new_rows), and     *)
(* appends at most one map entry or named row, or the theorem rows the      *)
(* record makes; NAME may append names mn, all new (nat_new_names). The     *)
(* name of N id n is EL (EL n nmap) nms, and the type of Y id y the         *)
(* decoding of EL y ymap. NEW_AXIOM is admitted under the policy as         *)
(* holr_step admits it (holr_axiom_ok).                                     *)
(*                                                                           *)
(* Kinds with a clause: NAME, TYVAR, TYAPP, VAR, CONST, COMB, ABS; REFL,    *)
(* TRANS, MK_COMB, ABS_RULE, BETA, ASSUME, EQ_MP, DEDUCT, INST_TYPE, INST;  *)
(* EXPECT_ALPHA, LABEL, EMIT, DROP_TYPE, DROP_TERM, DROP_THM, POLICY;       *)
(* NEW_TYPE, NEW_CONSTANT, NEW_AXIOM, NEW_DEFINITION, NEW_TYPEDEF. A record *)
(* of any other kind (EXPECT, EXPECT_AXIOMS, EXPECT_REFUSED) has no native  *)
(* step, so no run contains it; holr_step has no clause for them either.    *)
(*                                                                           *)
(* NEW_TYPEDEF takes P and x from theorem row h's decoding: any welltyped  *)
(* P x whose image is the row's conclusion (an alpha-variant of the        *)
(* derivation's). Its two theorem rows decode to the images of HOL Light's *)
(* two theorems, and its appended type rows are ok in the extended context. *)
(* ------------------------------------------------------------------------- *)

let nat_step_RULES,nat_step_INDUCT,nat_step_CASES = new_inductive_definition
 `(!ctx nms tys ntms dbs ths nmap ymap drops pol bs mn i.
     i < LENGTH (APPEND nms mn) /\ EL i (APPEND nms mn) = holr_name bs /\
     nat_new_names nms mn
     ==> nat_step ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) (RName bs)
                  (ctx,APPEND nms mn,tys,ntms,dbs,ths,APPEND nmap [i],ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol n mt md y.
     n < LENGTH nmap /\ nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fdty nms (APPEND tys mt) y (TyVar (EL (EL n nmap) nms))
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTyVar n)
                  (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,ths,nmap,APPEND ymap [y],drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol n ys args mt md y.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTyApp n ys) /\
     n < LENGTH nmap /\
     hlookup (htype_list ctx) (EL (EL n nmap) nms) = SOME (LENGTH ys) /\
     ALL2 (\i ty. fdty nms tys (EL i ymap) ty) ys args /\
     nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fdty nms (APPEND tys mt) y (TyApp (EL (EL n nmap) nms) args)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTyApp n ys)
                  (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,ths,nmap,APPEND ymap [y],drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol n y ty mt md d.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RVar n y) /\
     n < LENGTH nmap /\ fdty nms tys (EL y ymap) ty /\ nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fddb nms (APPEND tys mt) (APPEND dbs md) d (hdbVar (EL (EL n nmap) nms) ty)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RVar n y)
                  (ctx,nms,APPEND tys mt,APPEND ntms [(0,EL n nmap,EL y ymap,EL y ymap,d)],
                   APPEND dbs md,ths,nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol n y ty ty0 tyin mt md d.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RConst n y) /\
     n < LENGTH nmap /\ hlookup (hconst_list ctx) (EL (EL n nmap) nms) = SOME ty0 /\
     fdty nms tys (EL y ymap) ty /\ ty = HTYPE_SUBST tyin ty0 /\ nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fddb nms (APPEND tys mt) (APPEND dbs md) d (hdbConst (EL (EL n nmap) nms) ty)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RConst n y)
                  (ctx,nms,APPEND tys mt,APPEND ntms [(1,EL n nmap,EL y ymap,EL y ymap,d)],
                   APPEND dbs md,ths,nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol s t ts tt B mt md yb d.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RComb s t) /\
     fdtm nms tys ntms s ts /\ fdtm nms tys ntms t tt /\ htypeof ts = HFun (htypeof tt) B /\
     nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\ fdty nms (APPEND tys mt) yb B /\
     fddb nms (APPEND tys mt) (APPEND dbs md) d (hdbComb (hdb ts) (hdb tt))
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RComb s t)
                  (ctx,nms,APPEND tys mt,APPEND ntms [(2,s,t,yb,d)],
                   APPEND dbs md,ths,nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol v t x ty tb mt md yf d.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAbs v t) /\
     fdtm nms tys ntms v (TmVar x ty) /\ fdtm nms tys ntms t tb /\
     nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\ fdty nms (APPEND tys mt) yf (HFun ty (htypeof tb)) /\
     fddb nms (APPEND tys mt) (APPEND dbs md) d (hdbAbs ty (hbind (x,ty) 0 (hdb tb)))
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAbs v t)
                  (ctx,nms,APPEND tys mt,APPEND ntms [(3,v,t,yf,d)],
                   APPEND dbs md,ths,nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol t tm mt md e k.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t) /\
     fdtm nms tys ntms t tm /\ nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fddbs nms (APPEND tys mt) (APPEND dbs md) e [] /\
     fddb nms (APPEND tys mt) (APPEND dbs md) k (hdb (tm =:= tm))
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t)
                  (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(e,k)],
                   nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol h1 h2 hs1 hs2 ty1 ty2 l mid r mt md hk k hs.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTrans h1 h2) /\
     fddbs nms tys dbs (FST(EL h1 ths)) hs1 /\ fddbs nms tys dbs (FST(EL h2 ths)) hs2 /\
     fddb nms tys dbs (SND(EL h1 ths)) (hdbComb (hdbComb (hdbConst "=" ty1) l) mid) /\
     fddb nms tys dbs (SND(EL h2 ths)) (hdbComb (hdbComb (hdbConst "=" ty2) mid) r) /\
     nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fddbs nms (APPEND tys mt) (APPEND dbs md) hk hs /\
     (!z. MEM z hs1 \/ MEM z hs2 ==> MEM z hs) /\
     fddb nms (APPEND tys mt) (APPEND dbs md) k (hdbComb (hdbComb (hdbConst "=" ty1) l) r)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTrans h1 h2)
                  (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(hk,k)],
                   nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol h1 h2 hs1 hs2 f g a b tx ty mt md hk k hs.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RMkComb h1 h2) /\
     fddbs nms tys dbs (FST(EL h1 ths)) hs1 /\ fddbs nms tys dbs (FST(EL h2 ths)) hs2 /\
     fddb nms tys dbs (SND(EL h1 ths))
       (hdbComb (hdbComb (hdbConst "=" (HFun (HFun tx ty) (HFun (HFun tx ty) HBool))) f) g) /\
     fddb nms tys dbs (SND(EL h2 ths))
       (hdbComb (hdbComb (hdbConst "=" (HFun tx (HFun tx HBool))) a) b) /\
     nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fddbs nms (APPEND tys mt) (APPEND dbs md) hk hs /\
     (!z. MEM z hs1 \/ MEM z hs2 ==> MEM z hs) /\
     fddb nms (APPEND tys mt) (APPEND dbs md) k
       (hdbComb (hdbComb (hdbConst "=" (HFun ty (HFun ty HBool))) (hdbComb f a)) (hdbComb g b))
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RMkComb h1 h2)
                  (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(hk,k)],
                   nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol t h x ty hs A l r mt md hk k.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAbsRule t h) /\
     fdtm nms tys ntms t (TmVar x ty) /\
     fddbs nms tys dbs (FST(EL h ths)) hs /\
     fddb nms tys dbs (SND(EL h ths))
       (hdbComb (hdbComb (hdbConst "=" (HFun A (HFun A HBool))) l) r) /\
     (!p. MEM p hs ==> ~hdbVFREE_IN (hdbVar x ty) p) /\
     nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fddbs nms (APPEND tys mt) (APPEND dbs md) hk hs /\
     fddb nms (APPEND tys mt) (APPEND dbs md) k
       (hdbComb (hdbComb (hdbConst "=" (HFun (HFun ty A) (HFun (HFun ty A) HBool)))
                         (hdbAbs ty (hbind (x,ty) 0 l))) (hdbAbs ty (hbind (x,ty) 0 r)))
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAbsRule t h)
                  (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(hk,k)],
                   nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol t x ty tb mt md e k.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RBeta t) /\
     fdtm nms tys ntms t (TmComb (TmAbs (TmVar x ty) tb) (TmVar x ty)) /\
     nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fddbs nms (APPEND tys mt) (APPEND dbs md) e [] /\
     fddb nms (APPEND tys mt) (APPEND dbs md) k
       (hdb (TmComb (TmAbs (TmVar x ty) tb) (TmVar x ty) =:= tb))
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RBeta t)
                  (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(e,k)],
                   nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol t p mt md hk k hs.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAssume t) /\
     fdtm nms tys ntms t p /\ htypeof p = HBool /\ nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fddbs nms (APPEND tys mt) (APPEND dbs md) hk hs /\ MEM (hdb p) hs /\
     fddb nms (APPEND tys mt) (APPEND dbs md) k (hdb p)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAssume t)
                  (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(hk,k)],
                   nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol h1 h2 hs1 hs2 ty p q mt md hk k hs.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REqMp h1 h2) /\
     fddbs nms tys dbs (FST(EL h1 ths)) hs1 /\ fddbs nms tys dbs (FST(EL h2 ths)) hs2 /\
     fddb nms tys dbs (SND(EL h1 ths)) (hdbComb (hdbComb (hdbConst "=" ty) p) q) /\
     fddb nms tys dbs (SND(EL h2 ths)) p /\
     nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fddbs nms (APPEND tys mt) (APPEND dbs md) hk hs /\
     (!z. MEM z hs1 \/ MEM z hs2 ==> MEM z hs) /\
     fddb nms (APPEND tys mt) (APPEND dbs md) k q
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REqMp h1 h2)
                  (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(hk,k)],
                   nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol h1 h2 hs1 hs2 p q mt md hk k hs.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RDeduct h1 h2) /\
     fddbs nms tys dbs (FST(EL h1 ths)) hs1 /\ fddbs nms tys dbs (FST(EL h2 ths)) hs2 /\
     fddb nms tys dbs (SND(EL h1 ths)) p /\ fddb nms tys dbs (SND(EL h2 ths)) q /\
     nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fddbs nms (APPEND tys mt) (APPEND dbs md) hk hs /\
     (!z. (MEM z hs1 /\ ~(z = q)) \/ (MEM z hs2 /\ ~(z = p)) ==> MEM z hs) /\
     fddb nms (APPEND tys mt) (APPEND dbs md) k
       (hdbComb (hdbComb (hdbConst "=" (HFun HBool (HFun HBool HBool))) p) q)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RDeduct h1 h2)
                  (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(hk,k)],
                   nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol ps h tyin hs1 C mt md hk k hs.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RInstType ps h) /\
     ALL2 (\ip it. fdty nms tys (EL (FST ip) ymap) (FST it) /\
                   fdty nms tys (EL (SND ip) ymap) (SND it)) ps tyin /\
     fddbs nms tys dbs (FST(EL h ths)) hs1 /\ fddb nms tys dbs (SND(EL h ths)) C /\
     nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fddbs nms (APPEND tys mt) (APPEND dbs md) hk hs /\
     (!z. MEM z hs1 ==> MEM (hdbINST tyin z) hs) /\
     fddb nms (APPEND tys mt) (APPEND dbs md) k (hdbINST tyin C)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RInstType ps h)
                  (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(hk,k)],
                   nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol ps h ilist hs1 C mt md hk k hs.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RInst ps h) /\
     ALL2 (\ip it. fdtm nms tys ntms (FST ip) (FST it) /\
                   fdtm nms tys ntms (SND ip) (SND it)) ps ilist /\
     (!s s'. MEM (s',s) ilist ==> ?x ty. s = TmVar x ty /\ htypeof s' = ty) /\
     fddbs nms tys dbs (FST(EL h ths)) hs1 /\ fddb nms tys dbs (SND(EL h ths)) C /\
     nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fddbs nms (APPEND tys mt) (APPEND dbs md) hk hs /\
     (!z. MEM z hs1 ==> MEM (hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) ilist) z) hs) /\
     fddb nms (APPEND tys mt) (APPEND dbs md) k
       (hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) ilist) C)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RInst ps h)
                  (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(hk,k)],
                   nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol h hl c hsd cn hyps.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RExpectAlpha h hl c) /\
     fddbs nms tys dbs (FST(EL h ths)) hsd /\
     fdtm nms tys ntms c cn /\ fddb nms tys dbs (SND(EL h ths)) (hdb cn) /\
     ALL2 (fdtm nms tys ntms) hl hyps /\ ALL (\p. htypeof p = HBool) hyps /\
     (!x. MEM x hsd <=> MEM x (MAP hdb hyps))
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RExpectAlpha h hl c)
                  (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol h n.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RLabel h n) /\
     n < LENGTH nmap
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RLabel h n)
                  (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol h.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REmit h)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REmit h)
                  (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol y.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RDropType y)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RDropType y)
                  (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,CONS (1,y) drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol t.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RDropTerm t)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RDropTerm t)
                  (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,CONS (2,t) drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol h.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RDropThm h)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RDropThm h)
                  (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,CONS (3,h) drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol p.
     p <= 2
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RPolicy p)
                  (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,MAX pol p)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol n a.
     n < LENGTH nmap /\ hlookup (htype_list ctx) (EL (EL n nmap) nms) = NONE
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RNewType n a)
                  (CONS (HNewType (EL (EL n nmap) nms) a) ctx,nms,tys,ntms,dbs,ths,
                   nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol n y ty.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RNewConstant n y) /\
     n < LENGTH nmap /\ hlookup (hconst_list ctx) (EL (EL n nmap) nms) = NONE /\
     fdty nms tys (EL y ymap) ty
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RNewConstant n y)
                  (CONS (HNewConst (EL (EL n nmap) nms) ty) ctx,nms,tys,ntms,dbs,ths,
                   nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol t p mt md e k.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RNewAxiom t) /\
     holr_axiom_ok pol ctx p /\ fdtm nms tys ntms t p /\ htypeof p = HBool /\ nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fddbs nms (APPEND tys mt) (APPEND dbs md) e [] /\
     fddb nms (APPEND tys mt) (APPEND dbs md) k (hdb p)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RNewAxiom t)
                  (CONS (HNewAxiom p) ctx,nms,APPEND tys mt,ntms,APPEND dbs md,
                   APPEND ths [(e,k)],nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol t c ty r mt md e k.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RNewDefinition t) /\
     fdtm nms tys ntms t (TmVar c ty =:= r) /\ hlookup (hconst_list ctx) c = NONE /\
     HCLOSED r /\ (!v. MEM v (htvars r) ==> MEM v (htyvars ty)) /\
     nat_tys_ok ctx nms tys mt /\ nat_new_rows nms tys dbs mt md /\
     fddbs nms (APPEND tys mt) (APPEND dbs md) e [] /\
     fddb nms (APPEND tys mt) (APPEND dbs md) k (hdb (TmConst c ty =:= r))
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RNewDefinition t)
                  (CONS (HConstSpec [c,r] (TmVar c ty =:= r)) ctx,nms,APPEND tys mt,ntms,
                   APPEND dbs md,APPEND ths [(e,k)],nmap,ymap,drops,pol)) /\
  (!ctx nms tys ntms dbs ths nmap ymap drops pol n a r h P x params mt md e1 k1 e2 k2.
     nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RNewTypedef n a r h) /\
     n < LENGTH nmap /\ a < LENGTH nmap /\ r < LENGTH nmap /\
     fddbs nms tys dbs (FST(EL h ths)) [] /\
     fddb nms tys dbs (SND(EL h ths)) (hdb (TmComb P x)) /\ hwelltyped (TmComb P x) /\
     HCLOSED P /\
     hlookup (htype_list ctx) (EL (EL n nmap) nms) = NONE /\
     hlookup (hconst_list ctx) (EL (EL a nmap) nms) = NONE /\
     hlookup (hconst_list ctx) (EL (EL r nmap) nms) = NONE /\
     ~(EL (EL a nmap) nms = EL (EL r nmap) nms) /\
     hstring_sorted params /\ (!v. MEM v params <=> MEM v (htvars P)) /\
     nat_tys_ok (CONS (HTypeDefn (EL (EL n nmap) nms) P (EL (EL a nmap) nms)
                                 (EL (EL r nmap) nms)) ctx) nms tys mt /\
     nat_new_rows nms tys dbs mt md /\
     fddbs nms (APPEND tys mt) (APPEND dbs md) e1 [] /\
     fddb nms (APPEND tys mt) (APPEND dbs md) k1
       (hdb (htydef_abs (EL (EL n nmap) nms) (EL (EL a nmap) nms) (EL (EL r nmap) nms)
                        x params)) /\
     fddbs nms (APPEND tys mt) (APPEND dbs md) e2 [] /\
     fddb nms (APPEND tys mt) (APPEND dbs md) k2
       (hdb (htydef_rep (EL (EL n nmap) nms) (EL (EL a nmap) nms) (EL (EL r nmap) nms)
                        P x params))
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RNewTypedef n a r h)
                  (CONS (HTypeDefn (EL (EL n nmap) nms) P (EL (EL a nmap) nms)
                                   (EL (EL r nmap) nms)) ctx,
                   nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(e1,k1); (e2,k2)],
                   nmap,ymap,drops,pol))`;;

(* ------------------------------------------------------------------------- *)
(* Decoding: a decoded id is a row, and decodings survive appended rows.     *)
(* ------------------------------------------------------------------------- *)

let FDTY_BOUND = prove
 (`!nms tys. (!i t. fdty nms tys i t ==> i < LENGTH tys) /\
             (!i l. fdtys nms tys i l ==> i < LENGTH tys)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[fdty_CASES] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let FDDB_BOUND = prove
 (`!nms tys dbs. (!i t. fddb nms tys dbs i t ==> i < LENGTH dbs) /\
                 (!i l. fddbs nms tys dbs i l ==> i < LENGTH dbs)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[fddb_CASES] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let FDTM_BOUND = prove
 (`!nms tys ntms i t. fdtm nms tys ntms i t ==> i < LENGTH ntms`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[fdtm_CASES] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let NAT_EXT = prove
 (`!nms tys dbs ntms mt md nt.
      (!i t. fdty nms tys i t ==> fdty nms (APPEND tys mt) i t) /\
      (!i l. fdtys nms tys i l ==> fdtys nms (APPEND tys mt) i l) /\
      (!i t. fddb nms tys dbs i t ==> fddb nms (APPEND tys mt) (APPEND dbs md) i t) /\
      (!i l. fddbs nms tys dbs i l ==> fddbs nms (APPEND tys mt) (APPEND dbs md) i l) /\
      (!i t. fdtm nms tys ntms i t ==> fdtm nms (APPEND tys mt) (APPEND ntms nt) i t) /\
      (!i t. fdtm nms tys ntms i t ==> fdtm nms (APPEND tys mt) ntms i t)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `[]:string list`;
                 `mt:(num#num#num)list`] FDTY_EXTEND) THEN
  MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                 `[]:string list`; `mt:(num#num#num)list`; `md:(num#num#num)list`]
                FDDB_EXTEND) THEN
  MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`;
                 `ntms:(num#num#num#num#num)list`; `[]:string list`;
                 `mt:(num#num#num)list`; `nt:(num#num#num#num#num)list`] FDTM_EXTEND) THEN
  MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`;
                 `ntms:(num#num#num#num#num)list`; `[]:string list`;
                 `mt:(num#num#num)list`; `[]:(num#num#num#num#num)list`] FDTM_EXTEND) THEN
  REWRITE_TAC[APPEND_NIL] THEN SIMP_TAC[]);;

let NAT_EXT_OK = prove
 (`!ctx nms tys dbs ntms mt md nt.
      (!i. fibre_ty_ok ctx nms tys i ==> fibre_ty_ok ctx nms (APPEND tys mt) i) /\
      (!i. i < LENGTH ntms /\ fibre_tm_ok ctx nms tys dbs ntms i
           ==> fibre_tm_ok ctx nms (APPEND tys mt) (APPEND dbs md) (APPEND ntms nt) i) /\
      (!i. i < LENGTH ntms /\ fibre_tm_ok ctx nms tys dbs ntms i
           ==> fibre_tm_ok ctx nms (APPEND tys mt) (APPEND dbs md) ntms i) /\
      (!th. fibre_thm_ok ctx nms tys dbs th
            ==> fibre_thm_ok ctx nms (APPEND tys mt) (APPEND dbs md) th) /\
      (!th w. fibre_thm_wit ctx nms tys dbs th w
              ==> fibre_thm_wit ctx nms (APPEND tys mt) (APPEND dbs md) th w)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                 `[]:string list`; `mt:(num#num#num)list`] FIBRE_TY_OK_EXTEND) THEN
  MP_TAC(ISPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                 `dbs:(num#num#num)list`; `ntms:(num#num#num#num#num)list`;
                 `[]:string list`; `mt:(num#num#num)list`; `md:(num#num#num)list`;
                 `nt:(num#num#num#num#num)list`] FIBRE_TM_OK_EXTEND) THEN
  MP_TAC(ISPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                 `dbs:(num#num#num)list`; `ntms:(num#num#num#num#num)list`;
                 `[]:string list`; `mt:(num#num#num)list`; `md:(num#num#num)list`;
                 `[]:(num#num#num#num#num)list`] FIBRE_TM_OK_EXTEND) THEN
  MP_TAC(ISPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                 `dbs:(num#num#num)list`; `[]:string list`; `mt:(num#num#num)list`;
                 `md:(num#num#num)list`] FIBRE_THM_OK_EXTEND) THEN
  REWRITE_TAC[APPEND_NIL] THEN SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; fibre_thm_wit] THEN
  MESON_TAC[NAT_EXT]);;

(* ------------------------------------------------------------------------- *)
(* Lists of operands, decoded.                                               *)
(* ------------------------------------------------------------------------- *)

let ALL2_MEM_RIGHT = prove
 (`!P (l:A list) (m:B list) y. ALL2 P l m /\ MEM y m ==> ?x. MEM x l /\ P x y`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; MEM] THEN ASM_MESON_TAC[]);;

let ALL2_MEM_LEFT = prove
 (`!P (l:A list) (m:B list) x. ALL2 P l m /\ MEM x l ==> ?y. MEM y m /\ P x y`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; MEM] THEN ASM_MESON_TAC[]);;

(* Decoded operand lists are the HOLR state's objects, by functionality.    *)
let NAT_ALL2_TMS = prove
 (`!nms tys ntms htms.
      (!j. j < LENGTH ntms ==> fdtm nms tys ntms j (EL j htms))
      ==> !hl hyps. ALL2 (fdtm nms tys ntms) hl hyps ==> hyps = MAP (\i. EL i htms) hl`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; MAP; CONS_11] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FDTM_FUNCTIONAL; FDTM_BOUND]; ASM_MESON_TAC[]]);;

let NAT_ALL2_TYS = prove
 (`!nms tys ymap htys.
      (!j. j < LENGTH ymap ==> fdty nms tys (EL j ymap) (EL j htys))
      ==> !ys args. ALL (\y. y < LENGTH ymap) ys /\
                    ALL2 (\i ty. fdty nms tys (EL i ymap) ty) ys args
                    ==> args = MAP (\i. EL i htys) ys`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; ALL2; MAP; CONS_11] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FDTY_FUNCTIONAL]; ASM_MESON_TAC[]]);;

let ALL_HOLR_PAIRS_FLAT = prove
 (`!P ps. ALL P (holr_pairs_flat ps) <=> ALL (\p. P (FST p) /\ P (SND p)) ps`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[holr_pairs_flat; ALL] THEN
  SPEC_TAC(`h:num#num`,`p:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  ASM_REWRITE_TAC[holr_pairs_flat; ALL; CONJ_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Reading the invariant and the simulation.                                 *)
(* ------------------------------------------------------------------------- *)

let NAT_OPS_LIVE_SIM = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol hctx hnms htys htms hths hdrops hpol r.
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (hctx,hnms,htys,htms,hths,hdrops,hpol)
      ==> (holr_ops_live (hctx,hnms,htys,htms,hths,hdrops,hpol) r <=>
           nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nat_sim] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[holr_ops_live; nat_ops_live]);;

let NAT_SIM_CTX = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol hctx hnms htys htms hths hdrops hpol.
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (hctx,hnms,htys,htms,hths,hdrops,hpol)
      ==> hctx = ctx /\ hdrops = drops /\ hpol = pol`,
  REWRITE_TAC[nat_sim] THEN MESON_TAC[]);;

let NAT_SIM_NAME = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol hctx hnms htys htms hths hdrops hpol n.
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (hctx,hnms,htys,htms,hths,hdrops,hpol) /\ n < LENGTH nmap
      ==> n < LENGTH hnms /\ EL n hnms = EL (EL n nmap) nms`,
  REWRITE_TAC[nat_sim] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LENGTH_MAP; EL_MAP]);;

let NAT_SIM_TYPEOF = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol hctx hnms htys htms hths hdrops hpol y ty.
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (hctx,hnms,htys,htms,hths,hdrops,hpol) /\
      y < LENGTH ymap /\ fdty nms tys (EL y ymap) ty
      ==> EL y htys = ty`,
  REWRITE_TAC[nat_sim] THEN MESON_TAC[FDTY_FUNCTIONAL]);;

let NAT_SIM_TERMOF = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol hctx hnms htys htms hths hdrops hpol t tm.
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (hctx,hnms,htys,htms,hths,hdrops,hpol) /\
      fdtm nms tys ntms t tm
      ==> EL t htms = tm`,
  REWRITE_TAC[nat_sim] THEN MESON_TAC[FDTM_FUNCTIONAL; FDTM_BOUND]);;

let NAT_OK_THEORY = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
      ==> ctx hextends hinit_ctxt /\ htheory_ok (hthyof ctx)`,
  REWRITE_TAC[nat_rows_ok; fibre_inv] THEN MESON_TAC[HEXTENDS_THEORY_OK; HINIT_THEORY_OK]);;

let NAT_OK_TY = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol i ty.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\ fdty nms tys i ty
      ==> fibre_ty_ok ctx nms tys i /\ htype_ok (FST(hsigof ctx)) ty`,
  REWRITE_TAC[nat_rows_ok; fibre_inv] THEN MESON_TAC[FDTY_BOUND; FIBRE_TY_OK_GET]);;

let NAT_OK_TM = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol i t.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\ fdtm nms tys ntms i t
      ==> i < LENGTH ntms /\ fibre_tm_ok ctx nms tys dbs ntms i /\
          hterm_ok (hsigof ctx) t /\ hwelltyped t /\
          fdty nms tys (ntm_ty (EL i ntms)) (htypeof t) /\
          fddb nms tys dbs (ntm_db (EL i ntms)) (hdb t)`,
  REWRITE_TAC[nat_rows_ok; fibre_inv] THEN
  MESON_TAC[FDTM_BOUND; FIBRE_TM_OK_GET; HTERM_OK_WELLTYPED]);;

let NAT_OK_THM = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol h.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\ h < LENGTH ths
      ==> fibre_thm_ok ctx nms tys dbs (FST(EL h ths),SND(EL h ths))`,
  REWRITE_TAC[nat_rows_ok; fibre_inv; GSYM ALL_MEM; PAIR] THEN MESON_TAC[MEM_EL]);;

let NAT_OK_NAMEROW = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol n.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\ n < LENGTH nmap
      ==> EL n nmap < LENGTH nms`,
  REWRITE_TAC[nat_rows_ok; GSYM ALL_MEM] THEN MESON_TAC[MEM_EL]);;

(* ------------------------------------------------------------------------- *)
(* Frames: appended type and de Bruijn rows keep the invariant and the      *)
(* simulation; so does one new Y entry, named row or theorem row that       *)
(* decodes to the HOLR state's new object.                                  *)
(* ------------------------------------------------------------------------- *)

let NAT_GROW = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol mt md hr.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) hr /\
      nat_tys_ok ctx nms tys mt
      ==> nat_rows_ok (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,ths,nmap,ymap,drops,pol) /\
          nat_sim (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,ths,nmap,ymap,drops,pol) hr`,
  REPEAT GEN_TAC THEN SPEC_TAC(`hr:hrstate`,`hr:hrstate`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`hctx:hupdate list`; `hnms:string list`; `htys:holtype list`;
                       `htms:holterm list`; `hths:(holterm list#holterm)list`;
                       `hdrops:(num#num)list`; `hpol:num`] THEN
  REWRITE_TAC[nat_rows_ok; fibre_inv; nat_sim; nat_tys_ok; LENGTH_APPEND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `mt:(num#num#num)list`;
                `md:(num#num#num)list`; `[]:(num#num#num#num#num)list`] NAT_EXT) THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `dbs:(num#num#num)list`; `ntms:(num#num#num#num#num)list`;
                `mt:(num#num#num)list`; `md:(num#num#num)list`;
                `[]:(num#num#num#num#num)list`] NAT_EXT_OK) THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THENL
   [ASM_CASES_TAC `i < LENGTH (tys:(num#num#num)list)` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `!i. LENGTH (tys:(num#num#num)list) <= i /\
                     i < LENGTH tys + LENGTH (mt:(num#num#num)list)
                     ==> fibre_ty_ok ctx nms (APPEND tys mt) i` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `fibre_thm_ok ctx nms tys dbs` THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\y. ?ty. fdty nms tys y ty` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let NAT_PUSH_TY = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol hctx hnms htys htms hths hdrops hpol y ty.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (hctx,hnms,htys,htms,hths,hdrops,hpol) /\
      fdty nms tys y ty
      ==> nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,APPEND ymap [y],drops,pol) /\
          nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,APPEND ymap [y],drops,pol)
                  (hctx,hnms,APPEND htys [ty],htms,hths,hdrops,hpol)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nat_rows_ok; nat_sim; ALL_APPEND; ALL; LENGTH_APPEND; LENGTH] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[EL_APPEND] THEN
  ASM_CASES_TAC `j < LENGTH (ymap:num list)` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `j = LENGTH (ymap:num list)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[SUB_REFL; EL; HD]]);;

let NAT_PUSH_TM = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol hctx hnms htys htms hths hdrops hpol row t.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (hctx,hnms,htys,htms,hths,hdrops,hpol) /\
      fibre_tm_ok ctx nms tys dbs (APPEND ntms [row]) (LENGTH ntms) /\
      fdtm nms tys (APPEND ntms [row]) (LENGTH ntms) t
      ==> nat_rows_ok (ctx,nms,tys,APPEND ntms [row],dbs,ths,nmap,ymap,drops,pol) /\
          nat_sim (ctx,nms,tys,APPEND ntms [row],dbs,ths,nmap,ymap,drops,pol)
                  (hctx,hnms,htys,APPEND htms [t],hths,hdrops,hpol)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nat_rows_ok; fibre_inv; nat_sim; LENGTH_APPEND; LENGTH] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `[]:(num#num#num)list`;
                `[]:(num#num#num)list`; `[row:num#num#num#num#num]`] NAT_EXT) THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `dbs:(num#num#num)list`; `ntms:(num#num#num#num#num)list`;
                `[]:(num#num#num)list`; `[]:(num#num#num)list`;
                `[row:num#num#num#num#num]`] NAT_EXT_OK) THEN
  REWRITE_TAC[APPEND_NIL] THEN REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC `i < LENGTH (ntms:(num#num#num#num#num)list)` THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `i = LENGTH (ntms:(num#num#num#num#num)list)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[EL_APPEND] THEN
    ASM_CASES_TAC `j < LENGTH (ntms:(num#num#num#num#num)list)` THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `j = LENGTH (ntms:(num#num#num#num#num)list)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[SUB_REFL; EL; HD]]]);;

let NAT_PUSH_TH = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol hctx hnms htys htms hths hdrops hpol
    th hyps tm.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (hctx,hnms,htys,htms,hths,hdrops,hpol) /\
      fibre_thm_wit ctx nms tys dbs th (hyps,tm)
      ==> nat_rows_ok (ctx,nms,tys,ntms,dbs,APPEND ths [th],nmap,ymap,drops,pol) /\
          nat_sim (ctx,nms,tys,ntms,dbs,APPEND ths [th],nmap,ymap,drops,pol)
                  (hctx,hnms,htys,htms,APPEND hths [hyps,tm],hdrops,hpol)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nat_rows_ok; fibre_inv; nat_sim; LENGTH_APPEND; LENGTH; ALL_APPEND; ALL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FIBRE_THM_OK_WIT]; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[EL_APPEND] THEN
  ASM_CASES_TAC `j < LENGTH (ths:(num#num)list)` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `j = LENGTH (ths:(num#num)list)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[SUB_REFL; EL; HD]]);;

(* ------------------------------------------------------------------------- *)
(* The clauses of holr_step and of the decoders, by name.                    *)
(* ------------------------------------------------------------------------- *)

let HOLR_STEP_NAME = el 0 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_TYVAR = el 1 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_TYAPP = el 2 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_VAR = el 3 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_CONST = el 4 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_COMB = el 5 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_ABS = el 6 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_RULE = el 7 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_NEW_TYPE = el 8 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_NEW_CONSTANT = el 9 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_NEW_AXIOM = el 10 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_NEW_DEFINITION = el 11 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_NEW_TYPEDEF = el 12 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_POLICY = el 13 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_EXPECT_ALPHA = el 14 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_LABEL = el 15 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_EMIT = el 16 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_DROP_TYPE = el 17 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_DROP_TERM = el 18 (CONJUNCTS holr_step_RULES);;
let HOLR_STEP_DROP_THM = el 19 (CONJUNCTS holr_step_RULES);;

let FDTM_VAR,FDTM_CONST,FDTM_COMB,FDTM_ABS =
  match map (GENL [`nms:string list`; `tys:(num#num#num)list`;
                   `ntms:(num#num#num#num#num)list`])
            (CONJUNCTS(SPEC_ALL fdtm_RULES)) with
    [a;b;c;d] -> a,b,c,d | _ -> failwith "fdtm_RULES";;

let EL_LENGTH_APPEND_SING = prove
 (`!(l:A list) x. LENGTH l < LENGTH (APPEND l [x]) /\ EL (LENGTH l) (APPEND l [x]) = x`,
  REWRITE_TAC[LENGTH_APPEND; LENGTH; EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN
  ARITH_TAC);;

(* The live operands of a record are in range. *)
let NAT_LIVE_BOUNDS = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol r.
      nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) r
      ==> ALL (\y. y < LENGTH ymap) (FST(holr_operands r)) /\
          ALL (\t. t < LENGTH ntms) (FST(SND(holr_operands r))) /\
          ALL (\h. h < LENGTH ths) (SND(SND(holr_operands r)))`,
  REWRITE_TAC[nat_ops_live; holr_live; GSYM ALL_MEM] THEN MESON_TAC[]);;

let nat_vars = [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`;
                `ths:(num#num)list`; `nmap:num list`; `ymap:num list`;
                `drops:(num#num)list`; `pol:num`];;

let hr_vars = [`hctx:hupdate list`; `hnms:string list`; `htys:holtype list`;
               `htms:holterm list`; `hths:(holterm list#holterm)list`;
               `hdrops:(num#num)list`; `hpol:num`];;

(* ------------------------------------------------------------------------- *)
(* The three shapes of a step: a theorem row, a named row, a Y entry.        *)
(* ------------------------------------------------------------------------- *)

let NAT_SIM_RULE = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol mt md hk k r
    hctx hnms htys htms hths hdrops hpol.
      holr_is_rule r /\ nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) r /\
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (hctx,hnms,htys,htms,hths,hdrops,hpol) /\
      nat_tys_ok ctx nms tys mt /\
      fibre_thm_ok ctx nms (APPEND tys mt) (APPEND dbs md) (hk,k)
      ==> nat_rows_ok (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [hk,k],
                  nmap,ymap,drops,pol) /\
          ?hr'. holr_step (hctx,hnms,htys,htms,hths,hdrops,hpol) r hr' /\
                nat_sim (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [hk,k],
                         nmap,ymap,drops,pol) hr'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `holr_ops_live (hctx,hnms,htys,htms,hths,hdrops,hpol) r` ASSUME_TAC THENL
   [ASM_MESON_TAC[NAT_OPS_LIVE_SIM]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NAT_SIM_CTX) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  MP_TAC(SPECL (nat_vars @ [`mt:(num#num#num)list`; `md:(num#num#num)list`;
                            `(ctx,hnms,htys,htms,hths,drops,pol):hrstate`]) NAT_GROW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `fibre_thm_ok ctx nms (APPEND tys mt) (APPEND dbs md) (hk,k)` THEN
  REWRITE_TAC[FIBRE_THM_OK_WIT; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`hyps:holterm list`; `tm:holterm`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `APPEND tys mt:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `APPEND dbs md:(num#num#num)list`;
                `ths:(num#num)list`; `nmap:num list`; `ymap:num list`;
                `drops:(num#num)list`; `pol:num`; `ctx:hupdate list`; `hnms:string list`;
                `htys:holtype list`; `htms:holterm list`;
                `hths:(holterm list#holterm)list`; `drops:(num#num)list`; `pol:num`;
                `(hk:num,k:num)`; `hyps:holterm list`; `tm:holterm`] NAT_PUSH_TH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(ctx,hnms,htys,htms,APPEND hths [hyps,tm],drops,pol):hrstate` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOLR_STEP_RULE THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[fibre_thm_wit]);;

let NAT_SIM_TERM = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol mt md row t r
    hctx hnms htys htms hths hdrops hpol.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (hctx,hnms,htys,htms,hths,hdrops,hpol) /\
      nat_tys_ok ctx nms tys mt /\
      fibre_tm_ok ctx nms (APPEND tys mt) (APPEND dbs md) (APPEND ntms [row]) (LENGTH ntms) /\
      fdtm nms (APPEND tys mt) (APPEND ntms [row]) (LENGTH ntms) t /\
      holr_step (hctx,hnms,htys,htms,hths,hdrops,hpol) r
                (hctx,hnms,htys,APPEND htms [t],hths,hdrops,hpol)
      ==> nat_rows_ok (ctx,nms,APPEND tys mt,APPEND ntms [row],APPEND dbs md,ths,
                  nmap,ymap,drops,pol) /\
          ?hr'. holr_step (hctx,hnms,htys,htms,hths,hdrops,hpol) r hr' /\
                nat_sim (ctx,nms,APPEND tys mt,APPEND ntms [row],APPEND dbs md,ths,
                         nmap,ymap,drops,pol) hr'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (nat_vars @ [`mt:(num#num#num)list`; `md:(num#num#num)list`;
                            `(hctx,hnms,htys,htms,hths,hdrops,hpol):hrstate`]) NAT_GROW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `APPEND tys mt:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `APPEND dbs md:(num#num#num)list`;
                `ths:(num#num)list`; `nmap:num list`; `ymap:num list`;
                `drops:(num#num)list`; `pol:num`; `hctx:hupdate list`; `hnms:string list`;
                `htys:holtype list`; `htms:holterm list`;
                `hths:(holterm list#holterm)list`; `hdrops:(num#num)list`; `hpol:num`;
                `row:num#num#num#num#num`; `t:holterm`] NAT_PUSH_TM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(hctx,hnms,htys,APPEND htms [t],hths,hdrops,hpol):hrstate` THEN
  ASM_REWRITE_TAC[]);;

let NAT_SIM_TYPE = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol mt md y ty r
    hctx hnms htys htms hths hdrops hpol.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (hctx,hnms,htys,htms,hths,hdrops,hpol) /\
      nat_tys_ok ctx nms tys mt /\ fdty nms (APPEND tys mt) y ty /\
      holr_step (hctx,hnms,htys,htms,hths,hdrops,hpol) r
                (hctx,hnms,APPEND htys [ty],htms,hths,hdrops,hpol)
      ==> nat_rows_ok (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,ths,nmap,APPEND ymap [y],
                  drops,pol) /\
          ?hr'. holr_step (hctx,hnms,htys,htms,hths,hdrops,hpol) r hr' /\
                nat_sim (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,ths,nmap,APPEND ymap [y],
                         drops,pol) hr'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (nat_vars @ [`mt:(num#num#num)list`; `md:(num#num#num)list`;
                            `(hctx,hnms,htys,htms,hths,hdrops,hpol):hrstate`]) NAT_GROW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `APPEND tys mt:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `APPEND dbs md:(num#num#num)list`;
                `ths:(num#num)list`; `nmap:num list`; `ymap:num list`;
                `drops:(num#num)list`; `pol:num`; `hctx:hupdate list`; `hnms:string list`;
                `htys:holtype list`; `htms:holterm list`;
                `hths:(holterm list#holterm)list`; `hdrops:(num#num)list`; `hpol:num`;
                `y:num`; `ty:holtype`] NAT_PUSH_TY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(hctx,hnms,APPEND htys [ty],htms,hths,hdrops,hpol):hrstate` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Appended names keep every decoding and every row predicate.              *)
(* ------------------------------------------------------------------------- *)

let NAT_EXT_NAMES = prove
 (`!ctx nms tys dbs ntms mn.
      (!i t. fdty nms tys i t ==> fdty (APPEND nms mn) tys i t) /\
      (!i t. fdtm nms tys ntms i t ==> fdtm (APPEND nms mn) tys ntms i t) /\
      (!i. fibre_ty_ok ctx nms tys i ==> fibre_ty_ok ctx (APPEND nms mn) tys i) /\
      (!i. i < LENGTH ntms /\ fibre_tm_ok ctx nms tys dbs ntms i
           ==> fibre_tm_ok ctx (APPEND nms mn) tys dbs ntms i) /\
      (!th. fibre_thm_ok ctx nms tys dbs th ==> fibre_thm_ok ctx (APPEND nms mn) tys dbs th) /\
      (!th w. fibre_thm_wit ctx nms tys dbs th w
              ==> fibre_thm_wit ctx (APPEND nms mn) tys dbs th w)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `mn:string list`;
                 `[]:(num#num#num)list`] FDTY_EXTEND) THEN
  MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                 `mn:string list`; `[]:(num#num#num)list`; `[]:(num#num#num)list`]
                FDDB_EXTEND) THEN
  MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`;
                 `ntms:(num#num#num#num#num)list`; `mn:string list`;
                 `[]:(num#num#num)list`; `[]:(num#num#num#num#num)list`] FDTM_EXTEND) THEN
  MP_TAC(ISPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                 `mn:string list`; `[]:(num#num#num)list`] FIBRE_TY_OK_EXTEND) THEN
  MP_TAC(ISPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                 `dbs:(num#num#num)list`; `ntms:(num#num#num#num#num)list`;
                 `mn:string list`; `[]:(num#num#num)list`; `[]:(num#num#num)list`;
                 `[]:(num#num#num#num#num)list`] FIBRE_TM_OK_EXTEND) THEN
  MP_TAC(ISPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                 `dbs:(num#num#num)list`; `mn:string list`; `[]:(num#num#num)list`;
                 `[]:(num#num#num)list`] FIBRE_THM_OK_EXTEND) THEN
  REWRITE_TAC[APPEND_NIL] THEN SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; fibre_thm_wit] THEN ASM_MESON_TAC[]);;

(* A context extension keeps the invariant and the simulation. *)
let NAT_CTX = prove
 (`!ctx ctx' nms tys ntms dbs ths nmap ymap drops pol hnms htys htms hths.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (ctx,hnms,htys,htms,hths,drops,pol) /\
      ctx' hextends ctx
      ==> nat_rows_ok (ctx',nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
          nat_sim (ctx',nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
                  (ctx',hnms,htys,htms,hths,drops,pol)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nat_rows_ok; fibre_inv; nat_sim] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HEXTENDS_TRANS];
    ASM_MESON_TAC[FIBRE_CTX_EXTEND];
    ASM_MESON_TAC[FIBRE_CTX_EXTEND];
    MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `fibre_thm_ok ctx nms tys dbs` THEN
    ASM_MESON_TAC[FIBRE_CTX_EXTEND];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term ((=) `fibre_thm_wit`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`EL j (hths:(holterm list#holterm)list)`,`w:holterm list#holterm`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; fibre_thm_wit] THEN ASM_MESON_TAC[HEXTENDS_PROVES]]);;

(* ------------------------------------------------------------------------- *)
(* Per record kind. Each statement is generated from the kind's clause of   *)
(* nat_step: for all the clause's variables, its premises imply that for    *)
(* every HOLR state hr that the state before simulates, the state after is  *)
(* ok, and some HOLR step of the same record leads from hr to a state that  *)
(* the state after simulates.                                                *)
(* ------------------------------------------------------------------------- *)

let NAT_SIM_TYS = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol hctx hnms htys htms hths hdrops hpol.
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (hctx,hnms,htys,htms,hths,hdrops,hpol)
      ==> (!j. j < LENGTH ymap ==> fdty nms tys (EL j ymap) (EL j htys)) /\
          (!j. j < LENGTH ntms ==> fdtm nms tys ntms j (EL j htms))`,
  REWRITE_TAC[nat_sim] THEN MESON_TAC[]);;

let nat_sim_goal cl =
  let vs,bod = strip_forall cl in
  let ant,cn = dest_imp bod in
  let ns = rand(rator(rator cn)) and r = rand(rator cn) and ns' = rand cn in
  let hr = `hr:hrstate` and hr' = `hr':hrstate` in
  let ok s = mk_comb(`nat_rows_ok`,s) and sim s h = list_mk_comb(`nat_sim`,[s;h]) in
  list_mk_forall(vs, mk_imp(ant,
    mk_forall(hr, mk_imp(mk_conj(ok ns, sim ns hr),
      mk_conj(ok ns', mk_exists(hr', mk_conj(list_mk_comb(`holr_step`,[hr;r;hr']),
                                             sim ns' hr')))))));;

let nat_clause k = el k (conjuncts(concl nat_step_RULES));;

let NAT_CASE_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC hr_vars THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NAT_SIM_CTX) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NAT_SIM_TYS) THEN
  TRY(FIRST_ASSUM(STRIP_ASSUME_TAC o
        REWRITE_RULE[holr_operands; ALL; FST; SND; ALL_HOLR_PAIRS_FLAT] o
        MATCH_MP NAT_LIVE_BOUNDS));;

(* The HOLR name of N id n is the native name of its row. *)
let NAT_NAME_TAC n =
  SUBGOAL_THEN (subst [n,`n:num`] `n < LENGTH (hnms:string list) /\
                                   EL (EL n nmap) nms = EL n (hnms:string list)`)
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL [ASM_MESON_TAC[NAT_SIM_NAME]; ALL_TAC];;

(* A live native operand is a live HOLR operand. *)
let NAT_LIVE_TAC =
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NAT_OPS_LIVE_SIM th] THEN
                        ASM_REWRITE_TAC[] THEN NO_TAC);;

let NAT_EXT_TAC nt =
  STRIP_ASSUME_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                          `ntms:(num#num#num#num#num)list`; `mt:(num#num#num)list`;
                          `md:(num#num#num)list`; nt] NAT_EXT) THEN
  STRIP_ASSUME_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                          `dbs:(num#num#num)list`; `ntms:(num#num#num#num#num)list`;
                          `mt:(num#num#num)list`; `md:(num#num#num)list`; nt] NAT_EXT_OK);;

(* NAME. *)
let NAT_SIM_NAME_REC = prove
 (nat_sim_goal (nat_clause 0),
  NAT_CASE_TAC THEN
  REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM] THEN
  EXISTS_TAC `(ctx,APPEND hnms [holr_name bs],htys,htms,hths,drops,pol):hrstate` THEN
  REWRITE_TAC[HOLR_STEP_NAME] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `holr_name bs`)) THEN
  STRIP_ASSUME_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                          `dbs:(num#num#num)list`; `ntms:(num#num#num#num#num)list`;
                          `mn:string list`] NAT_EXT_NAMES) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[nat_rows_ok; fibre_inv; nat_sim; ALL_APPEND; ALL; MAP_APPEND; MAP] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `fibre_thm_ok ctx nms tys dbs` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\i. i < LENGTH (nms:string list)` THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
    MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\y. ?ty. fdty nms tys y ty` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN MATCH_MP_TAC ALL_IMP THEN
    EXISTS_TAC `\i. i < LENGTH (nms:string list)` THEN ASM_SIMP_TAC[EL_APPEND]]);;

(* TYVAR. *)
let NAT_SIM_TYVAR = prove
 (nat_sim_goal (nat_clause 1),
  NAT_CASE_TAC THEN
  MATCH_MP_TAC NAT_SIM_TYPE THEN EXISTS_TAC `TyVar (EL (EL n nmap) nms)` THEN
  ASM_REWRITE_TAC[] THEN NAT_NAME_TAC `n:num` THEN
  MATCH_MP_TAC HOLR_STEP_TYVAR THEN ASM_REWRITE_TAC[]);;

(* TYAPP. *)
let NAT_SIM_TYAPP = prove
 (nat_sim_goal (nat_clause 2),
  NAT_CASE_TAC THEN
  SUBGOAL_THEN `args = MAP (\i. EL i (htys:holtype list)) ys` SUBST_ALL_TAC THENL
   [MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `ymap:num list`;
                  `htys:holtype list`] NAT_ALL2_TYS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC NAT_SIM_TYPE THEN
  EXISTS_TAC `TyApp (EL (EL n nmap) nms) (MAP (\i. EL i (htys:holtype list)) ys)` THEN
  ASM_REWRITE_TAC[] THEN NAT_NAME_TAC `n:num` THEN
  MATCH_MP_TAC HOLR_STEP_TYAPP THEN NAT_LIVE_TAC);;

(* VAR. *)
let NAT_SIM_VAR = prove
 (nat_sim_goal (nat_clause 3),
  NAT_CASE_TAC THEN
  MATCH_MP_TAC NAT_SIM_TERM THEN EXISTS_TAC `TmVar (EL (EL n nmap) nms) ty` THEN
  ASM_REWRITE_TAC[] THEN
  NAT_EXT_TAC `[0,EL n nmap,EL y ymap,EL y ymap,d]:(num#num#num#num#num)list` THEN
  SUBGOAL_THEN `EL n nmap < LENGTH (nms:string list) /\ fibre_ty_ok ctx nms tys (EL y ymap)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[NAT_OK_NAMEROW; NAT_OK_TY]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FIBRE_VAR THEN
    MAP_EVERY EXISTS_TAC [`EL n (nmap:num list)`; `EL y (ymap:num list)`; `d:num`;
                          `ty:holtype`] THEN
    ASM_SIMP_TAC[EL_LENGTH_APPEND_SING];
    MATCH_MP_TAC FDTM_VAR THEN
    MAP_EVERY EXISTS_TAC [`EL y (ymap:num list)`; `EL y (ymap:num list)`; `d:num`] THEN
    ASM_SIMP_TAC[EL_LENGTH_APPEND_SING];
    SUBGOAL_THEN `EL y (htys:holtype list) = ty` (SUBST1_TAC o SYM) THENL
     [ASM_MESON_TAC[NAT_SIM_TYPEOF]; ALL_TAC] THEN
    NAT_NAME_TAC `n:num` THEN MATCH_MP_TAC HOLR_STEP_VAR THEN NAT_LIVE_TAC]);;

(* CONST, at any instance of the constant's generic type. *)
let NAT_SIM_CONST = prove
 (nat_sim_goal (nat_clause 4),
  NAT_CASE_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ty = HTYPE_SUBST tyin ty0`)) THEN
  MATCH_MP_TAC NAT_SIM_TERM THEN
  EXISTS_TAC `TmConst (EL (EL n nmap) nms) (HTYPE_SUBST tyin ty0)` THEN
  ASM_REWRITE_TAC[] THEN
  NAT_EXT_TAC `[1,EL n nmap,EL y ymap,EL y ymap,d]:(num#num#num#num#num)list` THEN
  SUBGOAL_THEN `EL n nmap < LENGTH (nms:string list) /\ fibre_ty_ok ctx nms tys (EL y ymap)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[NAT_OK_NAMEROW; NAT_OK_TY]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FIBRE_CONST THEN
    MAP_EVERY EXISTS_TAC [`EL n (nmap:num list)`; `EL y (ymap:num list)`; `d:num`;
                          `HTYPE_SUBST tyin ty0`; `ty0:holtype`;
                          `tyin:(holtype#holtype)list`] THEN
    ASM_SIMP_TAC[EL_LENGTH_APPEND_SING; hsigof];
    MATCH_MP_TAC FDTM_CONST THEN
    MAP_EVERY EXISTS_TAC [`EL y (ymap:num list)`; `EL y (ymap:num list)`; `d:num`] THEN
    ASM_SIMP_TAC[EL_LENGTH_APPEND_SING];
    SUBGOAL_THEN `EL y (htys:holtype list) = HTYPE_SUBST tyin ty0`
      (fun th -> ASSUME_TAC th THEN SUBST1_TAC(SYM th))
    THENL [ASM_MESON_TAC[NAT_SIM_TYPEOF]; ALL_TAC] THEN
    NAT_NAME_TAC `n:num` THEN MATCH_MP_TAC HOLR_STEP_CONST THEN
    MAP_EVERY EXISTS_TAC [`ty0:holtype`; `tyin:(holtype#holtype)list`] THEN NAT_LIVE_TAC]);;

(* COMB. *)
let NAT_SIM_COMB = prove
 (nat_sim_goal (nat_clause 5),
  NAT_CASE_TAC THEN
  MATCH_MP_TAC NAT_SIM_TERM THEN EXISTS_TAC `TmComb ts tt` THEN ASM_REWRITE_TAC[] THEN
  NAT_EXT_TAC `[2,s,t,yb,d]:(num#num#num#num#num)list` THEN
  SUBGOAL_THEN `fibre_tm_ok ctx nms tys dbs ntms s /\ fibre_tm_ok ctx nms tys dbs ntms t`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[NAT_OK_TM]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FIBRE_COMB THEN
    MAP_EVERY EXISTS_TAC [`s:num`; `t:num`; `yb:num`; `d:num`; `ts:holterm`; `tt:holterm`;
                          `B:holtype`] THEN
    ASM_SIMP_TAC[EL_LENGTH_APPEND_SING];
    MATCH_MP_TAC FDTM_COMB THEN MAP_EVERY EXISTS_TAC [`s:num`; `t:num`; `yb:num`; `d:num`] THEN
    ASM_SIMP_TAC[EL_LENGTH_APPEND_SING];
    SUBGOAL_THEN `EL s (htms:holterm list) = ts /\ EL t (htms:holterm list) = tt`
      (fun th -> ASSUME_TAC th THEN MAP_EVERY (SUBST1_TAC o SYM) (CONJUNCTS th)) THENL
     [ASM_MESON_TAC[NAT_SIM_TERMOF]; ALL_TAC] THEN
    MATCH_MP_TAC HOLR_STEP_COMB THEN EXISTS_TAC `B:holtype` THEN NAT_LIVE_TAC]);;

(* ABS, the named abstraction. *)
let NAT_SIM_ABS = prove
 (nat_sim_goal (nat_clause 6),
  NAT_CASE_TAC THEN
  MATCH_MP_TAC NAT_SIM_TERM THEN EXISTS_TAC `TmAbs (TmVar x ty) tb` THEN ASM_REWRITE_TAC[] THEN
  NAT_EXT_TAC `[3,v,t,yf,d]:(num#num#num#num#num)list` THEN
  SUBGOAL_THEN `fibre_tm_ok ctx nms tys dbs ntms v /\ fibre_tm_ok ctx nms tys dbs ntms t`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[NAT_OK_TM]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FIBRE_ABSN THEN
    MAP_EVERY EXISTS_TAC [`v:num`; `t:num`; `yf:num`; `d:num`; `x:string`; `ty:holtype`;
                          `tb:holterm`] THEN
    ASM_SIMP_TAC[EL_LENGTH_APPEND_SING];
    MATCH_MP_TAC FDTM_ABS THEN MAP_EVERY EXISTS_TAC [`v:num`; `t:num`; `yf:num`; `d:num`] THEN
    ASM_SIMP_TAC[EL_LENGTH_APPEND_SING];
    SUBGOAL_THEN `EL v (htms:holterm list) = TmVar x ty /\ EL t (htms:holterm list) = tb`
      (fun th -> ASSUME_TAC th THEN MAP_EVERY (SUBST1_TAC o SYM) (CONJUNCTS th)) THENL
     [ASM_MESON_TAC[NAT_SIM_TERMOF]; ALL_TAC] THEN
    MATCH_MP_TAC HOLR_STEP_ABS THEN MAP_EVERY EXISTS_TAC [`x:string`; `ty:holtype`] THEN
    NAT_LIVE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The rules. The record's fibre lemma, applied in the grown state, gives   *)
(* the new theorem row's derivation; NAT_SIM_RULE appends it to both states.*)
(* ------------------------------------------------------------------------- *)

let HTERM_OK_BETA_REDEX = prove
 (`!sig x ty t. hterm_ok sig (TmComb (TmAbs (TmVar x ty) t) (TmVar x ty))
                ==> htype_ok (FST sig) ty /\ hterm_ok sig t`,
  REWRITE_TAC[hterm_ok; holterm_INJ] THEN MESON_TAC[]);;

let NAT_TYIN_OK = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
      ==> !ps tyin. ALL2 (\ip it. fdty nms tys (EL (FST ip) ymap) (FST it) /\
                                  fdty nms tys (EL (SND ip) ymap) (SND it)) ps tyin
                    ==> ALL (htype_ok (FST(hsigof ctx))) (MAP FST tyin)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; MAP; ALL] THEN ASM_MESON_TAC[NAT_OK_TY]);;

let NAT_ILIST_OK = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
      ==> !ps ilist. ALL2 (\ip it. fdtm nms tys ntms (FST ip) (FST it) /\
                                   fdtm nms tys ntms (SND ip) (SND it)) ps ilist
                     ==> !s' s. MEM (s',s) ilist
                                ==> hterm_ok (hsigof ctx) s' /\ hwelltyped s'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; MEM] THEN ASM_MESON_TAC[NAT_OK_TM; FST]);;

let NAT_HYPS_OK = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
      ==> !hl hyps. ALL2 (fdtm nms tys ntms) hl hyps
                    ==> ALL (\p. hterm_ok (hsigof ctx) p /\ hwelltyped p) hyps`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; ALL] THEN ASM_MESON_TAC[NAT_OK_TM]);;

let NAT_RULE_TAC =
  NAT_CASE_TAC THEN MATCH_MP_TAC NAT_SIM_RULE THEN ASM_REWRITE_TAC[holr_is_rule] THEN
  NAT_EXT_TAC `[]:(num#num#num#num#num)list`;;

let NAT_THM_TAC h =
  MP_TAC(SPECL (nat_vars @ [h]) NAT_OK_THM) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let NAT_SIM_REFL = prove
 (nat_sim_goal (nat_clause 7),
  NAT_RULE_TAC THEN MATCH_MP_TAC FIBRE_REFL THEN EXISTS_TAC `tm:holterm` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NAT_OK_THEORY; NAT_OK_TM]);;

let NAT_SIM_TRANS = prove
 (nat_sim_goal (nat_clause 8),
  NAT_RULE_TAC THEN NAT_THM_TAC `h1:num` THEN NAT_THM_TAC `h2:num` THEN
  MATCH_MP_TAC FIBRE_TRANS THEN
  MAP_EVERY EXISTS_TAC
   [`FST(EL h1 (ths:(num#num)list))`; `SND(EL h1 (ths:(num#num)list))`;
    `FST(EL h2 (ths:(num#num)list))`; `SND(EL h2 (ths:(num#num)list))`;
    `ty1:holtype`; `ty2:holtype`; `l:hdbterm`; `mid:hdbterm`; `r:hdbterm`;
    `hs1:hdbterm list`; `hs2:hdbterm list`; `hs:hdbterm list`] THEN
  ASM_SIMP_TAC[]);;

let NAT_SIM_MK_COMB = prove
 (nat_sim_goal (nat_clause 9),
  NAT_RULE_TAC THEN NAT_THM_TAC `h1:num` THEN NAT_THM_TAC `h2:num` THEN
  MATCH_MP_TAC FIBRE_MK_COMB THEN
  MAP_EVERY EXISTS_TAC
   [`FST(EL h1 (ths:(num#num)list))`; `SND(EL h1 (ths:(num#num)list))`;
    `FST(EL h2 (ths:(num#num)list))`; `SND(EL h2 (ths:(num#num)list))`;
    `f:hdbterm`; `g:hdbterm`; `a:hdbterm`; `b:hdbterm`; `tx:holtype`; `ty:holtype`;
    `hs1:hdbterm list`; `hs2:hdbterm list`; `hs:hdbterm list`] THEN
  ASM_SIMP_TAC[]);;

let NAT_SIM_ABS_RULE = prove
 (nat_sim_goal (nat_clause 10),
  NAT_RULE_TAC THEN NAT_THM_TAC `h:num` THEN
  SUBGOAL_THEN `htype_ok (FST(hsigof ctx)) ty` ASSUME_TAC THENL
   [MP_TAC(SPECL (nat_vars @ [`t:num`; `TmVar x ty`]) NAT_OK_TM) THEN
    ASM_REWRITE_TAC[hterm_ok] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC FIBRE_ABS THEN
  MAP_EVERY EXISTS_TAC
   [`FST(EL h (ths:(num#num)list))`; `SND(EL h (ths:(num#num)list))`;
    `x:string`; `ty:holtype`; `A:holtype`; `l:hdbterm`; `r:hdbterm`; `hs:hdbterm list`] THEN
  ASM_SIMP_TAC[]);;

let NAT_SIM_BETA = prove
 (nat_sim_goal (nat_clause 11),
  NAT_RULE_TAC THEN
  SUBGOAL_THEN `htype_ok (FST(hsigof ctx)) ty /\ hterm_ok (hsigof ctx) tb` STRIP_ASSUME_TAC
  THENL [ASM_MESON_TAC[NAT_OK_TM; HTERM_OK_BETA_REDEX]; ALL_TAC] THEN
  MATCH_MP_TAC FIBRE_BETA THEN
  MAP_EVERY EXISTS_TAC [`x:string`; `ty:holtype`; `tb:holterm`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NAT_OK_THEORY]);;

let NAT_SIM_ASSUME = prove
 (nat_sim_goal (nat_clause 12),
  NAT_RULE_TAC THEN MATCH_MP_TAC FIBRE_ASSUME THEN
  MAP_EVERY EXISTS_TAC [`p:holterm`; `hs:hdbterm list`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NAT_OK_THEORY; NAT_OK_TM; HWELLTYPED]);;

let NAT_SIM_EQ_MP = prove
 (nat_sim_goal (nat_clause 13),
  NAT_RULE_TAC THEN NAT_THM_TAC `h1:num` THEN NAT_THM_TAC `h2:num` THEN
  MATCH_MP_TAC FIBRE_EQ_MP THEN
  MAP_EVERY EXISTS_TAC
   [`FST(EL h1 (ths:(num#num)list))`; `SND(EL h1 (ths:(num#num)list))`;
    `FST(EL h2 (ths:(num#num)list))`; `SND(EL h2 (ths:(num#num)list))`;
    `ty:holtype`; `p:hdbterm`; `q:hdbterm`;
    `hs1:hdbterm list`; `hs2:hdbterm list`; `hs:hdbterm list`] THEN
  ASM_SIMP_TAC[]);;

let NAT_SIM_DEDUCT = prove
 (nat_sim_goal (nat_clause 14),
  NAT_RULE_TAC THEN NAT_THM_TAC `h1:num` THEN NAT_THM_TAC `h2:num` THEN
  MATCH_MP_TAC FIBRE_DEDUCT THEN
  MAP_EVERY EXISTS_TAC
   [`FST(EL h1 (ths:(num#num)list))`; `SND(EL h1 (ths:(num#num)list))`;
    `FST(EL h2 (ths:(num#num)list))`; `SND(EL h2 (ths:(num#num)list))`;
    `p:hdbterm`; `q:hdbterm`;
    `hs1:hdbterm list`; `hs2:hdbterm list`; `hs:hdbterm list`] THEN
  ASM_SIMP_TAC[]);;

let NAT_SIM_INST_TYPE = prove
 (nat_sim_goal (nat_clause 15),
  NAT_RULE_TAC THEN NAT_THM_TAC `h:num` THEN
  SUBGOAL_THEN `ALL (htype_ok (FST(hsigof ctx))) (MAP FST (tyin:(holtype#holtype)list))`
    ASSUME_TAC THENL [ASM_MESON_TAC[NAT_TYIN_OK]; ALL_TAC] THEN
  MATCH_MP_TAC FIBRE_INST_TYPE THEN
  MAP_EVERY EXISTS_TAC
   [`FST(EL h (ths:(num#num)list))`; `SND(EL h (ths:(num#num)list))`;
    `C:hdbterm`; `tyin:(holtype#holtype)list`; `hs1:hdbterm list`; `hs:hdbterm list`] THEN
  ASM_SIMP_TAC[]);;

let NAT_SIM_INST = prove
 (nat_sim_goal (nat_clause 16),
  NAT_RULE_TAC THEN NAT_THM_TAC `h:num` THEN
  SUBGOAL_THEN `!s s'. MEM (s',s) ilist
                       ==> ?x ty. s = TmVar x ty /\ s' hhas_type ty /\
                                  hterm_ok (hsigof ctx) s'` ASSUME_TAC THENL
   [MP_TAC(SPECL nat_vars NAT_ILIST_OK) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`ps:(num#num)list`; `ilist:(holterm#holterm)list`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[HWELLTYPED];
    ALL_TAC] THEN
  MATCH_MP_TAC FIBRE_INST THEN
  MAP_EVERY EXISTS_TAC
   [`FST(EL h (ths:(num#num)list))`; `SND(EL h (ths:(num#num)list))`;
    `C:hdbterm`; `ilist:(holterm#holterm)list`; `hs1:hdbterm list`; `hs:hdbterm list`] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Checks, releases and the policy.                                          *)
(* ------------------------------------------------------------------------- *)

(* Drops and the policy are carried alike by both states. *)
let NAT_SIM_DROPS = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol hnms htys htms hths d p.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (ctx,hnms,htys,htms,hths,drops,pol)
      ==> nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,d,p) /\
          nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,d,p) (ctx,hnms,htys,htms,hths,d,p)`,
  REWRITE_TAC[nat_rows_ok; nat_sim] THEN MESON_TAC[]);;

let NAT_SAME_TAC =
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM] THEN
  EXISTS_TAC `(ctx,hnms,htys,htms,hths,drops,pol):hrstate` THEN ASM_REWRITE_TAC[];;

(* EXPECT_ALPHA: the claim, read with the HOLR state's terms, is derivable. *)
let NAT_SIM_EXPECT_ALPHA = prove
 (nat_sim_goal (nat_clause 17),
  NAT_CASE_TAC THEN NAT_SAME_TAC THEN
  MATCH_MP_TAC HOLR_STEP_EXPECT_ALPHA THEN
  CONJ_TAC THENL [NAT_LIVE_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `MAP (\i. EL i (htms:holterm list)) hl = hyps /\ EL c htms = cn`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`;
                    `ntms:(num#num#num#num#num)list`; `htms:holterm list`] NAT_ALL2_TMS) THEN
      ASM_SIMP_TAC[];
      ASM_MESON_TAC[NAT_SIM_TERMOF]];
    ALL_TAC] THEN
  NAT_THM_TAC `h:num` THEN
  MP_TAC(SPECL nat_vars NAT_HYPS_OK) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`hl:num list`; `hyps:holterm list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC FIBRE_EXPECT_ALPHA THEN
  MAP_EVERY EXISTS_TAC
   [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
    `FST(EL h (ths:(num#num)list))`; `SND(EL h (ths:(num#num)list))`;
    `hsd:hdbterm list`; `hdb cn`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `ALL (\p. htypeof p = HBool) (hyps:holterm list)` THEN
    UNDISCH_TAC `ALL (\p. hterm_ok (hsigof ctx) p /\ hwelltyped p) (hyps:holterm list)` THEN
    REWRITE_TAC[IMP_IMP; AND_ALL] THEN MATCH_MP_TAC MONO_ALL THEN
    MESON_TAC[HWELLTYPED];
    ASM_MESON_TAC[NAT_OK_TM];
    ASM_REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]]);;

let NAT_SIM_LABEL = prove
 (nat_sim_goal (nat_clause 18),
  NAT_CASE_TAC THEN NAT_SAME_TAC THEN MATCH_MP_TAC HOLR_STEP_LABEL THEN
  CONJ_TAC THENL [NAT_LIVE_TAC; ASM_MESON_TAC[NAT_SIM_NAME]]);;

let NAT_SIM_EMIT = prove
 (nat_sim_goal (nat_clause 19),
  NAT_CASE_TAC THEN NAT_SAME_TAC THEN MATCH_MP_TAC HOLR_STEP_EMIT THEN NAT_LIVE_TAC);;

let NAT_SIM_DROP_TYPE = prove
 (nat_sim_goal (nat_clause 20),
  NAT_CASE_TAC THEN
  SUBGOAL_THEN `holr_step (ctx,hnms,htys,htms,hths,drops,pol) (RDropType y)
                          (ctx,hnms,htys,htms,hths,CONS (1,y) drops,pol)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOLR_STEP_DROP_TYPE THEN NAT_LIVE_TAC; ALL_TAC] THEN
  MP_TAC(SPECL (nat_vars @ [`hnms:string list`; `htys:holtype list`; `htms:holterm list`;
                            `hths:(holterm list#holterm)list`;
                            `CONS (1,y) drops:(num#num)list`; `pol:num`]) NAT_SIM_DROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(ctx,hnms,htys,htms,hths,CONS (1,y) drops,pol):hrstate` THEN
  ASM_REWRITE_TAC[]);;

let NAT_SIM_DROP_TERM = prove
 (nat_sim_goal (nat_clause 21),
  NAT_CASE_TAC THEN
  SUBGOAL_THEN `holr_step (ctx,hnms,htys,htms,hths,drops,pol) (RDropTerm t)
                          (ctx,hnms,htys,htms,hths,CONS (2,t) drops,pol)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOLR_STEP_DROP_TERM THEN NAT_LIVE_TAC; ALL_TAC] THEN
  MP_TAC(SPECL (nat_vars @ [`hnms:string list`; `htys:holtype list`; `htms:holterm list`;
                            `hths:(holterm list#holterm)list`;
                            `CONS (2,t) drops:(num#num)list`; `pol:num`]) NAT_SIM_DROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(ctx,hnms,htys,htms,hths,CONS (2,t) drops,pol):hrstate` THEN
  ASM_REWRITE_TAC[]);;

let NAT_SIM_DROP_THM = prove
 (nat_sim_goal (nat_clause 22),
  NAT_CASE_TAC THEN
  SUBGOAL_THEN `holr_step (ctx,hnms,htys,htms,hths,drops,pol) (RDropThm h)
                          (ctx,hnms,htys,htms,hths,CONS (3,h) drops,pol)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOLR_STEP_DROP_THM THEN NAT_LIVE_TAC; ALL_TAC] THEN
  MP_TAC(SPECL (nat_vars @ [`hnms:string list`; `htys:holtype list`; `htms:holterm list`;
                            `hths:(holterm list#holterm)list`;
                            `CONS (3,h) drops:(num#num)list`; `pol:num`]) NAT_SIM_DROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(ctx,hnms,htys,htms,hths,CONS (3,h) drops,pol):hrstate` THEN
  ASM_REWRITE_TAC[]);;

let NAT_SIM_POLICY = prove
 (nat_sim_goal (nat_clause 23),
  NAT_CASE_TAC THEN
  MP_TAC(SPECL (nat_vars @ [`hnms:string list`; `htys:holtype list`; `htms:holterm list`;
                            `hths:(holterm list#holterm)list`;
                            `drops:(num#num)list`; `MAX pol p`]) NAT_SIM_DROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(ctx,hnms,htys,htms,hths,drops,MAX pol p):hrstate` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOLR_STEP_POLICY THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Theory records. The context extends by HOL Light's operation; the rows   *)
(* stay ok in the extended context (FIBRE_CTX_EXTEND), and the new axiom or *)
(* definition is a theorem row whose sequent is the one holr_step appends.  *)
(* ------------------------------------------------------------------------- *)

let NAT_SIM_NEW_TYPE = prove
 (nat_sim_goal (nat_clause 24),
  NAT_CASE_TAC THEN
  SUBGOAL_THEN `CONS (HNewType (EL (EL n nmap) nms) a) ctx hextends ctx` ASSUME_TAC THENL
   [MATCH_MP_TAC FIBRE_NEW_TYPE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL ([`ctx:hupdate list`; `CONS (HNewType (EL (EL n nmap) nms) a) ctx`] @
                tl nat_vars @ [`hnms:string list`; `htys:holtype list`;
                               `htms:holterm list`; `hths:(holterm list#holterm)list`])
               NAT_CTX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(CONS (HNewType (EL (EL n nmap) nms) a) ctx,hnms,htys,htms,hths,drops,pol)
              :hrstate` THEN
  ASM_REWRITE_TAC[] THEN NAT_NAME_TAC `n:num` THEN
  MATCH_MP_TAC HOLR_STEP_NEW_TYPE THEN ASM_REWRITE_TAC[]);;

let NAT_SIM_NEW_CONSTANT = prove
 (nat_sim_goal (nat_clause 25),
  NAT_CASE_TAC THEN
  SUBGOAL_THEN `htype_ok (htype_list ctx) ty` ASSUME_TAC THENL
   [MP_TAC(SPECL (nat_vars @ [`EL y (ymap:num list)`; `ty:holtype`]) NAT_OK_TY) THEN
    ASM_SIMP_TAC[hsigof];
    ALL_TAC] THEN
  SUBGOAL_THEN `CONS (HNewConst (EL (EL n nmap) nms) ty) ctx hextends ctx` ASSUME_TAC THENL
   [MATCH_MP_TAC FIBRE_NEW_CONSTANT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL ([`ctx:hupdate list`; `CONS (HNewConst (EL (EL n nmap) nms) ty) ctx`] @
                tl nat_vars @ [`hnms:string list`; `htys:holtype list`;
                               `htms:holterm list`; `hths:(holterm list#holterm)list`])
               NAT_CTX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(CONS (HNewConst (EL (EL n nmap) nms) ty) ctx,hnms,htys,htms,hths,drops,pol)
              :hrstate` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `EL y (htys:holtype list) = ty` (fun th -> ASSUME_TAC th THEN SUBST1_TAC(SYM th))
  THENL [ASM_MESON_TAC[NAT_SIM_TYPEOF]; ALL_TAC] THEN
  NAT_NAME_TAC `n:num` THEN MATCH_MP_TAC HOLR_STEP_NEW_CONSTANT THEN NAT_LIVE_TAC);;

let NAT_SIM_NEW_AXIOM = prove
 (nat_sim_goal (nat_clause 26),
  NAT_CASE_TAC THEN
  SUBGOAL_THEN `htheory_ok (hthyof ctx) /\ hterm_ok (hsigof ctx) p /\ p hhas_type HBool`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NAT_OK_THEORY; NAT_OK_TM; HWELLTYPED]; ALL_TAC] THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `p:holterm`] HOL_NEW_AXIOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (nat_vars @ [`mt:(num#num#num)list`; `md:(num#num#num)list`;
                            `(ctx,hnms,htys,htms,hths,drops,pol):hrstate`]) NAT_GROW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `CONS (HNewAxiom p) ctx`; `nms:string list`;
                `APPEND tys mt:(num#num#num)list`; `ntms:(num#num#num#num#num)list`;
                `APPEND dbs md:(num#num#num)list`; `ths:(num#num)list`; `nmap:num list`;
                `ymap:num list`; `drops:(num#num)list`; `pol:num`; `hnms:string list`;
                `htys:holtype list`; `htms:holterm list`;
                `hths:(holterm list#holterm)list`] NAT_CTX) THEN
  ASM_SIMP_TAC[FIBRE_HUPDATES_EXTENDS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`CONS (HNewAxiom p) ctx`; `nms:string list`;
                `APPEND tys mt:(num#num#num)list`; `ntms:(num#num#num#num#num)list`;
                `APPEND dbs md:(num#num#num)list`; `ths:(num#num)list`; `nmap:num list`;
                `ymap:num list`; `drops:(num#num)list`; `pol:num`;
                `CONS (HNewAxiom p) ctx`; `hnms:string list`; `htys:holtype list`;
                `htms:holterm list`; `hths:(holterm list#holterm)list`;
                `drops:(num#num)list`; `pol:num`; `(e:num,k:num)`; `[]:holterm list`;
                `p:holterm`] NAT_PUSH_TH) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[fibre_thm_wit; MEM] THEN EXISTS_TAC `[]:hdbterm list` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(CONS (HNewAxiom p) ctx,hnms,htys,htms,APPEND hths [[],p],drops,pol)
              :hrstate` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `EL t (htms:holterm list) = p` (fun th -> ASSUME_TAC th THEN SUBST1_TAC(SYM th))
  THENL [ASM_MESON_TAC[NAT_SIM_TERMOF]; ALL_TAC] THEN
  MATCH_MP_TAC HOLR_STEP_NEW_AXIOM THEN NAT_LIVE_TAC);;

let NAT_SIM_NEW_DEFINITION = prove
 (nat_sim_goal (nat_clause 27),
  NAT_CASE_TAC THEN
  SUBGOAL_THEN `htheory_ok (hthyof ctx) /\ hterm_ok (hsigof ctx) (TmVar c ty =:= r)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[NAT_OK_THEORY; NAT_OK_TM]; ALL_TAC] THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `c:string`; `ty:holtype`; `r:holterm`]
               HOL_NEW_BASIC_DEFINITION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (nat_vars @ [`mt:(num#num#num)list`; `md:(num#num#num)list`;
                            `(ctx,hnms,htys,htms,hths,drops,pol):hrstate`]) NAT_GROW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `CONS (HConstSpec [c,r] (TmVar c ty =:= r)) ctx`;
                `nms:string list`;
                `APPEND tys mt:(num#num#num)list`; `ntms:(num#num#num#num#num)list`;
                `APPEND dbs md:(num#num#num)list`; `ths:(num#num)list`; `nmap:num list`;
                `ymap:num list`; `drops:(num#num)list`; `pol:num`; `hnms:string list`;
                `htys:holtype list`; `htms:holterm list`;
                `hths:(holterm list#holterm)list`] NAT_CTX) THEN
  ASM_SIMP_TAC[FIBRE_HUPDATES_EXTENDS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`CONS (HConstSpec [c,r] (TmVar c ty =:= r)) ctx`; `nms:string list`;
                `APPEND tys mt:(num#num#num)list`; `ntms:(num#num#num#num#num)list`;
                `APPEND dbs md:(num#num#num)list`; `ths:(num#num)list`; `nmap:num list`;
                `ymap:num list`; `drops:(num#num)list`; `pol:num`;
                `CONS (HConstSpec [c,r] (TmVar c ty =:= r)) ctx`; `hnms:string list`;
                `htys:holtype list`; `htms:holterm list`;
                `hths:(holterm list#holterm)list`; `drops:(num#num)list`; `pol:num`;
                `(e:num,k:num)`; `[]:holterm list`; `TmConst c ty =:= r`] NAT_PUSH_TH) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[fibre_thm_wit; MEM] THEN EXISTS_TAC `[]:hdbterm list` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(CONS (HConstSpec [c,r] (TmVar c ty =:= r)) ctx,hnms,htys,htms,
               APPEND hths [[],TmConst c ty =:= r],drops,pol):hrstate` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOLR_STEP_NEW_DEFINITION THEN
  SUBGOAL_THEN `EL t (htms:holterm list) = (TmVar c ty =:= r)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NAT_SIM_TERMOF]; ALL_TAC] THEN
  NAT_LIVE_TAC);;

(* NEW_TYPEDEF. HOL Light's operation applied to the chosen P x, at the     *)
(* native names, gives the two theorems the new rows stand for.             *)
let HOL_TYPEDEF_THMS = prove
 (`!ctxt tyname absname repname P x params.
        htheory_ok (hthyof ctxt) /\
        hproves (hthyof ctxt) [] (TmComb P x) /\
        HCLOSED P /\
        hlookup (htype_list ctxt) tyname = NONE /\
        hlookup (hconst_list ctxt) absname = NONE /\
        hlookup (hconst_list ctxt) repname = NONE /\
        ~(absname = repname) /\
        hstring_sorted params /\ (!v. MEM v params <=> MEM v (htvars P))
        ==> HTypeDefn tyname P absname repname hupdates ctxt /\
            hproves (hthyof (CONS (HTypeDefn tyname P absname repname) ctxt)) []
                    (htydef_abs tyname absname repname x params) /\
            hproves (hthyof (CONS (HTypeDefn tyname P absname repname) ctxt)) []
                    (htydef_rep tyname absname repname P x params)`,
  REWRITE_TAC[htydef_abs; htydef_rep] THEN MATCH_ACCEPT_TAC HOL_NEW_BASIC_TYPE_DEFINITION);;

let NAT_SIM_THM_WIT = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol hnms htys htms hths h.
      nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
              (ctx,hnms,htys,htms,hths,drops,pol) /\ h < LENGTH ths
      ==> fibre_thm_wit ctx nms tys dbs (EL h ths) (EL h hths)`,
  REWRITE_TAC[nat_sim] THEN MESON_TAC[]);;

let APPEND_SING_SING = prove
 (`!(l:A list) a b. APPEND (APPEND l [a]) [b] = APPEND l [a; b]`,
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

(* The HOLR entry for row h is ([],c) with c alpha-equivalent to the chosen *)
(* P x, which is what holr_step's clause asks; the context then extends by  *)
(* the same update on both sides.                                            *)
let NAT_SIM_NEW_TYPEDEF = prove
 (nat_sim_goal (nat_clause 28),
  NAT_CASE_TAC THEN
  SUBGOAL_THEN `?c. EL h (hths:(holterm list#holterm)list) = ([],c) /\
                    hproves (hthyof ctx) [] c /\ hdb c = hdb (TmComb P x)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL (nat_vars @ [`hnms:string list`; `htys:holtype list`; `htms:holterm list`;
                              `hths:(holterm list#holterm)list`; `h:num`]) NAT_SIM_THM_WIT) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`EL h (hths:(holterm list#holterm)list)`,`w:holterm list#holterm`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; fibre_thm_wit; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`hy:holterm list`; `c:holterm`] THEN
    DISCH_THEN(X_CHOOSE_THEN `hs0:hdbterm list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c:holterm` THEN
    SUBGOAL_THEN `hs0:hdbterm list = []` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[FDDB_FUNCTIONAL]; ALL_TAC] THEN
    SUBGOAL_THEN `hy:holterm list = []` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[MEM; list_CASES]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FDDB_FUNCTIONAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `HACONV c (TmComb P x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HACONV_DB; FIBRE_PROVES_WELLTYPED]; ALL_TAC] THEN
  SUBGOAL_THEN `htheory_ok (hthyof ctx)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NAT_OK_THEORY]; ALL_TAC] THEN
  SUBGOAL_THEN `hproves (hthyof ctx) [] (TmComb P x)` ASSUME_TAC THENL
   [MATCH_MP_TAC HPROVES_ACONV THEN
    MAP_EVERY EXISTS_TAC [`[]:holterm list`; `c:holterm`] THEN ASM_REWRITE_TAC[MEM; ALL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `EL (EL n nmap) (nms:string list)`;
                `EL (EL a nmap) (nms:string list)`; `EL (EL r nmap) (nms:string list)`;
                `P:holterm`; `x:holterm`; `params:string list`] HOL_TYPEDEF_THMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `ctx' = CONS (HTypeDefn (EL (EL n nmap) nms) P (EL (EL a nmap) nms)
                                     (EL (EL r nmap) nms)) ctx` THEN
  SUBGOAL_THEN `ctx' hextends ctx` ASSUME_TAC THENL
   [EXPAND_TAC "ctx'" THEN MATCH_MP_TAC FIBRE_HUPDATES_EXTENDS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL ([`ctx:hupdate list`; `ctx':hupdate list`] @ tl nat_vars @
                [`hnms:string list`; `htys:holtype list`; `htms:holterm list`;
                 `hths:(holterm list#holterm)list`]) NAT_CTX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL ([`ctx':hupdate list`] @ tl nat_vars @
                [`mt:(num#num#num)list`; `md:(num#num#num)list`;
                 `(ctx',hnms,htys,htms,hths,drops,pol):hrstate`]) NAT_GROW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ctx':hupdate list`; `nms:string list`; `APPEND tys mt:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `APPEND dbs md:(num#num#num)list`;
                `ths:(num#num)list`; `nmap:num list`; `ymap:num list`;
                `drops:(num#num)list`; `pol:num`; `ctx':hupdate list`; `hnms:string list`;
                `htys:holtype list`; `htms:holterm list`;
                `hths:(holterm list#holterm)list`; `drops:(num#num)list`; `pol:num`;
                `(e1:num,k1:num)`; `[]:holterm list`;
                `htydef_abs (EL (EL n nmap) nms) (EL (EL a nmap) nms) (EL (EL r nmap) nms)
                            x params`] NAT_PUSH_TH) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[fibre_thm_wit; MEM] THEN EXISTS_TAC `[]:hdbterm list` THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(SPECL [`ctx':hupdate list`; `nms:string list`; `APPEND tys mt:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `APPEND dbs md:(num#num#num)list`;
                `APPEND ths [e1:num,k1:num]`; `nmap:num list`; `ymap:num list`;
                `drops:(num#num)list`; `pol:num`; `ctx':hupdate list`; `hnms:string list`;
                `htys:holtype list`; `htms:holterm list`;
                `APPEND hths [[]:holterm list,
                  htydef_abs (EL (EL n nmap) nms) (EL (EL a nmap) nms) (EL (EL r nmap) nms)
                             x params]`;
                `drops:(num#num)list`; `pol:num`;
                `(e2:num,k2:num)`; `[]:holterm list`;
                `htydef_rep (EL (EL n nmap) nms) (EL (EL a nmap) nms) (EL (EL r nmap) nms)
                            P x params`] NAT_PUSH_TH) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[fibre_thm_wit; MEM] THEN EXISTS_TAC `[]:hdbterm list` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[APPEND_SING_SING] THEN STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC
   `(ctx',hnms,htys,htms,
     APPEND hths [[],htydef_abs (EL (EL n nmap) nms) (EL (EL a nmap) nms)
                                (EL (EL r nmap) nms) x params;
                  [],htydef_rep (EL (EL n nmap) nms) (EL (EL a nmap) nms)
                                (EL (EL r nmap) nms) P x params],
     drops,pol):hrstate` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rand(concl th) = `ctx':hupdate list`)) THEN
  NAT_NAME_TAC `n:num` THEN NAT_NAME_TAC `a:num` THEN NAT_NAME_TAC `r:num` THEN
  MATCH_MP_TAC HOLR_STEP_NEW_TYPEDEF THEN
  MAP_EVERY EXISTS_TAC [`c:holterm`; `x:holterm`; `params:string list`] THEN
  ASM_REWRITE_TAC[] THEN NAT_LIVE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Canonicity is kept. A row decodes as a type or as a list of types, not   *)
(* both (and likewise for de Bruijn rows); a row that decodes keeps its     *)
(* decoding when rows or names are appended; so rows that were not the same *)
(* object stay so, and appended rows are new by the step's premise.         *)
(* ------------------------------------------------------------------------- *)

let FDTY_NOT_BOTH = prove
 (`!nms tys i t l. ~(fdty nms tys i t /\ fdtys nms tys i l)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[fdty_CASES] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[PAIR_EQ; ARITH_RULE `~(0 = 2) /\ ~(0 = 3) /\ ~(1 = 2) /\ ~(1 = 3)`]);;

let FDDB_NOT_BOTH = prove
 (`!nms tys dbs i t l. ~(fddb nms tys dbs i t /\ fddbs nms tys dbs i l)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[fddb_CASES] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[PAIR_EQ; ARITH_RULE
    `~(0 = 5) /\ ~(0 = 6) /\ ~(1 = 5) /\ ~(1 = 6) /\ ~(2 = 5) /\ ~(2 = 6) /\
     ~(3 = 5) /\ ~(3 = 6) /\ ~(4 = 5) /\ ~(4 = 6)`]);;

let FDTY_STABLE = prove
 (`!nms tys nm ty i.
      (?t. fdty nms tys i t) \/ (?l. fdtys nms tys i l)
      ==> (!t. fdty (APPEND nms nm) (APPEND tys ty) i t <=> fdty nms tys i t) /\
          (!l. fdtys (APPEND nms nm) (APPEND tys ty) i l <=> fdtys nms tys i l)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `nm:string list`;
                `ty:(num#num#num)list`] FDTY_EXTEND) THEN
  MP_TAC(SPECL [`APPEND nms nm:string list`; `APPEND tys ty:(num#num#num)list`]
               FDTY_FUNCTIONAL) THEN
  MP_TAC(SPECL [`APPEND nms nm:string list`; `APPEND tys ty:(num#num#num)list`]
               FDTY_NOT_BOTH) THEN
  MESON_TAC[]);;

let FDDB_STABLE = prove
 (`!nms tys dbs nm ty db i.
      (?t. fddb nms tys dbs i t) \/ (?l. fddbs nms tys dbs i l)
      ==> (!t. fddb (APPEND nms nm) (APPEND tys ty) (APPEND dbs db) i t <=>
               fddb nms tys dbs i t) /\
          (!l. fddbs (APPEND nms nm) (APPEND tys ty) (APPEND dbs db) i l <=>
               fddbs nms tys dbs i l)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                `nm:string list`; `ty:(num#num#num)list`; `db:(num#num#num)list`]
               FDDB_EXTEND) THEN
  MP_TAC(SPECL [`APPEND nms nm:string list`; `APPEND tys ty:(num#num#num)list`;
                `APPEND dbs db:(num#num#num)list`] FDDB_FUNCTIONAL) THEN
  MP_TAC(SPECL [`APPEND nms nm:string list`; `APPEND tys ty:(num#num#num)list`;
                `APPEND dbs db:(num#num#num)list`] FDDB_NOT_BOTH) THEN
  MESON_TAC[]);;

let FDTY_SAME_SYM_BOUND = prove
 (`!nms tys i j. fdty_same nms tys i j
                 ==> fdty_same nms tys j i /\ i < LENGTH tys /\ j < LENGTH tys`,
  REWRITE_TAC[fdty_same] THEN MESON_TAC[FDTY_BOUND]);;

let FDDB_SAME_SYM_BOUND = prove
 (`!nms tys dbs i j. fddb_same nms tys dbs i j
                     ==> fddb_same nms tys dbs j i /\ i < LENGTH dbs /\ j < LENGTH dbs`,
  REWRITE_TAC[fddb_same] THEN MESON_TAC[FDDB_BOUND]);;

let FDTY_SAME_STABLE = prove
 (`!nms tys nm ty i j.
      ((?t. fdty nms tys i t) \/ (?l. fdtys nms tys i l)) /\
      ((?t. fdty nms tys j t) \/ (?l. fdtys nms tys j l))
      ==> (fdty_same (APPEND nms nm) (APPEND tys ty) i j <=> fdty_same nms tys i j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `nm:string list`;
                `ty:(num#num#num)list`; `i:num`] FDTY_STABLE) THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `nm:string list`;
                `ty:(num#num#num)list`; `j:num`] FDTY_STABLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[fdty_same]);;

let FDDB_SAME_STABLE = prove
 (`!nms tys dbs nm ty db i j.
      ((?t. fddb nms tys dbs i t) \/ (?l. fddbs nms tys dbs i l)) /\
      ((?t. fddb nms tys dbs j t) \/ (?l. fddbs nms tys dbs j l))
      ==> (fddb_same (APPEND nms nm) (APPEND tys ty) (APPEND dbs db) i j <=>
           fddb_same nms tys dbs i j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                `nm:string list`; `ty:(num#num#num)list`; `db:(num#num#num)list`;
                `i:num`] FDDB_STABLE) THEN
  MP_TAC(SPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                `nm:string list`; `ty:(num#num#num)list`; `db:(num#num#num)list`;
                `j:num`] FDDB_STABLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[fddb_same]);;

(* A relation on ids that is one-to-one below n0, and relates no id at or  *)
(* above n0 to an earlier one, is one-to-one.                              *)
let CANON_EXTEND = prove
 (`!(same:num->num->bool) n0 n.
      (!i j. same i j ==> same j i /\ i < n /\ j < n) /\
      (!i j. i < n0 /\ j < n0 /\ same i j ==> i = j) /\
      (!k j. k < n /\ n0 <= k /\ j < k ==> ~same j k)
      ==> !i j. same i j ==> i = j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(same:num->num->bool) j i /\ i < n /\ j < n` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < n0 /\ j < n0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `i < j:num` THENL
   [UNDISCH_TAC `!k j. k < n /\ n0 <= k /\ j < k ==> ~(same:num->num->bool) j k` THEN
    DISCH_THEN(MP_TAC o SPECL [`j:num`; `i:num`]) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    UNDISCH_TAC `!k j. k < n /\ n0 <= k /\ j < k ==> ~(same:num->num->bool) j k` THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* Appending new type and de Bruijn rows keeps canonicity. *)
let NAT_CANON_ROWS = prove
 (`!nms tys dbs mt md.
      nat_canon nms tys dbs /\
      (!i. i < LENGTH tys ==> (?t. fdty nms tys i t) \/ (?l. fdtys nms tys i l)) /\
      nat_new_rows nms tys dbs mt md
      ==> nat_canon nms (APPEND tys mt) (APPEND dbs md)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nat_canon; nat_new_rows] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i < LENGTH (APPEND dbs md:(num#num#num)list)
        ==> (?t. fddb nms (APPEND tys mt) (APPEND dbs md) i t) \/
            (?l. fddbs nms (APPEND tys mt) (APPEND dbs md) i l)`
   ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[LENGTH_APPEND] THEN DISCH_TAC THEN
    ASM_CASES_TAC `i < LENGTH (dbs:(num#num#num)list)` THENL
     [MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                     `[]:string list`; `mt:(num#num#num)list`; `md:(num#num#num)list`]
                    FDDB_EXTEND) THEN
      REWRITE_TAC[APPEND_NIL] THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `APPEND dbs md:(num#num#num)list`)) (concl th) &&
        not (can (find_term ((=) `fddb_same`)) (concl th)))) THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CANON_EXTEND THEN
    MAP_EVERY EXISTS_TAC [`LENGTH (tys:(num#num#num)list)`;
                          `LENGTH (APPEND tys mt:(num#num#num)list)`] THEN
    REPEAT CONJ_TAC THENL
     [MESON_TAC[FDTY_SAME_SYM_BOUND];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `[]:string list`;
                     `mt:(num#num#num)list`; `i:num`; `j:num`] FDTY_SAME_STABLE) THEN
      REWRITE_TAC[APPEND_NIL] THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
      REWRITE_TAC[LENGTH_APPEND] THEN ASM_MESON_TAC[]];
    MATCH_MP_TAC CANON_EXTEND THEN
    MAP_EVERY EXISTS_TAC [`LENGTH (dbs:(num#num#num)list)`;
                          `LENGTH (APPEND dbs md:(num#num#num)list)`] THEN
    REPEAT CONJ_TAC THENL
     [MESON_TAC[FDDB_SAME_SYM_BOUND];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                     `[]:string list`; `mt:(num#num#num)list`; `md:(num#num#num)list`;
                     `i:num`; `j:num`] FDDB_SAME_STABLE) THEN
      REWRITE_TAC[APPEND_NIL] THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
      REWRITE_TAC[LENGTH_APPEND] THEN ASM_MESON_TAC[]]]);;

(* Appending new names keeps canonicity. *)
let NAT_CANON_NAMES = prove
 (`!nms tys dbs mn.
      nat_canon nms tys dbs /\
      (!i. i < LENGTH tys ==> (?t. fdty nms tys i t) \/ (?l. fdtys nms tys i l)) /\
      nat_new_names nms mn
      ==> nat_canon (APPEND nms mn) tys dbs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nat_canon; nat_new_names] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\i j. i < LENGTH (APPEND nms mn:string list) /\
                          j < LENGTH (APPEND nms mn:string list) /\
                          EL i (APPEND nms mn:string list) = EL j (APPEND nms mn)`;
                   `LENGTH (nms:string list)`; `LENGTH (APPEND nms mn:string list)`]
                  CANON_EXTEND) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MESON_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `EL:num->string list->string`)) (concl th) &&
        not (can (find_term ((=) `mn:string list`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `EL i (APPEND nms mn:string list) = EL j (APPEND nms mn)` THEN
      ASM_SIMP_TAC[EL_APPEND];
      REWRITE_TAC[LENGTH_APPEND] THEN ASM_MESON_TAC[]];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                   `mn:string list`; `[]:(num#num#num)list`; `[]:(num#num#num)list`]
                  FDDB_EXTEND) THEN
    REWRITE_TAC[APPEND_NIL] THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FDTY_SAME_SYM_BOUND) THEN
    MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `mn:string list`;
                   `[]:(num#num#num)list`; `i:num`; `j:num`] FDTY_SAME_STABLE) THEN
    REWRITE_TAC[APPEND_NIL] THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FDDB_SAME_SYM_BOUND) THEN
    MP_TAC(ISPECL [`nms:string list`; `tys:(num#num#num)list`; `dbs:(num#num#num)list`;
                   `mn:string list`; `[]:(num#num#num)list`; `[]:(num#num#num)list`;
                   `i:num`; `j:num`] FDDB_SAME_STABLE) THEN
    REWRITE_TAC[APPEND_NIL] THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]]);;

let NAT_ROWS_OK_TYS = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol.
      nat_rows_ok (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
      ==> !i. i < LENGTH tys ==> (?t. fdty nms tys i t) \/ (?l. fdtys nms tys i l)`,
  REWRITE_TAC[nat_rows_ok; fibre_inv; fibre_ty_ok] THEN MESON_TAC[]);;

(* Every step keeps canonicity. *)
let NAT_STEP_CANON = prove
 (`!ns r ns'. nat_step ns r ns' ==> nat_ok ns /\ nat_rows_ok ns' ==> nat_ok ns'`,
  MATCH_MP_TAC nat_step_INDUCT THEN REWRITE_TAC[nat_ok] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL nat_vars NAT_ROWS_OK_TYS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST [MATCH_MP_TAC NAT_CANON_ROWS THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC NAT_CANON_NAMES THEN ASM_REWRITE_TAC[] THEN NO_TAC]);;

let NAT_OK_ROWS = prove
 (`!ns. nat_ok ns ==> nat_rows_ok ns`,
  REWRITE_TAC[FORALL_PAIR_THM; nat_ok] THEN MESON_TAC[]);;

(* Under canonicity, ids are equal exactly when their objects are: a test  *)
(* on ids decides equality of names, types and terms.                      *)
(*                                                                           *)
(* nat_step states every guard on decoded objects, so the simulation above *)
(* needs no canonicity. A native handler decides guards on ids. A test     *)
(* that two ids are equal is sound by functionality alone (equal ids,       *)
(* equal objects); canonicity is what makes sound a test that two objects  *)
(* differ, that a name is undeclared, or that a search found every         *)
(* occurrence:                                                               *)
(*   NEW_TYPE, NEW_CONSTANT, NEW_DEFINITION, NEW_TYPEDEF: the name is not  *)
(*     declared yet (decided per name row), and NEW_TYPEDEF's two constant *)
(*     names differ (name ids differ);                                      *)
(*   ABS_RULE: the variable is free in no hypothesis (no hypothesis row    *)
(*     reaches the variable's row);                                         *)
(*   ABS and ABS_RULE: binding replaces every occurrence of the variable,  *)
(*     found by its row;                                                    *)
(*   INST and INST_TYPE: substitution finds every variable or type         *)
(*     variable it replaces, by its row.                                    *)
(* The tests that only need equal objects (TRANS's middle term, EQ_MP,     *)
(* MK_COMB's types, ASSUME, CONST's instance, EXPECT_ALPHA's hypothesis    *)
(* sets) are sound without canonicity, and complete with it. DEDUCT's      *)
(* removal of a hypothesis by id, and the unions of hypothesis lists, keep  *)
(* extra hypotheses at worst, which the clauses allow.                      *)
let NAT_CANON_NAME_EQ = prove
 (`!nms tys dbs i j. nat_canon nms tys dbs /\ i < LENGTH nms /\ j < LENGTH nms
                     ==> (EL i nms = EL j nms <=> i = j)`,
  REWRITE_TAC[nat_canon] THEN MESON_TAC[]);;

let NAT_CANON_TY_EQ = prove
 (`!nms tys dbs i j t u.
      nat_canon nms tys dbs /\ fdty nms tys i t /\ fdty nms tys j u ==> (i = j <=> t = u)`,
  REWRITE_TAC[nat_canon; fdty_same] THEN MESON_TAC[FDTY_FUNCTIONAL]);;

let NAT_CANON_TYS_EQ = prove
 (`!nms tys dbs i j l m.
      nat_canon nms tys dbs /\ fdtys nms tys i l /\ fdtys nms tys j m ==> (i = j <=> l = m)`,
  REWRITE_TAC[nat_canon; fdty_same] THEN MESON_TAC[FDTY_FUNCTIONAL]);;

let NAT_CANON_DB_EQ = prove
 (`!nms tys dbs i j t u.
      nat_canon nms tys dbs /\ fddb nms tys dbs i t /\ fddb nms tys dbs j u ==> (i = j <=> t = u)`,
  REWRITE_TAC[nat_canon; fddb_same] THEN MESON_TAC[FDDB_FUNCTIONAL]);;

let NAT_CANON_DBS_EQ = prove
 (`!nms tys dbs i j l m.
      nat_canon nms tys dbs /\ fddbs nms tys dbs i l /\ fddbs nms tys dbs j m ==> (i = j <=> l = m)`,
  REWRITE_TAC[nat_canon; fddb_same] THEN MESON_TAC[FDDB_FUNCTIONAL]);;

(* ------------------------------------------------------------------------- *)
(* One step, and runs.                                                       *)
(* ------------------------------------------------------------------------- *)

let NAT_SIM_CASES =
  [NAT_SIM_NAME_REC; NAT_SIM_TYVAR; NAT_SIM_TYAPP; NAT_SIM_VAR; NAT_SIM_CONST;
   NAT_SIM_COMB; NAT_SIM_ABS; NAT_SIM_REFL; NAT_SIM_TRANS; NAT_SIM_MK_COMB;
   NAT_SIM_ABS_RULE; NAT_SIM_BETA; NAT_SIM_ASSUME; NAT_SIM_EQ_MP; NAT_SIM_DEDUCT;
   NAT_SIM_INST_TYPE; NAT_SIM_INST; NAT_SIM_EXPECT_ALPHA; NAT_SIM_LABEL; NAT_SIM_EMIT;
   NAT_SIM_DROP_TYPE; NAT_SIM_DROP_TERM; NAT_SIM_DROP_THM; NAT_SIM_POLICY;
   NAT_SIM_NEW_TYPE; NAT_SIM_NEW_CONSTANT; NAT_SIM_NEW_AXIOM; NAT_SIM_NEW_DEFINITION;
   NAT_SIM_NEW_TYPEDEF];;

let NAT_STEP_ROWS_SIM = prove
 (`!ns r ns' hr. nat_step ns r ns' /\ nat_rows_ok ns /\ nat_sim ns hr
                 ==> nat_rows_ok ns' /\ ?hr'. holr_step hr r hr' /\ nat_sim ns' hr'`,
  SUBGOAL_THEN
   `!ns r ns'. nat_step ns r ns'
               ==> !hr. nat_rows_ok ns /\ nat_sim ns hr
                        ==> nat_rows_ok ns' /\ ?hr'. holr_step hr r hr' /\ nat_sim ns' hr'`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC nat_step_INDUCT THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC NAT_SIM_CASES));;

let NAT_STEP_SIM = prove
 (`!ns r ns' hr. nat_step ns r ns' /\ nat_ok ns /\ nat_sim ns hr
                 ==> nat_ok ns' /\ ?hr'. holr_step hr r hr' /\ nat_sim ns' hr'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ns:nstate`; `r:holr_record`; `ns':nstate`; `hr:hrstate`]
               NAT_STEP_ROWS_SIM) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[NAT_OK_ROWS]; ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`ns:nstate`; `r:holr_record`; `ns':nstate`] NAT_STEP_CANON) THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `hr':hrstate` THEN ASM_REWRITE_TAC[]]);;

let NAT_RUN_SIM = prove
 (`!recs ns ns' hr. tc_path nat_step recs ns ns' /\ nat_ok ns /\ nat_sim ns hr
                    ==> nat_ok ns' /\ ?hr'. tc_path holr_step recs hr hr' /\ nat_sim ns' hr'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[tc_path] THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `hr:hrstate` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:nstate` STRIP_ASSUME_TAC)
                             STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`ns:nstate`; `h:holr_record`; `u:nstate`; `hr:hrstate`] NAT_STEP_SIM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `hu:hrstate` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:nstate`; `ns':nstate`; `hu:hrstate`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `hv:hrstate` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `hv:hrstate` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `hu:hrstate` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Acceptance.                                                               *)
(* ------------------------------------------------------------------------- *)

(* A bootstrap state: HOL's initial context, canonical rows whose type rows *)
(* are ok in it, and no named rows, theorem rows, N or Y entries. It is ok  *)
(* and simulates HOLR's initial state; no HOLR id refers to its rows.       *)
let NAT_BOOT = prove
 (`!nms0 tys0 dbs0 pol.
      (!i. i < LENGTH tys0 ==> fibre_ty_ok hinit_ctxt nms0 tys0 i) /\
      nat_canon nms0 tys0 dbs0
      ==> nat_ok (hinit_ctxt,nms0,tys0,[],dbs0,[],[],[],[],pol) /\
          nat_sim (hinit_ctxt,nms0,tys0,[],dbs0,[],[],[],[],pol)
                  (hinit_ctxt,[],[],[],[],[],pol)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[nat_ok; nat_rows_ok; fibre_inv; nat_sim; LENGTH; ALL; MAP; CONJUNCT1 LT;
                  hextends_RULES]);;

(* The top theorem: when the bytes are the encoding of records under a      *)
(* header policy, and the native steps run the records from a bootstrap    *)
(* state at the larger of the host's floor and that policy, the stream is   *)
(* accepted in HOLR's meaning under the host's floor.                       *)
let NAT_ACCEPTS = prove
 (`!hpol bytes pol recs nms0 tys0 dbs0 ns.
      bytes = holr_stream pol 0 recs /\ pol <= 2 /\
      (!i. i < LENGTH tys0 ==> fibre_ty_ok hinit_ctxt nms0 tys0 i) /\
      nat_canon nms0 tys0 dbs0 /\
      tc_path nat_step recs (hinit_ctxt,nms0,tys0,[],dbs0,[],[],[],[],MAX hpol pol) ns
      ==> holr_accepts hpol bytes`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`nms0:string list`; `tys0:(num#num#num)list`; `dbs0:(num#num#num)list`;
                `MAX hpol pol`] NAT_BOOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`recs:holr_record list`;
                `(hinit_ctxt,nms0,tys0,[],dbs0,[],[],[],[],MAX hpol pol):nstate`; `ns:nstate`;
                `(hinit_ctxt,[],[],[],[],[],MAX hpol pol):hrstate`] NAT_RUN_SIM) THEN
  ASM_REWRITE_TAC[holr_accepts] THEN
  DISCH_THEN(X_CHOOSE_THEN `hr':hrstate` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  MAP_EVERY EXISTS_TAC [`pol:num`; `recs:holr_record list`; `hr':hrstate`] THEN
  ASM_REWRITE_TAC[]);;

(* With it, the final native state: its context is a valid extension of     *)
(* HOL's initial context that meets the policy (under STANDARD every axiom  *)
(* is standard, under SEALED there is none), every theorem row is derivable *)
(* in its theory by de Bruijn image, and its rows are canonical.            *)
let NAT_ACCEPTS_SOUND = prove
 (`!hpol bytes pol recs nms0 tys0 dbs0 ctx nms tys ntms dbs ths nmap ymap drops pol'.
      bytes = holr_stream pol 0 recs /\ pol <= 2 /\
      (!i. i < LENGTH tys0 ==> fibre_ty_ok hinit_ctxt nms0 tys0 i) /\
      nat_canon nms0 tys0 dbs0 /\
      tc_path nat_step recs (hinit_ctxt,nms0,tys0,[],dbs0,[],[],[],[],MAX hpol pol)
              (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol')
      ==> holr_accepts hpol bytes /\
          ctx hextends hinit_ctxt /\ htheory_ok (hthyof ctx) /\
          (1 <= MAX hpol pol ==> hstd_axioms_ok ctx) /\
          (2 <= MAX hpol pol ==> hno_axioms ctx) /\
          ALL (fibre_thm_ok ctx nms tys dbs) ths /\ nat_canon nms tys dbs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC NAT_ACCEPTS THEN
    MAP_EVERY EXISTS_TAC [`pol:num`; `recs:holr_record list`; `nms0:string list`;
                          `tys0:(num#num#num)list`; `dbs0:(num#num#num)list`;
                          `(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol'):nstate`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`nms0:string list`; `tys0:(num#num#num)list`; `dbs0:(num#num#num)list`;
                `MAX hpol pol`] NAT_BOOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`recs:holr_record list`;
                `(hinit_ctxt,nms0,tys0,[],dbs0,[],[],[],[],MAX hpol pol):nstate`;
                `(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol'):nstate`;
                `(hinit_ctxt,[],[],[],[],[],MAX hpol pol):hrstate`] NAT_RUN_SIM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `hr':hrstate` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[nat_ok; nat_rows_ok; fibre_inv] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[HEXTENDS_THEORY_OK; HINIT_THEORY_OK]; ALL_TAC] THEN
  SUBGOAL_THEN `hr_ctx hr' = ctx` (SUBST1_TAC o SYM) THENL
   [UNDISCH_TAC `nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol') hr'` THEN
    SPEC_TAC(`hr':hrstate`,`hr':hrstate`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; nat_sim; hr_ctx] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`recs:holr_record list`;
                `(hinit_ctxt,[],[],[],[],[],MAX hpol pol):hrstate`; `hr':hrstate`]
               HOLR_RUN_POLICY) THEN
  ASM_REWRITE_TAC[hr_pol; hr_ctx; HINIT_AXIOMS] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The first native slice's bootstrap: names bool, fun, =, A; type rows     *)
(* [], bool, A, [bool], [A; bool], A->bool, [A->bool], [A; A->bool],        *)
(* A->A->bool; and the empty hypothesis list. Its type rows are ok in HOL's *)
(* initial context and its rows are canonical (NAT_BOOT_CANON), so the top  *)
(* theorem holds from it without a premise on its rows.                     *)
(* ------------------------------------------------------------------------- *)

let nat_boot_nms = new_definition
 `nat_boot_nms = ["bool"; "fun"; "="; "A"]`;;

let nat_boot_tys = new_definition
 `nat_boot_tys:(num#num#num)list =
    [2,0,0; 1,0,0; 0,3,0; 3,1,0; 3,2,3; 1,1,4; 3,5,0; 3,2,6; 1,1,7]`;;

let nat_boot_dbs = new_definition
 `nat_boot_dbs:(num#num#num)list = [5,0,0]`;;

let NAT_BOOT_TYS_OK = prove
 (`!i. i < LENGTH nat_boot_tys ==> fibre_ty_ok hinit_ctxt nat_boot_nms nat_boot_tys i`,
  let nms = rand(concl nat_boot_nms) and tys = rand(concl nat_boot_tys) in
  let row_tac (asl,w) =
    let k = dest_small_numeral(rand w) in
    let tac =
      try let th = fdty_thm nms tys k in
          DISJ1_TAC THEN EXISTS_TAC (rand(concl th)) THEN REWRITE_TAC[th]
      with Failure _ ->
          let th = fdtys_thm nms tys k in
          DISJ2_TAC THEN EXISTS_TAC (rand(concl th)) THEN REWRITE_TAC[th] in
    (REWRITE_TAC[fibre_ty_ok] THEN tac THEN
     REWRITE_TAC[HTYPE_OK; ALL; LENGTH; hsigof; hinit_ctxt; htype_list; hflat; MAP;
                 htypes_of_upd; APPEND; hlookup; HFun; HBool] THEN
     CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV) (asl,w) in
  REWRITE_TAC[nat_boot_nms; nat_boot_tys; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `i < 9 <=> i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
                                    i = 5 \/ i = 6 \/ i = 7 \/ i = 8`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN row_tac);;

(* ------------------------------------------------------------------------- *)
(* Canonicity and freshness of explicit rows: each row's decoding, as an    *)
(* equation, turns "the same object" into a comparison of decoded objects;  *)
(* bounded quantifiers over ids are expanded.                               *)
(* ------------------------------------------------------------------------- *)

let FDTY_IFF = prove
 (`!nms tys i t0. fdty nms tys i t0
      ==> (!t. fdty nms tys i t <=> t = t0) /\ (!l. fdtys nms tys i l <=> F)`,
  MESON_TAC[FDTY_FUNCTIONAL; FDTY_NOT_BOTH]);;

let FDTYS_IFF = prove
 (`!nms tys i l0. fdtys nms tys i l0
      ==> (!t. fdty nms tys i t <=> F) /\ (!l. fdtys nms tys i l <=> l = l0)`,
  MESON_TAC[FDTY_FUNCTIONAL; FDTY_NOT_BOTH]);;

let FDDB_IFF = prove
 (`!nms tys dbs i t0. fddb nms tys dbs i t0
      ==> (!t. fddb nms tys dbs i t <=> t = t0) /\ (!l. fddbs nms tys dbs i l <=> F)`,
  MESON_TAC[FDDB_FUNCTIONAL; FDDB_NOT_BOTH]);;

let FDDBS_IFF = prove
 (`!nms tys dbs i l0. fddbs nms tys dbs i l0
      ==> (!t. fddb nms tys dbs i t <=> F) /\ (!l. fddbs nms tys dbs i l <=> l = l0)`,
  MESON_TAC[FDDB_FUNCTIONAL; FDDB_NOT_BOTH]);;

let CANON_BY_RANGE = prove
 (`!(same:num->num->bool) n.
      (!i j. same i j ==> i < n /\ j < n) /\
      (!i. i < n ==> !j. j < n ==> same i j ==> i = j)
      ==> !i j. same i j ==> i = j`,
  MESON_TAC[]);;

let NAT_NEW_ROWS_NIL = prove
 (`!nms tys dbs. nat_new_rows nms tys dbs [] []`,
  REWRITE_TAC[nat_new_rows; LENGTH; ADD_CLAUSES; APPEND_NIL] THEN
  MESON_TAC[ARITH_RULE `!a k. ~(k < a /\ a <= k)`]);;

let NAT_NEW_NAMES_NIL = prove
 (`!nms. nat_new_names nms []`,
  REWRITE_TAC[nat_new_names; LENGTH; ADD_CLAUSES] THEN
  MESON_TAC[ARITH_RULE `!a k. ~(k < a /\ a <= k)`]);;

(* The decodings of every row of explicit type and de Bruijn regions. *)
let nat_row_iffs nms tys dbs =
  let nt = length(dest_list tys) and nd = length(dest_list dbs) in
  let ty i = try CONJUNCTS(MATCH_MP FDTY_IFF (fdty_thm nms tys i))
             with Failure _ -> try CONJUNCTS(MATCH_MP FDTYS_IFF (fdtys_thm nms tys i))
             with Failure _ -> [] in
  let db i = try CONJUNCTS(MATCH_MP FDDB_IFF (fddb_thm nms tys dbs i))
             with Failure _ -> try CONJUNCTS(MATCH_MP FDDBS_IFF (fddbs_thm nms tys dbs i))
             with Failure _ -> [] in
  flat(map ty (0--(nt-1))) @ flat(map db (0--(nd-1)));;

let NAT_EXPLICIT_TAC iffs =
  REWRITE_TAC[LENGTH; APPEND; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[fdty_same; fddb_same] THEN CONV_TAC FIBRE_EVAL_CONV THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC iffs THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2; EXISTS_REFL; EXISTS_SIMP] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN
  REWRITE_TAC[holtype_INJ; holtype_DISTINCT; hdbterm_INJ; hdbterm_DISTINCT; CONS_11;
              NOT_CONS_NIL; GSYM NOT_CONS_NIL] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN CONV_TAC(DEPTH_CONV CHAR_EQ_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

(* A step's freshness premise, on explicit rows. *)
let NAT_NEW_CONV iffs tm =
  let c = fst(strip_comb tm) in
  if is_const c && mem (fst(dest_const c)) ["nat_new_rows"; "nat_new_names"]
  then EQT_INTRO(prove(tm, REWRITE_TAC[NAT_NEW_ROWS_NIL; NAT_NEW_NAMES_NIL] THEN
                           REWRITE_TAC[nat_new_rows; nat_new_names] THEN
                           NAT_EXPLICIT_TAC iffs))
  else failwith "NAT_NEW_CONV";;

let NAT_BOOT_CANON = prove
 (`nat_canon nat_boot_nms nat_boot_tys nat_boot_dbs`,
  let nms = rand(concl nat_boot_nms) and tys = rand(concl nat_boot_tys)
  and dbs = rand(concl nat_boot_dbs) in
  let iffs = nat_row_iffs nms tys dbs in
  let range_tac bound n =
    MATCH_MP_TAC CANON_BY_RANGE THEN EXISTS_TAC (mk_small_numeral n) THEN CONJ_TAC THENL
     [MP_TAC bound THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[];
      NAT_EXPLICIT_TAC iffs] in
  REWRITE_TAC[nat_canon; nat_boot_nms; nat_boot_tys; nat_boot_dbs] THEN
  REPEAT CONJ_TAC THENL
   [NAT_EXPLICIT_TAC iffs;
    NAT_EXPLICIT_TAC iffs;
    range_tac (ISPECL [nms; tys] FDTY_SAME_SYM_BOUND) (length(dest_list tys));
    range_tac (ISPECL [nms; tys; dbs] FDDB_SAME_SYM_BOUND) (length(dest_list dbs))]);;

let NAT_ACCEPTS_BOOT = prove
 (`!hpol bytes pol recs ns.
      bytes = holr_stream pol 0 recs /\ pol <= 2 /\
      tc_path nat_step recs
              (hinit_ctxt,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],MAX hpol pol) ns
      ==> holr_accepts hpol bytes`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NAT_ACCEPTS THEN
  MAP_EVERY EXISTS_TAC [`pol:num`; `recs:holr_record list`; `nat_boot_nms`;
                        `nat_boot_tys`; `nat_boot_dbs`; `ns:nstate`] THEN
  ASM_REWRITE_TAC[NAT_BOOT_TYS_OK; NAT_BOOT_CANON]);;

(* ------------------------------------------------------------------------- *)
(* Composing the type rows a handler appends: none, one ok row, or the rows *)
(* of two successive appends. With FIBRE_TYVAR, FIBRE_TYAPP, FIBRE_TYNIL    *)
(* and FIBRE_TYCONS for each interned row, a handler's appended type rows   *)
(* meet nat_tys_ok one row at a time.                                        *)
(* ------------------------------------------------------------------------- *)

let NAT_TYS_OK_NIL = prove
 (`!ctx nms tys. nat_tys_ok ctx nms tys []`,
  REWRITE_TAC[nat_tys_ok; LENGTH; ADD_CLAUSES] THEN
  MESON_TAC[ARITH_RULE `!a i. ~(a <= i /\ i < a)`]);;

let NAT_TYS_OK_ONE = prove
 (`!ctx nms tys row.
      fibre_ty_ok ctx nms (APPEND tys [row]) (LENGTH tys) ==> nat_tys_ok ctx nms tys [row]`,
  REWRITE_TAC[nat_tys_ok; LENGTH] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i = LENGTH (tys:(num#num#num)list)` (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

let NAT_TYS_OK_APPEND = prove
 (`!ctx nms tys mt mt'.
      nat_tys_ok ctx nms tys mt /\ nat_tys_ok ctx nms (APPEND tys mt) mt'
      ==> nat_tys_ok ctx nms tys (APPEND mt mt')`,
  REWRITE_TAC[nat_tys_ok; LENGTH_APPEND; APPEND_ASSOC; ADD_ASSOC] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `i < LENGTH (tys:(num#num#num)list) + LENGTH (mt:(num#num#num)list)` THENL
   [MP_TAC(ISPECL [`ctx:hupdate list`; `nms:string list`; `APPEND tys mt:(num#num#num)list`;
                   `[]:string list`; `mt':(num#num#num)list`; `i:num`] FIBRE_TY_OK_EXTEND) THEN
    REWRITE_TAC[APPEND_NIL] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC) ;
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `mt':(num#num#num)list`)) (concl th))) THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A positive control. A stream of the first native slice's record kinds,  *)
(* ending in an EXPECT_ALPHA claim, runs through nat_step from the slice's  *)
(* bootstrap, so the top theorem's run premise is met by a real stream and *)
(* the stream is accepted in HOLR's meaning.                                *)
(*   names  "=", "A", "bool", "fun" (found), "x" (new)                      *)
(*   types  A, bool, A->bool, A->A->bool (all found)                         *)
(*   terms  0 x:A, 1 (=):A->A->bool, 2 (=) x, 3 x = x                        *)
(*   rules  REFL x, then TRANS of it with itself; the claim [] |- x = x.     *)
(* ------------------------------------------------------------------------- *)


let ctl_recs = new_definition
 `ctl_recs =
    [RName [61]; RName [65]; RTyVar 1; RName [98;111;111;108]; RName [102;117;110];
     RTyApp 2 []; RTyApp 3 [0;1]; RTyApp 3 [0;2]; RName [120]; RVar 4 0; RConst 0 3;
     RComb 1 0; RComb 2 0; RRefl 0; RTrans 0 0; RExpectAlpha 1 [] 3]`;;

let rec fdtm_thm nms tys ntms i =
  let rules = CONJUNCTS(SPECL [nms; tys; ntms] fdtm_RULES) in
  let r = el i (dest_list ntms) in
  let tag,r1 = dest_pair r in
  let a,r2 = dest_pair r1 in
  let b,r3 = dest_pair r2 in
  let c,d = dest_pair r3 in
  let n = mk_small_numeral i in
  let tg = dest_small_numeral tag in
  if tg = 0 || tg = 1 then
    let tth = fdty_thm nms tys (dest_small_numeral b) in
    fibre_mp (SPECL [n; a; b; c; d; rand(concl tth)] (el tg rules)) [tth]
  else if tg = 2 || tg = 3 then
    let s = fdtm_thm nms tys ntms (dest_small_numeral a)
    and t = fdtm_thm nms tys ntms (dest_small_numeral b) in
    fibre_mp (SPECL [n; a; b; c; d; rand(concl s); rand(concl t)] (el tg rules)) [s; t]
  else failwith "fdtm_thm";;

let ctl_state = map (fun s -> parse_term s)
 ["hinit_ctxt"; "[\"bool\"; \"fun\"; \"=\"; \"A\"]";
  "[2,0,0; 1,0,0; 0,3,0; 3,1,0; 3,2,3; 1,1,4; 3,5,0; 3,2,6; 1,1,7]:(num#num#num)list";
  "[]:(num#num#num#num#num)list"; "[5,0,0]:(num#num#num)list"; "[]:(num#num)list";
  "[]:num list"; "[]:num list"; "[]:(num#num)list"; "pol:num"];;

let rec strip_tuple t = try let a,b = dest_pair t in a :: strip_tuple b with Failure _ -> [t];;

let ctl_A = `TyVar "A"` and ctl_bool = `TyApp "bool" []`
and ctl_AB = `TyApp "fun" [TyVar "A"; TyApp "bool" []]`
and ctl_AAB = `TyApp "fun" [TyVar "A"; TyApp "fun" [TyVar "A"; TyApp "bool" []]]`;;
let ctl_x = `TmVar "x" (TyVar "A")`;;
let ctl_eq = mk_comb(mk_comb(`TmConst`,`"="`),ctl_AAB);;
let ctl_eqx = list_mk_comb(`TmComb`,[ctl_eq;ctl_x]);;
let ctl_xx = list_mk_comb(`TmComb`,[ctl_eqx;ctl_x]);;
let ctl_dbx = `hdbVar "x" (TyVar "A")`;;

(* Discharge a step's premises by evaluating them on the explicit rows. *)
let NAT_CTL_TAC decs =
  REWRITE_TAC[NAT_TYS_OK_NIL; APPEND; nat_ops_live; holr_operands; holr_live; ALL; ALL2;
              MEM; MAP; FST; SND; holr_name; hchar_of] THEN
  CONV_TAC FIBRE_EVAL_CONV THEN
  REWRITE_TAC[hlookup; htype_list; hconst_list; hinit_ctxt; hflat; MAP; htypes_of_upd;
              hconsts_of_upd; APPEND; HFun; HBool; htypeof; hdb; hequation; HEqual;
              hcodomain; HTYPE_SUBST_NIL] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN
  REWRITE_TAC(decs @ [option_INJ; LENGTH; MEM; MAP]) THEN CONV_TAC NUM_REDUCE_CONV;;

(* One step: the clause instantiated at the state and the step's values. *)
let ctl_step k st extra =
  let cl = el k (CONJUNCTS nat_step_RULES) in
  let th = SPECL (st @ extra) cl in
  let ant = lhand(concl th) in
  let s' = rand(rand(concl th)) in
  let rd = REWRITE_CONV[APPEND] THENC FIBRE_EVAL_CONV in
  let st' = strip_tuple(rand(concl(rd s'))) in
  let nms' = el 1 st' and tys' = el 2 st' and ntms' = el 3 st' and dbs' = el 4 st' in
  let decs = ref [] in
  let add f = (try decs := f() :: !decs with Failure _ -> ()) in
  for i = 0 to length(dest_list tys') - 1 do
    add (fun () -> fdty_thm nms' tys' i); add (fun () -> fdtys_thm nms' tys' i) done;
  for i = 0 to length(dest_list dbs') - 1 do
    add (fun () -> fddb_thm nms' tys' dbs' i); add (fun () -> fddbs_thm nms' tys' dbs' i) done;
  for i = 0 to length(dest_list ntms') - 1 do
    add (fun () -> fdtm_thm nms' tys' ntms' i) done;
  let olds = el 1 st and oldt = el 2 st and oldn = el 3 st and oldd = el 4 st in
  for i = 0 to length(dest_list oldt) - 1 do
    add (fun () -> fdty_thm olds oldt i); add (fun () -> fdtys_thm olds oldt i) done;
  for i = 0 to length(dest_list oldd) - 1 do
    add (fun () -> fddb_thm olds oldt oldd i); add (fun () -> fddbs_thm olds oldt oldd i) done;
  for i = 0 to length(dest_list oldn) - 1 do
    add (fun () -> fdtm_thm olds oldt oldn i) done;
  let iffs = nat_row_iffs nms' tys' dbs' in
  let ath = prove(ant, CONV_TAC(ONCE_DEPTH_CONV (NAT_NEW_CONV iffs)) THEN
                       NAT_CTL_TAC (!decs)) in
  let sth = CONV_RULE (RAND_CONV rd) (MP th ath) in
  sth, strip_tuple(rand(concl sth));;

let TC_PATH_CONS_STEP = prove
 (`!(step:S->E->S->bool) e es s u t.
      step s e u /\ tc_path step es u t ==> tc_path step (CONS e es) s t`,
  REWRITE_TAC[tc_path] THEN MESON_TAC[]);;

let ctl_nil3 = `[]:(num#num#num)list`;;

let ctl_path =
  let plan =
   [0, [`[61]`; `[]:string list`; `2`];
    0, [`[65]`; `[]:string list`; `3`];
    1, [`1`; ctl_nil3; ctl_nil3; `2`];
    0, [`[98;111;111;108]`; `[]:string list`; `0`];
    0, [`[102;117;110]`; `[]:string list`; `1`];
    2, [`2`; `[]:num list`; `[]:holtype list`; ctl_nil3; ctl_nil3; `1`];
    2, [`3`; `[0;1]`; mk_list([ctl_A; ctl_bool],`:holtype`); ctl_nil3; ctl_nil3; `5`];
    2, [`3`; `[0;2]`; mk_list([ctl_A; ctl_AB],`:holtype`); ctl_nil3; ctl_nil3; `8`];
    0, [`[120]`; `["x"]`; `4`];
    3, [`4`; `0`; ctl_A; ctl_nil3; `[0,4,2]:(num#num#num)list`; `1`];
    4, [`0`; `3`; ctl_AAB; `HFun (TyVar "A") (HFun (TyVar "A") HBool)`;
        `[]:(holtype#holtype)list`; ctl_nil3; `[2,2,8]:(num#num#num)list`; `2`];
    5, [`1`; `0`; ctl_eq; ctl_x; ctl_AB; ctl_nil3; `[3,2,1]:(num#num#num)list`; `5`; `3`];
    5, [`2`; `0`; ctl_eqx; ctl_x; ctl_bool; ctl_nil3; `[3,3,1]:(num#num#num)list`; `1`; `4`];
    7, [`0`; ctl_x; ctl_nil3; ctl_nil3; `0`; `4`];
    8, [`0`; `0`; `[]:hdbterm list`; `[]:hdbterm list`; ctl_AAB; ctl_AAB; ctl_dbx; ctl_dbx;
        ctl_dbx; ctl_nil3; ctl_nil3; `0`; `4`; `[]:hdbterm list`];
    17, [`1`; `[]:num list`; `3`; `[]:hdbterm list`; ctl_xx; `[]:holterm list`]] in
  let rec run st = function
      [] -> ISPECL [`nat_step`; end_itlist (curry mk_pair) st] (prove
              (`!(step:S->E->S->bool) s. tc_path step [] s s`, REWRITE_TAC[tc_path]))
    | (k,extra)::rest ->
        let sth,st' = ctl_step k st extra in
        let pth = run st' rest in
        MATCH_MP (ISPEC `nat_step` TC_PATH_CONS_STEP) (CONJ sth pth) in
  run ctl_state plan;;

let NAT_CONTROL_RUN = prove
 (`!pol. ?ns. tc_path nat_step ctl_recs
                (hinit_ctxt,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],pol) ns`,
  GEN_TAC THEN REWRITE_TAC[ctl_recs; nat_boot_nms; nat_boot_tys; nat_boot_dbs] THEN
  EXISTS_TAC (rand(concl ctl_path)) THEN ACCEPT_TAC ctl_path);;

(* The control stream is accepted in HOLR's meaning, through the native run, *)
(* under every host floor and header policy.                                 *)
let NAT_CONTROL_ACCEPTS = prove
 (`!hpol pol. pol <= 2 ==> holr_accepts hpol (holr_stream pol 0 ctl_recs)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `MAX hpol pol` NAT_CONTROL_RUN) THEN DISCH_THEN(X_CHOOSE_TAC `ns:nstate`) THEN
  MATCH_MP_TAC NAT_ACCEPTS_BOOT THEN
  MAP_EVERY EXISTS_TAC [`pol:num`; `ctl_recs`; `ns:nstate`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Negative controls at the native level. No native run from the bootstrap  *)
(* carries the streams the meaning refuses (HOLR_NEG_CONST_AXIOM and       *)
(* HOLR_NEG_VAR_AXIOM): such a run would make them accepted.               *)
(* ------------------------------------------------------------------------- *)

let NAT_NEG_CONST_AXIOM = prove
 (`!hpol ns. ~tc_path nat_step holr_neg_const_axiom
                 (hinit_ctxt,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],MAX hpol 1) ns`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `hpol:num` HOLR_NEG_CONST_AXIOM) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC NAT_ACCEPTS_BOOT THEN
  MAP_EVERY EXISTS_TAC [`1`; `holr_neg_const_axiom`; `ns:nstate`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let NAT_NEG_VAR_AXIOM = prove
 (`!hpol ns. ~tc_path nat_step holr_neg_var_axiom
                 (hinit_ctxt,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],MAX hpol 1) ns`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `hpol:num` HOLR_NEG_VAR_AXIOM) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC NAT_ACCEPTS_BOOT THEN
  MAP_EVERY EXISTS_TAC [`1`; `holr_neg_var_axiom`; `ns:nstate`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Statement binding, natively. The checker compares each EMIT's theorem   *)
(* row with the host's expected sequent by de Bruijn image: the row's       *)
(* conclusion is the image of the expected conclusion, and each of the     *)
(* row's hypotheses is the image of an expected hypothesis. With the        *)
(* expected sequents well formed in the final context, and every name the   *)
(* specification mentions standard there or declared as the specification  *)
(* declares it, the stream is accepted against the host's specification     *)
(* (holr_accepts_spec), so every expected sequent is derivable and its     *)
(* names mean what the specification says (HOLR_ACCEPTS_SPEC).             *)
(* ------------------------------------------------------------------------- *)

let nat_matches = new_definition
 `nat_matches nms tys dbs (th:num#num) ((hyps,c):holterm list#holterm) <=>
    ?hs. fddbs nms tys dbs (FST th) hs /\ fddb nms tys dbs (SND th) (hdb c) /\
         (!x. MEM x hs ==> ?y. MEM y hyps /\ x = hdb y)`;;

let NAT_MATCHES_ENTAILS = prove
 (`!ctx nms tys dbs th hy tm hyps c.
      fibre_thm_wit ctx nms tys dbs th (hy,tm) /\ nat_matches nms tys dbs th (hyps,c) /\
      holr_spec_ok ctx (hyps,c)
      ==> holr_entails (hy,tm) (hyps,c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fibre_thm_wit; nat_matches; holr_spec_ok; holr_entails] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `hs0:hdbterm list` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `hs:hdbterm list` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `hs0:hdbterm list = hs /\ hdb tm = hdb c` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FDDB_FUNCTIONAL]; ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FIBRE_PROVES_WELLTYPED) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[HACONV_DB; HTERM_OK_WELLTYPED]; ALL_TAC] THEN
  X_GEN_TAC `x:holterm` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?y. MEM y hyps /\ hdb x = hdb y` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `y:holterm` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[HACONV_DB; HTERM_OK_WELLTYPED]);;

let NAT_ACCEPTS_SPEC = prove
 (`!hpol decls axs spec bytes pol recs nms0 tys0 dbs0 ctx nms tys ntms dbs ths nmap ymap drops pol'.
      bytes = holr_stream pol 0 recs /\ pol <= 2 /\
      (!i. i < LENGTH tys0 ==> fibre_ty_ok hinit_ctxt nms0 tys0 i) /\
      nat_canon nms0 tys0 dbs0 /\
      tc_path nat_step recs (hinit_ctxt,nms0,tys0,[],dbs0,[],[],[],[],MAX hpol pol)
              (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol') /\
      ALL2 (\h sp. nat_matches nms tys dbs (EL h ths) sp) (holr_emits recs) spec /\
      ALL (holr_spec_ok ctx) spec /\ holr_spec_pinned decls spec ctx /\
      holr_axioms_allowed decls axs ctx
      ==> holr_accepts_spec hpol decls axs spec bytes`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`nms0:string list`; `tys0:(num#num#num)list`; `dbs0:(num#num#num)list`;
                `MAX hpol pol`] NAT_BOOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`recs:holr_record list`;
                `(hinit_ctxt,nms0,tys0,[],dbs0,[],[],[],[],MAX hpol pol):nstate`;
                `(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol'):nstate`;
                `(hinit_ctxt,[],[],[],[],[],MAX hpol pol):hrstate`] NAT_RUN_SIM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hr':hrstate` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  REWRITE_TAC[holr_accepts_spec] THEN
  MAP_EVERY EXISTS_TAC [`pol:num`; `recs:holr_record list`; `hr':hrstate`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o MATCH_MP HOLR_RUN_DELIVERS) THEN
  UNDISCH_TAC `nat_sim (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol') hr'` THEN
  SPEC_TAC(`hr':hrstate`,`hr':hrstate`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`hctx:hupdate list`; `hnms:string list`; `htys:holtype list`;
                       `htms:holterm list`; `hths:(holterm list#holterm)list`;
                       `hdrops:(num#num)list`; `hp:num`] THEN
  REWRITE_TAC[nat_sim; hr_ctx; hr_ths; holr_delivered] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `ALL (\h. h < LENGTH (ths:(num#num)list)) (holr_emits recs)` MP_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; MEM_HOLR_EMITS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `ALL2 (\h sp. nat_matches nms tys dbs (EL h ths) sp) (holr_emits recs) spec` THEN
  UNDISCH_TAC `ALL (holr_spec_ok ctx) spec` THEN
  SPEC_TAC(`spec:(holterm list#holterm)list`,`sp:(holterm list#holterm)list`) THEN
  SPEC_TAC(`holr_emits recs`,`es:num list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; ALL2; MAP] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `fibre_thm_wit ctx nms tys dbs (EL h ths) (EL h (hths:(holterm list#holterm)list))`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `nat_matches nms tys dbs (EL h ths) h'` THEN
  UNDISCH_TAC `holr_spec_ok ctx h'` THEN
  SPEC_TAC(`h':holterm list#holterm`,`q:holterm list#holterm`) THEN
  SPEC_TAC(`EL h (hths:(holterm list#holterm)list)`,`w:holterm list#holterm`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[NAT_MATCHES_ENTAILS]);;
