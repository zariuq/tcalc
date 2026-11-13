(* ========================================================================= *)
(* The fibre's row decoders, verbatim from holfibre.ml (its sections         *)
(* "Decoding types and type lists", "Decoding de Bruijn terms and term       *)
(* lists", and the growth and functionality lemmas of those decoders).       *)
(*                                                                           *)
(* For sessions built on s2n-bignum's x86 base (the t-ISA leaves): there     *)
(* Harrison's Model does not load (Model/modelset.ml fails with              *)
(* Failure "ABS"), so neither do HolInHol's embedding.ml and kernel_ops.ml,  *)
(* which holfibre.ml's theory records use. The decoders need only HolInHol's *)
(* syntax.ml and dbterm.ml. HOL Light takes an inductive definition stated   *)
(* again with the same text as a benign redefinition, so in a session that  *)
(* also loads holfibre.ml, in either order, fdty and fddb are its constants. *)
(* ========================================================================= *)

needs "HolInHol/syntax.ml";;
needs "HolInHol/dbterm.ml";;

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
(* Growth: appending rows preserves every decoding and the predicate.        *)
(* ------------------------------------------------------------------------- *)

let FIBRE_EL_APPEND = prove
 (`!(l:A list) m i. i < LENGTH l
      ==> i < LENGTH (APPEND l m) /\ EL i (APPEND l m) = EL i l`,
  SIMP_TAC[LENGTH_APPEND; EL_APPEND] THEN ARITH_TAC);;

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
