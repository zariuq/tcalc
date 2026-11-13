(* ========================================================================= *)
(* From the native fibre's rows to what a stream claims.                     *)
(*                                                                           *)
(* FIBRE_EXPECT_ALPHA: when a theorem row's conclusion is the de Bruijn     *)
(* image of a claim's conclusion, and its hypotheses are, as a set, the     *)
(* images of the claim's hypotheses, the claim is derivable. The claim's    *)
(* terms must be ok in the signature and its hypotheses boolean: the fibre  *)
(* records that a row's hypotheses include the images of its derivation's  *)
(* hypotheses, not that every listed hypothesis is boolean, so the checker  *)
(* tests the claim's hypothesis types (one comparison each). The test never *)
(* refuses a claim HOL Light accepts: an alpha-equivalent of a boolean      *)
(* hypothesis is boolean.                                                    *)
(* ========================================================================= *)

let FIBRE_EXPECT_ALPHA = prove
 (`!ctx nms tys dbs h c hs C hyps concl.
      fibre_thm_ok ctx nms tys dbs (h,c) /\
      fddbs nms tys dbs h hs /\ fddb nms tys dbs c C /\
      ALL (\p. hterm_ok (hsigof ctx) p /\ p hhas_type HBool) hyps /\
      hterm_ok (hsigof ctx) concl /\ hdb concl = C /\
      (!x. MEM x hs ==> ?p. MEM p hyps /\ hdb p = x)
      ==> hproves (hthyof ctx) hyps concl`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `dbs:(num#num#num)list`; `h:num`; `c:num`; `hs:hdbterm list`;
                `C:hdbterm`] FIBRE_THM_GET) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h0:holterm list`; `t0:holterm`] THEN STRIP_TAC THEN
  MATCH_MP_TAC HPROVES_ACONV THEN
  MAP_EVERY EXISTS_TAC [`h0:holterm list`; `t0:holterm`] THEN
  ASM_REWRITE_TAC[hthyof; FST] THEN
  SUBGOAL_THEN `hwelltyped t0 /\ (!x. MEM x h0 ==> hwelltyped x)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FIBRE_PROVES_WELLTYPED]; ALL_TAC] THEN
  SUBGOAL_THEN `hwelltyped concl` ASSUME_TAC THENL
   [ASM_MESON_TAC[HTERM_OK_WELLTYPED]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:holterm` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?p. MEM p hyps /\ hdb p = hdb x` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:holterm` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `hwelltyped p` ASSUME_TAC THENL
     [UNDISCH_TAC `ALL (\p. hterm_ok (hsigof ctx) p /\ p hhas_type HBool) hyps` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[HTERM_OK_WELLTYPED];
      ALL_TAC] THEN
    ASM_MESON_TAC[HACONV_DB];
    ASM_MESON_TAC[HACONV_DB];
    FIRST_ASSUM ACCEPT_TAC]);;
