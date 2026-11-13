(* ========================================================================= *)
(* The native HOL fibre as an instance of the transform step.                *)
(*                                                                           *)
(* A state is a context and five row regions. An event's occurrence is what *)
(* the step appends: the new context (an extension) and the new rows. Its   *)
(* preparation is the fibre's admission: the context extends the old one,   *)
(* and every appended row satisfies its region's predicate in the new       *)
(* state. Permission is a parameter (the axiom policy is one).              *)
(*                                                                           *)
(* FIBRE_PATH_INVARIANT: along every path of admitted events, from the       *)
(* initial state, every row of every region satisfies its predicate. In     *)
(* particular every theorem row is derivable in the context's theory.       *)
(* Each record's lemma in holfibre.ml shows that the rows its handler       *)
(* appends satisfy the preparation.                                          *)
(*                                                                           *)
(* Loaded by holfibre_all.ml, after the transform development, the port of *)
(* HOL's logic and holfibre.ml.                                              *)
(* ========================================================================= *)

new_type_abbrev("fstate",
  `:hupdate list # string list # (num#num#num)list # (num#num#num#num#num)list #
    (num#num#num)list # (num#num)list`);;

let fibre_inv = new_definition
 `fibre_inv ((ctx,nms,tys,ntms,dbs,ths):fstate) <=>
    ctx hextends hinit_ctxt /\
    (!i. i < LENGTH tys ==> fibre_ty_ok ctx nms tys i) /\
    (!i. i < LENGTH ntms ==> fibre_tm_ok ctx nms tys dbs ntms i) /\
    ALL (fibre_thm_ok ctx nms tys dbs) ths`;;

let fibre_result = new_definition
 `fibre_result ((ctx,nms,tys,ntms,dbs,ths):fstate) (f:num)
               ((ctx',nm,ty,nt,db,th):fstate) =
    (ctx',APPEND nms nm,APPEND tys ty,APPEND ntms nt,APPEND dbs db,APPEND ths th):fstate`;;

let fibre_prep = new_definition
 `fibre_prep ((ctx,nms,tys,ntms,dbs,ths):fstate) (f:num)
             ((ctx',nm,ty,nt,db,th):fstate) <=>
    ctx' hextends ctx /\
    (!i. LENGTH tys <= i /\ i < LENGTH tys + LENGTH ty
         ==> fibre_ty_ok ctx' (APPEND nms nm) (APPEND tys ty) i) /\
    (!i. LENGTH ntms <= i /\ i < LENGTH ntms + LENGTH nt
         ==> fibre_tm_ok ctx' (APPEND nms nm) (APPEND tys ty) (APPEND dbs db)
                         (APPEND ntms nt) i) /\
    ALL (fibre_thm_ok ctx' (APPEND nms nm) (APPEND tys ty) (APPEND dbs db)) th`;;

let fibre_step = new_definition
 `fibre_step allow (s:fstate) ((f,p):num#fstate) (t:fstate) <=>
    tc_admitted_event fibre_prep fibre_result allow s f p t`;;

let FIBRE_INIT_INV = prove
 (`fibre_inv (hinit_ctxt,nms,[],[],dbs,[])`,
  REWRITE_TAC[fibre_inv; LENGTH; LT; ALL] THEN MESON_TAC[hextends_RULES]);;

let FIBRE_STEP_INVARIANT = prove
 (`!allow s e t. fibre_step allow s e t /\ fibre_inv s ==> fibre_inv t`,
  GEN_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; fibre_step; tc_admitted_event; tc_prepared_event] THEN
  MAP_EVERY X_GEN_TAC
   [`ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
    `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
    `f:num`; `ctx':hupdate list`; `nm:string list`; `ty:(num#num#num)list`;
    `nt:(num#num#num#num#num)list`; `db:(num#num#num)list`; `th:(num#num)list`;
    `ctx2:hupdate list`; `nms2:string list`; `tys2:(num#num#num)list`;
    `ntms2:(num#num#num#num#num)list`; `dbs2:(num#num#num)list`; `ths2:(num#num)list`] THEN
  REWRITE_TAC[fibre_prep; fibre_result; fibre_inv; PAIR_EQ] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HEXTENDS_TRANS];
    REWRITE_TAC[LENGTH_APPEND] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i < LENGTH (tys:(num#num#num)list)` THENL
     [ASM_MESON_TAC[FIBRE_CTX_EXTEND; FIBRE_TY_OK_EXTEND];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    REWRITE_TAC[LENGTH_APPEND] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i < LENGTH (ntms:(num#num#num#num#num)list)` THENL
     [ASM_MESON_TAC[FIBRE_CTX_EXTEND; FIBRE_TM_OK_EXTEND];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    REWRITE_TAC[ALL_APPEND] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ALL_IMP THEN
    EXISTS_TAC `fibre_thm_ok ctx nms tys dbs` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FIBRE_CTX_EXTEND; FIBRE_THM_OK_EXTEND]]);;

let FIBRE_PATH_INVARIANT = prove
 (`!allow events s t.
      tc_path (fibre_step allow) events s t /\ fibre_inv s ==> fibre_inv t`,
  GEN_TAC THEN MATCH_MP_TAC TC_PATH_INVARIANT THEN
  MESON_TAC[FIBRE_STEP_INVARIANT]);;

(* What it gives: every theorem row reached from the initial state is       *)
(* derivable in its context's theory, which extends the initial theory.     *)
let FIBRE_PATH_SOUND = prove
 (`!allow events nms0 dbs0 ctx nms tys ntms dbs ths th.
      tc_path (fibre_step allow) events (hinit_ctxt,nms0,[],[],dbs0,[])
              (ctx,nms,tys,ntms,dbs,ths) /\ MEM th ths
      ==> ctx hextends hinit_ctxt /\ htheory_ok (hthyof ctx) /\
          fibre_thm_ok ctx nms tys dbs th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `fibre_inv (ctx,nms,tys,ntms,dbs,ths)` MP_TAC THENL
   [MATCH_MP_TAC FIBRE_PATH_INVARIANT THEN
    MAP_EVERY EXISTS_TAC [`allow:fstate->num->fstate->bool`; `events:(num#fstate)list`;
                          `(hinit_ctxt,nms0,[],[],dbs0,[]):fstate`] THEN
    ASM_REWRITE_TAC[FIBRE_INIT_INV];
    REWRITE_TAC[fibre_inv; GSYM ALL_MEM] THEN
    ASM_MESON_TAC[HEXTENDS_THEORY_OK; HINIT_THEORY_OK]]);;
