(* ========================================================================= *)
(* The native checker's record steps as an instance of the transform step.  *)
(*                                                                           *)
(* An event is a record with its effect: what the record's handler leaves  *)
(* in the native state. The rows it appends (names, type rows, named rows,  *)
(* de Bruijn rows, theorem rows, N and Y entries) are the effect's lists;  *)
(* the context, drops and policy after the step are given whole.           *)
(* Admission (the preparation) is the record's guards: the record's clause *)
(* of nat_step holds from the state to the state the effect makes. It is a *)
(* premise on decoded rows and does not mention the invariant; that the    *)
(* invariant is kept is a theorem (NAT_STEP_SIM). Permission is a          *)
(* parameter, as in every transform step.                                   *)
(*                                                                           *)
(* NAT_INST_STEP: the instance's steps are the native steps, each with its *)
(* effect, under the permission; NAT_STEP_EFFECT: every native step has an *)
(* effect, so no native step is left out.                                   *)
(* NAT_PREP_NEW_AXIOM: admitting NEW_AXIOM requires the policy's guard.     *)
(* NAT_INST_PATH_INVARIANT: along every path of admitted events, the native *)
(* invariant holds and the native state decodes to a HOLR state            *)
(* (TC_PATH_INVARIANT with NAT_STEP_SIM).                                   *)
(* NAT_INST_PATH_HOLR: the records of such a path run in HOLR's meaning,   *)
(* from the decoding of its first state to a decoding of its last.          *)
(* NAT_INST_PATH_SOUND: from a canonical bootstrap state, every theorem row *)
(* reached is derivable in a context that extends HOL's initial context,   *)
(* and the rows are canonical.                                               *)
(*                                                                           *)
(* Loaded after holr_native.ml.                                             *)
(* ========================================================================= *)

let nat_result = new_definition
 `nat_result ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) (r:holr_record)
             ((ctx',mn,mt,nt,md,mh,nm,ym,drops',pol'):nstate) =
    (ctx',APPEND nms mn,APPEND tys mt,APPEND ntms nt,APPEND dbs md,APPEND ths mh,
     APPEND nmap nm,APPEND ymap ym,drops',pol'):nstate`;;

let nat_prep = new_definition
 `nat_prep (s:nstate) (r:holr_record) (e:nstate) <=> nat_step s r (nat_result s r e)`;;

let nat_inst_step = new_definition
 `nat_inst_step (allow:nstate->holr_record->nstate->bool) (s:nstate)
                ((r,e):holr_record#nstate) (t:nstate) <=>
    tc_admitted_event nat_prep nat_result allow s r e t`;;

let NAT_INST_STEP = prove
 (`!allow s r e t. nat_inst_step allow s (r,e) t <=>
                   nat_step s r t /\ t = nat_result s r e /\ allow s r e`,
  REWRITE_TAC[nat_inst_step; tc_admitted_event; tc_prepared_event; nat_prep] THEN
  MESON_TAC[]);;

let NAT_STEP_EFFECT = prove
 (`!s r t. nat_step s r t ==> ?e. t = nat_result s r e`,
  MATCH_MP_TAC nat_step_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[EXISTS_PAIR_THM; nat_result; PAIR_EQ] THEN
  MESON_TAC[APPEND_NIL; APPEND]);;

(* Every native step is an admitted event of the instance whenever the      *)
(* permission allows its effect.                                            *)
let NAT_STEP_INST = prove
 (`!allow s r t. nat_step s r t /\ (!e. allow s r e)
                 ==> ?e. nat_inst_step allow s (r,e) t`,
  REWRITE_TAC[NAT_INST_STEP] THEN MESON_TAC[NAT_STEP_EFFECT]);;

(* Admission is the record's guards: for NEW_AXIOM, the policy's.           *)
let NAT_PREP_NEW_AXIOM = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol t e.
      nat_prep (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RNewAxiom t) e
      ==> ?p. fdtm nms tys ntms t p /\ htypeof p = HBool /\ holr_axiom_ok pol ctx p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nat_prep] THEN
  ONCE_REWRITE_TAC[nat_step_CASES] THEN
  REWRITE_TAC[HOLR_RECORD_DISTINCT; HOLR_RECORD_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

(* The invariant of the instance: the native invariant, and a HOLR state    *)
(* the native state decodes to.                                             *)
let nat_inst_inv = new_definition
 `nat_inst_inv (s:nstate) <=> nat_ok s /\ ?hr. nat_sim s hr`;;

let NAT_INST_STEP_INV = prove
 (`!allow s ev t. nat_inst_step allow s ev t /\ nat_inst_inv s ==> nat_inst_inv t`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; NAT_INST_STEP; nat_inst_inv] THEN
  MESON_TAC[NAT_STEP_SIM]);;

let NAT_INST_PATH_INVARIANT = prove
 (`!allow events s t.
      tc_path (nat_inst_step allow) events s t /\ nat_inst_inv s ==> nat_inst_inv t`,
  GEN_TAC THEN MATCH_MP_TAC TC_PATH_INVARIANT THEN MESON_TAC[NAT_INST_STEP_INV]);;

let NAT_INST_PATH_NATIVE = prove
 (`!allow events s t.
      tc_path (nat_inst_step allow) events s t ==> tc_path nat_step (MAP FST events) s t`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[tc_path; MAP] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  SPEC_TAC(`h:holr_record#nstate`,`ev:holr_record#nstate`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; NAT_INST_STEP] THEN ASM_MESON_TAC[]);;

let NAT_INST_PATH_HOLR = prove
 (`!allow events s t hr.
      tc_path (nat_inst_step allow) events s t /\ nat_ok s /\ nat_sim s hr
      ==> nat_ok t /\ ?hr'. tc_path holr_step (MAP FST events) hr hr' /\ nat_sim t hr'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC NAT_RUN_SIM THEN
  EXISTS_TAC `s:nstate` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[NAT_INST_PATH_NATIVE]);;

let NAT_INST_PATH_SOUND = prove
 (`!allow events nms0 tys0 dbs0 pol ctx nms tys ntms dbs ths nmap ymap drops pol' th.
      (!i. i < LENGTH tys0 ==> fibre_ty_ok hinit_ctxt nms0 tys0 i) /\
      nat_canon nms0 tys0 dbs0 /\
      tc_path (nat_inst_step allow) events (hinit_ctxt,nms0,tys0,[],dbs0,[],[],[],[],pol)
              (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol') /\
      MEM th ths
      ==> ctx hextends hinit_ctxt /\ htheory_ok (hthyof ctx) /\
          fibre_thm_ok ctx nms tys dbs th /\ nat_canon nms tys dbs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`nms0:string list`; `tys0:(num#num#num)list`; `dbs0:(num#num#num)list`;
                `pol:num`] NAT_BOOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `nat_inst_inv (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol')` MP_TAC THENL
   [MATCH_MP_TAC NAT_INST_PATH_INVARIANT THEN
    MAP_EVERY EXISTS_TAC [`allow:nstate->holr_record->nstate->bool`;
                          `events:(holr_record#nstate)list`;
                          `(hinit_ctxt,nms0,tys0,[],dbs0,[],[],[],[],pol):nstate`] THEN
    ASM_REWRITE_TAC[nat_inst_inv] THEN ASM_MESON_TAC[];
    REWRITE_TAC[nat_inst_inv; nat_ok; nat_rows_ok; fibre_inv; GSYM ALL_MEM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[HEXTENDS_THEORY_OK; HINIT_THEORY_OK]]);;
