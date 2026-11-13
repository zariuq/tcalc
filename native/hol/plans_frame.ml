(* ========================================================================= *)
(* What a record plan leaves behind when it does not fire.                   *)
(*                                                                           *)
(* The plan theorems of plans_abs.ml (PL_<KIND>) say what a FIRED run does   *)
(* and exactly when a run is REFUSED. They say nothing of the state after a *)
(* run that did not fire. This file adds that, per record kind:             *)
(*                                                                           *)
(*   PL_<KIND>_FRAME: from a state with the invariant,                      *)
(*     - a REFUSED run (outcome 0) leaves the native state as it was;       *)
(*     - a run with any outcome but FIRED leaves the committed components   *)
(*       as they were (pl_frame): the context, the names, the term rows,    *)
(*       the theorem rows, both maps, the drops and the policy are equal,   *)
(*       and the type rows and de Bruijn rows are the old rows followed by  *)
(*       a suffix (rows interned before the run stopped; they carry no      *)
(*       claim: no theorem row and no term row names them);                 *)
(*     - the operand stack is never changed.                                *)
(*   EXPECT_ALPHA writes no row at all: its state is unchanged whatever the *)
(*   outcome.                                                                *)
(*                                                                           *)
(* The control words (the first component of a plan state) are private to   *)
(* the plan: a step writes its payload word whatever its outcome, so they   *)
(* are not part of the frame.                                                *)
(*                                                                           *)
(* These theorems license reading the committed state after a failed        *)
(* record against what was observed before it. They do not license          *)
(* continuing the record loop, which stops at the first outcome that is     *)
(* not FIRED.                                                                *)
(*                                                                           *)
(* Loaded after plans_abs.ml.                                                *)
(* ========================================================================= *)

let pl_frame = new_definition
 `pl_frame ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate)
           ((ctx',nms',tys',ntms',dbs',ths',nmap',ymap',drops',pol'):nstate) <=>
    ctx' = ctx /\ nms' = nms /\ ntms' = ntms /\ ths' = ths /\ nmap' = nmap /\ ymap' = ymap /\
    drops' = drops /\ pol' = pol /\
    (?mt. tys' = APPEND tys mt) /\ (?md. dbs' = APPEND dbs md)`;;

(* A state frames itself. *)
let PL_FRAME_REFL = prove
 (`!ns. pl_frame ns ns`,
  REWRITE_TAC[FORALL_PAIR_THM; pl_frame] THEN MESON_TAC[APPEND_NIL]);;

(* Every branch a symbolic run ends in: the outcome is a numeral, or known   *)
(* only to differ from 0 and 1; the final rows are the old rows with the    *)
(* suffixes the interning steps appended.                                    *)
let PL_FRAME_END_TAC =
  ASM_REWRITE_TAC[ARITH_EQ; pl_frame; PAIR_EQ; GSYM APPEND_ASSOC; APPEND_NIL] THEN
  TRY(MESON_TAC[APPEND_NIL]);;

let pl_frame_goal plan opers =
  let base = `pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)` in
  let run = mk_comb(mk_comb(mk_comb(mk_comb(`pl_run`, plan), `0`),
              `(cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate`),
              `(k,i,(cw',ns',stk')):num#num#pstate`) in
  let concl = `(k = 0 ==> ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) /\
               (~(k = 1) ==> pl_frame (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) ns') /\
               stk' = (stk:num list)` in
  let body = mk_imp(list_mk_conj([base] @ opers @ [run]), concl) in
  list_mk_forall(sort (<) (frees body), body);;

let PL_FRAME_TAC plan = PL_START_TAC plan THEN PL_FRAME_END_TAC;;

let PL_ASSUME_FRAME = prove
 (pl_frame_goal `pl_plan_assume` [`(cw:num->num) 8 = t`],
  PL_FRAME_TAC pl_plan_assume);;

let PL_REFL_FRAME = prove
 (pl_frame_goal `pl_plan_refl` [`(cw:num->num) 8 = t`],
  PL_FRAME_TAC pl_plan_refl);;

let PL_EQMP_FRAME = prove
 (pl_frame_goal `pl_plan_eqmp` [`(cw:num->num) 8 = h1`; `(cw:num->num) 9 = h2`],
  PL_FRAME_TAC pl_plan_eqmp);;

let PL_TRANS_FRAME = prove
 (pl_frame_goal `pl_plan_trans` [`(cw:num->num) 8 = h1`; `(cw:num->num) 9 = h2`],
  PL_FRAME_TAC pl_plan_trans);;

let PL_MKCOMB_FRAME = prove
 (pl_frame_goal `pl_plan_mkcomb` [`(cw:num->num) 8 = h1`; `(cw:num->num) 9 = h2`],
  PL_FRAME_TAC pl_plan_mkcomb);;

(* EXPECT_ALPHA: no row is written, whatever the outcome. The listed terms  *)
(* lie in the operand stack (cw 13 the start, cw 12 the count), as in      *)
(* PL_EXPECT_ALPHA.                                                         *)
let PL_EXPECT_ALPHA_KEEPS = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h c k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     cw 8 = h /\ cw 10 = c /\ cw 13 + cw 12 <= LENGTH stk /\
     pl_run pl_plan_expect_alpha 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
            (k,i,(cw',ns',stk'))
     ==> ns' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\ stk' = stk`,
  PL_START_TAC pl_plan_expect_alpha THEN ASM_REWRITE_TAC[PAIR_EQ]);;
