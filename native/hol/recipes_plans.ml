(* ========================================================================= *)
(* The record plans that take a union, with the union as a call to recipe 1: *)
(* the same steps as plans_abs.ml's plans, the union leaf replaced by the    *)
(* call. Each theorem is the plan theorem of plans_abs.ml with pl_run        *)
(* replaced by rc_exec over a table P whose recipe 1 is rc_union.            *)
(* ========================================================================= *)

let rc_call_c r args =
  let res = !pl_next in pl_next := res + 1; pl_buf := !pl_buf @ [rc_callstep r args res]; res;;
let rc_union_c a b = rc_call_c rc_UNION [a; b];;

pl_begin();;
let _ = let _ = pl_live_th pl_OP0 in let _ = pl_live_th pl_OP1 in
        let c = pl_f_th pl_OP0 1 in let (_,p,q,_) = pl_eqparts c in
        let c2 = pl_f_th pl_OP1 1 in let _ = pl_eqw_c p c2 in
        let h1 = pl_f_th pl_OP0 0 in let h2 = pl_f_th pl_OP1 0 in
        let hk = rc_union_c h1 h2 in pl_append_c hk q;;
let rc_plan_eqmp = new_definition(mk_eq(`rc_plan_eqmp:(int64 list)list`, pl_plan()));;

pl_begin();;
let _ = let _ = pl_live_th pl_OP0 in let _ = pl_live_th pl_OP1 in
        let c1 = pl_f_th pl_OP0 1 in let (e1,_,m1,_) = pl_eqparts c1 in
        let c2 = pl_f_th pl_OP1 1 in let (_,m2,r,_) = pl_eqparts c2 in
        let _ = pl_eqw_c m1 m2 in let k = pl_idb 3 e1 r in
        let h1 = pl_f_th pl_OP0 0 in let h2 = pl_f_th pl_OP1 0 in
        let hk = rc_union_c h1 h2 in pl_append_c hk k;;
let rc_plan_trans = new_definition(mk_eq(`rc_plan_trans:(int64 list)list`, pl_plan()));;

pl_begin();;
let _ = let _ = pl_live_th pl_OP0 in let _ = pl_live_th pl_OP1 in
        let c1 = pl_f_th pl_OP0 1 in let (_,f,g,t1) = pl_eqparts c1 in
        let c2 = pl_f_th pl_OP1 1 in let (_,a,b,t2) = pl_eqparts c2 in
        let (fy,r1) = pl_funargs t1 in let (fy',b1) = pl_funargs r1 in
        let _ = pl_eqw_c fy' fy in let _ = pl_eqw_c b1 1 in
        let (tx,ty) = pl_funargs fy in
        let (tx2,r2) = pl_funargs t2 in let _ = pl_eqw_c tx2 tx in
        let (tx3,b2) = pl_funargs r2 in let _ = pl_eqw_c tx3 tx in let _ = pl_eqw_c b2 1 in
        let fa = pl_idb 3 f a in let gb = pl_idb 3 g b in
        let k = pl_eqbuild ty fa gb in
        let h1 = pl_f_th pl_OP0 0 in let h2 = pl_f_th pl_OP1 0 in
        let hk = rc_union_c h1 h2 in pl_append_c hk k;;
let rc_plan_mkcomb = new_definition(mk_eq(`rc_plan_mkcomb:(int64 list)list`, pl_plan()));;

(* The plan theorem over the recipe machine: pl_run plan becomes rc_exec P  *)
(* plan', with the union recipe at index 1 of P.                            *)
let rc_goal_of plgoal plplan rcplan =
  let vs,body = strip_forall plgoal in
  let P = `P:(((int64 list)list)list)list` in
  let old = mk_comb(`pl_run`, plplan) in
  let nw = mk_comb(mk_comb(`rc_exec`, P), rcplan) in
  let ant,con = dest_imp(subst [nw,old] body) in
  let ant' = mk_conj(`1 < LENGTH (P:(((int64 list)list)list)list) /\ EL 1 P = rc_union`, ant) in
  list_mk_forall(P :: vs, mk_imp(ant', con));;

(* What a union call needs of the invariant. *)
let PL_INV_UNION_PRE = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> nat_keys tys dbs /\ keys_distinct dbs /\ LENGTH dbs < 2 EXP 60 /\
         (!h. h < LENGTH ths ==> ?I. pl_ids dbs (FST(EL h ths)) I /\ PAIRWISE (<) I)`,
  REWRITE_TAC[pl_inv] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

RC_FORWARDS := [PL_INTERNED_LEN; PL_INTERNED_KEYS];;

let RC_PLAN_START_TAC plan =
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(W(fun (_,w) -> if is_imp w && not(is_const_app "rc_exec" (lhand w)) then DISCH_TAC else NO_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PL_K) THEN PL_ROWS_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV o MATCH_MP PL_INV_UNION_PRE) THEN
  REWRITE_TAC[plan] THEN RC_RUN_TAC [RC_UNION_FRAME] [RC_UNION_LEAF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[rc_union_post]);;

let RC_SET_LOW_TAC =
  GEN_TAC THEN DISCH_THEN(fun th -> SIMP_TAC[th; PL_SET_LOW_LEMMA; ARITH]);;
let rc_is_low_goal w =
  is_forall w && (let v,b = dest_forall w in
                  is_imp b && lhand b = mk_binop `(<=):num->num->bool` v `6`);;
(* plans_abs.ml's PL_FIRED_TAC (its last form), the low control words by    *)
(* RC_SET_LOW_TAC.                                                          *)
let RC_FIRED_TAC th =
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ]) THEN
  MATCH_MP_TAC(REWRITE_RULE[pl_eq_rhs; pl_eq_lhs; pl_eq_ty; pl_fun_dom; pl_fun_cod] th) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  PL_WITNESS_TAC THEN ASM_REWRITE_TAC[pl_eq_ok; pl_fun_ok] THEN
  REPEAT CONJ_TAC THEN
  W(fun (_,w) -> if rc_is_low_goal w then RC_SET_LOW_TAC else
                 TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
                 TRY(PL_WITNESS_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC));;

let RC_EQMP = prove(rc_goal_of pl_eqmp_goal `pl_plan_eqmp` `rc_plan_eqmp`,
  RC_PLAN_START_TAC rc_plan_eqmp THEN
  PL_INV_ASM(fun th -> REWRITE_TAC[MATCH_MP PL_EQMP_GUARDS th]) THEN
  REWRITE_TAC[ARITH_EQ; pl_eq_ok; pl_eq_lhs] THEN
  ASM_REWRITE_TAC[] THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN RC_FIRED_TAC PL_EQMP_FIRED);;

let RC_TRANS = prove(rc_goal_of pl_trans_goal `pl_plan_trans` `rc_plan_trans`,
  RC_PLAN_START_TAC rc_plan_trans THEN
  PL_INV_ASM(fun th -> REWRITE_TAC[MATCH_MP PL_TRANS_GUARDS th]) THEN
  REWRITE_TAC[ARITH_EQ; pl_eq_ok; pl_eq_lhs; pl_eq_rhs] THEN
  ASM_REWRITE_TAC[] THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN RC_FIRED_TAC PL_TRANS_FIRED);;

let RC_MKCOMB = prove(rc_goal_of pl_mkcomb_goal `pl_plan_mkcomb` `rc_plan_mkcomb`,
  RC_PLAN_START_TAC rc_plan_mkcomb THEN
  PL_INV_ASM(fun th -> REWRITE_TAC[MATCH_MP PL_MK_GUARDS th]) THEN
  REWRITE_TAC[ARITH_EQ; pl_eq_ok; pl_eq_lhs; pl_eq_rhs; pl_eq_ty; pl_fun_ok; pl_fun_dom; pl_fun_cod] THEN
  ASM_REWRITE_TAC[] THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN RC_FIRED_TAC PL_MKCOMB_FIRED);;
