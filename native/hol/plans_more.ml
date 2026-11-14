(* ========================================================================= *)
(* Plans for further records, beyond the six of plans_abs.ml, on the same   *)
(* abstract plan machine (pl_run) and in the same form: a guards lemma, a   *)
(* FIRED lemma, and the plan's theorem (its FIRED run is the record's       *)
(* nat_step and keeps pl_inv; it is REFUSED exactly when the guard fails).  *)
(* Loaded after plans_abs.ml.                                                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* EMIT h (OP0 = h): theorem h live [REFUSED otherwise]. No row is written; *)
(* the native state is unchanged (the delivered theorems are read from the  *)
(* record stream, holr_emits).                                               *)
(* ------------------------------------------------------------------------- *)

pl_begin();;
let _ = pl_live_th pl_OP0;;
let pl_plan_emit = new_definition(mk_eq(`pl_plan_emit:(int64 list)list`, pl_plan()));;

let PL_EMIT_GUARDS = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
     ==> (nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REmit h) <=>
          holr_live 3 h (LENGTH ths) drops)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND]);;

let nat_emit_rule =
  find (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "REmit")) (concl th))
       (CONJUNCTS nat_step_RULES);;

let pl_emit_fired_goal = `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h cw'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     holr_live 3 h (LENGTH ths) drops /\ (!n. n <= 6 ==> cw' n = cw n)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REmit h)
                  (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
         pl_inv (cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`;;

let PL_EMIT_FIRED = prove(pl_emit_fired_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC nat_emit_rule THEN REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND] THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[pl_inv] o check (is_pl_inv o concl)) THEN
    REWRITE_TAC[pl_inv] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let pl_emit_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = h /\
     pl_run pl_plan_emit 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) (k,i,(cw',ns',stk'))
     ==> (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REmit h) ns' /\
                    pl_inv (cw',ns',stk')) /\
         (k = 0 <=> ~nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REmit h))`;;

(* PL_EMIT: the plan's FIRED run is EMIT's nat_step and keeps pl_inv; it is *)
(* REFUSED exactly when h is not a live theorem.                            *)
let PL_EMIT = prove(pl_emit_goal,
  PL_START_TAC pl_plan_emit THEN
  PL_INV_ASM(fun th -> REWRITE_TAC[MATCH_MP PL_EMIT_GUARDS th]) THEN REWRITE_TAC[ARITH_EQ] THEN
  ASM_REWRITE_TAC[] THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN PL_FIRED_TAC PL_EMIT_FIRED);;
