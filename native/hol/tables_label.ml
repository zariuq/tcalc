(* ========================================================================= *)
(* LABEL h n: the plan (PLANS.txt, section 6: live h among the theorems,    *)
(* live n among the N ids; nothing written), its analysis over HOL's tables *)
(* (PL_LABEL: FIRED = LABEL's nat_step + pl_inv; REFUSED exactly when h is *)
(* not a live theorem or n not an N id), and through the driver over HOL's  *)
(* full layout (PL_LABEL_TAB).                                               *)
(*                                                                           *)
(* Loaded after tables_comb.ml.                                              *)
(* ========================================================================= *)

pl_begin();;
let _ = let _ = pl_live_th pl_OP0 in pl_emit pl_LIVE pl_NLIVE pl_OP1 0 [];;
let pl_plan_label = new_definition(mk_eq(`pl_plan_label:(int64 list)list`, pl_plan()));;

let NAT_STEP_LABEL =
  find (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "RLabel")) (concl th))
       (CONJUNCTS nat_step_RULES);;

let PL_LABEL_FIRED = prove
 (`!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h n cw'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     holr_live 3 h (LENGTH ths) drops /\ n < LENGTH nmap /\ (!m. m <= 6 ==> cw' m = cw m)
     ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RLabel h n)
                  (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) /\
         pl_inv (cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC NAT_STEP_LABEL THEN REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND] THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[pl_inv] o check (is_pl_inv o concl)) THEN
    REWRITE_TAC[pl_inv] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let pl_label_goal =
 `!cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp h n k i cw' ns' stk'.
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ (!j. ~MEM (0,j) drops) /\
     cw 8 = h /\ cw 9 = n /\
     tab_run hol_tables inp pl_plan_label 0 (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
             (k,i,(cw',ns',stk'))
     ==> (k = 1 ==> nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RLabel h n) ns' /\
                    pl_inv (cw',ns',stk')) /\
         (k = 0 <=> ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RLabel h n) /\
                      n < LENGTH nmap))`;;

(* PL_LABEL: the plan's FIRED run is LABEL's nat_step and keeps pl_inv; it   *)
(* is REFUSED exactly when h is not a live theorem or n not an N id.        *)
let PL_LABEL = prove(pl_label_goal,
  REWRITE_TAC[nat_ops_live; holr_operands; ALL; FST; SND; holr_live] THEN
  TAB_START_TAC pl_plan_label THEN
  MATCH_MP_TAC(REWRITE_RULE[holr_live] PL_LABEL_FIRED) THEN PL_WITNESS_TAC THEN
  ASM_REWRITE_TAC[] THEN PL_SET_LOW_TAC);;

let TAB_IMPL_LABEL = prove(tab_plan_impl_goal `pl_plan_label`, TAB_PLAN_IMPL_TAC2 pl_plan_label);;
let TAB_SAFE_LABEL = prove(tab_safe_goal `pl_plan_label`, TAB_SAFE_PLAN_TAC pl_plan_label);;
let PL_LABEL_TAB = tab_drv_lift PL_LABEL `pl_plan_label` TAB_IMPL_LABEL TAB_SAFE_LABEL;;

(* Every theorem this file states, for the audits. *)
let tables_label_theorems =
 ["PL_LABEL_FIRED", PL_LABEL_FIRED; "PL_LABEL", PL_LABEL; "TAB_IMPL_LABEL", TAB_IMPL_LABEL;
  "TAB_SAFE_LABEL", TAB_SAFE_LABEL; "PL_LABEL_TAB", PL_LABEL_TAB];;
