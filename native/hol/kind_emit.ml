(* ========================================================================= *)
(* EMIT h, compiled: its plan (plans_more.ml) through the driver           *)
(* (PL_EMIT_DRV), its one leaf bridged (PL_LEAF_EMIT_LIVE), the plan under  *)
(* plan_rel (PL_EMIT_REL), its handler (HANDLER_EMIT), its contract         *)
(* (KC_EMIT) and its every-run contract (KE_EMIT). EMIT writes no row: it  *)
(* FIRES exactly when h is a live theorem.                                   *)
(*                                                                           *)
(* Loaded after rec_every.ml.                                                *)
(* ========================================================================= *)

needs "native/hol/plans_more.ml";;
needs "native/hol/rec_every.ml";;

let PL_EMIT_DRV = prove
 (`!prel progs bw ctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h.
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_emit 5 /\
     drv_sem progs bw ctl budget cfr pl_plan_emit 0 m used res /\
     prel m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = h
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REmit h) (FST(SND s')) /\
                    pl_inv s') /\ prel (FST(SND(SND res))) s') /\
         (FST res = word 0 <=> ~nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REmit h))`,
  PL_DRV_TAC pl_plan_emit PL_EMIT);;

let PL_LEAF_EMIT_LIVE = prove
 (`!progs bw ctl nctl budget cfr. pl_progs_ok progs /\ pl_cw_range nctl pl_plan_emit
     ==> pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr pl_plan_emit 5`,
  PL_LEAF_IMPL_TAC pl_plan_emit);;

let PL_EMIT_REL = prove
 (`!progs bw ctl nctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h.
     pl_progs_ok progs /\ pl_cw_range nctl pl_plan_emit /\
     drv_sem progs bw ctl budget cfr pl_plan_emit 0 m used res /\
     plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = h
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REmit h) (FST(SND s')) /\
                    pl_inv s') /\ plan_rel bw ctl nctl cfr (FST(SND(SND res))) s') /\
         (FST res = word 0 <=> ~nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REmit h))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`plan_rel bw ctl nctl cfr`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
                `budget:int64`; `cfr:int64`; `m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`;
                `cw:num->num`; `ctx:hupdate list`; `nms:string list`; `tys:(num#num#num)list`;
                `ntms:(num#num#num#num#num)list`; `dbs:(num#num#num)list`; `ths:(num#num)list`;
                `nmap:num list`; `ymap:num list`; `drops:(num#num)list`; `pol:num`; `stk:num list`; `h:num`]
               PL_EMIT_DRV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC PL_LEAF_EMIT_LIVE THEN ASM_REWRITE_TAC[]);;

let pl_handler_emit, HANDLER_EMIT, _ = kind_handler "emit" op0_shape pl_plan_emit PL_EMIT_REL;;
let KC_EMIT = kind_contract_of HANDLER_EMIT `50`;;
let KE_EMIT = kind_every_of KC_EMIT pl_handler_emit op0_shape pl_plan_emit PL_EMIT_REL;;

(* Every theorem this file states, for the audits. *)
let kind_emit_theorems =
 ["PL_EMIT_DRV", PL_EMIT_DRV; "PL_LEAF_EMIT_LIVE", PL_LEAF_EMIT_LIVE; "PL_EMIT_REL", PL_EMIT_REL;
  "HANDLER_EMIT", HANDLER_EMIT; "KC_EMIT", KC_EMIT; "KE_EMIT", KE_EMIT];;
