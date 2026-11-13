(* ========================================================================= *)
(* The record plans through the driver: drv_sem (driver.ml) runs a plan as  *)
(* pl_run (plans_abs.ml) does, for any relation prel between the driver's   *)
(* memory and the abstract state under which every step's leaf implements   *)
(* its abstract semantics (pl_impl). Then each PL_<KIND> theorem holds of   *)
(* the plan's run through the driver, parametric in those leaf premises,    *)
(* as DRV_CORRECT is parametric in its leaves.                              *)
(*                                                                           *)
(* Loaded in a session on s2n-bignum's base after the driver's files and    *)
(* the Model world (model_world_load.ml, which loads plans_abs.ml).         *)
(* ========================================================================= *)

(* The step's leaf implements its abstract semantics under prel: from       *)
(* related states, the run of the leaf on the child state the driver builds *)
(* is an abstract step with its outcome code (below 8) and the value of its *)
(* payload word; the receipt stays within the allowance (a leaf may pay    *)
(* fuel); and when the leaf FIRED, the memory the driver keeps after it is  *)
(* related to the abstract state after it. After any other outcome the plan *)
(* ends, and nothing is claimed of its memory.                              *)
let pl_impl = new_definition
 `pl_impl (prel:(int64->byte)->pstate->bool) progs bw ctl budget cfr (st:int64 list) <=>
    !m used s t k u.
      prel m s /\ ~(val budget < val used) /\
      drv_child bw ctl budget cfr st m used t /\
      tisa_entry_ok (progs (val(EL 0 st))) t /\ tisa_run (progs (val(EL 0 st))) t = TStop k u
      ==> ?k' ns'. pl_leaf st s k' (val(tisa_fword u 19)) ns' /\ k' < 8 /\
                   tisa_fword u 18 = word k' /\ ~(val budget < val(tisa_fword u 21)) /\
                   (k' = 1
                    ==> prel (drv_after ctl st u)
                          (pl_set (FST s) (val(EL 17 st)) (val(tisa_fword u 19)),ns',SND(SND s)))`;;

(* Leaf n implements its semantics in every step of plan P that calls it.  *)
(* One premise per leaf: the ledger's LEAF_<name> items.                    *)
let pl_leaf_impl = new_definition
 `pl_leaf_impl prel progs bw ctl budget cfr (P:(int64 list)list) n <=>
    !st. MEM st P /\ val(EL 0 st) = n ==> pl_impl prel progs bw ctl budget cfr st`;;

let PL_WORD_SMALL_EQ = prove
 (`!a b. a < 8 /\ b < 8 ==> ((word a:int64) = word b <=> a = b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_WORD_EQ THEN ASM_ARITH_TAC);;

(* drv_sem is pl_run, step for step: the same outcome and ending step, the  *)
(* receipt within the allowance, and the final memory related to the final *)
(* abstract state when the plan FIRED.                                      *)
let PL_DRV_BRIDGE = prove
 (`!prel progs bw ctl budget cfr sts i m used res s.
     (!st. MEM st sts ==> pl_impl prel progs bw ctl budget cfr st) /\
     drv_sem progs bw ctl budget cfr sts i m used res /\ prel m s /\ ~(val budget < val used)
     ==> ?k j s'. pl_run sts i s (k,j,s') /\ k < 8 /\ FST res = word k /\ FST(SND res) = j /\
                 (k = 1 ==> prel (FST(SND(SND res))) s') /\ ~(val budget < val(SND(SND(SND res))))`,
  REPLICATE_TAC 6 GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[drv_sem; MEM] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`1`; `i:num`; `s:pstate`] THEN ASM_REWRITE_TAC[pl_run] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  ASM_REWRITE_TAC[drv_sem] THEN
  DISCH_THEN(X_CHOOSE_THEN `tc:tisa_state` (X_CHOOSE_THEN `kc:num`
    (X_CHOOSE_THEN `u:tisa_state` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[pl_impl] o SPEC `h:int64 list` o
              check (fun th -> is_forall(concl th) && can (find_term (is_const_app "pl_impl")) (concl th))) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:int64->byte`; `used:int64`; `s:pstate`; `tc:tisa_state`;
                             `kc:num`; `u:tisa_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `ns1:nstate` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `tisa_fword u 18 = word 1 <=> k1 = 1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_WORD_SMALL_EQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k1 = 1` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k1 = 1`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`; `drv_after ctl h u`; `tisa_fword u 21`;
                    `res:int64#num#(int64->byte)#int64`;
                    `(pl_set (FST(s:pstate)) (val(EL 17 (h:int64 list))) (val(tisa_fword u 19)),ns1,SND(SND(s:pstate))):pstate`] o
                  check (fun th -> is_forall(concl th) && can (find_term (is_const_app "drv_sem")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                       can (find_term (is_const_app "pl_impl")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `j:num`; `s':pstate`] THEN ASM_REWRITE_TAC[pl_run] THEN
    MAP_EVERY EXISTS_TAC [`1`; `val(tisa_fword u 19)`; `ns1:nstate`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`k1:num`; `i:num`;
                          `(pl_set (FST(s:pstate)) (val(EL 17 (h:int64 list))) (val(tisa_fword u 19)),ns1,SND(SND(s:pstate))):pstate`] THEN
    ASM_REWRITE_TAC[pl_run] THEN
    MAP_EVERY EXISTS_TAC [`k1:num`; `val(tisa_fword u 19)`; `ns1:nstate`] THEN ASM_REWRITE_TAC[]]);;

(* From the per-leaf premises to every step of a plan: the leaves a plan    *)
(* calls are computed from its data.                                         *)
let PL_LEAVES_TAC plan =
  X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pl_leaf_impl]) THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_const_app "MEM" (concl th))) THEN
  REWRITE_TAC[plan; MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `st:int64 list`
                          then SUBST_ALL_TAC th else failwith "") THEN
  FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     CONV_TAC(DEPTH_CONV EL_CONV THENC DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) THEN NO_TAC]);;

(* A plan's abstract theorem carries over to the driver: whatever the plan *)
(* proves of its FIRED runs (Q) and of when it is REFUSED (G), drv_sem's run *)
(* from a related state has, with the final memory related to a state Q   *)
(* holds of.                                                                *)
let PL_DRV_GENERIC = prove
 (`!prel progs bw ctl budget cfr P m used res s Q G.
     (!st. MEM st P ==> pl_impl prel progs bw ctl budget cfr st) /\
     drv_sem progs bw ctl budget cfr P 0 m used res /\ prel m s /\ ~(val budget < val used) /\
     (!k j s'. pl_run P 0 s (k,j,s') ==> (k = 1 ==> Q s') /\ (k = 0 <=> G))
     ==> (FST res = word 1 ==> ?s'. Q s' /\ prel (FST(SND(SND res))) s') /\ (FST res = word 0 <=> G)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`prel:(int64->byte)->pstate->bool`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
                `budget:int64`; `cfr:int64`; `P:(int64 list)list`; `0`; `m:int64->byte`; `used:int64`;
                `res:int64#num#(int64->byte)#int64`; `s:pstate`] PL_DRV_BRIDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(FST(res:int64#num#(int64->byte)#int64) = word 1 <=> k = 1) /\ (FST res = word 0 <=> k = 0)`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC PL_WORD_SMALL_EQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `j:num`; `s':pstate`] o
                check (fun th -> is_forall(concl th) && can (find_term (is_const_app "pl_run")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN EXISTS_TAC `s':pstate` THEN ASM_MESON_TAC[]);;

(* A record's theorem through the driver, from its abstract theorem PL_<KIND> *)
(* and the plan's data: the leaves it calls are its premises (pl_leaf_impl). *)
let PL_DRV_TAC plan_def levelA =
  let plan = lhs(concl plan_def) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,w) ->
    let c1,c2 = dest_conj w in
    let g_tm = rand c2 in
    let s',b = dest_exists (rand c1) in
    let q_tm = mk_abs(s', lhand b) in
    let s0 = rand(concl(snd(find (fun (_,th) -> is_const_app "pl_inv" (concl th)) asl))) in
    let res = rand(lhand(lhand c1)) in
    MP_TAC(ISPECL [`prel:(int64->byte)->pstate->bool`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
                   `budget:int64`; `cfr:int64`; plan; `m:int64->byte`; `used:int64`; res; s0; q_tm; g_tm]
                  PL_DRV_GENERIC)) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [PL_LEAVES_TAC plan_def; ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC levelA THEN
  W(fun (asl,w) ->
    let s0 = rand(concl(snd(find (fun (_,th) -> is_const_app "pl_inv" (concl th)) asl))) in
    let cw0 = fst(dest_pair s0) and stk0 = snd(dest_pair(snd(dest_pair s0))) in
    let vs,_ = strip_exists w in
    MAP_EVERY (fun v -> let ty = type_of v in
                        EXISTS_TAC (if ty = `:num->num` then cw0 else if ty = `:num list` then stk0
                                    else `j:num`)) vs) THEN
  ASM_REWRITE_TAC[];;

(* The records through the driver: for any representation prel under which  *)
(* the leaves a plan calls implement their abstract semantics (one premise  *)
(* per leaf, LEAF_<name> in LEDGER.txt), the driver's run of the plan from  *)
(* a related state is the record's nat_step when it FIRES, with the final   *)
(* memory related to a state satisfying pl_inv, and is REFUSED exactly when *)
(* the clause's guards fail.                                                *)

let PL_ASSUME_DRV = prove
 (`!prel progs bw ctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t.
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_assume 0 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_assume 1 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_assume 3 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_assume 4 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_assume 5 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_assume 6 /\
     drv_sem progs bw ctl budget cfr pl_plan_assume 0 m used res /\
     prel m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = t
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAssume t) (FST(SND s')) /\
                    pl_inv s') /\ prel (FST(SND(SND res))) s') /\
         (FST res = word 0 <=>
          ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RAssume t) /\
            ?p. fdtm nms tys ntms t p /\ htypeof p = HBool))`,
  PL_DRV_TAC pl_plan_assume PL_ASSUME);;

let PL_EQMP_DRV = prove
 (`!prel progs bw ctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2.
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_eqmp 2 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_eqmp 3 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_eqmp 4 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_eqmp 5 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_eqmp 6 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_eqmp 7 /\
     drv_sem progs bw ctl budget cfr pl_plan_eqmp 0 m used res /\
     prel m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = h1 /\ cw 9 = h2
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REqMp h1 h2) (FST(SND s')) /\
                    pl_inv s') /\ prel (FST(SND(SND res))) s') /\
         (FST res = word 0 <=>
          ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (REqMp h1 h2) /\
            ?ty p q. fddb nms tys dbs (SND(EL h1 ths)) (hdbComb (hdbComb (hdbConst "=" ty) p) q) /\
                     fddb nms tys dbs (SND(EL h2 ths)) p))`,
  PL_DRV_TAC pl_plan_eqmp PL_EQMP);;

let PL_TRANS_DRV = prove
 (`!prel progs bw ctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2.
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_trans 0 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_trans 1 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_trans 2 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_trans 3 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_trans 4 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_trans 5 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_trans 6 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_trans 7 /\
     drv_sem progs bw ctl budget cfr pl_plan_trans 0 m used res /\
     prel m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = h1 /\ cw 9 = h2
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTrans h1 h2) (FST(SND s')) /\
                    pl_inv s') /\ prel (FST(SND(SND res))) s') /\
         (FST res = word 0 <=>
          ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RTrans h1 h2) /\
            ?ty1 ty2 l mid r.
              fddb nms tys dbs (SND(EL h1 ths)) (hdbComb (hdbComb (hdbConst "=" ty1) l) mid) /\
              fddb nms tys dbs (SND(EL h2 ths)) (hdbComb (hdbComb (hdbConst "=" ty2) mid) r)))`,
  PL_DRV_TAC pl_plan_trans PL_TRANS);;

let PL_REFL_DRV = prove
 (`!prel progs bw ctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk t.
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_refl 0 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_refl 1 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_refl 4 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_refl 5 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_refl 6 /\
     drv_sem progs bw ctl budget cfr pl_plan_refl 0 m used res /\
     prel m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = t
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t) (FST(SND s')) /\
                    pl_inv s') /\ prel (FST(SND(SND res))) s') /\
         (FST res = word 0 <=>
          ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t) /\
            ?tm. fdtm nms tys ntms t tm))`,
  PL_DRV_TAC pl_plan_refl PL_REFL);;

let PL_EXPECT_ALPHA_DRV = prove
 (`!prel progs bw ctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h c hl.
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_expect_alpha 3 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_expect_alpha 4 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_expect_alpha 5 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_expect_alpha 8 /\
     drv_sem progs bw ctl budget cfr pl_plan_expect_alpha 0 m used res /\
     prel m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     cw 8 = h /\ cw 10 = c /\ cw 13 + cw 12 <= LENGTH stk /\
     list_of_seq (\j. EL (cw 13 + j) stk) (cw 12) = hl
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RExpectAlpha h hl c) (FST(SND s')) /\
                    pl_inv s') /\ prel (FST(SND(SND res))) s') /\
         (FST res = word 0 <=>
          ~(?hsd cn hyps. nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RExpectAlpha h hl c) /\
                          fddbs nms tys dbs (FST(EL h ths)) hsd /\
                          fdtm nms tys ntms c cn /\ fddb nms tys dbs (SND(EL h ths)) (hdb cn) /\
                          ALL2 (fdtm nms tys ntms) hl hyps /\ ALL (\p. htypeof p = HBool) hyps /\
                          (!x. MEM x hsd <=> MEM x (MAP hdb hyps))))`,
  PL_DRV_TAC pl_plan_expect_alpha PL_EXPECT_ALPHA);;

let PL_MKCOMB_DRV = prove
 (`!prel progs bw ctl budget cfr m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk h1 h2.
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_mkcomb 0 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_mkcomb 1 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_mkcomb 2 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_mkcomb 3 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_mkcomb 4 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_mkcomb 5 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_mkcomb 6 /\
     pl_leaf_impl prel progs bw ctl budget cfr pl_plan_mkcomb 7 /\
     drv_sem progs bw ctl budget cfr pl_plan_mkcomb 0 m used res /\
     prel m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\ cw 8 = h1 /\ cw 9 = h2
     ==> (FST res = word 1
          ==> ?s'. (nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RMkComb h1 h2) (FST(SND s')) /\
                    pl_inv s') /\ prel (FST(SND(SND res))) s') /\
         (FST res = word 0 <=>
          ~(nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RMkComb h1 h2) /\
            ?f g a b tx ty.
              fddb nms tys dbs (SND(EL h1 ths))
                (hdbComb (hdbComb (hdbConst "=" (HFun (HFun tx ty) (HFun (HFun tx ty) HBool))) f) g) /\
              fddb nms tys dbs (SND(EL h2 ths))
                (hdbComb (hdbComb (hdbConst "=" (HFun tx (HFun tx HBool))) a) b)))`,
  PL_DRV_TAC pl_plan_mkcomb PL_MKCOMB);;
