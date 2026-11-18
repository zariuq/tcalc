(* ========================================================================= *)
(* The contracts the record loop needs of its handlers, over the general    *)
(* relation. A kind's handler H for opcode op, run from a state whose       *)
(* relations hold at the cursor c (the byte after the opcode): when it      *)
(* FIRES, the header was seen (HDR); the bytes at c are the rest of some    *)
(* record's encoding (enc) whose first byte is op; the record's step holds; *)
(* the invariant and both relations hold after it at the cursor past the   *)
(* record; the count is one more and the words 18..23 are kept. The kinds   *)
(* whose handlers run over HOL's tables meet it (KC_<KIND>_TAB); the header *)
(* plan meets the header's contract (HC_HDR_TAB).                            *)
(*                                                                           *)
(* Loaded after handlers_hol.ml and reader_plans_tab.ml.                     *)
(* ========================================================================= *)

let tab_kind_contract = new_definition
 `tab_kind_contract (tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool))
                    L (Inv:(num->num)#S#num list->bool) (step:S->R->S->bool) (enc:R->num list)
                    progs bw ctl nctl budget cfr H op <=>
    !m used res cw s stk inp c.
      drv_sem progs bw ctl budget cfr H 0 m used res /\
      tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ Inv (cw,s,stk) /\
      rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
      ==> (FST res = word 1
           ==> cw 20 = 1 /\
               ?rec rest s'. enc rec = CONS op (TL (enc rec)) /\
                             rd_from inp c = APPEND (TL (enc rec)) rest /\
                             step s rec (FST(SND s')) /\ Inv s' /\
                             tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND res))) s' /\
                             rd_rel bw ctl nctl cfr (FST(SND(SND res))) inp (c + LENGTH (TL (enc rec))) /\
                             FST s' 17 = cw 17 + 1 /\
                             (!j. 18 <= j /\ j < 24 ==> FST s' j = cw j))`;;

(* A handler theorem (HANDLER_<KIND>_TAB) gives its kind's contract: HDR    *)
(* from its prefix, the record its native step names (NAME's bytes by       *)
(* NAME_FIRES_KEY), its encoding by holr_rec_enc, the words 18..23 from the *)
(* frame.                                                                     *)
let TAB_CONTRACT_TAC handler_th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tab_kind_contract] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL handler_th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN
    MP_TAC(MP (CONJUNCT1 th) (ASSUME `FST(res:int64#num#(int64->byte)#int64) = word 1`))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRY(FIRST_ASSUM(fun th -> if is_const_app "name_fires" (concl th) then
        RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP NAME_FIRES_KEY th]) THEN
        STRIP_ASSUME_TAC(REWRITE_RULE[name_fires] th) else failwith "")) THEN
  TRY(FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [leb_fires] o
                    check (fun th -> is_const_app "leb_fires" (concl th)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_const_app "nat_step" (concl th)
                        then EXISTS_TAC (el 1 (snd(strip_comb(concl th)))) else failwith "") THEN
  MAP_EVERY EXISTS_TAC [`rest:num list`; `s':pstate`] THEN
  REWRITE_TAC[holr_rec_enc; TL; LENGTH_APPEND] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `FST(s':pstate)`)) (concl th)
                        then MP_TAC(SPEC `j:num` th) else failwith "") THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[pl_set] THEN
  ASM_SIMP_TAC[ARITH_RULE `18 <= j ==> ~(j = 8) /\ ~(j = 9) /\ ~(j = 10) /\ ~(j = 11)`;
               ARITH_RULE `j < 24 ==> ~(j = 24)`];;

(* The contract's statement for a handler: its static premises (those that   *)
(* name no state, run or input) outside.                                     *)
let tab_kind_contract_goal handler_th op =
  let _, body = strip_forall(concl handler_th) in
  let ant, _ = dest_imp body in
  let dyn = [`m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`; `s:nstate`;
             `stk:num list`; `inp:num list`; `c:num`] in
  let static = filter (fun p -> not (exists (fun v -> vfree_in v p) dyn)) (conjuncts ant) in
  let drv = find (fun p -> is_const_app "drv_sem" p) (conjuncts ant) in
  let h = el 5 (snd(strip_comb drv)) in
  let cncl = list_mk_icomb "tab_kind_contract"
    [`hol_tables`; `hol_layout`; `hol_inv`; `nat_step`; `holr_rec_enc`; `progs:num->tisa_prog`; `bw:num->int64`;
     `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; h; op] in
  let body = mk_imp(list_mk_conj static, cncl) in
  list_mk_forall(filter (fun v -> vfree_in v body)
    [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`], body);;

let tab_kind_contract_of handler_th op =
  prove(tab_kind_contract_goal handler_th op, TAB_CONTRACT_TAC handler_th);;

let KC_NAME_TAB = tab_kind_contract_of HANDLER_NAME_TAB `1`;;
let KC_TYVAR_TAB = tab_kind_contract_of HANDLER_TYVAR_TAB `2`;;
let KC_VAR_TAB = tab_kind_contract_of HANDLER_VAR_TAB `4`;;
let KC_COMB_TAB = tab_kind_contract_of HANDLER_COMB_TAB `6`;;
let KC_REFL_TAB = tab_kind_contract_of HANDLER_REFL_TAB `16`;;
let KC_BETA_TAB = tab_kind_contract_of HANDLER_BETA_TAB `20`;;
let KC_ASSUME_TAB = tab_kind_contract_of HANDLER_ASSUME_TAB `21`;;
let KC_LABEL_TAB = tab_kind_contract_of HANDLER_LABEL_TAB `49`;;
let KC_EMIT_TAB = tab_kind_contract_of HANDLER_EMIT_TAB `50`;;
let KC_DROP_TYPE_TAB = tab_kind_contract_of HANDLER_DROP_TYPE_TAB `64`;;
let KC_DROP_TERM_TAB = tab_kind_contract_of HANDLER_DROP_TERM_TAB `65`;;
let KC_DROP_THM_TAB = tab_kind_contract_of HANDLER_DROP_THM_TAB `66`;;

(* ------------------------------------------------------------------------- *)
(* The header's contract over HOL's tables: a FIRED run saw HDR 0, read the  *)
(* header of a policy p <= 2, and leaves the relations past it at the state *)
(* with the policy raised to p and HDR set.                                  *)
(* ------------------------------------------------------------------------- *)

(* The relation reads the state only through its rows, counts and marks. *)
let TAB_REL_STATE_CONG = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput L inp bw ctl nctl cfr m cw s s' stk.
     (!j. trow j s' = trow j s) /\ (!c. tn c s' = tn c s) /\ (!jm. tdrop jm s' = tdrop jm s)
     ==> (tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr m (cw,s',stk) <=>
          tab_rel (trow,tn,twd,tdrop,tapp,tput) L inp bw ctl nctl cfr m (cw,s,stk))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tab_rel] THEN
  SUBGOAL_THEN `tab_mem (trow,tn,twd,tdrop,tapp,tput) inp bw m (s':S) = tab_mem (trow,tn,twd,tdrop,tapp,tput) inp bw m s`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `d:tabdesc` THEN
  STRUCT_CASES_TAC(SPEC `d:tabdesc` (cases "tabdesc")) THEN ASM_REWRITE_TAC[tab_mem]);;

(* HOL's tables do not read the policy. *)
let TAB_REL_POL_HOL = prove
 (`!L inp bw ctl nctl cfr m cw ctx nms tys ntms dbs ths nmap ymap drops pol pol' stk.
     tab_rel hol_tables L inp bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol'),stk) <=>
     tab_rel hol_tables L inp bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_tables] THEN MATCH_MP_TAC TAB_REL_STATE_CONG THEN
  SUBGOAL_THEN `!j. hol_tw j (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol') =
                    hol_tw j (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; hol_tw]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; hol_trow; hol_tn; hol_tdrop]);;

(* The row/constant part is independent of the policy's logical value. *)
let HOL_CORE_INV_POL_CW = prove
 (`!cw cw' ctx nms tys ntms dbs ths nmap ymap drops pol pol' stk.
     hol_core_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     (!n. n <= 6 ==> cw' n = cw n) /\ cw' 22 = cw 22
     ==> hol_core_inv (cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol'),stk)`,
  REWRITE_TAC[HOL_CORE_INV] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_INV_POL THEN EXISTS_TAC `pol:num` THEN
    MATCH_MP_TAC PL_INV_CW THEN EXISTS_TAC `cw:num->num` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* Updating policy requires the corresponding machine word to agree. *)
let HOL_INV_POL_CW = prove
 (`!cw cw' ctx nms tys ntms dbs ths nmap ymap drops pol pol' stk.
     hol_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     (!n. n <= 6 ==> cw' n = cw n) /\ cw' 22 = cw 22 /\ cw' 7 = pol'
     ==> hol_inv (cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol'),stk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_inv;tab_value_fact;nat_policy;FST;SND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOL_CORE_INV_POL_CW THEN
  MAP_EVERY EXISTS_TAC [`cw:num->num`;`pol:num`] THEN ASM_REWRITE_TAC[]);;

let tab_header_contract = new_definition
 `tab_header_contract L progs bw ctl nctl budget cfr H <=>
    !m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
      drv_sem progs bw ctl budget cfr H 0 m used res /\
      tab_rel hol_tables L inp bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
      hol_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
      rd_rel bw ctl nctl cfr m inp c /\ rd_hdr_rel bw cfr m /\ ~(val budget < val used)
      ==> (FST res = word 1
           ==> cw 20 = 0 /\
               ?p rest s'. p <= 2 /\ rd_from inp c = APPEND (TL (holr_body p 0 [])) rest /\
                           FST(SND s') = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,MAX pol p) /\
                           hol_inv s' /\
                           tab_rel hol_tables L inp bw ctl nctl cfr (FST(SND(SND res))) s' /\
                           rd_rel bw ctl nctl cfr (FST(SND(SND res))) inp
                                  (c + LENGTH (TL (holr_body p 0 []))) /\
                           FST s' 20 = 1 /\ (!j. 17 <= j /\ j < 24 /\ ~(j = 20) ==> FST s' j = cw j))`;;

let HC_HDR_TAB = prove
 (`!L progs bw ctl nctl budget cfr.
     progs 3 = eqw /\ rd_progs_ok progs /\ progs 31 = const_next /\ progs 20 = pol_max /\ 27 < nctl /\
     rd_tab_apart L bw
     ==> tab_header_contract L progs bw ctl nctl budget cfr pl_plan_hdr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tab_header_contract] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(cw:num->num) 7 = pol` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOL_INV];ALL_TAC] THEN
  MP_TAC(ISPECL [`hol_tables`; `L:tabdesc list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                 `budget:int64`; `cfr:int64`; `0`; `m:int64->byte`; `used:int64`;
                 `res:int64#num#(int64->byte)#int64`; `cw:num->num`;
                 `(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`; `stk:num list`; `inp:num list`; `c:num`]
                PL_HDR_TAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(MP (CONJUNCT2 th) (ASSUME `FST(res:int64#num#(int64->byte)#int64) = word 1`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `cw':num->num`
    STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `rest:num list`;
    `(cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,MAX pol p),stk):pstate`] THEN
  REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC HOL_INV_POL_CW THEN MAP_EVERY EXISTS_TAC [`cw:num->num`; `pol:num`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    TRY(X_GEN_TAC `n:num` THEN DISCH_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `cw':num->num`)) (concl th))) THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL TAB_REL_POL_HOL)))) THEN EXISTS_TAC `pol:num` THEN
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `cw':num->num`)) (concl th))) THEN ASM_ARITH_TAC]);;

(* Every theorem this file states, for the audits. *)
let contract_tab_theorems =
 ["KC_NAME_TAB", KC_NAME_TAB; "KC_TYVAR_TAB", KC_TYVAR_TAB; "KC_VAR_TAB", KC_VAR_TAB; "KC_COMB_TAB", KC_COMB_TAB;
  "KC_REFL_TAB", KC_REFL_TAB; "KC_BETA_TAB", KC_BETA_TAB; "KC_ASSUME_TAB", KC_ASSUME_TAB;
  "KC_LABEL_TAB", KC_LABEL_TAB; "KC_EMIT_TAB", KC_EMIT_TAB; "TAB_REL_STATE_CONG", TAB_REL_STATE_CONG;
  "TAB_REL_POL_HOL", TAB_REL_POL_HOL;"HOL_CORE_INV_POL_CW",HOL_CORE_INV_POL_CW;
  "HOL_INV_POL_CW", HOL_INV_POL_CW; "HC_HDR_TAB", HC_HDR_TAB;
  "KC_DROP_TYPE_TAB", KC_DROP_TYPE_TAB; "KC_DROP_TERM_TAB", KC_DROP_TERM_TAB; "KC_DROP_THM_TAB", KC_DROP_THM_TAB];;
