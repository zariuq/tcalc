(* The ABS admission prefix, from the linked driver and leaf bytes to the
   exact logical guard and unchanged HOL tables. *)
needs "native/hol/tables_abs_guards.ml";;
needs "tisa/hol/tisa_x86_evidence.ml";;
needs "native/leaves/eqw/eqw.hol";;
needs "native/leaves/row_word/row_word.hol";;
needs "native/leaves/live/live.hol";;
needs "native/leaves/common/leaf_join_lib.ml";;

let ABS_GUARD_EQW_SPEC = leaf_spec "eqw" 0 EQW_TERM EQW_DECLS;;
let ABS_GUARD_ROW_WORD_SPEC =
  leaf_spec "row_word" 2 ROW_WORD_TERM ROW_WORD_DECLS;;
let ABS_GUARD_LIVE_SPEC = leaf_spec "live" 2 LIVE_TERM LIVE_DECLS;;

let abs_guard_progs = new_definition
 `abs_guard_progs j = if j = 4 then row_word else if j = 5 then live else eqw`;;
let abs_guard_mcs = new_definition
 `abs_guard_mcs j = if j = 4 then row_word_mc else if j = 5 then live_mc else eqw_mc`;;
let abs_guard_pcs = new_definition
 `abs_guard_pcs (eqpc:num) (rowpc:num) (livepc:num) j =
    if j = 4 then rowpc else if j = 5 then livepc else eqpc`;;

let ABS_GUARD_LEAVES = prove
 (`!eqpc rowpc livepc j. tisa_leaf_wf (abs_guard_progs j) /\
     tisa_leaf_spec (abs_guard_progs j) (abs_guard_mcs j)
                    (abs_guard_pcs eqpc rowpc livepc j)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `j = 4` THEN ASM_CASES_TAC `j = 5` THEN
  ASM_REWRITE_TAC[abs_guard_progs;abs_guard_mcs;abs_guard_pcs;
    EQW_LEAF_WF;ROW_WORD_LEAF_WF;LIVE_LEAF_WF;
    ABS_GUARD_EQW_SPEC;ABS_GUARD_ROW_WORD_SPEC;ABS_GUARD_LIVE_SPEC]);;

let ABS_GUARD_FIXED_IMPL = prove
 (`!inp bw ctl nctl budget cfr.
     pl_cw_range nctl pl_abs_guard_plan
     ==> !st. MEM st pl_abs_guard_plan ==>
       tab_impl (tab_rel hol_tables hol_layout inp bw ctl nctl cfr)
                hol_tables inp abs_guard_progs bw ctl budget cfr st`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!f. 10 <= f /\ f < 18 ==> val(EL f (st:int64 list)) < nctl`
    ASSUME_TAC THENL [ASM_MESON_TAC[pl_cw_range];ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "MEM" (concl th))) THEN
  REWRITE_TAC[pl_abs_guard_plan;MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN
  TAB_HOL_IMPL_TAC2 THEN REWRITE_TAC[abs_guard_progs] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let abs_guard_receipt = new_definition
 `abs_guard_receipt inp bw ctl nctl cfr budget m
   ((cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate)
   (res:int64#num#(int64->byte)#int64) <=>
    ?k cw'. (k = 0 \/ k = 1) /\ FST res = word k /\
      (k = 1 <=> nat_ops_live (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol)
                              (RAbs (cw 8) (cw 9)) /\
                 ?x ty tb. fdtm nms tys ntms (cw 8) (TmVar x ty) /\
                           fdtm nms tys ntms (cw 9) tb) /\
      tab_rel hol_tables hol_layout inp bw ctl nctl cfr m
        (cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
      (!j. j < 24 ==> cw' j = cw j) /\
      val(SND(SND(SND res))) <= val(budget:int64)`;;

let ABS_GUARD_DRIVER_RUN = prove
 (`!inp bw ctl nctl cfr budget m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk.
     pl_cw_range nctl pl_abs_guard_plan /\ ~(val budget < val used) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     tab_rel hol_tables hol_layout inp bw ctl nctl cfr m
             (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     drv_sem abs_guard_progs bw ctl budget cfr pl_abs_guard_plan 0 m used res
     ==> abs_guard_receipt inp bw ctl nctl cfr budget (FST(SND(SND res)))
           (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) res`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tab_rel hol_tables hol_layout inp bw ctl nctl cfr`;
    `hol_tables`;`inp:num list`;`abs_guard_progs`;`bw:num->int64`;
    `ctl:int64`;`budget:int64`;`cfr:int64`;`pl_abs_guard_plan`;`0`;
    `m:int64->byte`;`used:int64`;`res:int64#num#(int64->byte)#int64`;
    `(cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate`] TAB_DRV_BRIDGE) THEN
  ASM_SIMP_TAC[ABS_GUARD_FIXED_IMPL;TAB_SAFE_ABS_GUARDS] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `i:num`
    (X_CHOOSE_THEN `post:pstate` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPEC `post:pstate`
    (prove(`!p:pstate. ?c ns st. p = (c,ns,st)`,
      REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cw':num->num` (X_CHOOSE_THEN `ns':nstate`
    (X_CHOOSE_THEN `stk':num list` SUBST_ALL_TAC))) THEN
  MP_TAC(SPECL ([`cw:num->num`] @ pl_ns_vars @
    [`stk:num list`;`inp:num list`;`(cw:num->num) 8`;`(cw:num->num) 9`;
     `k:num`;`i:num`;`cw':num->num`;`ns':nstate`;`stk':num list`])
    PL_ABS_GUARD_RUN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[abs_guard_receipt] THEN MAP_EVERY EXISTS_TAC [`k:num`;`cw':num->num`] THEN
  ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  ASM_MESON_TAC[PL_ABS_GUARDS]);;

(* The descriptor receipt and the machine stack lie outside the table
   representation. Transfer the relation onto the actual outgoing memory. *)
let TAB_REL_BYTE_AGREE = prove
 (`!tb L inp bw ctl nctl cfr m m' cw (s:S) stk.
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\
     (!j a. MEM j (tab_slots L) /\ drv_in a (bw j) (val(bw(j + 1)))
            ==> m' a = m a) /\
     (!a. drv_in a ctl (8 * nctl) ==> m' a = m a)
     ==> tab_rel tb L inp bw ctl nctl cfr m' (cw,s,stk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_rel] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_cwords] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pl_mw m' ctl j = pl_mw m ctl j` SUBST1_TAC THENL
     [MATCH_MP_TAC PL_MW_REGION THEN EXISTS_TAC `8 * nctl` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[tab_layout];ASM_ARITH_TAC];
      ASM_MESON_TAC[pl_cwords]];
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `d:tabdesc` THEN DISCH_TAC THEN
    MATCH_MP_TAC TAB_MEM_AGREE THEN EXISTS_TAC `m:int64->byte` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[ALL_MEM];ALL_TAC] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    BETA_TAC THEN SUBGOAL_THEN `MEM (j:num) (tab_slots L)` ASSUME_TAC THENL
     [ASM_MESON_TAC[TAB_SLOTS_DESC];ALL_TAC] THEN
    ASM_MESON_TAC[TAB_LAYOUT_SLOT;LT_IMP_LE];
    MATCH_MP_TAC PL_STK_AGREE THEN EXISTS_TAC `m:int64->byte` THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `L:tabdesc list` TAB_SLOTS_STK) THEN
    ASM_MESON_TAC[TAB_LAYOUT_SLOT;LT_IMP_LE;ARITH_RULE `40 + 1 = 41`]]);;

let ABS_GUARD_FINAL_RECEIPT = prove
 (`!inp bw ctl nctl cfr budget d plan res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk m'.
     val(d:int64) + 64 <= 2 EXP 64 /\ drv_apart ctl (8 * nctl) d 64 /\
     (!j. MEM j (tab_slots hol_layout)
          ==> drv_apart (bw j) (val(bw(j + 1))) d 64) /\
     (!a. ~drv_stack cfr a ==> m' a = drv_final d plan res a) /\
     abs_guard_receipt inp bw ctl nctl cfr budget (FST(SND(SND res)))
       (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) res
     ==> abs_guard_receipt inp bw ctl nctl cfr budget m'
       (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) res`,
  REWRITE_TAC[abs_guard_receipt] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `cw':num->num`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) o check (is_exists o concl)) THEN
  MAP_EVERY EXISTS_TAC [`k:num`;`cw':num->num`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a. ~drv_stack cfr a /\ ~drv_in a d 64
        ==> m' a = FST(SND(SND(res:int64#num#(int64->byte)#int64))) a`
   ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ZINIT_FINAL_BYTE];
    ALL_TAC] THEN
  MATCH_MP_TAC TAB_REL_BYTE_AGREE THEN
  EXISTS_TAC `FST(SND(SND(res:int64#num#(int64->byte)#int64)))` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC;ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[tab_rel] o
      check (fun th -> is_const_app "tab_rel" (concl th))) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[tab_layout] o
      check (fun th -> is_const_app "tab_layout" (concl th))) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`j:num`;`a:int64`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(ASSUME
     `!a. ~drv_stack cfr a /\ ~drv_in a d 64
          ==> m' a = FST(SND(SND(res:int64#num#(int64->byte)#int64))) a`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DRV_IN_NOT_STACK THEN
      MAP_EVERY EXISTS_TAC [`bw(j:num):int64`;`val(bw(j + 1):int64)`] THEN
      MP_TAC(SPECL [`hol_layout:tabdesc list`;`bw:num->int64`;`ctl:int64`;
                    `nctl:num`;`cfr:int64`;`j:num`] TAB_LAYOUT_SLOT) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MATCH_MP_TAC DRV_APART_IN THEN
      MAP_EVERY EXISTS_TAC [`bw(j:num):int64`;`val(bw(j + 1):int64)`] THEN
      ASM_SIMP_TAC[]];
    X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ASSUME
     `!a. ~drv_stack cfr a /\ ~drv_in a d 64
          ==> m' a = FST(SND(SND(res:int64#num#(int64->byte)#int64))) a`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TAB_CTL_ADDR THEN
      MAP_EVERY EXISTS_TAC [`hol_layout:tabdesc list`;`bw:num->int64`;`ctl:int64`;`nctl:num`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC DRV_APART_IN THEN MAP_EVERY EXISTS_TAC [`ctl:int64`;`8 * nctl`] THEN
      ASM_REWRITE_TAC[]]]);;

(* Strengthen the same result witness that supplies the driver's frame and
   return register. No step interpreter or correctness axiom is involved. *)
let ABS_GUARD_DRIVER_X86 =
  let driver = REWRITE_RULE[ABS_GUARD_LEAVES]
    (ISPECL [`abs_guard_progs`;`abs_guard_pcs eqpc rowpc livepc`;`abs_guard_mcs`;
      `6`;`pc:num`;`stackpointer:int64`;`d:int64`;`plan:int64`;`4`;`ctl:int64`;
      `nctl:num`;`bind:int64`;`nbw:num`;`leaves:int64`;`bw:num->int64`;`pl_abs_guard_plan`;
      `budget:int64`;`used0:int64`;`m0:int64->byte`;`ret:int64`;
      `rbxv:int64`;`rbpv:int64`;`r12v:int64`;`r13v:int64`;`r14v:int64`;`r15v:int64`]
      DRV_CORRECT) in
  let assumptions,ensures_tm = dest_imp(concl driver) in
  let h,args = strip_comb ensures_tm in
  let model,pre,post,frame = match args with
    | [model;pre;post;frame] -> model,pre,post,frame
    | _ -> failwith "ABS guard driver: expected ensures" in
  let state,body = dest_abs post in
  let receipt = find_term (fun t -> is_exists t &&
    can (find_term ((=) `drv_sem`)) t) body in
  let result,abi_result = dest_exists receipt in
  let correctness = list_mk_comb(`abs_guard_receipt`,
    [`inp:num list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
     `word_sub stackpointer (word 248):int64`;`budget:int64`;
     mk_comb(`read memory:x86state->int64->byte`,state);
     `(cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate`;result]) in
  let strengthened = mk_abs(state,
    subst [mk_exists(result,mk_conj(abi_result,correctness)),receipt] body) in
  let admission =
    `pl_cw_range nctl pl_abs_guard_plan /\ ~(val(budget:int64) < val(used0:int64)) /\
     (!j. MEM j (tab_slots hol_layout) ==> drv_apart (bw j) (val(bw(j + 1))) d 64) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     tab_rel hol_tables hol_layout inp bw ctl nctl (word_sub stackpointer (word 248)) m0
             (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)` in
  let goal = mk_imp(mk_conj(assumptions,admission),
                    list_mk_comb(h,[model;pre;strengthened;frame])) in
  GEN_ALL(prove(goal,
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "driver") STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC post THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `res:int64#num#(int64->byte)#int64` STRIP_ASSUME_TAC o
                    check (is_exists o concl)) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "driver" (STRIP_ASSUME_TAC o REWRITE_RULE[drv_layout]) THEN
      MATCH_MP_TAC ABS_GUARD_FINAL_RECEIPT THEN
      MAP_EVERY EXISTS_TAC [`d:int64`;`plan:int64`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC ABS_GUARD_DRIVER_RUN THEN
      MAP_EVERY EXISTS_TAC [`m0:int64->byte`;`used0:int64`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC driver THEN USE_THEN "driver" ACCEPT_TAC]));;

let abs_guard_native_theorems =
 ["ABS_GUARD_LEAVES",ABS_GUARD_LEAVES;
  "ABS_GUARD_FIXED_IMPL",ABS_GUARD_FIXED_IMPL;
  "ABS_GUARD_DRIVER_RUN",ABS_GUARD_DRIVER_RUN;
  "TAB_REL_BYTE_AGREE",TAB_REL_BYTE_AGREE;
  "ABS_GUARD_FINAL_RECEIPT",ABS_GUARD_FINAL_RECEIPT;
  "ABS_GUARD_DRIVER_X86",ABS_GUARD_DRIVER_X86];;
