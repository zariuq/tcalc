(* Transfer the ABS table contract to memory at the linked x86 return. *)
needs "native/hol/tables_abs_images.ml";;
needs "native/hol/tables_abs_every.ml";;

let TAB_REL_DRV_FINAL = prove
 (`!tb L inp bw ctl nctl cfr d plan (res:int64#num#(int64->byte)#int64) m' (p:(num->num)#S#num list).
     val(d:int64) + 64 <= 2 EXP 64 /\ drv_apart ctl (8 * nctl) d 64 /\
     (!j. MEM j (tab_slots L) ==> drv_apart (bw j) (val(bw(j + 1))) d 64) /\
     (!a. ~drv_stack cfr a ==> m' a = drv_final d plan res a) /\
     tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND res))) p
     ==> tab_rel tb L inp bw ctl nctl cfr m' p`,
  REPLICATE_TAC 11 GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!a. ~drv_stack cfr a /\ ~drv_in a d 64
        ==> m' a = FST(SND(SND(res:int64#num#(int64->byte)#int64))) a`
   ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN STRIP_TAC THEN ASM_SIMP_TAC[ZINIT_FINAL_BYTE];ALL_TAC] THEN
  MATCH_MP_TAC TAB_REL_BYTE_AGREE THEN
  EXISTS_TAC `FST(SND(SND(res:int64#num#(int64->byte)#int64)))` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC;ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_LAYOUT o check (is_const_app "tab_rel" o concl)) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`j:num`;`a:int64`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(ASSUME
     `!a. ~drv_stack cfr a /\ ~drv_in a d 64
          ==> m' a = FST(SND(SND(res:int64#num#(int64->byte)#int64))) a`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DRV_IN_NOT_STACK THEN
      MAP_EVERY EXISTS_TAC [`bw(j:num):int64`;`val(bw(j + 1):int64)`] THEN
      MP_TAC(SPECL [`L:tabdesc list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`cfr:int64`;`j:num`] TAB_LAYOUT_SLOT) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MATCH_MP_TAC DRV_APART_IN THEN
      MAP_EVERY EXISTS_TAC [`bw(j:num):int64`;`val(bw(j + 1):int64)`] THEN ASM_SIMP_TAC[]];
    X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ASSUME
     `!a. ~drv_stack cfr a /\ ~drv_in a d 64
          ==> m' a = FST(SND(SND(res:int64#num#(int64->byte)#int64))) a`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TAB_CTL_ADDR THEN
      MAP_EVERY EXISTS_TAC [`L:tabdesc list`;`bw:num->int64`;`ctl:int64`;`nctl:num`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC DRV_APART_IN THEN MAP_EVERY EXISTS_TAC [`ctl:int64`;`8 * nctl`] THEN ASM_REWRITE_TAC[]]]);;

let ABS_PLAN_DRIVER_X86 =
  let drv = abs_exact_driver `pl_plan_abs` in
  let admitted,ensures_tm = dest_imp(concl drv) in
  let h,args = strip_comb ensures_tm in
  let model,pre,post,frame = match args with
    | [model;pre;post;frame] -> model,pre,post,frame
    | _ -> failwith "ABS driver: expected ensures" in
  let state,body = dest_abs post in
  let receipt = find_term (fun tm -> is_exists tm &&
    can (find_term (is_const_app "drv_sem")) tm) body in
  let res,driver_post = dest_exists receipt in
  let property = rand(concl(SPEC_ALL TAB_ABS_DRIVER_RUN)) in
  let memory = mk_comb(`read memory:x86state->int64->byte`,state) in
  let property = subst [res,`res:int64#num#(int64->byte)#int64`] property in
  let semantic_mem = subst [res,`res:int64#num#(int64->byte)#int64`]
    `FST(SND(SND(res:int64#num#(int64->byte)#int64)))` in
  let property = subst [memory,semantic_mem;`word_sub stackpointer (word 248):int64`,`cfr:int64`] property in
  let strengthened = mk_abs(state,subst [mk_exists(res,mk_conj(driver_post,property)),receipt] body) in
  let physical_pre =
    `pl_cw_range nctl pl_plan_abs /\ ~(val(budget:int64) < val(used0:int64)) /\
     (!j. MEM j (tab_slots hol_layout) ==> drv_apart (bw j) (val(bw(j + 1))) d 64) /\
     pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     tab_rel hol_tables hol_layout inp bw ctl nctl (word_sub stackpointer (word 248)) m0
             (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)` in
  let goal = mk_imp(mk_conj(admitted,physical_pre),list_mk_comb(h,[model;pre;strengthened;frame])) in
  GEN_ALL(prove(goal,
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "driver") STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC post THEN CONJ_TAC THENL
     [X_GEN_TAC `machine:x86state` THEN BETA_TAC THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `res:int64#num#(int64->byte)#int64` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
                    check (is_exists o concl)) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL ([`inp:num list`;`abs_progs`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;
        `word_sub stackpointer (word 248):int64`;`m0:int64->byte`;`used0:int64`;
        `res:int64#num#(int64->byte)#int64`;`cw:num->num`] @ pl_ns_vars @ [`stk:num list`])
        TAB_ABS_DRIVER_RUN) THEN
      ASM_REWRITE_TAC[ABS_X86_PROGS] THEN
      DISCH_THEN(X_CHOOSE_THEN `cw':num->num` (X_CHOOSE_THEN `ns':nstate`
        (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
      MAP_EVERY EXISTS_TAC [`cw':num->num`;`ns':nstate`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC TAB_REL_DRV_FINAL THEN
      MAP_EVERY EXISTS_TAC [`d:int64`;`plan:int64`;`res:int64#num#(int64->byte)#int64`] THEN
      USE_THEN "driver" (STRIP_ASSUME_TAC o REWRITE_RULE[drv_layout]) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC drv THEN USE_THEN "driver" ACCEPT_TAC]));;

let ABS_NATIVE_KIND_EVERY = prove
 (`!bw ctl nctl budget cfr.
     rd_tab_apart hol_layout bw /\ pl_cw_range nctl pl_plan_abs
     ==> tab_kind_every hol_layout abs_progs bw ctl nctl budget cfr pl_handler_abs 7`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KE_ABS_TAB THEN ASM_REWRITE_TAC[ABS_X86_PROGS]);;

let DRV_SEM_FUEL_BOUND = prove
 (`!progs bw ctl budget cfr P i m used res.
     (!st. MEM st P ==> tisa_leaf_wf (progs (val(EL 0 st)))) /\ val used <= val budget /\
     drv_sem progs bw ctl budget cfr P i m used res
     ==> val(SND(SND(SND res))) <= val budget`,
  REPLICATE_TAC 5 GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[drv_sem;MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[FST;SND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[MEM] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(val(budget:int64) < val(used:int64))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NOT_LT];ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_const_app "drv_sem" o concl)) THEN
  ASM_REWRITE_TAC[drv_sem] THEN
  DISCH_THEN(X_CHOOSE_THEN `tc:tisa_state` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u:tisa_state`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))) THEN
  SUBGOAL_THEN `tisa_fword tc 20 = budget` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `20` o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[drv_child] o
      check (is_const_app "drv_child" o concl)) THEN REWRITE_TAC[drv_fw] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(tisa_fword u 21) <= val(budget:int64)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`progs(val(EL 0 (h:int64 list))):tisa_prog`;`tc:tisa_state`;`k:num`;`u:tisa_state`] TISA_RUN_FUEL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`i + 1`;`drv_after ctl h u`;`tisa_fword u 21`;
      `res:int64#num#(int64->byte)#int64`] o check (fun th -> is_forall(concl th) &&
      tab_has_const "drv_sem" (concl th))) THEN ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[SND]]);;

let RD_REL_DRV_FINAL = prove
 (`!bw ctl nctl cfr d plan res m' inp c.
     48 <= val(cfr:int64) /\ val(d:int64) + 64 <= 2 EXP 64 /\
     drv_apart (bw 54) (val(bw 55)) d 64 /\ drv_apart (bw 58) (val(bw 59)) d 64 /\
     (!a. ~drv_stack cfr a ==> m' a = drv_final d plan res a) /\
     rd_rel bw ctl nctl cfr (FST(SND(SND res))) inp c
     ==> rd_rel bw ctl nctl cfr m' inp c`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC RD_REL_AGREE THEN EXISTS_TAC `FST(SND(SND(res:int64#num#(int64->byte)#int64)))` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rd_layout] o CONJUNCT1 o REWRITE_RULE[rd_rel] o
    check (is_const_app "rd_rel" o concl)) THEN
  SUBGOAL_THEN
   `!a. ~drv_stack cfr a /\ ~drv_in a d 64
        ==> m' a = FST(SND(SND(res:int64#num#(int64->byte)#int64))) a`
   ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[ZINIT_FINAL_BYTE]; ALL_TAC] THEN
  X_GEN_TAC `a:int64` THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC(ASSUME
   `!a. ~drv_stack cfr a /\ ~drv_in a d 64
        ==> m' a = FST(SND(SND(res:int64#num#(int64->byte)#int64))) a`) THEN
  let prove_slot j =
    let region = mk_comb(`bw:num->int64`,j) and size = mk_comb(`val:int64->num`,
      mk_comb(`bw:num->int64`,rhs(concl(NUM_REDUCE_CONV(mk_binop `(+):num->num->num` j `1`))))) in
    CONJ_TAC THENL
     [MATCH_MP_TAC DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [region;size] THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o SPEC j o check (fun th -> is_forall(concl th) && tab_has_const "drv_apart" (concl th))) THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
      MATCH_MP_TAC DRV_APART_IN THEN MAP_EVERY EXISTS_TAC [region;size] THEN ASM_REWRITE_TAC[]] in
  FIRST [prove_slot `54` THEN NO_TAC; prove_slot `58`]);;

let abs_record_post = new_definition
 `abs_record_post inp bw ctl nctl cfr (budget:int64) (used:int64) c m'
     ((cw,ns,stk):pstate) (res:int64#num#(int64->byte)#int64) <=>
    (exists post. tab_rel hol_tables hol_layout inp bw ctl nctl cfr m' post /\
                  pl_grows ns (FST(SND post))) /\
    val used <= val(SND(SND(SND res))) /\ val(SND(SND(SND res))) <= val budget /\
    (FST res = word 1 ==> cw 20 = 1 /\
     ?rec rest post. holr_rec_enc rec = CONS 7 (TL(holr_rec_enc rec)) /\
       rd_from inp c = APPEND (TL(holr_rec_enc rec)) rest /\ nat_step ns rec (FST(SND post)) /\
       hol_inv post /\ tab_rel hol_tables hol_layout inp bw ctl nctl cfr m' post /\
       rd_rel bw ctl nctl cfr m' inp (c + LENGTH(TL(holr_rec_enc rec))) /\ FST post 17 = cw 17 + 1 /\
       (!j. 18 <= j /\ j < 24 ==> FST post j = cw j))`;;

let ABS_RECORD_RETURN = prove
 (`!inp bw ctl nctl cfr budget m used res cw ns stk c d plan m'.
     pl_cw_range nctl pl_plan_abs /\ rd_tab_apart hol_layout bw /\
     48 <= val cfr /\ val(d:int64) + 64 <= 2 EXP 64 /\
     drv_apart ctl (8 * nctl) d 64 /\ drv_apart (bw 58) (val(bw 59)) d 64 /\
     (!j. MEM j (tab_slots hol_layout) ==> drv_apart (bw j) (val(bw(j + 1))) d 64) /\
     (!a. ~drv_stack cfr a ==> m' a = drv_final d plan res a) /\
     ~(val budget < val used) /\ drv_sem abs_progs bw ctl budget cfr pl_handler_abs 0 m used res /\
     tab_rel hol_tables hol_layout inp bw ctl nctl cfr m (cw,ns,stk) /\ hol_inv (cw,ns,stk) /\
     rd_rel bw ctl nctl cfr m inp c
     ==> abs_record_post inp bw ctl nctl cfr budget used c m' (cw,ns,stk) res`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `!st. MEM st pl_handler_abs ==> tisa_leaf_wf(abs_progs(val(EL 0 st)))` ASSUME_TAC THENL
   [REWRITE_TAC[ABS_X86_LEAVES];ALL_TAC] THEN
  SUBGOAL_THEN `drv_apart (bw 54) (val(bw 55)) d 64` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `54` o check (fun th -> is_forall(concl th) &&
      tab_has_const "tab_slots" (concl th) && tab_has_const "drv_apart" (concl th))) THEN
    REWRITE_TAC[TAB_SLOTS_HOL;MEM] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[abs_record_post] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`abs_progs`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;
       `cfr:int64`;`m:int64->byte`;`used:int64`;`res:int64#num#(int64->byte)#int64`;
       `cw:num->num`;`ns:nstate`;`stk:num list`;`inp:num list`;`c:num`] ABS_HANDLER_GROWS) THEN
    ASM_REWRITE_TAC[ABS_X86_PROGS] THEN DISCH_THEN(X_CHOOSE_THEN `post:pstate` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `post:pstate` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TAB_REL_DRV_FINAL THEN
    MAP_EVERY EXISTS_TAC [`d:int64`;`plan:int64`;`res:int64#num#(int64->byte)#int64`] THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`abs_progs`;`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`pl_handler_abs`;
       `0`;`m:int64->byte`;`used:int64`;`res:int64#num#(int64->byte)#int64`] DRV_SEM_FUEL) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`abs_progs`;`bw:num->int64`;`ctl:int64`;`budget:int64`;`cfr:int64`;`pl_handler_abs`;
       `0`;`m:int64->byte`;`used:int64`;`res:int64#num#(int64->byte)#int64`] DRV_SEM_FUEL_BOUND) THEN
    ASM_REWRITE_TAC[GSYM NOT_LT];
    DISCH_TAC THEN
    let kc = SPECL [`bw:num->int64`;`ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`] ABS_NATIVE_KIND_CONTRACT in
    let applied = MP kc (CONJ (ASSUME `rd_tab_apart hol_layout bw`) (ASSUME `pl_cw_range nctl pl_plan_abs`)) in
    MP_TAC(SPECL [`m:int64->byte`;`used:int64`;`res:int64#num#(int64->byte)#int64`;`cw:num->num`;
      `ns:nstate`;`stk:num list`;`inp:num list`;`c:num`] (REWRITE_RULE[tab_kind_contract] applied)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `rec:holr_record` (X_CHOOSE_THEN `rest:num list` (X_CHOOSE_THEN `post:pstate` STRIP_ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`rec:holr_record`;`rest:num list`;`post:pstate`] THEN
    REPEAT CONJ_TAC THEN
    FIRST [REFL_TAC;FIRST_ASSUM ACCEPT_TAC;
      ((MATCH_MP_TAC TAB_REL_DRV_FINAL ORELSE MATCH_MP_TAC RD_REL_DRV_FINAL) THEN
       MAP_EVERY EXISTS_TAC [`d:int64`;`plan:int64`;`res:int64#num#(int64->byte)#int64`] THEN ASM_REWRITE_TAC[])]]);;

let ABS_HANDLER_X86 =
  let drv = abs_exact_driver `pl_handler_abs` in
  let admitted,ensures_tm = dest_imp(concl drv) in
  let h,args = strip_comb ensures_tm in
  let model,pre,post,frame = match args with
    | [model;pre;post;frame] -> model,pre,post,frame
    | _ -> failwith "ABS handler: expected ensures" in
  let state,body = dest_abs post in
  let receipt = find_term (fun tm -> is_exists tm &&
    can (find_term (is_const_app "drv_sem")) tm) body in
  let res,driver_post = dest_exists receipt in
  let cfr = `word_sub stackpointer (word 248):int64` in
  let memory = mk_comb(`read memory:x86state->int64->byte`,state) in
  let property = list_mk_comb(`abs_record_post`,
    [`inp:num list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;cfr;`budget:int64`;`used0:int64`;`c:num`;
     memory;`(cw,ns,stk):pstate`;res]) in
  let strengthened = mk_abs(state,subst [mk_exists(res,mk_conj(driver_post,property)),receipt] body) in
  let physical_pre =
    `pl_cw_range nctl pl_plan_abs /\ rd_tab_apart hol_layout bw /\ ~(val(budget:int64) < val(used0:int64)) /\
     (!j. MEM j (tab_slots hol_layout) ==> drv_apart (bw j) (val(bw(j + 1))) d 64) /\
     drv_apart (bw 58) (val(bw 59)) d 64 /\ hol_inv (cw,ns,stk) /\
     tab_rel hol_tables hol_layout inp bw ctl nctl (word_sub stackpointer (word 248)) m0 (cw,ns,stk) /\
     rd_rel bw ctl nctl (word_sub stackpointer (word 248)) m0 inp c` in
  let goal = mk_imp(mk_conj(admitted,physical_pre),list_mk_comb(h,[model;pre;strengthened;frame])) in
  GEN_ALL(prove(goal,
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "driver") STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC post THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `res:int64#num#(int64->byte)#int64` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
                    check (is_exists o concl)) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ABS_RECORD_RETURN THEN
      MAP_EVERY EXISTS_TAC [`m0:int64->byte`;`d:int64`;`plan:int64`] THEN
      USE_THEN "driver" (STRIP_ASSUME_TAC o REWRITE_RULE[drv_layout]) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC drv THEN USE_THEN "driver" ACCEPT_TAC]));;

let ABS_HANDLER_OVER_BUDGET = prove
 (`!progs bw ctl budget cfr m used res.
     val budget < val used /\ drv_sem progs bw ctl budget cfr pl_handler_abs 0 m used res
     ==> res = (word 3,0,m,used)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[ABS_HANDLER_WORDS;drv_sem] THEN ASM_REWRITE_TAC[]);;

let ABS_HANDLER_EXHAUSTED_X86 =
  let drv = abs_exact_driver `pl_handler_abs` in
  let admitted,ensures_tm = dest_imp(concl drv) in
  let h,args = strip_comb ensures_tm in
  let model,pre,post,frame = match args with
    | [model;pre;post;frame] -> model,pre,post,frame
    | _ -> failwith "ABS handler: expected ensures" in
  let state,body = dest_abs post in
  let receipt = find_term (fun tm -> is_exists tm && can (find_term (is_const_app "drv_sem")) tm) body in
  let res,driver_post = dest_exists receipt in
  let result = mk_eq(res,`(word 3,0,m0,used0):int64#num#(int64->byte)#int64`) in
  let strengthened = mk_abs(state,subst [mk_exists(res,mk_conj(driver_post,result)),receipt] body) in
  let goal = mk_imp(mk_conj(admitted,`val(budget:int64) < val(used0:int64)`),
                    list_mk_comb(h,[model;pre;strengthened;frame])) in
  GEN_ALL(prove(goal,
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "driver") ASSUME_TAC) THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC post THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `res:int64#num#(int64->byte)#int64` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
                    check (is_exists o concl)) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`abs_progs`;`bw:num->int64`;`ctl:int64`;`budget:int64`;
        `word_sub stackpointer (word 248):int64`;`m0:int64->byte`;`used0:int64`;
        `res:int64#num#(int64->byte)#int64`] ABS_HANDLER_OVER_BUDGET) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC drv THEN USE_THEN "driver" ACCEPT_TAC]));;
