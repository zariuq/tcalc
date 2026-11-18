(* A stored word agrees with a logical value across framed operations. *)
needs "native/hol/kernel_table_frames_load.ml";;

let tab_value_fact = new_definition
 `tab_value_fact j (value:S->num) (state:(num->num)#S#num list) <=>
    FST state j = value (FST(SND state))`;;

let TAB_PLAN_CONTROL_VALUE_KEPT = prove
 (`!(tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
        (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool))
    L inp progs bw ctl nctl budget cfr P i m used res before after j.
     drv_sem progs bw ctl budget cfr P i m used res /\
     tab_rel tb L inp bw ctl nctl cfr m before /\
     tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND res))) after /\
     tab_rd_plan_ok L progs nctl P /\ j < nctl /\
     (!st. MEM st P ==> ~(val(EL 17 st) = j))
     ==> FST after j = FST before j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TAB_REL_LAYOUT o check (is_const_app "tab_rel" o concl)) THEN
  MP_TAC(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
                     (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
                 `L:tabdesc list`;`inp:num list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`cfr:int64`;
                 `m:int64->byte`;`before:(num->num)#S#num list`;`j:num`] TAB_REL_CW) THEN
  MP_TAC(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
                     (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
                 `L:tabdesc list`;`inp:num list`;`bw:num->int64`;`ctl:int64`;`nctl:num`;`cfr:int64`;
                 `FST(SND(SND(res:int64#num#(int64->byte)#int64)))`;
                 `after:(num->num)#S#num list`;`j:num`] TAB_REL_CW) THEN
  MP_TAC(SPECL [`L:tabdesc list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
                `budget:int64`;`cfr:int64`;`P:(int64 list)list`;`i:num`;`m:int64->byte`;
                `used:int64`;`res:int64#num#(int64->byte)#int64`;`j:num`] TAB_PLAN_CW_KEPT) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let TAB_VALUE_FACT_FRAME = prove
 (`!(tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
        (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool))
    L inp progs bw ctl nctl budget cfr P i m used res before after j (value:S->num).
     drv_sem progs bw ctl budget cfr P i m used res /\
     tab_rel tb L inp bw ctl nctl cfr m before /\
     tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND res))) after /\
     tab_rd_plan_ok L progs nctl P /\ j < nctl /\
     (!st. MEM st P ==> ~(val(EL 17 st) = j)) /\
     value (FST(SND after)) = value (FST(SND before)) /\ tab_value_fact j value before
     ==> tab_value_fact j value after`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST(after:(num->num)#S#num list) j = FST(before:(num->num)#S#num list) j` ASSUME_TAC THENL
   [MATCH_MP_TAC TAB_PLAN_CONTROL_VALUE_KEPT THEN
    MAP_EVERY EXISTS_TAC
     [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
          (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
      `L:tabdesc list`;`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
      `budget:int64`;`cfr:int64`;`P:(int64 list)list`;`i:num`;`m:int64->byte`;`used:int64`;
      `res:int64#num#(int64->byte)#int64`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tab_value_fact]) THEN
  REWRITE_TAC[tab_value_fact] THEN ASM_MESON_TAC[]);;

let TAB_LIFTS_VALUE_FRAME = prove
 (`!(tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
        (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool))
    L PK P Q G Inv j (value:S->num).
     tab_lifts tb L PK P Q G Inv /\
     (!progs nctl. PK progs /\ pl_cw_range nctl P ==> tab_rd_plan_ok L progs nctl P) /\
     (!nctl. pl_cw_range nctl P ==> j < nctl) /\
     (!st. MEM st P ==> ~(val(EL 17 st) = j)) /\
     (!inp before following. Q inp before following
          ==> value following = value (FST(SND before)))
     ==> tab_lifts tb L PK P Q G (\state. Inv state /\ tab_value_fact j value state)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tab_lifts] THEN
  REPEAT GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;
                              `ctl:int64`;`nctl:num`;`budget:int64`;`cfr:int64`;`m:int64->byte`;
                              `used:int64`;`res:int64#num#(int64->byte)#int64`;
                              `s:(num->num)#S#num list`] o
    REWRITE_RULE[tab_lifts] o check (is_const_app "tab_lifts" o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    lhand(concl th) = `FST(res:int64#num#(int64->byte)#int64) = word 1`)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `after:(num->num)#S#num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `after:(num->num)#S#num list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC TAB_VALUE_FACT_FRAME THEN
  MAP_EVERY EXISTS_TAC
   [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#
        (num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
    `L:tabdesc list`;`inp:num list`;`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;`nctl:num`;
    `budget:int64`;`cfr:int64`;`P:(int64 list)list`;`0`;`m:int64->byte`;`used:int64`;
    `res:int64#num#(int64->byte)#int64`;`s:(num->num)#S#num list`] THEN ASM_MESON_TAC[]);;

let protected_value_frame_theorems =
 ["TAB_PLAN_CONTROL_VALUE_KEPT",TAB_PLAN_CONTROL_VALUE_KEPT;"TAB_VALUE_FACT_FRAME",TAB_VALUE_FACT_FRAME;
  "TAB_LIFTS_VALUE_FRAME",TAB_LIFTS_VALUE_FRAME];;
leaf_audit protected_value_frame_theorems protected_value_frame_theorems;;

(* Compose a concrete lift with its semantic and control-word frame proofs. *)
let tab_lift_small_value j value lf rdok nctl payloads kept =
  let tb,l,pk,p,q,g,inv = match snd(strip_comb(concl lf)) with
    [tb;l;pk;p;q;g;inv] -> tb,l,pk,p,q,g,inv | _ -> failwith "tab_lift_small_value: lift" in
  let th = ISPECL [tb;l;pk;p;q;g;inv;mk_small_numeral j;value] TAB_LIFTS_VALUE_FRAME in
  let premises = conjuncts(lhand(concl th)) in
  let bounded = prove(el 2 premises,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `nctl:num` nctl) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC) in
  let apart = prove(el 3 premises,
    GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `st:int64 list` payloads) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC) in
  MATCH_MP th (end_itlist CONJ [lf;rdok;bounded;apart;kept]);;
