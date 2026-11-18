(* Driver loop facts for the generalized physical stack relation. *)
needs "native/driver/stack_driver_call_memory.ml";;

let STACK_DRV_STATIC_READ_TAC sname x b len k =
  let s = mk_var(sname, `:x86state`) in
  let goal = subst [s, `s:x86state`; x, `x:int64`]
               `read (memory :> bytes64 x) s = drv_word m0 x` in
  SUBGOAL_THEN goal ASSUME_TAC THENL
   [MATCH_MP_TAC STACK_DRV_READ_STATIC THEN
    MAP_EVERY EXISTS_TAC [`reserve:num`; `M:int64->byte`; `cfr:int64`;
                          `drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC STACK_DRV_AREA_BYTES THEN MAP_EVERY EXISTS_TAC [b; len; k] THEN
    ASM_REWRITE_TAC[] THEN DRV_SIDE_TAC;
    ALL_TAC];;

let STACK_DRV_LOADED_TAC sname p mc len =
  let s = mk_var(sname, `:x86state`) in
  SUBGOAL_THEN (list_mk_comb(`bytes_loaded`, [s; mk_comb(`word:num->int64`, p); mc])) ASSUME_TAC THENL
   [MATCH_MP_TAC DRV_LOADED_CODE THEN EXISTS_TAC `m0:int64->byte` THEN
    REWRITE_TAC[COMPUTE_LENGTH_RULE drv_mc] THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    SUBGOAL_THEN (subst [s, `s:x86state`] `read memory s a = M a`) SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `stack_drv_stack reserve`)) (concl th) &&
                                                     is_forall(concl th))) THEN
      MATCH_MP_TAC STACK_DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [mk_comb(`word:num->int64`, p); len] THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `drv_static`)) (concl th) &&
                                                     is_forall(concl th))) THEN
      REWRITE_TAC[drv_static] THEN ASM_REWRITE_TAC[]];
    ALL_TAC];;

let stack_drv_fact_th static b len k (asl,w) =
  let lem =
    if static then ISPECL [`reserve:num`; `s0:x86state`; `M:int64->byte`; `m0:int64->byte`; static_P; `cfr:int64`; b; len; k]
                     STACK_DRV_AREA_READ_STATIC
    else ISPECL [`reserve:num`; `s0:x86state`; `M:int64->byte`; `cfr:int64`; b; len; k] STACK_DRV_AREA_READ in
  let ant = lhand(concl lem) in
  MP lem (TAC_PROOF((asl, ant), DRV_ANTS_TAC));;

let STACK_DRV_DESC_FACTS_TAC =
  W(fun (asl,w) ->
    MAP_EVERY (fun k ->
      let th = stack_drv_fact_th true `d:int64` `64` (mk_small_numeral k) (asl,w) in
      let eqs = mapfilter (fun (_,a) -> let c = concl a in
                  if is_eq c && (match lhs c with Comb(Comb(Const("drv_word",_),Var("m0",_)),_) -> true | _ -> false)
                  then a else failwith "") asl in
      STRIP_ASSUME_TAC (REWRITE_RULE eqs th)) [8; 16; 24; 32; 40]);;

let STACK_DRV_PLAN_FACTS_TAC =
  W(fun (asl,w) ->
    let hp = find_assum holds_plan_tm asl in
    let hi = find_assum `EL i stepl = h:int64 list` asl in
    let stp_eq = find_assum `word_add plan (word(144 * i)):int64 = stp` asl in
    let ilt = find_assum `i < ns` asl in
    MAP_EVERY (fun f ->
      let k = if f = 0 then `144 * i` else nadd `144 * i` (mul8 (mk_small_numeral f)) in
      let th = stack_drv_fact_th true `plan:int64` `144 * ns` k (asl,w) in
      let v = MP (SPECL [`i:num`; mk_small_numeral f] hp)
                 (CONJ ilt (EQT_ELIM(NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral f) `18`)))) in
      let v = CONV_RULE (REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES] THENC NUM_REDUCE_CONV) v in
      let th = CONV_RULE (NUM_REDUCE_CONV THENC REWRITE_CONV[v; hi]) th in
      let th = CONV_RULE (REWRITE_CONV[GSYM DRV_ADDR_ASSOC] THENC REWRITE_CONV[stp_eq]) th in
      STRIP_ASSUME_TAC th) (0--17));;

let STACK_DRV_BIND_FACTS_TAC =
  W(fun (asl,w) ->
    let hb = find_assum holds_bind_tm asl in
    MAP_EVERY (fun r ->
      let wv = val_tm (el_h (r + 1)) in
      let k1 = mul8 wv and k2 = nadd (mul8 wv) `8` in
      let th1 = stack_drv_fact_th true `bind:int64` `8 * nbw` k1 (asl,w) in
      let th2 = stack_drv_fact_th true `bind:int64` `8 * nbw` k2 (asl,w) in
      let v1 = MP (SPEC wv hb) (drv_arith (mk_binop `(<):num->num->bool` wv `nbw:num`) (asl,w)) in
      let v2 = MP (SPEC (nadd wv `1`) hb) (drv_arith (mk_binop `(<):num->num->bool` (nadd wv `1`) `nbw:num`) (asl,w)) in
      let v2 = REWRITE_RULE[ARITH_RULE `8 * (x + 1) = 8 * x + 8`] v2 in
      STRIP_ASSUME_TAC (REWRITE_RULE[v1] th1) THEN STRIP_ASSUME_TAC (REWRITE_RULE[v2] th2)) (0--8));;

let STACK_DRV_LEAF_FACTS_TAC =
  W(fun (asl,w) ->
    let hl = find_assum holds_leaf_tm asl in
    let jv = val_tm (el_h 0) in
    let th = stack_drv_fact_th true `leaves:int64` `8 * nl` (mul8 jv) (asl,w) in
    let v = MP (SPEC jv hl) (drv_arith (mk_binop `(<):num->num->bool` jv `nl:num`) (asl,w)) in
    STRIP_ASSUME_TAC (REWRITE_RULE[v] th));;

let STACK_DRV_CTL_FACTS_TAC =
  W(fun (asl,w) ->
    MAP_EVERY (fun f ->
      STRIP_ASSUME_TAC (stack_drv_fact_th false `ctl:int64` `8 * nctl` (mul8 (val_tm (el_h f))) (asl,w))) (10--17));;

let STACK_DRV_M1_TAC =
  ABBREV_TAC `stp = word_add plan (word(144 * i)):int64` THEN
  SUBGOAL_THEN `val(stp:int64) = val(plan:int64) + 144 * i` ASSUME_TAC THENL
   [EXPAND_TAC "stp" THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  STACK_DRV_LOADED_TAC "s0" `pc:num` `drv_mc` `522` THEN
  DRV_INST_TAC `!r. r < 9 ==> val(EL (1 + r) (h:int64 list)) + 1 < nbw` (0--8) THEN
  DRV_INST_TAC `!f. 10 <= f /\ f < 18 ==> val(EL f (h:int64 list)) < nctl` (10--17) THEN
  STACK_DRV_DESC_FACTS_TAC THEN STACK_DRV_PLAN_FACTS_TAC THEN STACK_DRV_BIND_FACTS_TAC THEN STACK_DRV_CTL_FACTS_TAC THEN
  STACK_DRV_LEAF_FACTS_TAC THEN DRV_CODE_FACTS_TAC THEN DRV_FUEL_OK_TAC THEN
  X86_STEPS_TAC DRV_EXEC (1--5);;

let STACK_DRV_M6_COMMON_TAC =
  SUBGOAL_THEN `!a. ~stack_drv_stack reserve cfr a ==> read memory s8 a = drv_after ctl (h:int64 list) u a` ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `read memory s8` then REWRITE_TAC[th]
                          else failwith "") THEN
    REWRITE_TAC[drv_after] THEN
    MP_TAC(ISPECL [`\a:int64. ~stack_drv_stack reserve cfr a`; `m1:int64->byte`; `tmem u`; drv_cx; `tisa_fword u 19`]
                  DRV_WRITE_CONG) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [X_GEN_TAC `b:int64` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term ((=) `component_stack_saved reserve`)) (concl th) && can (find_term ((=) `m1:int64->byte`)) (concl th))) THEN
      MATCH_MP_TAC STACK_DRV_NOT_SAVED THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `read memory s8`)) THEN
  SUBGOAL_THEN `!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a
                    ==> drv_after ctl (h:int64 list) u a = (m0:int64->byte) a` ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN REWRITE_TAC[drv_after] THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `val(word_add ctl (word(8 * val(EL 17 (h:int64 list)))):int64) =
                      val ctl + 8 * val(EL 17 h)` SUBST1_TAC THENL
         [MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC; DRV_ARITH_TAC];
        MATCH_MP_TAC DRV_CTL_NOT_STATIC THEN
        MAP_EVERY EXISTS_TAC [`pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `nctl:num`; `bind:int64`;
                              `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`] THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `~stack_drv_stack reserve cfr a` ASSUME_TAC THENL
     [MATCH_MP_TAC STACK_DRV_STATIC_NOT_STACK THEN
      MAP_EVERY EXISTS_TAC [`pc:num`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`; `nctl:num`; `bind:int64`;
                            `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(m1:int64->byte) a = tmem u a` (fun th -> REWRITE_TAC[SYM th]) THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term ((=) `component_stack_saved reserve`)) (concl th) && can (find_term ((=) `m1:int64->byte`)) (concl th))) THEN
      MATCH_MP_TAC STACK_DRV_NOT_SAVED THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term ((=) `drv_static`)) (concl th) && can (find_term ((=) `m1:int64->byte`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC];;


let STACK_DRV_TOP_PRO_TAC =
  MP_TAC(SPECL [`pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `used0:int64`; `rbxv:int64`; `rbpv:int64`;
                `r12v:int64`; `r13v:int64`; `r14v:int64`; `r15v:int64`; `m0:int64->byte`] DRV_PROLOGUE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DRV_ARITH_TAC;
      DRV_APART_TAC `word_sub cfr (word 48):int64` `304` `word pc:int64` `522` `48` `0`;
      DRV_APART_TAC `word_sub cfr (word 48):int64` `304` `d:int64` `64` `48` `0`];
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP DRV_ENSURES_WEAKEN)] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[DRV_READ64] THEN
    MATCH_MP_TAC DRV_LOADED_CODE THEN EXISTS_TAC `m0:int64->byte` THEN
    ASM_REWRITE_TAC[COMPUTE_LENGTH_RULE drv_mc];
    X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN ASM_MESON_TAC[STACK_DRV_STACK_LEGACY];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

let STACK_DRV_TOP_EPI_PRE_TAC =
  X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DRV_LOADED_CODE THEN EXISTS_TAC `m0:int64->byte` THEN
    ASM_REWRITE_TAC[COMPUTE_LENGTH_RULE drv_mc] THEN X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~stack_drv_stack reserve cfr a /\ drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC STACK_DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [`word pc:int64`; `522`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[drv_static] THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[]];
    REWRITE_TAC[DRV_READ64] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `ret:int64`)) THEN
    MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`reserve:num`; `pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `bind:int64`; `nbw:num`;
                  `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`; `i:num`] STACK_DRV_RET_SLOT) THEN
    ASM_SIMP_TAC[]];;

let STACK_DRV_TOP_EPI_POST_TAC =
  X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN REWRITE_TAC[drv_final] THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\a:int64. ~stack_drv_stack reserve cfr a`;
       `write (bytes64 (word_add d (word 48))) (SND(SND(SND(res:int64#num#(int64->byte)#int64)))) (m:int64->byte)`;
       `write (bytes64 (word_add d (word 48))) (SND(SND(SND(res:int64#num#(int64->byte)#int64))))
              (FST(SND(SND(res:int64#num#(int64->byte)#int64))))`;
       `word_add d (word 56):int64`;
       `word_add plan (word(144 * FST(SND(res:int64#num#(int64->byte)#int64)))):int64`] DRV_WRITE_CONG)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(BETA_RULE(ISPECL
        [`\a:int64. ~stack_drv_stack reserve cfr a`; `m:int64->byte`;
         `FST(SND(SND(res:int64#num#(int64->byte)#int64)))`; `word_add d (word 48):int64`;
         `SND(SND(SND(res:int64#num#(int64->byte)#int64)))`] DRV_WRITE_CONG)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
    SUBGOAL_THEN `val(a:int64) < val(d:int64) + 48 \/ val d + 64 <= val a` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
                                              can (find_term ((=) `drv_in`)) (concl th))) THEN
      REWRITE_TAC[drv_in] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
           ANTS_TAC THENL
            [ASM_REWRITE_TAC[] THEN
             FIRST_ASSUM(MP_TAC o check (fun th -> is_disj(concl th) &&
                                                   can (find_term ((=) `val(a:int64)`)) (concl th))) THEN
             DRV_ARITH_TAC;
             DISCH_THEN SUBST1_TAC]) THEN
    SUBGOAL_THEN `~stack_drv_stack reserve cfr a` ASSUME_TAC THENL
     [MATCH_MP_TAC STACK_DRV_STATIC_NOT_STACK THEN
      MAP_EVERY EXISTS_TAC [`pc:num`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`; `nctl:num`;
                            `bind:int64`; `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`;
                            `lmc:num->byte list`] THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]]];;
