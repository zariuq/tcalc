(* Handler composition over the shared frame and lift contracts. *)
needs "native/hol/kernel_table_frames_load.ml";;

let TAB_HANDLER_GEN = prove
 (`!(tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) L R pfx (D:num list->A->bool) W Ln PK P Q G Inv progs bw ctl nctl budget cfr m used res
    cw (s:S) stk inp c.
     tab_prefix_rd tb L R pfx D W Ln /\ (!bs v1 v2. D bs v1 /\ D bs v2 ==> v1 = v2) /\
     (!cw c s stk v. Inv (cw,s,stk) ==> Inv (W cw c v,s,stk)) /\ (!cw c v. W cw c v 17 = cw 17) /\
     (!cw s stk n. Inv (cw,s,stk) ==> Inv (pl_set cw 17 n,s,stk)) /\
     tab_lifts tb L PK P Q G Inv /\
     tab_rd_plan_ok L progs nctl P /\ rd_tab_apart L bw /\
     (!st. MEM st P ==> ~(17 <= val(EL 17 st) /\ val(EL 17 st) < 24)) /\
     PK progs /\ R progs /\ progs 3 = eqw /\ rd_progs_ok progs /\ pl_cw_range nctl P /\ 24 < nctl /\
     drv_sem progs bw ctl budget cfr (APPEND pfx (APPEND P pl_inc_cnt)) 0 m used res /\
     tab_rel tb L inp bw ctl nctl cfr m (cw,s,stk) /\ Inv (cw,s,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> (FST res = word 1
          ==> ?v s'. cw 20 = 1 /\ D (rd_from inp c) v /\ Q inp (W cw c v,s,stk) (FST(SND s')) /\
                     Inv s' /\ tab_rel tb L inp bw ctl nctl cfr (FST(SND(SND res))) s' /\
                     rd_rel bw ctl nctl cfr (FST(SND(SND res))) inp (c + Ln v) /\
                     FST s' 17 = cw 17 + 1 /\
                     (!j. 18 <= j /\ j < 24 ==> FST s' j = W cw c v j)) /\
         (FST res = word 0 <=>
          ~(cw 20 = 1) \/ (!v. ~D (rd_from inp c) v) \/ (?v. D (rd_from inp c) v /\ G inp (W cw c v,s,stk)))`,
  let r1 = `r1:int64#num#(int64->byte)#int64` and r2 = `r2:int64#num#(int64->byte)#int64` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[DRV_SEM_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN r1 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`inp:num list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                             `budget:int64`; `cfr:int64`; `0`; `m:int64->byte`; `used:int64`; r1; `cw:num->num`;
                             `s:S`; `stk:num list`; `c:num`] o
    REWRITE_RULE[tab_prefix_rd] o check (fun th -> is_const_app "tab_prefix_rd" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `FST(r1:int64#num#(int64->byte)#int64) = word 1` THENL
   [(* The prefix FIRED: the header checked, the operands v read. *)
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
                               lhand(concl th) = `FST(r1:int64#num#(int64->byte)#int64) = word 1` then
       X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC (MP th (ASSUME `FST(r1:int64#num#(int64->byte)#int64) = word 1`))
     else failwith "") THEN
    SUBGOAL_THEN `(cw:num->num) 20 = 1` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_iff(concl th) &&
         lhand(concl th) = `FST(r1:int64#num#(int64->byte)#int64) = word 1`
         then MP_TAC(EQ_MP th (ASSUME `FST(r1:int64#num#(int64->byte)#int64) = word 1`)) else failwith "") THEN
      SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `FST(r1:int64#num#(int64->byte)#int64) = word 1`;
                ASSUME `SND(SND(SND(r1:int64#num#(int64->byte)#int64))) = used`] THEN
    DISCH_THEN(X_CHOOSE_THEN r2 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MP_TAC(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`; `L:tabdesc list`; `PK:(num->tisa_prog)->bool`; `P:(int64 list)list`;
                  `Q:num list->(num->num)#S#num list->S->bool`; `G:num list->(num->num)#S#num list->bool`;
                  `Inv:(num->num)#S#num list->bool`; `inp:num list`;
                  `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                  `0 + LENGTH (pfx:(int64 list)list)`; `FST(SND(SND(r1:int64#num#(int64->byte)#int64)))`;
                  `used:int64`; r2; `((W:(num->num)->num->A->num->num) cw c v,s,stk):(num->num)#S#num list`;
                  `c + (Ln:A->num) v`] TAB_PLAN_IN_HANDLER) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC;
             FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
               can (find_term (fun t -> try fst(dest_var t) = "W" with Failure _ -> false)) (concl th) &&
               can (find_term (fun t -> try fst(dest_var t) = "Inv" with Failure _ -> false)) (concl th))) THEN
             FIRST_ASSUM ACCEPT_TAC;
             ASM_MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    ASM_CASES_TAC `FST(r2:int64#num#(int64->byte)#int64) = word 1` THENL
     [(* The plan FIRED: its final state, then the count's increment. *)
      FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
                                 lhand(concl th) = `FST(r2:int64#num#(int64->byte)#int64) = word 1` then
         MP_TAC(REWRITE_RULE[EXISTS_PAIR_THM]
           (MP th (ASSUME `FST(r2:int64#num#(int64->byte)#int64) = word 1`)))
       else failwith "") THEN
      REWRITE_TAC[FST; SND] THEN DISCH_THEN(RD_CHOOSE_ALL [`cw2:num->num`; `s2:S`; `stk2:num list`] STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[ASSUME `FST(r2:int64#num#(int64->byte)#int64) = word 1`] THEN
      REWRITE_TAC[pl_inc_cnt; drv_sem] THEN CONV_TAC STEP_EL_CONV THEN
      ASM_CASES_TAC `val(budget:int64) < val(SND(SND(SND(r2:int64#num#(int64->byte)#int64))))` THEN
      ASM_REWRITE_TAC[] THENL
       [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; WORD_SMALL_NE] THEN (THIN_INV_TAC THEN ASM_MESON_TAC[WORD_SMALL_NE]);
        ALL_TAC] THEN
      SUBGOAL_THEN `progs 32 = inc` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[rd_progs_ok]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t3:tisa_state` (X_CHOOSE_THEN `k3:num` (X_CHOOSE_THEN `u3:tisa_state`
        STRIP_ASSUME_TAC))) THEN
      MP_TAC(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`; `L:tabdesc list`; `inp:num list`;
                     `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_inc_cnt_st;
                     `FST(SND(SND(r2:int64#num#(int64->byte)#int64)))`;
                     `SND(SND(SND(r2:int64#num#(int64->byte)#int64)))`;
                     `t3:tisa_state`; `k3:num`; `u3:tisa_state`; `cw2:num->num`; `s2:S`; `stk2:num list`;
                     `c + (Ln:A->num) v`] TAB_STEP_INC) THEN
      CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `cw2:num->num`)) (concl th)
                            then ASSUME_TAC(MP (SPEC `17` th) (ARITH_RULE `17 <= 17 /\ 17 < 24`)) else failwith "") THEN
      SUBGOAL_THEN `(cw2:num->num) 17 = cw 17` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(cw:num->num) 17 + 1 < 4611686018427387904` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
      TRY(FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `val(tisa_fword u3 19)`
                                then RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "")) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th) &&
         can (find_term ((=) `res:int64#num#(int64->byte)#int64`)) (concl th))) THEN
      ASM_REWRITE_TAC[WORD_SMALL_NE] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND; WORD_SMALL_NE] THENL
       [CONJ_TAC THENL
         [EXISTS_TAC `v:A` THEN
          EXISTS_TAC `(pl_set cw2 17 (cw 17 + 1),s2,stk2):(num->num)#S#num list` THEN
          ASM_REWRITE_TAC[FST; SND] THEN CONJ_TAC THENL
           [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
              can (find_term (fun t -> try fst(dest_var t) = "Inv" with Failure _ -> false)) (concl th) &&
              can (find_term ((=) `17`)) (concl th))) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
          CONJ_TAC THENL [REWRITE_TAC[pl_set]; ALL_TAC] THEN
          X_GEN_TAC `j:num` THEN STRIP_TAC THEN
          ASM_SIMP_TAC[pl_set; ARITH_RULE `18 <= j ==> ~(j = 17)`] THEN
          FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `cw2:num->num`)) (concl th))) THEN ASM_ARITH_TAC;
          (THIN_INV_TAC THEN ASM_MESON_TAC[WORD_SMALL_NE])];
        (THIN_INV_TAC THEN ASM_MESON_TAC[WORD_SMALL_NE])];
      (* The plan did not FIRE: the handler's outcome is the plan's. *)
      REWRITE_TAC[ASSUME `~(FST(r2:int64#num#(int64->byte)#int64) = word 1)`] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[] THEN (THIN_INV_TAC THEN ASM_MESON_TAC[WORD_SMALL_NE])];
    (* The prefix did not FIRE: the handler's outcome is the prefix's. *)
    REWRITE_TAC[ASSUME `~(FST(r1:int64#num#(int64->byte)#int64) = word 1)`] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[] THEN THIN_INV_TAC THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Operand prefixes over the tables: the one-operand prefix to OP0, and one  *)
(* more LEB operand appended to any prefix, so operands compose one by one.  *)
(* ------------------------------------------------------------------------- *)

(* One operand, read to OP0: the prefix's writes and length. *)
let OP0_WC = `\(cw:num->num) (c:num) (t:num). pl_set (pl_set cw 24 1) 8 t`;;

let TAB_PREFIX_OP0_RD = prove
 (list_mk_forall([`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
                  `L:tabdesc list`; `R:(num->tisa_prog)->bool`],
   list_mk_icomb "tab_prefix_rd" [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
                                  `L:tabdesc list`; `R:(num->tisa_prog)->bool`; `pl_prefix_op0`; `leb_fires`;
                                  OP0_WC; OP0_L]),
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_prefix_rd] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MP_TAC(SPEC_ALL(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
                          `L:tabdesc list`] PREFIX_OP0_TAB)) THEN
  ASM_REWRITE_TAC[]);;

let tab_enc_reads = new_definition
 `tab_enc_reads (tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) L (R:(num->tisa_prog)->bool) pfx (ok:A->bool) (E:A->num list)
                (W:(num->num)->num->A->num->num) <=>
    tab_prefix_rd tb L R pfx (\bs v. ok v /\ ?rest. bs = APPEND (E v) rest) W (\v. LENGTH (E v))`;;

let tab_w_snoc = new_definition
 `tab_w_snoc (W:(num->num)->num->A->num->num) k cw c (p:A#num) = pl_set (W cw c (FST p)) k (SND p)`;;

let TAB_ENC_READS_SNOC_GOAL =
  let body = subst [pl_leb_step_tm, `stp:int64 list`]
   `tab_enc_reads (tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) L R pfx (ok:A->bool) E W /\ enc_unique ok E /\ 6 < k /\ k < 24
     ==> tab_enc_reads tb L R (APPEND pfx [stp]) (ok_snoc ok) (enc_snoc E) (tab_w_snoc W k)` in
  list_mk_forall([`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`; `L:tabdesc list`; `R:(num->tisa_prog)->bool`;
                  `pfx:(int64 list)list`; `ok:A->bool`; `E:A->num list`;
                  `W:(num->num)->num->A->num->num`; `k:num`], body);;

let TAB_ENC_READS_SNOC = prove(TAB_ENC_READS_SNOC_GOAL,
  let r1 = `r1:int64#num#(int64->byte)#int64` in
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_enc_reads; tab_prefix_rd] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXISTS_PAIR_THM; ok_snoc; enc_snoc; tab_w_snoc; FST; SND] THEN
  (* the prefix, then the step *)
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN REWRITE_TAC[DRV_SEM_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN r1 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`inp:num list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
     `budget:int64`; `cfr:int64`; `i:num`; `m:int64->byte`; `used:int64`; r1; `cw:num->num`;
     `s:S`; `stk:num list`; `c:num`] o
     check (fun th -> is_forall(concl th) && can (find_term ((=) `pfx:(int64 list)list`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC (mk_eq(mk_icomb(`FST:A#B->A`, r1), `word 1:int64`)) THENL
   [ALL_TAC;
    (* the prefix did not FIRE: the outcome is its *)
    REWRITE_TAC[ASSUME (mk_neg(mk_eq(mk_icomb(`FST:A#B->A`, r1), `word 1:int64`)))] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[SNOC_PREFIX]] THEN
  FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = mk_eq(mk_icomb(`FST:A#B->A`, r1), `word 1:int64`)
     then MP_TAC (MP th (ASSUME (mk_eq(mk_icomb(`FST:A#B->A`, r1), `word 1:int64`)))) else failwith "") THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A` (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `rest1:num list`))
            (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN `(cw:num->num) 20 = 1` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RD_FROM_APPEND o check (fun th -> is_eq(concl th) &&
     can (find_term ((=) `rest1:num list`)) (concl th))) THEN
  REWRITE_TAC[ASSUME (mk_eq(mk_icomb(`FST:A#B->A`, r1), `word 1:int64`));
              ASSUME `SND(SND(SND(r1:int64#num#(int64->byte)#int64))) = used`] THEN
  REWRITE_TAC[drv_sem] THEN CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[rd_progs_ok]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`; `L:tabdesc list`; `inp:num list`;
                 `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_leb_step_tm;
                 `FST(SND(SND(r1:int64#num#(int64->byte)#int64)))`; `used:int64`; `t2:tisa_state`; `k2:num`;
                 `u2:tisa_state`; `(W:(num->num)->num->A->num->num) cw c v`; `s:S`; `stk:num list`;
                 `c + LENGTH((E:A->num list) v)`] TAB_STEP_LEB) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC))) THEN
  TRY(FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `val(tisa_fword u2 19)`
                            then RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "")) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THENL
   [(* the step FIRED with b: the tuple (v, b) *)
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [leb_fires] o check (fun th -> is_const_app "leb_fires" (concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `rest2:num list`)) THEN
    SUBGOAL_THEN `rd_from inp c = APPEND (APPEND ((E:A->num list) v) (leb_enc b)) rest2` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM APPEND_ASSOC]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[LENGTH_APPEND; ADD_ASSOC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `b < 4611686018427387904` ASSUME_TAC THENL
     [UNDISCH_TAC `b < 2 EXP 62` THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN MAP_EVERY EXISTS_TAC [`v:A`; `b:num`] THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN EXISTS_TAC `rest2:num list` THEN REFL_TAC;
    (* the step REFUSED: no second operand, so no tuple *)
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p1:A) = v` SUBST_ALL_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[enc_unique] o check (fun th -> is_const_app "enc_unique" (concl th))) THEN
      MAP_EVERY EXISTS_TAC [`APPEND (leb_enc p2) rest`; `rd_from inp (c + LENGTH((E:A->num list) v))`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && can (find_term ((=) `rest:num list`)) (concl th))) THEN
    REWRITE_TAC[APPEND_LCANCEL] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p2:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (is_const_app "leb_fires")) (concl th))) THEN
    REWRITE_TAC[leb_fires] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[]]);;

(* NAME's operand prefix, with skip at leaf 28: the name's bytes v decoded;  *)
(* the writes and the cursor's advance are its length's and its bytes'.     *)
let NAME_WC = `\(cw:num->num) (c:num) (v:num list).
  pl_set (pl_set (pl_set (pl_set cw 24 1) 9 (LENGTH v)) 8 (c + LENGTH(leb_enc(LENGTH v))))
         24 ((c + LENGTH(leb_enc(LENGTH v))) + LENGTH v)`;;
let NAME_L = `\v:num list. LENGTH(leb_enc(LENGTH v)) + LENGTH v`;;

let TAB_PREFIX_NAME_RD = prove
 (list_mk_forall([`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
                  `L:tabdesc list`],
   list_mk_icomb "tab_prefix_rd" [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
                                  `L:tabdesc list`; `\progs:num->tisa_prog. progs 28 = skip`; `pl_prefix_name`;
                                  `name_fires`; NAME_WC; NAME_L]),
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_prefix_rd] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ADD_ASSOC] THEN
  MP_TAC(SPEC_ALL(ISPECL [`tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)`;
                          `L:tabdesc list`] PREFIX_NAME_TAB)) THEN
  ASM_REWRITE_TAC[]);;

(* Every theorem this file states, for the audits. *)
let handlers_tab_theorems =
 ["TAB_PLAN_CW_KEPT", TAB_PLAN_CW_KEPT; "TAB_REL_LAYOUT", TAB_REL_LAYOUT; "TAB_REL_CW", TAB_REL_CW; "TAB_PLAN_IN_HANDLER", TAB_PLAN_IN_HANDLER; "TAB_HANDLER_GEN", TAB_HANDLER_GEN; "TAB_PREFIX_RD_MONO", TAB_PREFIX_RD_MONO;
  "TAB_PREFIX_OP0_RD", TAB_PREFIX_OP0_RD; "TAB_ENC_READS_SNOC", TAB_ENC_READS_SNOC;
  "TAB_PREFIX_NAME_RD", TAB_PREFIX_NAME_RD];;
