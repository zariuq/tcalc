(* ========================================================================= *)
(* Handlers by composition. A record plan P whose driver run, under plan_rel *)
(* and pl_inv, does Q when it FIRES and is REFUSED exactly when G           *)
(* (plan_lifts P Q G pend, pend the leaves not yet built, whose             *)
(* implementations stay premises) keeps the reader's relation inside a      *)
(* handler (PLAN_IN_HANDLER). An operand prefix that checks the header and  *)
(* reads an operand tuple (prefix_reads) composes with any lifted plan and  *)
(* the count's increment into the handler's theorem (HANDLER_GEN). Prefixes *)
(* of numeric operands are the one-operand prefix extended by one leb_next  *)
(* step per operand (ENC_READS_SNOC).                                        *)
(*                                                                           *)
(* Loaded after reader_end.ml.                                               *)
(* ========================================================================= *)

needs "native/hol/reader_end.ml";;

(* The native state's ten components (RD_NS_VARS ends with the stack). *)
let pl_ns_vars = butlast RD_NS_VARS;;

let plan_lifts = new_definition
 `plan_lifts P (Q:pstate->nstate->bool) (G:pstate->bool) (pend:num list) <=>
    !progs bw ctl nctl budget cfr m used res s.
      ALL (pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr P) pend /\
      pl_progs_ok progs /\ pl_cw_range nctl P /\
      drv_sem progs bw ctl budget cfr P 0 m used res /\
      plan_rel bw ctl nctl cfr m s /\ ~(val budget < val used) /\ pl_inv s
      ==> (FST res = word 1
           ==> ?s'. (Q s (FST(SND s')) /\ pl_inv s') /\ plan_rel bw ctl nctl cfr (FST(SND(SND res))) s') /\
          (FST res = word 0 <=> G s)`;;

let PL_REL_LAYOUT = prove
 (`!bw ctl nctl cfr m s. plan_rel bw ctl nctl cfr m s ==> pl_layout bw ctl nctl cfr`,
  REWRITE_TAC[FORALL_PAIR_THM; plan_rel] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* A lifted plan inside a handler: from any step index, the reader's state  *)
(* kept and the control words below 24 kept.                                 *)
let PLAN_IN_HANDLER = prove
 (`!P Q G pend progs bw ctl nctl budget cfr i m used r s inp c.
     plan_lifts P Q G pend /\ ALL (pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr P) pend /\
     rd_plan_ok progs nctl P /\ (!st. MEM st P ==> 24 <= val(EL 17 st)) /\
     pl_progs_ok progs /\ pl_cw_range nctl P /\ 24 < nctl /\
     drv_sem progs bw ctl budget cfr P i m used r /\
     plan_rel bw ctl nctl cfr m s /\ pl_inv s /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp c /\
         (FST r = word 1
          ==> ?s'. Q s (FST(SND s')) /\ pl_inv s' /\ plan_rel bw ctl nctl cfr (FST(SND(SND r))) s' /\
                   (!j. j < 24 ==> FST s' j = FST s j)) /\
         (FST r = word 0 <=> G s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_REL_LAYOUT) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RD_PLAN_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`progs:num->tisa_prog`; `budget:int64`; `P:(int64 list)list`; `i:num`;
                          `m:int64->byte`; `used:int64`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `r0:int64#num#(int64->byte)#int64` STRIP_ASSUME_TAC o MATCH_MP DRV_SEM_AT0 o
    check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                             `cfr:int64`; `m:int64->byte`; `used:int64`; `r0:int64#num#(int64->byte)#int64`;
                             `s:pstate`] o
    REWRITE_RULE[plan_lifts] o check (fun th -> is_const_app "plan_lifts" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FST(SND(SND(r0:int64#num#(int64->byte)#int64))) = FST(SND(SND(r:int64#num#(int64->byte)#int64)))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_eq(lhand(concl th)))) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s':pstate` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`;
                `FST(SND(SND(r:int64#num#(int64->byte)#int64)))`; `s':pstate`; `j:num`] PL_REL_CW) THEN
  MP_TAC(SPECL [`bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `m:int64->byte`; `s:pstate`; `j:num`]
               PL_REL_CW) THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                `P:(int64 list)list`; `i:num`; `m:int64->byte`; `used:int64`;
                `r:int64#num#(int64->byte)#int64`; `j:num`] PL_PLAN_CW_KEPT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `j < nctl` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `!x j. j < 24 /\ 24 <= x ==> ~(x = j)`) THEN ASM_SIMP_TAC[];
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The operand prefix as a parameter. prefix_reads pfx D W L: the prefix    *)
(* pfx checks the header and reads an operand tuple v that the bytes at the *)
(* cursor decode to (D), leaving the control words W cw v and the cursor   *)
(* L v bytes on. HANDLER_GEN composes any such prefix with any lifted plan *)
(* and the count's increment.                                               *)
(* ------------------------------------------------------------------------- *)

let prefix_reads = new_definition
 `prefix_reads pfx (D:num list->A->bool) (W:(num->num)->A->num->num) (L:A->num) <=>
    !progs bw ctl nctl budget cfr i m used r cw ns stk inp c.
      progs 3 = eqw /\ rd_progs_ok progs /\ 24 < nctl /\
      drv_sem progs bw ctl budget cfr pfx i m used r /\
      plan_rel bw ctl nctl cfr m (cw,ns,stk) /\ rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
      ==> SND(SND(SND r)) = used /\
          (FST r = word 1 <=> cw 20 = 1 /\ ?v. D (rd_from inp c) v) /\
          (FST r = word 0 <=> ~(cw 20 = 1 /\ ?v. D (rd_from inp c) v)) /\
          (FST r = word 1
           ==> ?v. D (rd_from inp c) v /\
                   plan_rel bw ctl nctl cfr (FST(SND(SND r))) (W cw v,ns,stk) /\
                   rd_rel bw ctl nctl cfr (FST(SND(SND r))) inp (c + L v))`;;

let HANDLER_GEN = prove
 (`!pfx (D:num list->A->bool) W L P Q G pend progs bw ctl nctl budget cfr m used res cw ns stk inp c.
     prefix_reads pfx D W L /\ (!bs v1 v2. D bs v1 /\ D bs v2 ==> v1 = v2) /\
     (!cw ns stk v. pl_inv (cw,ns,stk) ==> pl_inv (W cw v,ns,stk)) /\ (!cw v. W cw v 17 = cw 17) /\
     plan_lifts P Q G pend /\ ALL (pl_leaf_impl (plan_rel bw ctl nctl cfr) progs bw ctl budget cfr P) pend /\
     rd_plan_ok progs nctl P /\ (!st. MEM st P ==> 24 <= val(EL 17 st)) /\
     pl_progs_ok progs /\ rd_progs_ok progs /\ pl_cw_range nctl P /\ 24 < nctl /\
     drv_sem progs bw ctl budget cfr (APPEND pfx (APPEND P pl_inc_cnt)) 0 m used res /\
     plan_rel bw ctl nctl cfr m (cw,ns,stk) /\ pl_inv (cw,ns,stk) /\
     rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
     ==> (FST res = word 1
          ==> ?v s'. cw 20 = 1 /\ D (rd_from inp c) v /\ Q (W cw v,ns,stk) (FST(SND s')) /\
                     pl_inv s' /\ plan_rel bw ctl nctl cfr (FST(SND(SND res))) s' /\
                     rd_rel bw ctl nctl cfr (FST(SND(SND res))) inp (c + L v) /\
                     FST s' 17 = cw 17 + 1 /\
                     (!j. j < 24 /\ ~(j = 17) ==> FST s' j = W cw v j)) /\
         (FST res = word 0 <=>
          ~(cw 20 = 1) \/ (!v. ~D (rd_from inp c) v) \/ (?v. D (rd_from inp c) v /\ G (W cw v,ns,stk)))`,
  let r1 = `r1:int64#num#(int64->byte)#int64` and r2 = `r2:int64#num#(int64->byte)#int64` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `progs 3 = eqw` ASSUME_TAC THENL [ASM_MESON_TAC[pl_progs_ok]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN
  REWRITE_TAC[DRV_SEM_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN r1 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                             `cfr:int64`; `0`; `m:int64->byte`; `used:int64`; r1; `cw:num->num`; `ns:nstate`;
                             `stk:num list`; `inp:num list`; `c:num`] o
    REWRITE_RULE[prefix_reads] o check (fun th -> is_const_app "prefix_reads" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `FST(r1:int64#num#(int64->byte)#int64) = word 1` THENL
   [(* The prefix FIRED: the header checked, the operands v read. *)
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
                               lhand(concl th) = `FST(r1:int64#num#(int64->byte)#int64) = word 1` then
       X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC (MP th (ASSUME `FST(r1:int64#num#(int64->byte)#int64) = word 1`))
     else failwith "") THEN
    SUBGOAL_THEN `(cw:num->num) 20 = 1` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `FST(r1:int64#num#(int64->byte)#int64) = word 1`;
                ASSUME `SND(SND(SND(r1:int64#num#(int64->byte)#int64))) = used`] THEN
    DISCH_THEN(X_CHOOSE_THEN r2 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MP_TAC(SPECL [`P:(int64 list)list`; `Q:pstate->nstate->bool`; `G:pstate->bool`; `pend:num list`;
                  `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`;
                  `0 + LENGTH (pfx:(int64 list)list)`; `FST(SND(SND(r1:int64#num#(int64->byte)#int64)))`;
                  `used:int64`; r2; `((W:(num->num)->A->num->num) cw v,ns,stk):pstate`;
                  `inp:num list`; `c + (L:A->num) v`] PLAN_IN_HANDLER) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    ASM_CASES_TAC `FST(r2:int64#num#(int64->byte)#int64) = word 1` THENL
     [(* The plan FIRED: its final state, then the count's increment. *)
      FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
                                 lhand(concl th) = `FST(r2:int64#num#(int64->byte)#int64) = word 1` then
         MP_TAC(REWRITE_RULE[EXISTS_PAIR_THM]
           (MP th (ASSUME `FST(r2:int64#num#(int64->byte)#int64) = word 1`)))
       else failwith "") THEN
      REWRITE_TAC[FST; SND] THEN DISCH_THEN(RD_CHOOSE_ALL RD_S2_VARS STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[ASSUME `FST(r2:int64#num#(int64->byte)#int64) = word 1`] THEN
      REWRITE_TAC[pl_inc_cnt; drv_sem] THEN CONV_TAC STEP_EL_CONV THEN
      ASM_CASES_TAC `val(budget:int64) < val(SND(SND(SND(r2:int64#num#(int64->byte)#int64))))` THEN
      ASM_REWRITE_TAC[] THENL
       [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; WORD_SMALL_NE] THEN ASM_MESON_TAC[WORD_SMALL_NE];
        ALL_TAC] THEN
      SUBGOAL_THEN `progs 32 = inc` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[rd_progs_ok]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t3:tisa_state` (X_CHOOSE_THEN `k3:num` (X_CHOOSE_THEN `u3:tisa_state`
        STRIP_ASSUME_TAC))) THEN
      MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_inc_cnt_st;
                     `FST(SND(SND(r2:int64#num#(int64->byte)#int64)))`;
                     `SND(SND(SND(r2:int64#num#(int64->byte)#int64)))`;
                     `t3:tisa_state`; `k3:num`; `u3:tisa_state`] @ RD_S2_VARS @
                    [`inp:num list`; `c + (L:A->num) v`]) RD_STEP_INC) THEN
      CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [STEP_RANGE_TAC; ALL_TAC] THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `cw2:num->num`)) (concl th)
                            then ASSUME_TAC(MP (SPEC `17` th) (ARITH_RULE `17 < 24`)) else failwith "") THEN
      SUBGOAL_THEN `(cw2:num->num) 17 = cw 17` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(cw:num->num) 17 + 1 < 4611686018427387904` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th) &&
         can (find_term ((=) `res:int64#num#(int64->byte)#int64`)) (concl th))) THEN
      ASM_REWRITE_TAC[WORD_SMALL_NE] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND; WORD_SMALL_NE] THENL
       [CONJ_TAC THENL
         [EXISTS_TAC `v:A` THEN
          EXISTS_TAC `(pl_set cw2 17 (cw 17 + 1),(ctx2,nms2,tys2,ntms2,dbs2,ths2,nmap2,ymap2,drops2,pol2),
                       stk2):pstate` THEN
          ASM_REWRITE_TAC[FST; SND] THEN CONJ_TAC THENL
           [MATCH_MP_TAC PL_INV_SET THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          CONJ_TAC THENL [REWRITE_TAC[pl_set]; ALL_TAC] THEN
          X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[pl_set] THEN
          FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `cw2:num->num`)) (concl th))) THEN ASM_REWRITE_TAC[];
          ASM_MESON_TAC[WORD_SMALL_NE]];
        ASM_MESON_TAC[WORD_SMALL_NE]];
      (* The plan did not FIRE: the handler's outcome is the plan's. *)
      REWRITE_TAC[ASSUME `~(FST(r2:int64#num#(int64->byte)#int64) = word 1)`] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[WORD_SMALL_NE]];
    (* The prefix did not FIRE: the handler's outcome is the prefix's. *)
    REWRITE_TAC[ASSUME `~(FST(r1:int64#num#(int64->byte)#int64) = word 1)`] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* One operand, read to OP0 (the prefix of PREFIX_OP0_REL).                   *)
(* ------------------------------------------------------------------------- *)

let OP0_W = `\(cw:num->num) (t:num). pl_set (pl_set cw 24 1) 8 t`;;
let OP0_L = `\t:num. LENGTH(leb_enc t)`;;

let PREFIX_OP0_READS = prove(list_mk_icomb "prefix_reads" [`pl_prefix_op0`; `leb_fires`; OP0_W; OP0_L],
  REWRITE_TAC[prefix_reads] THEN REPEAT GEN_TAC THEN SPEC_TAC(`ns:nstate`,`ns:nstate`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC PREFIX_OP0_REL THEN ASM_MESON_TAC[]);;

let OP0_SHAPE = prove(
  list_mk_conj [`!bs v1 v2. leb_fires bs v1 /\ leb_fires bs v2 ==> v1 = v2`;
    mk_forall(`cw:num->num`, list_mk_forall([`ns:nstate`; `stk:num list`; `v:num`],
      mk_imp(`pl_inv (cw,ns,stk)`, mk_icomb(`pl_inv`, mk_pair(list_mk_comb(OP0_W, [`cw:num->num`; `v:num`]),
                                                              `ns:nstate,stk:num list`)))));
    list_mk_forall([`cw:num->num`; `v:num`],
      mk_eq(mk_comb(list_mk_comb(OP0_W, [`cw:num->num`; `v:num`]), `17`), `(cw:num->num) 17`))],
  REPEAT CONJ_TAC THENL
   [MESON_TAC[LEB_FIRES_UNIQUE];
    REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC PL_INV_SET THEN CONJ_TAC THENL [MATCH_MP_TAC PL_INV_SET THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ARITH_TAC];
    REWRITE_TAC[pl_set] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* Prefixes of numeric operands by composition.                              *)
(* ------------------------------------------------------------------------- *)

let enc_reads = new_definition
 `enc_reads pfx (ok:A->bool) (E:A->num list) (W:(num->num)->A->num->num) <=>
    prefix_reads pfx (\bs v. ok v /\ ?rest. bs = APPEND (E v) rest) W (\v. LENGTH (E v))`;;

let enc_unique = new_definition
 `enc_unique (ok:A->bool) (E:A->num list) <=>
    !v1 v2 r1 r2. ok v1 /\ ok v2 /\ APPEND (E v1) r1 = APPEND (E v2) r2 ==> v1 = v2`;;

let ok_snoc = new_definition
 `ok_snoc (ok:A->bool) (p:A#num) <=> ok (FST p) /\ SND p < 2 EXP 62`;;
let enc_snoc = new_definition
 `enc_snoc (E:A->num list) (p:A#num) = APPEND (E (FST p)) (leb_enc (SND p))`;;
let w_snoc = new_definition
 `w_snoc (W:(num->num)->A->num->num) k cw (p:A#num) = pl_set (W cw (FST p)) k (SND p)`;;

(* The leb_next step that reads one operand to control word k. *)
let pl_leb_step_tm = `[word 26; word 54; word 58; word 56; word 56; word 56; word 56; word 56; word 56; word 56;
                       word 0; word 0; word 0; word 0; word 0; word 0; word 0; word k]:int64 list`;;

let ENC_UNIQUE_SNOC = prove
 (`!ok (E:A->num list). enc_unique ok E ==> enc_unique (ok_snoc ok) (enc_snoc E)`,
  REWRITE_TAC[enc_unique; ok_snoc; enc_snoc; FORALL_PAIR_THM; PAIR_EQ; GSYM APPEND_ASSOC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p1:A) = p1'` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th))) THEN REWRITE_TAC[APPEND_LCANCEL] THEN
  DISCH_TAC THEN MATCH_MP_TAC LEB_FIRES_UNIQUE THEN
  EXISTS_TAC `APPEND (leb_enc p2) r1` THEN REWRITE_TAC[leb_fires] THEN ASM_MESON_TAC[]);;

(* A decode of the extended tuple contains a decode of the shorter one. *)
let SNOC_PREFIX = prove
 (`!ok (E:A->num list) bs.
     (?p1 p2. (ok p1 /\ p2 < 2 EXP 62) /\ ?rest. bs = APPEND (APPEND (E p1) (leb_enc p2)) rest)
     ==> (?v. ok v /\ ?rest. bs = APPEND (E v) rest)`,
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN MESON_TAC[]);;

let ENC_READS_SNOC_GOAL =
  let body = subst [pl_leb_step_tm, `stp:int64 list`]
   `enc_reads pfx (ok:A->bool) E W /\ enc_unique ok E /\ 6 < k /\ k < 24
     ==> enc_reads (APPEND pfx [stp]) (ok_snoc ok) (enc_snoc E) (w_snoc W k)` in
  list_mk_forall([`pfx:(int64 list)list`; `ok:A->bool`; `E:A->num list`; `W:(num->num)->A->num->num`; `k:num`], body);;

let ENC_READS_SNOC = prove(ENC_READS_SNOC_GOAL,
  let r1 = `r1:int64#num#(int64->byte)#int64` in
  REPEAT GEN_TAC THEN REWRITE_TAC[enc_reads; prefix_reads] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN SPEC_TAC(`ns:nstate`,`ns:nstate`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC pl_ns_vars THEN STRIP_TAC THEN
  REWRITE_TAC[EXISTS_PAIR_THM; ok_snoc; enc_snoc; w_snoc; FST; SND] THEN
  (* the prefix, then the step *)
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "drv_sem" (concl th))) THEN REWRITE_TAC[DRV_SEM_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN r1 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
     `cfr:int64`; `i:num`; `m:int64->byte`; `used:int64`; r1; `cw:num->num`;
     end_itlist (curry mk_pair) pl_ns_vars; `stk:num list`; `inp:num list`; `c:num`] o
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
  MP_TAC(SPECL ([`bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`; pl_leb_step_tm;
                 `FST(SND(SND(r1:int64#num#(int64->byte)#int64)))`; `used:int64`; `t2:tisa_state`; `k2:num`;
                 `u2:tisa_state`; `(W:(num->num)->A->num->num) cw v`] @ pl_ns_vars @
                [`stk:num list`; `inp:num list`; `c + LENGTH((E:A->num list) v)`]) RD_STEP_LEB) THEN
  CONV_TAC STEP_EL_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
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

(* The facts HANDLER_GEN needs of a shape, for the extended tuple. *)
let ENC_D_UNIQUE = prove
 (`!ok (E:A->num list). enc_unique ok E
     ==> !bs v1 v2. (ok v1 /\ ?rest. bs = APPEND (E v1) rest) /\ (ok v2 /\ ?rest. bs = APPEND (E v2) rest)
                    ==> v1 = v2`,
  REWRITE_TAC[enc_unique] THEN MESON_TAC[]);;

let W_INV_SNOC = prove
 (`!W:(num->num)->A->num->num k.
     (!cw ns stk v. pl_inv (cw,ns,stk) ==> pl_inv (W cw v,ns,stk)) /\ 6 < k
     ==> !cw ns stk p. pl_inv (cw,ns,stk) ==> pl_inv (w_snoc W k cw p,ns,stk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; w_snoc] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PL_INV_SET THEN ASM_SIMP_TAC[]);;

let W17_SNOC = prove
 (`!W:(num->num)->A->num->num k.
     (!cw v. W cw v 17 = cw 17) /\ ~(k = 17) ==> !cw p. w_snoc W k cw p 17 = cw 17`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[w_snoc; pl_set] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_REWRITE_TAC[]);;

(* The base: one operand, read to OP0. *)
let ENC_OK0 = `\v:num. v < 2 EXP 62`;;
let ENC_READS_OP0 = prove
 (list_mk_icomb "enc_reads" [`pl_prefix_op0`; ENC_OK0; `leb_enc`; OP0_W],
  SUBGOAL_THEN `leb_fires = (\bs v. (\v:num. v < 2 EXP 62) v /\ ?rest. bs = APPEND (leb_enc v) rest)` MP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; leb_fires]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(REWRITE_RULE[th] PREFIX_OP0_READS)) THEN
  REWRITE_TAC[enc_reads] THEN DISCH_THEN ACCEPT_TAC);;

let ENC_UNIQUE_OP0 = prove
 (mk_icomb(mk_icomb(`enc_unique:(num->bool)->(num->num list)->bool`, ENC_OK0), `leb_enc`),
  REWRITE_TAC[enc_unique] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC LEB_FIRES_UNIQUE THEN
  EXISTS_TAC `APPEND (leb_enc v1) r1` THEN REWRITE_TAC[leb_fires] THEN ASM_MESON_TAC[]);;

(* Two operands, OP0 and OP1. *)
let pl_prefix_op01 = new_definition(mk_eq(`pl_prefix_op01:(int64 list)list`,
  list_mk_icomb "APPEND" [`pl_prefix_op0`; mk_list([subst [`9`, `k:num`] pl_leb_step_tm], `:int64 list`)]));;
let ENC_READS_OP01 =
  let th = MP (ISPECL [`pl_prefix_op0`; ENC_OK0; `leb_enc`; OP0_W; `9`] ENC_READS_SNOC)
              (end_itlist CONJ [ENC_READS_OP0; ENC_UNIQUE_OP0; ARITH_RULE `6 < 9`; ARITH_RULE `9 < 24`]) in
  REWRITE_RULE[GSYM pl_prefix_op01] th;;

let handlers_theorems =
 ["PL_REL_LAYOUT", PL_REL_LAYOUT; "PLAN_IN_HANDLER", PLAN_IN_HANDLER; "HANDLER_GEN", HANDLER_GEN;
  "PREFIX_OP0_READS", PREFIX_OP0_READS; "OP0_SHAPE", OP0_SHAPE; "ENC_UNIQUE_SNOC", ENC_UNIQUE_SNOC;
  "SNOC_PREFIX", SNOC_PREFIX; "ENC_READS_SNOC", ENC_READS_SNOC; "ENC_D_UNIQUE", ENC_D_UNIQUE;
  "W_INV_SNOC", W_INV_SNOC; "W17_SNOC", W17_SNOC; "ENC_READS_OP0", ENC_READS_OP0;
  "ENC_UNIQUE_OP0", ENC_UNIQUE_OP0; "ENC_READS_OP01", ENC_READS_OP01];;
