(* ========================================================================= *)
(* The record loop, every run: whatever the outcome, the loop's memory is   *)
(* related to a state whose tables grow those of a state meeting the plans' *)
(* invariant, which the bootstrap reaches by the records of a body prefix   *)
(* of the input, or the bootstrap state itself before the header           *)
(* (REC_EVERY). The decode and each handler are taken whatever their        *)
(* outcome: no table is written by the decode, the header or END           *)
(* (rd_only_ok), and a record kind's handler meets kind_every. The call,    *)
(* entry to return (REC_X86_EVERY); its theorem rows derivable             *)
(* (REC_EVERY_THMS).                                                         *)
(*                                                                           *)
(* Loaded after rec_induction.ml.                                            *)
(* ========================================================================= *)

needs "native/hol/rec_induction.ml";;
needs "native/hol/handlers_every.ml";;

let rec_entry_every = new_definition
 `rec_entry_every progs bw ctl nctl budget cfr k (H:(int64 list)list) <=>
    ((k = 127 \/ k = 72) ==> rd_only_ok progs nctl H) /\
    (~(k = 127) /\ ~(k = 72) ==> kind_every progs bw ctl nctl budget cfr H k)`;;

let rec_every_tbl_tm =
 `!k. k < val (nh:int64) /\ ~(drv_word m0 (word_add ht (word (8 * k))) = word 0)
      ==> rec_entry_every progs bw ctl nctl budget (word_sub E (word 312)) k
                          (pl (drv_word m0 (word_add ht (word (8 * k)))))`;;

let rec_every = new_definition
 `rec_every bw ctl nctl E hpol inp (m:int64->byte) <=>
    ?s cw0 ns0 stk0.
      plan_rel bw ctl nctl (word_sub E (word 312)) m s /\
      pl_inv (cw0,ns0,stk0) /\ pl_grows ns0 (FST(SND s)) /\
      (ns0 = (hinit_ctxt,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],hpol) \/
       ?pol0 recs n. pol0 <= 2 /\ list_of_seq (\j. EL j inp) n = holr_body pol0 0 recs /\
                     tc_path nat_step recs
                       (hinit_ctxt,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],MAX hpol pol0) ns0)`;;

let ev_ns_tuple = end_itlist (curry mk_pair) pl_ns_vars;;

(* The invariant's memory meets the every-run property. *)
let REC_INV_EVERY = prove
 (`!bw ctl nctl E ht nh m0 hpol inp m.
     rec_inv bw ctl nctl E ht nh m0 hpol inp m ==> rec_every bw ctl nctl E hpol inp m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rec_inv; rec_every; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC ([`cw:num->num`] @ RD_NS_VARS @ [`pos:num`]) THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [mk_pair(`cw:num->num`, mk_pair(ev_ns_tuple, `stk:num list`));
                        `cw:num->num`; ev_ns_tuple; `stk:num list`] THEN
  ASM_REWRITE_TAC[FST; SND; PL_GROWS_REFL] THEN
  DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`pol0:num`; `recs:holr_record list`; `pos:num`] THEN
  ASM_REWRITE_TAC[]);;

(* A plan run through its descriptor: what the run of its steps gives of the *)
(* memory they leave, under plan_rel, holds of the loop's memory after it.   *)
let REC_PLAN_REL_EVERY = prove
 (`!progs bw ctl nctl budget E pl d m used r R cw ns stk inp c (Phi:pstate->bool).
     rec_plan progs bw ctl budget E pl d m used r /\ val d + 64 <= 2 EXP 64 /\
     rel_reads bw ctl nctl (word_sub E (word 312)) R /\
     (!a. R a ==> ~rec_stack E a /\ ~drv_in a (word_add d (word 40)) 24) /\
     plan_rel bw ctl nctl (word_sub E (word 312)) m (cw,ns,stk) /\
     rd_rel bw ctl nctl (word_sub E (word 312)) m inp c /\
     (!m' res. drv_sem progs bw ctl budget (word_sub E (word 312)) (pl d) 0 m' used res /\
               plan_rel bw ctl nctl (word_sub E (word 312)) m' (cw,ns,stk) /\
               rd_rel bw ctl nctl (word_sub E (word 312)) m' inp c
               ==> ?s'. plan_rel bw ctl nctl (word_sub E (word 312)) (FST(SND(SND res))) s' /\ Phi s')
     ==> ?s'. plan_rel bw ctl nctl (word_sub E (word 312)) (FST(SND r)) s' /\ Phi s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `E:int64`;
                 `pl:int64->(int64 list)list`; `d:int64`; `m:int64->byte`; `used:int64`;
                 `r:int64#(int64->byte)#int64`; `R:int64->bool`] REC_PLAN_DRV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m':int64->byte` (X_CHOOSE_THEN `res:int64#num#(int64->byte)#int64`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m':int64->byte`; `res:int64#num#(int64->byte)#int64`] o
    check (fun th -> is_forall(concl th) && can (find_term (is_const_app "drv_sem")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REL_READS_PLAN THEN
      MAP_EVERY EXISTS_TAC [`R:int64->bool`; `m:int64->byte`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REL_READS_RD THEN
      MAP_EVERY EXISTS_TAC [`R:int64->bool`; `m:int64->byte`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s':pstate` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REL_READS_PLAN THEN
  MAP_EVERY EXISTS_TAC [`R:int64->bool`; `FST(SND(SND(res:int64#num#(int64->byte)#int64)))`] THEN
  ASM_REWRITE_TAC[]);;

(* The opcode byte and the record's other bytes: the record's encoding.     *)
let REC_BYTES = prove
 (`!inp pos op rec rest.
     op < 128 /\ leb_fires (rd_from inp pos) op /\
     holr_rec_enc rec = CONS op (TL (holr_rec_enc rec)) /\
     rd_from inp (pos + LENGTH (leb_enc op)) = APPEND (TL (holr_rec_enc rec)) rest
     ==> rd_from inp pos = APPEND (holr_rec_enc rec) rest`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `rest0:num list` o CONJUNCT2 o GEN_REWRITE_RULE I [leb_fires] o
                check (fun th -> is_const_app "leb_fires" (concl th))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RD_FROM_APPEND) THEN
  SUBGOAL_THEN `leb_enc op = [op]` ASSUME_TAC THENL
   [MATCH_MP_TAC LEB_ENC_ONE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rest0 = APPEND (TL (holr_rec_enc rec)) rest` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `rd_from inp (pos + LENGTH (leb_enc op))` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `rd_from inp pos`
                          then SUBST1_TAC th else failwith "") THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
    [ASSUME `holr_rec_enc rec = CONS op (TL (holr_rec_enc rec))`] THEN
  REWRITE_TAC[APPEND; ASSUME `leb_enc op = [op]`]);;

(* The decode, whatever its outcome. *)
let rec_dec_every_goal =
  let dyn = `rec_inv bw ctl nctl E ht nh m0 hpol inp m /\ ~(val budget <= val used) /\
             rec_plan progs bw ctl budget E pl dd m (word_add used (word 1)) r1` in
  rec_order (rec_static_names @ ["m"; "used"; "r1"])
    (mk_imp(mk_conj(rec_static_tm, dyn),
            `rec_every bw ctl nctl E hpol inp (FST(SND(r1:int64#(int64->byte)#int64)))`));;

let REC_INV_STATE_TAC =
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[rec_inv] o check (fun th -> is_const_app "rec_inv" (concl th))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC ([`cw:num->num`] @ RD_NS_VARS @ [`pos:num`]) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS);;

(* rec_every at a state with the invariant's tables. *)
let REC_EVERY_SAME_TAC =
  REWRITE_TAC[rec_every] THEN
  MAP_EVERY EXISTS_TAC [`s':pstate`; `cw:num->num`; ev_ns_tuple; `stk:num list`] THEN
  ASM_REWRITE_TAC[PL_GROWS_REFL] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `hinit_ctxt`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`pol0:num`; `recs:holr_record list`; `pos:num`] THEN ASM_REWRITE_TAC[];;

let REC_DECODE_EVERY = prove(rec_dec_every_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!d. MEM d ds ==> val(d:int64) + 64 <= 2 EXP 64` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> is_const_app "rec_layout" (concl th))) THEN
    REWRITE_TAC[rec_layout] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REC_INV_STATE_TAC THEN
  SUBGOAL_THEN `!a. (R:int64->bool) a ==> ~rec_stack E a /\ ~drv_in a (word_add dd (word 40)) 24` ASSUME_TAC THENL
   [REC_RFACTS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(dd:int64) + 64 <= 2 EXP 64` ASSUME_TAC THENL [REC_D64_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `E:int64`;
                 `pl:int64->(int64 list)list`; `dd:int64`; `m:int64->byte`; `word_add used (word 1):int64`;
                 `r1:int64#(int64->byte)#int64`; `R:int64->bool`; `cw:num->num`; ev_ns_tuple; `stk:num list`;
                 `inp:num list`; `pos:num`; mk_abs(`s':pstate`, mk_eq(`FST(SND(s':pstate))`, ev_ns_tuple))]
                REC_PLAN_REL_EVERY) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN BETA_TAC THEN
    EXISTS_TAC (mk_pair(`\k. if k < nctl then pl_mw (FST(SND(SND(res:int64#num#(int64->byte)#int64)))) ctl k
                             else (cw:num->num) k`, mk_pair(ev_ns_tuple, `stk:num list`))) THEN
    REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC RD_ONLY_KEEPS_PL THEN
    MAP_EVERY EXISTS_TAC [`progs:num->tisa_prog`; `budget:int64`; `(pl:int64->(int64 list)list) dd`; `0`;
                          `m':int64->byte`; `word_add used (word 1):int64`; `inp:num list`; `pos:num`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RD_ONLY_DD THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC) THEN
  REC_EVERY_SAME_TAC);;

(* A handler, whatever its outcome. *)
let rec_hdl_every_goal =
  let dyn = `rec_inv bw ctl nctl E ht nh m0 hpol inp m /\ ~(val budget <= val used) /\
             rec_plan progs bw ctl budget E pl dd m (word_add used (word 1)) r1 /\ FST r1 = word 1 /\
             ~rec_missing ht nh opa (FST(SND r1)) /\
             rec_plan progs bw ctl budget E pl (rec_handler ht opa (FST(SND r1))) (FST(SND r1)) (SND(SND r1)) r2` in
  rec_order (rec_static_names @ ["m"; "used"; "r1"; "r2"])
    (mk_imp(list_mk_conj [rec_static_tm; rec_every_tbl_tm; dyn],
            `rec_every bw ctl nctl E hpol inp (FST(SND(r2:int64#(int64->byte)#int64)))`));;

let REC_HANDLER_EVERY = prove(rec_hdl_every_goal,
  let r1m = `FST(SND(r1:int64#(int64->byte)#int64))`
  and used1 = `SND(SND(r1:int64#(int64->byte)#int64))`
  and r2 = `r2:int64#(int64->byte)#int64` in
  let dop = `drv_word m0 (word_add ht (word (8 * op)))` in
  let cw' = `pl_set (pl_set cw 21 pos) 18 op` and c' = `pos + LENGTH (leb_enc op)` in
  let is_tbl mt th = is_forall(concl th) && can (find_term ((=) `ht:int64`)) (concl th) &&
                     can (find_term ((=) mt)) (concl th) && can (find_term ((=) `m0:int64->byte`)) (concl th) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!d. MEM d ds ==> val(d:int64) + 64 <= 2 EXP 64` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> is_const_app "rec_layout" (concl th))) THEN
    REWRITE_TAC[rec_layout] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REC_INV_STATE_TAC THEN
  (* the table in the decode's memory *)
  SUBGOAL_THEN `!k. k < val(nh:int64)
                    ==> drv_word (FST(SND(r1:int64#(int64->byte)#int64))) (word_add ht (word (8 * k))) =
                        drv_word m0 (word_add ht (word (8 * k)))` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(rec_spec ["d", `dd:int64`; "used", `word_add used (word 1):int64`; "rr", `r1:int64#(int64->byte)#int64`]
                    REC_PLAN_TABLE) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (is_tbl `m:int64->byte`)) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the decode's descriptor, the lookup *)
  SUBGOAL_THEN `!a. (R:int64->bool) a ==> ~rec_stack E a /\ ~drv_in a (word_add dd (word 40)) 24` ASSUME_TAC THENL
   [REC_RFACTS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(dd:int64) + 64 <= 2 EXP 64` ASSUME_TAC THENL [REC_D64_TAC; ALL_TAC] THEN
  MP_TAC(SPEC_ALL REC_LOOKUP) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `op:num` STRIP_ASSUME_TAC)) THEN
  (* the entry: in ds, and its every-run contract *)
  FIRST_ASSUM(MP_TAC o SPEC `op:num` o check (fun th -> is_forall(concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "rec_entry")) (concl th))) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  FIRST_ASSUM(MP_TAC o SPEC `op:num` o check (fun th -> is_forall(concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "rec_entry_every")) (concl th))) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[rec_entry_every] THEN STRIP_TAC THEN
  (* the handler's run and descriptor *)
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "rec_plan" (concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "rec_handler")) (concl th))) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && is_const_app "rec_handler" (lhs(concl th))
                        then PURE_REWRITE_TAC[th] else failwith "") THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(val(budget:int64) < val(SND(SND(r1:int64#(int64->byte)#int64))))` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = used1 then PURE_REWRITE_TAC[th] else failwith "") THEN
    MATCH_MP_TAC REC_USED1 THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (subst [dop,`dd:int64`] `!a. (R:int64->bool) a ==> ~rec_stack E a /\ ~drv_in a (word_add dd (word 40)) 24`)
    ASSUME_TAC THENL [REC_RFACTS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (subst [dop,`dd:int64`] `val(dd:int64) + 64 <= 2 EXP 64`) ASSUME_TAC THENL [REC_D64_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `op < 128` ASSUME_TAC THENL
   [UNDISCH_TAC `op < val(nh:int64)` THEN UNDISCH_TAC `val(nh:int64) <= 128` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `op = 127 \/ op = 72` THENL
   [(* END or the header: no table written *)
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_disj(lhand(concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `E:int64`;
                   `pl:int64->(int64 list)list`; dop; r1m; used1; r2; `R:int64->bool`; cw'; ev_ns_tuple;
                   `stk:num list`; `inp:num list`; c';
                   mk_abs(`s':pstate`, mk_eq(`FST(SND(s':pstate))`, ev_ns_tuple))] REC_PLAN_REL_EVERY) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN BETA_TAC THEN
      EXISTS_TAC (mk_pair(mk_abs(`k:num`, mk_cond(`k < nctl`,
                    `pl_mw (FST(SND(SND(res:int64#num#(int64->byte)#int64)))) ctl k`, mk_comb(cw', `k:num`))),
                  mk_pair(ev_ns_tuple, `stk:num list`))) THEN
      REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC RD_ONLY_KEEPS_PL THEN
      MAP_EVERY EXISTS_TAC [`progs:num->tisa_prog`; `budget:int64`; mk_comb(`pl:int64->(int64 list)list`, dop);
                            `0`; `m':int64->byte`; used1; `inp:num list`; c'] THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC) THEN
    REC_EVERY_SAME_TAC;
    ALL_TAC] THEN
  (* a record kind: its every-run contract *)
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "kind_every")) (concl th))) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[DE_MORGAN_THM] o
      check (fun th -> is_neg(concl th) && is_disj(dest_neg(concl th))));
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `E:int64`;
                 `pl:int64->(int64 list)list`; dop; r1m; used1; r2; `R:int64->bool`; cw'; ev_ns_tuple;
                 `stk:num list`; `inp:num list`; c';
                 mk_abs(`s':pstate`,
                   subst [cw', `cw:num->num`; ev_ns_tuple, `ns:nstate`; c', `c:num`; `op:num`, `opk:num`]
                    `pl_grows ns (FST(SND(s':pstate))) \/
                     (cw:num->num) 20 = 1 /\
                     ?rec rest s0. holr_rec_enc rec = CONS opk (TL (holr_rec_enc rec)) /\
                                   rd_from inp c = APPEND (TL (holr_rec_enc rec)) rest /\
                                   nat_step ns rec (FST(SND s0)) /\ pl_inv s0 /\
                                   pl_grows (FST(SND s0)) (FST(SND(s':pstate)))`)] REC_PLAN_REL_EVERY) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN BETA_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[kind_every] o
      check (fun th -> is_const_app "kind_every" (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`m':int64->byte`; used1; `stk:num list`] THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_INV_SET THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_INV_SET THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ARITH_TAC]; ARITH_TAC];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `s':pstate` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV PL_SET_NUM_CONV)) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [REWRITE_TAC[rec_every] THEN
    MAP_EVERY EXISTS_TAC [`s':pstate`; `cw:num->num`; ev_ns_tuple; `stk:num list`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `hinit_ctxt`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`pol0:num`; `recs:holr_record list`; `pos:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the record's native step happened: the state one record further *)
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `rec:holr_record` (X_CHOOSE_THEN `rest:num list`
    (X_CHOOSE_THEN `s0:pstate` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `hinit_ctxt`)) (concl th))) THENL
   [(* before the header HDR is 0 *)
    UNDISCH_TAC `(cw:num->num) 20 = 1` THEN ASM_REWRITE_TAC[ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[rec_every] THEN
  MAP_EVERY EXISTS_TAC [`s':pstate`; `FST(s0:pstate)`; `FST(SND(s0:pstate))`; `SND(SND(s0:pstate))`] THEN
  ASM_REWRITE_TAC[PAIR] THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`pol0:num`; `APPEND recs [rec:holr_record]`; `pos + LENGTH (holr_rec_enc rec)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`inp:num list`; `pos:num`; `op:num`; `rec:holr_record`; `rest:num list`] REC_BYTES) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `rd_from inp pos`
                          then SUBST1_TAC(MATCH_MP LIST_OF_SEQ_RD_FROM th) else failwith "") THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && is_const_app "list_of_seq" (lhs(concl th))
                          then PURE_REWRITE_TAC[th] else failwith "") THEN
    REWRITE_TAC[HOLR_BODY_SNOC];
    MATCH_MP_TAC TC_PATH_SNOC THEN EXISTS_TAC ev_ns_tuple THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* The loop, every run. *)
let rec_every_goal =
  let run = `rec_run progs bw ctl budget E pl dd ht nh opa enda m used c res` in
  let inner = list_mk_forall([`m:int64->byte`; `used:int64`; `c:num`; `res:int64#num#(int64->byte)#int64`],
                mk_imp(run, mk_imp(`rec_inv bw ctl nctl E ht nh m0 hpol inp m`,
                                   `rec_every bw ctl nctl E hpol inp (FST(SND(SND(res:int64#num#(int64->byte)#int64))))`))) in
  rec_order rec_static_names (mk_imp(mk_conj(rec_static_tm, rec_every_tbl_tm), inner));;

let REC_EVERY = prove(rec_every_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC rec_run_INDUCT THEN REWRITE_TAC[FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [(* the allowance spent: the invariant's memory *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_ACCEPT_TAC REC_INV_EVERY;
    (* the decode did not fire *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(SPEC_ALL REC_DECODE_EVERY) THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    (* no handler *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(SPEC_ALL REC_DECODE_EVERY) THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    (* the handler did not fire *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(SPEC_ALL REC_HANDLER_EVERY) THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    (* END fired *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(SPEC_ALL REC_HANDLER_EVERY) THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    (* a handler fired with ENDW 0: the invariant again, then the rest of the run *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC_ALL REC_STEP) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN FIRST_ASSUM ACCEPT_TAC]);;

(* The theorem rows the loop's memory holds are derivable, in the context of *)
(* a state the bootstrap reaches by the records of a body prefix of the     *)
(* input (or the bootstrap context itself, before the header).               *)
let REC_EVERY_THMS = prove
 (`!bw ctl nctl E hpol inp m.
     rec_every bw ctl nctl E hpol inp m
     ==> ?s. plan_rel bw ctl nctl (word_sub E (word 312)) m s /\ pl_thms_ok (FST(SND s)) /\
             (FST(FST(SND s)) = hinit_ctxt \/
              ?pol0 recs n ns0. pol0 <= 2 /\ list_of_seq (\j. EL j inp) n = holr_body pol0 0 recs /\
                                tc_path nat_step recs
                                  (hinit_ctxt,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],MAX hpol pol0) ns0 /\
                                FST(FST(SND s)) = FST ns0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rec_every; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:pstate`; `cw0:num->num`; `ns0:nstate`; `stk0:num list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  EXISTS_TAC `s:pstate` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FST(FST(SND(s:pstate))) = FST(ns0:nstate)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_grows ns0 (FST(SND(s:pstate)))` THEN
    SPEC_TAC(`FST(SND(s:pstate))`,`ns:nstate`) THEN SPEC_TAC(`ns0:nstate`,`ns0:nstate`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; pl_grows; FST] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_GROWS_THMS THEN EXISTS_TAC `ns0:nstate` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `(cw0,ns0,stk0):pstate` PL_INV_THMS) THEN ASM_REWRITE_TAC[FST; SND];
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th))) THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[FST];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`pol0:num`; `recs:holr_record list`; `n:num`; `ns0:nstate`] THEN
      ASM_REWRITE_TAC[]]]);;

(* The every-run property reads only R. *)
let REC_EVERY_AGREE = prove
 (`!bw ctl nctl E hpol inp R M M'.
     rel_reads bw ctl nctl (word_sub E (word 312)) R /\ (!a. R a ==> M' a = M a) /\
     rec_every bw ctl nctl E hpol inp M
     ==> rec_every bw ctl nctl E hpol inp M'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rec_every] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:pstate`; `cw0:num->num`; `ns0:nstate`; `stk0:num list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`s:pstate`; `cw0:num->num`; `ns0:nstate`; `stk0:num list`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REL_READS_PLAN THEN
  MAP_EVERY EXISTS_TAC [`R:int64->bool`; `M:int64->byte`] THEN ASM_REWRITE_TAC[]);;

(* The record loop's call, entry to return, every run: the memory it        *)
(* returns meets the every-run property (with REC_EVERY_THMS, its theorem  *)
(* rows are derivable). R misses the descriptor words the return writes.   *)
let rec_x86_every_goal =
  let _, body = strip_forall(concl REC_CORRECT) in
  let prem, ens = dest_imp body in
  let f, frame = dest_comb ens in
  let f2, post = dest_comb f in
  let s, pb = dest_abs post in
  let ev = vsubst [s, `s:x86state`] `rec_every bw ctl nctl E hpol inp (read memory (s:x86state))` in
  let post' = mk_abs(s, mk_conj(pb, ev)) in
  let ens' = mk_comb(mk_comb(f2, post'), frame) in
  let prems = list_mk_conj [prem; rec_static_tm; rec_every_tbl_tm; `rec_inv bw ctl nctl E ht nh m0 hpol inp m0`;
                            `!a. (R:int64->bool) a ==> ~drv_in a (word_add r (word 56)) 16`] in
  let tm = mk_imp(prems, ens') in
  list_mk_forall(frees tm, tm);;

let REC_X86_EVERY = prove(rec_x86_every_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (let _, body = strip_forall(concl REC_CORRECT) in rand(rator(rand body))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REC_EVERY_AGREE THEN
      MAP_EVERY EXISTS_TAC [`R:int64->bool`; `FST(SND(SND(res:int64#num#(int64->byte)#int64)))`] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
        SUBGOAL_THEN `~rec_stack E (a:int64)` ASSUME_TAC THENL
         [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `rec_stack`)) (concl th) && not (can (find_term ((=) `drv_in`)) (concl th)))) THEN
          FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `rec_final`)) (concl th)
                              then REWRITE_TAC[MATCH_MP (SPEC `a:int64` th) (ASSUME `~rec_stack E (a:int64)`)]
                              else failwith "") THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `a:int64` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `word_add (r:int64) (word 56)`)) (concl th))) THEN
        ASM_REWRITE_TAC[rec_final; drv_in] THEN
        FIRST_ASSUM(MP_TAC o check (fun th -> is_const_app "rec_layout" (concl th))) THEN
        REWRITE_TAC[rec_layout] THEN STRIP_TAC THEN
        SUBGOAL_THEN `val(word_add r (word 56):int64) = val(r:int64) + 56 /\
                      val(word_add r (word 64):int64) = val(r:int64) + 64` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        REFL_TAC;
        MP_TAC(rec_spec ["m", `m0:int64->byte`; "used", `used0:int64`; "c", `0`;
                         "res", `res:int64#num#(int64->byte)#int64`] REC_EVERY) THEN
        ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`m0:int64->byte`; `used0:int64`; `0`; `res:int64#num#(int64->byte)#int64`]) THEN
        ASM_REWRITE_TAC[]]];
    MP_TAC(SPEC_ALL REC_CORRECT) THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]);;

(* Every theorem this file states, for the audits. *)
let rec_every_theorems =
 ["REC_INV_EVERY", REC_INV_EVERY;
  "REC_PLAN_REL_EVERY", REC_PLAN_REL_EVERY;
  "REC_BYTES", REC_BYTES;
  "REC_DECODE_EVERY", REC_DECODE_EVERY;
  "REC_HANDLER_EVERY", REC_HANDLER_EVERY;
  "REC_EVERY", REC_EVERY;
  "REC_EVERY_THMS", REC_EVERY_THMS;
  "REC_EVERY_AGREE", REC_EVERY_AGREE;
  "REC_X86_EVERY", REC_X86_EVERY];;
