(* ========================================================================= *)
(* The record loop's induction over the general relation: rec_induction.ml  *)
(* with tab_rel hol_tables L in place of plan_rel, hol_inv in place of       *)
(* pl_inv, and the contracts of contract_tab.ml. A turn keeps the loop's     *)
(* invariant or, at END, has read a whole stream (REC_STEP_TAB); by          *)
(* induction on rec_run a FIRED run has read a stream HOLR accepts           *)
(* (REC_INDUCTION_TAB, REC_ACCEPTS_TAB), and so does the loop's x86 call    *)
(* that returns FIRED (REC_X86_ACCEPTS_TAB). The relation-free lemmas are   *)
(* rec_induction.ml's.                                                       *)
(*                                                                           *)
(* Loaded after contract_tab.ml and rec_induction.ml.                        *)
(* ========================================================================= *)

(* What the relations read: a set R such that memories agreeing on R keep    *)
(* both the tables' relation and the reader's.                                *)
let tab_rel_reads = new_definition
 `tab_rel_reads (tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) L bw ctl nctl cfr (R:int64->bool) <=>
    !M M'. (!a. R a ==> M' a = M a)
           ==> (!inp s. tab_rel tb L inp bw ctl nctl cfr M s ==> tab_rel tb L inp bw ctl nctl cfr M' s) /\
               (!inp c. rd_rel bw ctl nctl cfr M inp c ==> rd_rel bw ctl nctl cfr M' inp c)`;;

let TAB_REL_READS_TAB = prove
 (`!(tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) L bw ctl nctl cfr R M M' inp s.
     tab_rel_reads tb L bw ctl nctl cfr R /\ (!a. R a ==> M' a = M a) /\ tab_rel tb L inp bw ctl nctl cfr M s
     ==> tab_rel tb L inp bw ctl nctl cfr M' s`,
  REWRITE_TAC[tab_rel_reads] THEN MESON_TAC[]);;

let TAB_REL_READS_RD = prove
 (`!(tb:(num->S->num->num list)#(num->S->num)#(num->num)#(num->S->num->bool)#(num->num->S->num list->S->bool)#(num->num->S->num->num->num->S->bool)) L bw ctl nctl cfr R M M' inp c.
     tab_rel_reads tb L bw ctl nctl cfr R /\ (!a. R a ==> M' a = M a) /\ rd_rel bw ctl nctl cfr M inp c
     ==> rd_rel bw ctl nctl cfr M' inp c`,
  REWRITE_TAC[tab_rel_reads] THEN MESON_TAC[]);;

(* Both relations moved from a memory to one that agrees with it on R. *)
let TAB_REL_MOVE_TAC m_old : tactic =
  CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC `hol_tables` TAB_REL_READS_TAB) THEN MAP_EVERY EXISTS_TAC [`R:int64->bool`; m_old] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC(ISPECL [`hol_tables`; `L:tabdesc list`] TAB_REL_READS_RD) THEN
    MAP_EVERY EXISTS_TAC [`R:int64->bool`; m_old] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];;

(* One relation (tab_rel or rd_rel) moved, as a single goal. *)
let TAB_REL_MOVE1_TAC m_old : tactic =
  FIRST [MATCH_MP_TAC(ISPEC `hol_tables` TAB_REL_READS_TAB);
         MATCH_MP_TAC(ISPECL [`hol_tables`; `L:tabdesc list`] TAB_REL_READS_RD)] THEN
  MAP_EVERY EXISTS_TAC [`R:int64->bool`; m_old] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;;

(* The plan run inside a rec_plan: REC_PLAN_DRV's witnesses, and the         *)
(* relations at the driver's start memory.                                  *)
let TAB_REC_PLAN_START_TAC d s_tm : tactic =
  MP_TAC(ISPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `E:int64`;
                 `pl:int64->(int64 list)list`; d; `m:int64->byte`; `used:int64`;
                 `r:int64#(int64->byte)#int64`; `R:int64->bool`] REC_PLAN_DRV) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m':int64->byte` (X_CHOOSE_THEN `res:int64#num#(int64->byte)#int64` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN (mk_conj(list_mk_icomb "tab_rel" [`hol_tables`; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                                                 `word_sub E (word 312):int64`; `m':int64->byte`; s_tm],
                        `rd_rel bw ctl nctl (word_sub E (word 312)) m' inp c`)) STRIP_ASSUME_TAC THENL
   [TAB_REL_MOVE_TAC `m:int64->byte`; ALL_TAC] THEN
  SUBGOAL_THEN `FST(res:int64#num#(int64->byte)#int64) = word 1` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `FST(r:int64#(int64->byte)#int64) = FST(res:int64#num#(int64->byte)#int64)`
                          then REWRITE_TAC[SYM th] else failwith "") THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;

(* Record k's decode, run by the record loop: an opcode at the cursor, the   *)
(* relations after it in the record loop's memory.                           *)
let REC_DECODE_TAB = prove
 (`!L progs bw ctl nctl budget E pl dd m used r R cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     rec_plan progs bw ctl budget E pl dd m used r /\ pl dd = pl_plan_dd /\ val dd + 64 <= 2 EXP 64 /\
     tab_rel_reads hol_tables L bw ctl nctl (word_sub E (word 312)) R /\
     (!a. R a ==> ~rec_stack E a /\ ~drv_in a (word_add dd (word 40)) 24) /\
     rd_progs_ok progs /\ 21 < nctl /\ rd_tab_apart L bw /\ ~(val budget < val used) /\
     tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl (word_sub E (word 312)) m inp c /\ FST r = word 1
     ==> SND(SND r) = used /\
         ?op. leb_fires (rd_from inp c) op /\
              tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) (FST(SND r))
                (pl_set (pl_set cw 21 c) 18 op,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
              rd_rel bw ctl nctl (word_sub E (word 312)) (FST(SND r)) inp (c + LENGTH(leb_enc op))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  TAB_REC_PLAN_START_TAC `dd:int64` `(cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate` THEN
  MP_TAC(ISPECL [`hol_tables`; `L:tabdesc list`; `inp:num list`; `progs:num->tisa_prog`; `bw:num->int64`;
                 `ctl:int64`; `nctl:num`; `budget:int64`; `word_sub E (word 312):int64`; `0`; `m':int64->byte`;
                 `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`; `(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`;
                 `stk:num list`; `c:num`] DD_TAB) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    FIRST_X_ASSUM(fun th -> if is_const_app "drv_sem" (concl th) then
       ACCEPT_TAC(PURE_REWRITE_RULE[ASSUME `(pl:int64->(int64 list)list) dd = pl_plan_dd`] th) else failwith "");
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (fun th -> MP_TAC(MP th (ASSUME `FST(res:int64#num#(int64->byte)#int64) = word 1`)))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `op:num` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
   [PURE_REWRITE_TAC[ASSUME `SND(SND(r:int64#(int64->byte)#int64)) = SND(SND(SND(res:int64#num#(int64->byte)#int64)))`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    EXISTS_TAC `op:num` THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    TAB_REL_MOVE_TAC `FST(SND(SND(res:int64#num#(int64->byte)#int64)))`]);;

(* A handler meeting the kind contract, run by the record loop: HDR, its     *)
(* record, the relations after it in the record loop's memory.               *)
let REC_HANDLER_TAB = prove
 (`!L progs bw ctl nctl budget E pl d H op m used r R cw ns stk inp c.
     rec_plan progs bw ctl budget E pl d m used r /\ pl d = H /\ val d + 64 <= 2 EXP 64 /\
     tab_rel_reads hol_tables L bw ctl nctl (word_sub E (word 312)) R /\
     (!a. R a ==> ~rec_stack E a /\ ~drv_in a (word_add d (word 40)) 24) /\
     tab_kind_contract hol_tables L hol_inv nat_step holr_rec_enc progs bw ctl nctl budget (word_sub E (word 312)) H op /\ ~(val budget < val used) /\
     tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) m (cw,ns,stk) /\ hol_inv (cw,ns,stk) /\
     rd_rel bw ctl nctl (word_sub E (word 312)) m inp c /\ FST r = word 1
     ==> cw 20 = 1 /\
         ?rec rest s'. holr_rec_enc rec = CONS op (TL (holr_rec_enc rec)) /\
                       rd_from inp c = APPEND (TL (holr_rec_enc rec)) rest /\
                       nat_step ns rec (FST(SND s')) /\ hol_inv s' /\
                       tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) (FST(SND r)) s' /\
                       rd_rel bw ctl nctl (word_sub E (word 312)) (FST(SND r)) inp
                              (c + LENGTH (TL (holr_rec_enc rec))) /\
                       FST s' 17 = cw 17 + 1 /\ (!j. 18 <= j /\ j < 24 ==> FST s' j = cw j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  TAB_REC_PLAN_START_TAC `d:int64` `(cw,ns,stk):pstate` THEN
  FIRST_ASSUM(MP_TAC o SPECL [`m':int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`;
                              `cw:num->num`; `ns:nstate`; `stk:num list`; `inp:num list`; `c:num`] o
              REWRITE_RULE[tab_kind_contract] o check (fun th -> is_const_app "tab_kind_contract" (concl th))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    FIRST_X_ASSUM(fun th -> if is_const_app "drv_sem" (concl th) then
       ACCEPT_TAC(PURE_REWRITE_RULE[ASSUME `(pl:int64->(int64 list)list) d = H`] th) else failwith "");
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(MP th (ASSUME `FST(res:int64#num#(int64->byte)#int64) = word 1`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `rec:holr_record` (X_CHOOSE_THEN `rest:num list`
    (X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC)))) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`rec:holr_record`; `rest:num list`; `s':pstate`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TAB_REL_MOVE1_TAC `FST(SND(SND(res:int64#num#(int64->byte)#int64)))`);;

(* The header's handler, run by the record loop. *)
let REC_HEADER_HANDLER_TAB = prove
 (`!L progs bw ctl nctl budget E pl d H m used r R cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     rec_plan progs bw ctl budget E pl d m used r /\ pl d = H /\ val d + 64 <= 2 EXP 64 /\
     tab_rel_reads hol_tables L bw ctl nctl (word_sub E (word 312)) R /\
     (!a. R a ==> ~rec_stack E a /\ ~drv_in a (word_add d (word 40)) 24) /\
     tab_header_contract L progs bw ctl nctl budget (word_sub E (word 312)) H /\ ~(val budget < val used) /\
     rd_hdr_rel bw (word_sub E (word 312)) m /\ (!a. drv_in a (bw 60) (val(bw 61)) ==> R a) /\
     tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     hol_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl (word_sub E (word 312)) m inp c /\ FST r = word 1
     ==> cw 20 = 0 /\
         ?p rest s'. p <= 2 /\ rd_from inp c = APPEND (TL (holr_body p 0 [])) rest /\
                     FST(SND s') = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,MAX pol p) /\ hol_inv s' /\
                     tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) (FST(SND r)) s' /\
                     rd_rel bw ctl nctl (word_sub E (word 312)) (FST(SND r)) inp
                            (c + LENGTH (TL (holr_body p 0 []))) /\
                     FST s' 20 = 1 /\ (!j. 17 <= j /\ j < 24 /\ ~(j = 20) ==> FST s' j = cw j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  TAB_REC_PLAN_START_TAC `d:int64` `(cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate` THEN
  SUBGOAL_THEN `rd_hdr_rel bw (word_sub E (word 312)) m'` ASSUME_TAC THENL
   [MATCH_MP_TAC RD_HDR_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `m':int64->byte`)) (concl th) && can (find_term ((=) `R:int64->bool`)) (concl th))) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(bw:num->int64) 60`)) (concl th) && can (find_term ((=) `R:int64->bool`)) (concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL ([`m':int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`] @
                              RD_NS_VARS @ [`inp:num list`; `c:num`]) o
              REWRITE_RULE[tab_header_contract] o check (fun th -> is_const_app "tab_header_contract" (concl th))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    FIRST_X_ASSUM(fun th -> if is_const_app "drv_sem" (concl th) then
       ACCEPT_TAC(PURE_REWRITE_RULE[ASSUME `(pl:int64->(int64 list)list) d = H`] th) else failwith "");
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(MP th (ASSUME `FST(res:int64#num#(int64->byte)#int64) = word 1`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `rest:num list`
    (X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC)))) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `rest:num list`; `s':pstate`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TAB_REL_MOVE1_TAC `FST(SND(SND(res:int64#num#(int64->byte)#int64)))`);;

(* END's handler, run by the record loop: a FIRED END plan saw the header,  *)
(* the input from the cursor is the count and the checksum of the bytes    *)
(* before RST, to the input's end; ENDW is 1 and the relations hold in the  *)
(* loop's memory with the cursor at the input's end.                        *)
let REC_END_HANDLER_TAB = prove
 (`!L progs bw ctl nctl budget E pl d m used r R cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
     rec_plan progs bw ctl budget E pl d m used r /\ pl d = pl_plan_end /\ val d + 64 <= 2 EXP 64 /\
     tab_rel_reads hol_tables L bw ctl nctl (word_sub E (word 312)) R /\
     (!a. R a ==> ~rec_stack E a /\ ~drv_in a (word_add d (word 40)) 24) /\
     progs 3 = eqw /\ progs 22 = fnv /\ rd_progs_ok progs /\ progs 29 = le8_next /\ progs 30 = at_end /\
     30 < nctl /\ cw 22 = val fnv_offset /\ rd_tab_apart L bw /\ ~(val budget < val used) /\
     tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl (word_sub E (word 312)) m inp c /\ FST r = word 1
     ==> cw 20 = 1 /\ cw 21 <= LENGTH inp /\
         rd_from inp c = APPEND (leb_enc (cw 17)) (le8 (fnv1a fnv_offset (list_of_seq (\j. EL j inp) (cw 21)))) /\
         ?cw'. cw' 19 = 1 /\ (!j. j < 24 /\ ~(j = 19) ==> cw' j = cw j) /\
               tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) (FST(SND r))
                 (cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
               rd_rel bw ctl nctl (word_sub E (word 312)) (FST(SND r)) inp (LENGTH inp)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  TAB_REC_PLAN_START_TAC `d:int64` `(cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate` THEN
  MP_TAC(ISPECL [`hol_tables`; `L:tabdesc list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
                 `nctl:num`; `budget:int64`; `word_sub E (word 312):int64`; `0`; `m':int64->byte`; `used:int64`;
                 `res:int64#num#(int64->byte)#int64`; `cw:num->num`; `(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`; `stk:num list`;
                 `inp:num list`; `c:num`] END_TAB) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    FIRST_X_ASSUM(fun th -> if is_const_app "drv_sem" (concl th) then
       ACCEPT_TAC(PURE_REWRITE_RULE[ASSUME `(pl:int64->(int64 list)list) d = pl_plan_end`] th) else failwith "");
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(MP (CONJUNCT2 th) (ASSUME `FST(res:int64#num#(int64->byte)#int64) = word 1`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `cw':num->num` STRIP_ASSUME_TAC)))) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  EXISTS_TAC `cw':num->num` THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TAB_REL_MOVE1_TAC `FST(SND(SND(res:int64#num#(int64->byte)#int64)))`);;

(* ------------------------------------------------------------------------- *)
(* The lookup: the decode, the opcode word, the table's entry.               *)
(* ------------------------------------------------------------------------- *)

let REC_LOOKUP_TAB = prove
 (`!L progs bw ctl nctl budget E pl dd ht nh opa m0 R m used r1
    cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp pos.
     tab_rel_reads hol_tables L bw ctl nctl (word_sub E (word 312)) R /\
     (!a. R a ==> ~rec_stack E a /\ ~drv_in a (word_add dd (word 40)) 24) /\
     val dd + 64 <= 2 EXP 64 /\ pl dd = pl_plan_dd /\ rd_progs_ok progs /\ 24 < nctl /\ rd_tab_apart L bw /\
     opa = word_add ctl (word (8 * 18)) /\
     tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl (word_sub E (word 312)) m inp pos /\ ~(val budget <= val used) /\
     rec_plan progs bw ctl budget E pl dd m (word_add used (word 1)) r1 /\ FST r1 = word 1 /\
     (!k. k < val nh ==> drv_word (FST(SND r1)) (word_add ht (word (8 * k))) =
                         drv_word m0 (word_add ht (word (8 * k)))) /\
     ~rec_missing ht nh opa (FST(SND r1))
     ==> SND(SND r1) = word_add used (word 1) /\
         ?op. leb_fires (rd_from inp pos) op /\ op < val nh /\
              ~(drv_word m0 (word_add ht (word (8 * op))) = word 0) /\
              rec_handler ht opa (FST(SND r1)) = drv_word m0 (word_add ht (word (8 * op))) /\
              tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) (FST(SND r1))
                (pl_set (pl_set cw 21 pos) 18 op,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
              rd_rel bw ctl nctl (word_sub E (word 312)) (FST(SND r1)) inp (pos + LENGTH (leb_enc op))`,
  let r1m = `FST(SND(r1:int64#(int64->byte)#int64))` in
  let opw = `val(drv_word (FST(SND(r1:int64#(int64->byte)#int64))) (word_add ctl (word (8 * 18)))) = op` in
  let agree_tm = `drv_word (FST(SND(r1:int64#(int64->byte)#int64))) (word_add ht (word (8 * op))) =
                  drv_word m0 (word_add ht (word (8 * op)))` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `opa:int64`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REC_USED1) THEN
  MP_TAC(SPECL ([`L:tabdesc list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `E:int64`;
                 `pl:int64->(int64 list)list`; `dd:int64`; `m:int64->byte`; `word_add used (word 1):int64`;
                 `r1:int64#(int64->byte)#int64`; `R:int64->bool`; `cw:num->num`] @ RD_NS_VARS @
                [`inp:num list`; `pos:num`]) REC_DECODE_TAB) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `op:num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN opw ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hol_tables`; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                   `word_sub E (word 312):int64`; r1m;
                   `(pl_set (pl_set cw 21 pos) 18 op,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate`;
                   `18`] TAB_REL_CW) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
    REWRITE_TAC[pl_mw; FST; PL_SET_IDX];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_const_app "rec_missing" (rand(concl th)))) THEN
  REWRITE_TAC[rec_missing; DE_MORGAN_THM; NOT_LE] THEN PURE_REWRITE_TAC[ASSUME opw] THEN STRIP_TAC THEN
  SUBGOAL_THEN agree_tm ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) && can (find_term ((=) r1m)) (concl th) &&
      can (find_term ((=) `m0:int64->byte`)) (concl th))) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  EXISTS_TAC `op:num` THEN REWRITE_TAC[rec_handler] THEN PURE_REWRITE_TAC[ASSUME opw] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  FIRST_X_ASSUM(fun th -> if is_neg(concl th) && can (find_term ((=) r1m)) (concl th) then MP_TAC th else failwith "") THEN
  PURE_REWRITE_TAC[ASSUME agree_tm] THEN DISCH_THEN ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The three kinds of entry: a record kind, END, the header.                 *)
(* ------------------------------------------------------------------------- *)

(* A record: HDR; the bytes at the cursor are the record's encoding, its     *)
(* nat_step holds, both relations hold in the loop's memory after it, CNT   *)
(* one more, the words 19..23 but RST kept.                                  *)
let REC_RECORD_TAB = prove
 (`!L progs bw ctl nctl budget E pl d H op m used r R cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp pos.
     rec_plan progs bw ctl budget E pl d m used r /\ pl d = H /\ val d + 64 <= 2 EXP 64 /\
     tab_rel_reads hol_tables L bw ctl nctl (word_sub E (word 312)) R /\
     (!a. R a ==> ~rec_stack E a /\ ~drv_in a (word_add d (word 40)) 24) /\
     tab_kind_contract hol_tables L hol_inv nat_step holr_rec_enc progs bw ctl nctl budget (word_sub E (word 312)) H op /\ ~(val budget < val used) /\
     op < 128 /\ leb_fires (rd_from inp pos) op /\
     tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) m
       (pl_set (pl_set cw 21 pos) 18 op,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     hol_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl (word_sub E (word 312)) m inp (pos + LENGTH (leb_enc op)) /\ FST r = word 1
     ==> cw 20 = 1 /\
         ?rec s'. (?rest. rd_from inp pos = APPEND (holr_rec_enc rec) rest) /\
                  nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) rec (FST(SND s')) /\ hol_inv s' /\
                  tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) (FST(SND r)) s' /\
                  rd_rel bw ctl nctl (word_sub E (word 312)) (FST(SND r)) inp
                         (pos + LENGTH (holr_rec_enc rec)) /\
                  FST s' 17 = cw 17 + 1 /\ (!j. 19 <= j /\ j < 24 /\ ~(j = 21) ==> FST s' j = cw j)`,
  let enc_eq = `holr_rec_enc rec = CONS op (TL (holr_rec_enc rec))` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `E:int64`;
                `pl:int64->(int64 list)list`; `d:int64`; `H:(int64 list)list`; `op:num`; `m:int64->byte`;
                `used:int64`; `r:int64#(int64->byte)#int64`; `R:int64->bool`;
                `pl_set (pl_set cw 21 pos) 18 op`; end_itlist (curry mk_pair) pl_ns_vars; `stk:num list`;
                `inp:num list`; `pos + LENGTH(leb_enc op)`] REC_HANDLER_TAB) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST
     [FIRST_ASSUM ACCEPT_TAC THEN NO_TAC;
      MATCH_MP_TAC HOL_INV_SET THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC HOL_INV_SET THEN REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ARITH_TAC; ARITH_TAC];
        ARITH_TAC; ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o CONV_RULE(TOP_DEPTH_CONV PL_SET_NUM_CONV))
    (X_CHOOSE_THEN `rec:holr_record` (X_CHOOSE_THEN `rest:num list` (X_CHOOSE_THEN `s':pstate`
      STRIP_ASSUME_TAC)))) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`rec:holr_record`; `s':pstate`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LEB_ENC_ONE) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [leb_fires] o
                check (fun th -> is_const_app "leb_fires" (concl th))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RD_FROM_APPEND o
              check (fun th -> is_eq(concl th) && lhs(concl th) = `rd_from inp pos`)) THEN
  RULE_ASSUM_TAC(PURE_REWRITE_RULE[ASSUME `leb_enc op = [op]`]) THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `rest:num list` THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [ASSUME enc_eq] THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `rd_from inp pos` then PURE_ONCE_REWRITE_TAC[th] else failwith "") THEN
    PURE_REWRITE_TAC[APPEND] THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && is_var(lhs(concl th)) && type_of(lhs(concl th)) = `:num list` &&
                             is_const_app "rd_from" (rhs(concl th)) then PURE_ONCE_REWRITE_TAC[th] else failwith "") THEN
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `pos + LENGTH (holr_rec_enc rec) = (pos + LENGTH [op:num]) + LENGTH (TL (holr_rec_enc rec))` SUBST1_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [ASSUME enc_eq] THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `FST(s':pstate) 17` then
       ACCEPT_TAC(CONV_RULE(TOP_DEPTH_CONV PL_SET_NUM_CONV) th) else failwith "");
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `FST(s':pstate)`)) (concl th) then
       MP_TAC(SPEC `j:num` th) else failwith "") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[pl_set] THEN ASM_SIMP_TAC[ARITH_RULE `19 <= j ==> ~(j = 18)`]]);;

(* ENDW in memory is word 0 exactly when the abstract word 19 is. *)
let REC_ENDW_TAB = prove
 (`!L inp bw ctl nctl cfr m s. tab_rel hol_tables L inp bw ctl nctl cfr m s /\ 19 < nctl
     ==> (drv_word m (word_add ctl (word (8 * 19))) = word 0 <=> FST s 19 = 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hol_tables`; `L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                `cfr:int64`; `m:int64->byte`; `s:pstate`; `19`] TAB_REL_CW) THEN
  ASM_REWRITE_TAC[pl_mw] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[VAL_EQ_0]);;

(* END: HDR; the input is the bytes before the opcode, the opcode, the count *)
(* and the checksum of the bytes before it; ENDW is set in the loop's memory. *)
let REC_END_RECORD_TAB = prove
 (`!L progs bw ctl nctl budget E pl d m used r R cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp pos.
     rec_plan progs bw ctl budget E pl d m used r /\ pl d = pl_plan_end /\ val d + 64 <= 2 EXP 64 /\
     tab_rel_reads hol_tables L bw ctl nctl (word_sub E (word 312)) R /\
     (!a. R a ==> ~rec_stack E a /\ ~drv_in a (word_add d (word 40)) 24) /\
     progs 3 = eqw /\ progs 22 = fnv /\ rd_progs_ok progs /\ progs 29 = le8_next /\ progs 30 = at_end /\
     30 < nctl /\ cw 22 = val fnv_offset /\ rd_tab_apart L bw /\ ~(val budget < val used) /\
     leb_fires (rd_from inp pos) 127 /\
     tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) m
       (pl_set (pl_set cw 21 pos) 18 127,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl (word_sub E (word 312)) m inp (pos + LENGTH (leb_enc 127)) /\ FST r = word 1
     ==> cw 20 = 1 /\
         inp = APPEND (list_of_seq (\j. EL j inp) pos)
                      (CONS 127 (APPEND (leb_enc (cw 17))
                                        (le8 (fnv1a fnv_offset (list_of_seq (\j. EL j inp) pos))))) /\
         ~(drv_word (FST(SND r)) (word_add ctl (word (8 * 19))) = word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL ([`L:tabdesc list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `E:int64`;
                 `pl:int64->(int64 list)list`; `d:int64`; `m:int64->byte`; `used:int64`;
                 `r:int64#(int64->byte)#int64`; `R:int64->bool`; `pl_set (pl_set cw 21 pos) 18 127`] @
                RD_NS_VARS @ [`inp:num list`; `pos + LENGTH (leb_enc 127)`]) REC_END_HANDLER_TAB) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    CONV_TAC(TOP_DEPTH_CONV PL_SET_NUM_CONV) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV PL_SET_NUM_CONV)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `cw':num->num` STRIP_ASSUME_TAC)))) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    GEN_REWRITE_TAC LAND_CONV [MATCH_MP RD_FROM_SPLIT (ASSUME `pos <= LENGTH(inp:num list)`)] THEN
    AP_TERM_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `rest:num list` o CONJUNCT2 o GEN_REWRITE_RULE I [leb_fires] o
                  check (fun th -> is_const_app "leb_fires" (concl th))) THEN
    FIRST_ASSUM(fun th -> PURE_ONCE_REWRITE_TAC[th] THEN PURE_ONCE_REWRITE_TAC[MATCH_MP RD_FROM_APPEND th]) THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `rd_from inp (pos + LENGTH (leb_enc 127))`
                          then PURE_ONCE_REWRITE_TAC[th] else failwith "") THEN
    REWRITE_TAC[MP (SPEC `127` LEB_ENC_ONE) (ARITH_RULE `127 < 128`); APPEND];
    MP_TAC(SPECL [`L:tabdesc list`; `inp:num list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `word_sub E (word 312):int64`;
                  `FST(SND(r:int64#(int64->byte)#int64))`;
                  `(cw',(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk):pstate`] REC_ENDW_TAB) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[FST] THEN PURE_REWRITE_TAC[ASSUME `(cw':num->num) 19 = 1`] THEN ARITH_TAC]);;

(* The header: no header before (HDR 0); the bytes at the cursor are the     *)
(* header of a policy p <= 2; the policy raised to p; HDR set, the words    *)
(* 17..23 but OPC, HDR and RST kept.                                         *)
let REC_HEADER_RECORD_TAB = prove
 (`!L progs bw ctl nctl budget E pl d H m used r R cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp pos.
     rec_plan progs bw ctl budget E pl d m used r /\ pl d = H /\ val d + 64 <= 2 EXP 64 /\
     tab_rel_reads hol_tables L bw ctl nctl (word_sub E (word 312)) R /\
     (!a. R a ==> ~rec_stack E a /\ ~drv_in a (word_add d (word 40)) 24) /\
     tab_header_contract L progs bw ctl nctl budget (word_sub E (word 312)) H /\ ~(val budget < val used) /\
     rd_hdr_rel bw (word_sub E (word 312)) m /\ (!a. drv_in a (bw 60) (val(bw 61)) ==> R a) /\
     leb_fires (rd_from inp pos) 72 /\
     tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) m
       (pl_set (pl_set cw 21 pos) 18 72,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     hol_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
     rd_rel bw ctl nctl (word_sub E (word 312)) m inp (pos + LENGTH (leb_enc 72)) /\ FST r = word 1
     ==> cw 20 = 0 /\
         ?p s'. p <= 2 /\ (?rest. rd_from inp pos = APPEND (holr_body p 0 []) rest) /\
                FST(SND s') = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,MAX pol p) /\ hol_inv s' /\
                tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) (FST(SND r)) s' /\
                rd_rel bw ctl nctl (word_sub E (word 312)) (FST(SND r)) inp
                       (pos + LENGTH (holr_body p 0 [])) /\
                FST s' 20 = 1 /\
                (!j. 17 <= j /\ j < 24 /\ ~(j = 18) /\ ~(j = 20) /\ ~(j = 21) ==> FST s' j = cw j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `leb_enc 72 = [72]` ASSUME_TAC THENL [MATCH_MP_TAC LEB_ENC_ONE THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL ([`L:tabdesc list`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `E:int64`;
                 `pl:int64->(int64 list)list`; `d:int64`; `H:(int64 list)list`; `m:int64->byte`; `used:int64`;
                 `r:int64#(int64->byte)#int64`; `R:int64->bool`; `pl_set (pl_set cw 21 pos) 18 72`] @
                RD_NS_VARS @ [`inp:num list`; `pos + LENGTH (leb_enc 72)`]) REC_HEADER_HANDLER_TAB) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST
     [FIRST_ASSUM ACCEPT_TAC THEN NO_TAC;
      MATCH_MP_TAC HOL_INV_SET THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC HOL_INV_SET THEN REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ARITH_TAC; ARITH_TAC];
        ARITH_TAC; ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o CONV_RULE(TOP_DEPTH_CONV PL_SET_NUM_CONV))
    (X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `rest:num list` (X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC)))) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `s':pstate`] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `rest0:num list` o CONJUNCT2 o GEN_REWRITE_RULE I [leb_fires] o
                check (fun th -> is_const_app "leb_fires" (concl th))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RD_FROM_APPEND o
              check (fun th -> is_eq(concl th) && lhs(concl th) = `rd_from inp pos`)) THEN
  SUBGOAL_THEN `LENGTH (holr_body p 0 []) = LENGTH (leb_enc 72) + LENGTH (TL (holr_body p 0 []))` ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [HOLR_BODY_HD] THEN
    REWRITE_TAC[LENGTH; ASSUME `leb_enc 72 = [72]`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    EXISTS_TAC `rest:num list` THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `rd_from inp pos` then PURE_ONCE_REWRITE_TAC[th] else failwith "") THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `rest0:num list` then PURE_ONCE_REWRITE_TAC[th] else failwith "") THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `rd_from inp (pos + LENGTH (leb_enc 72))`
                          then PURE_ONCE_REWRITE_TAC[th] else failwith "") THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [HOLR_BODY_HD] THEN
    REWRITE_TAC[ASSUME `leb_enc 72 = [72]`; APPEND];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    PURE_ONCE_REWRITE_TAC[ASSUME `LENGTH (holr_body p 0 []) = LENGTH (leb_enc 72) + LENGTH (TL (holr_body p 0 []))`] THEN
    PURE_REWRITE_TAC[ADD_ASSOC] THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `FST(s':pstate)`)) (concl th) then
       MP_TAC(SPEC `j:num` th) else failwith "") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[pl_set] THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The table, the invariant, one turn of the loop, the induction.            *)
(* ------------------------------------------------------------------------- *)

(* What a table entry k's plan H meets: END's plan at 127, the header        *)
(* contract at 72, opcode k's kind contract elsewhere.                       *)
let tab_rec_entry = new_definition
 `tab_rec_entry L progs bw ctl nctl budget cfr k (H:(int64 list)list) <=>
    (k = 127 ==> H = pl_plan_end) /\
    (k = 72 ==> tab_header_contract L progs bw ctl nctl budget cfr H) /\
    (~(k = 127) /\ ~(k = 72) ==> tab_kind_contract hol_tables L hol_inv nat_step holr_rec_enc progs bw ctl nctl budget cfr H k)`;;

(* The loop's memory m at the start of a turn: both relations hold and slot *)
(* 60 holds the header's constant, at a state whose ENDW is 0 and whose    *)
(* FNVB is FNV-1a's offset basis, with the                                  *)
(* handler table as in m0; before the header the cursor, CNT and HDR are 0 *)
(* and the native state is the bootstrap state under the host's floor; after *)
(* it HDR is 1, the bytes before the cursor are the body of a policy and    *)
(* CNT records, and those records' native steps lead from the bootstrap     *)
(* state under the larger policy to the state.                               *)
let tab_rec_inv = new_definition
 `tab_rec_inv L bw ctl nctl E (ht:int64) (nh:int64) (m0:int64->byte) hpol inp (m:int64->byte) <=>
    ?cw ctx nms tys ntms dbs ths nmap ymap drops pol stk pos.
      tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
      hol_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
      rd_rel bw ctl nctl (word_sub E (word 312)) m inp pos /\ rd_hdr_rel bw (word_sub E (word 312)) m /\
      cw 19 = 0 /\ cw 22 = val fnv_offset /\
      (!k. k < val nh ==> drv_word m (word_add ht (word (8 * k))) = drv_word m0 (word_add ht (word (8 * k)))) /\
      (cw 20 = 0 /\ cw 17 = 0 /\ pos = 0 /\
       (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) =
         (hinit_ctxt,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],hpol) \/
       cw 20 = 1 /\
       ?pol0 recs. pol0 <= 2 /\ cw 17 = LENGTH recs /\
                   list_of_seq (\j. EL j inp) pos = holr_body pol0 0 recs /\
                   tc_path nat_step recs
                     (hinit_ctxt,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],MAX hpol pol0)
                     (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol))`;;

(* The record program's static conditions: its layout and leaves, the plans *)
(* it may run, the set R the relations read (with slot 60, which no step of *)
(* any plan writes), the decode plan, the leaves                           *)
(* END reads, the opcode and END words, and a table whose entries meet      *)
(* their opcodes' contracts.                                                 *)
let tab_rec_static_tm =
 `rec_layout progs pcr pcd E r ht nh ds pl m0 opa enda ctl bind nbw leaves nl lpc lmc bw /\
  (!j. j < nl ==> tisa_leaf_wf (progs j) /\ tisa_leaf_spec (progs j) (lmc j) (lpc j)) /\
  ALL (rec_plan_ok progs pcd E ctl nctl bind nbw leaves nl lpc lmc bw pl m0) ds /\
  val ctl + 8 * nctl <= 2 EXP 64 /\
  tab_rel_reads hol_tables L bw ctl nctl (word_sub E (word 312)) R /\ (!a. R a ==> ~rec_stack E a) /\
  rd_tab_apart L bw /\
  (!d a. MEM d ds /\ R a ==> ~drv_in a (word_add d (word 40)) 24) /\
  (!a. drv_in a (bw 60) (val(bw 61)) ==> R a) /\
  (!d st a. MEM d ds /\ MEM st (pl d) /\
            ((?q. tisa_rw (tisa_decls (progs (val(EL 0 st)))) q /\
                  drv_in a (drv_base bw st q) (val(drv_len bw st q))) \/
             drv_in a (word_add ctl (word(8 * val(EL 17 st)))) 8)
            ==> ~drv_in a (bw 60) (val(bw 61))) /\
  MEM dd ds /\ pl dd = pl_plan_dd /\
  progs 3 = eqw /\ progs 22 = fnv /\ rd_progs_ok progs /\ progs 29 = le8_next /\ progs 30 = at_end /\
  30 < nctl /\ opa = word_add ctl (word (8 * 18)) /\ enda = word_add ctl (word (8 * 19)) /\ val nh <= 128 /\
  (!k. k < val nh /\ ~(drv_word m0 (word_add ht (word (8 * k))) = word 0)
       ==> MEM (drv_word m0 (word_add ht (word (8 * k)))) ds /\
           tab_rec_entry L progs bw ctl nctl budget (word_sub E (word 312)) k
                     (pl (drv_word m0 (word_add ht (word (8 * k))))))`;;

(* A run that ends FIRED has read a stream of a policy at most 2, whose      *)
(* records' native steps run from the bootstrap state under the larger      *)
(* policy (NAT_ACCEPTS_BOOT's premises).                                      *)
let tab_rec_static_names =
  ["L"; "progs"; "bw"; "ctl"; "nctl"; "budget"; "E"; "pl"; "dd"; "ht"; "nh"; "opa"; "enda"; "ds"; "m0"; "R";
   "hpol"; "inp"; "pcr"; "pcd"; "r"; "bind"; "nbw"; "leaves"; "nl"; "lpc"; "lmc"];;

(* Quantify tm's free variables in the order of names (all must be named). *)
let TAB_REC_INV_TAC pos_tm : tactic =
  let ns = `FST(SND(s':pstate))` in
  REWRITE_TAC[tab_rec_inv] THEN
  MAP_EVERY EXISTS_TAC ([`FST(s':pstate)`] @ map (pl_proj_ns ns) (0--9) @ [`SND(SND(s':pstate))`; pos_tm]) THEN
  REWRITE_TAC[PAIR];;

(* ENDW is 0 in the handler's memory, from the frame at 19. *)
let TAB_REC_ENDW0_TAC : tactic =
  SUBGOAL_THEN `drv_word (FST(SND(r2:int64#(int64->byte)#int64))) enda = word 0` ASSUME_TAC THENL
   [PURE_REWRITE_TAC[ASSUME `(enda:int64) = word_add ctl (word (8 * 19))`] THEN
    MP_TAC(rec_spec ["cfr", `word_sub E (word 312):int64`; "m", `FST(SND(r2:int64#(int64->byte)#int64))`;
                     "s", `s':pstate`] REC_ENDW_TAB) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]; DISCH_THEN SUBST1_TAC] THEN
    REC_FRAME_TAC 19 THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;

let tab_rec_step_goal =
  let dyn = `tab_rec_inv L bw ctl nctl E ht nh m0 hpol inp m /\ ~(val budget <= val used) /\
             rec_plan progs bw ctl budget E pl dd m (word_add used (word 1)) r1 /\ FST r1 = word 1 /\
             ~rec_missing ht nh opa (FST(SND r1)) /\
             rec_plan progs bw ctl budget E pl (rec_handler ht opa (FST(SND r1))) (FST(SND r1)) (SND(SND r1)) r2 /\
             FST r2 = word 1` in
  let cncl = mk_conj(`drv_word (FST(SND(r2:int64#(int64->byte)#int64))) enda = word 0
                      ==> tab_rec_inv L bw ctl nctl E ht nh m0 hpol inp (FST(SND r2))`,
                     mk_imp(`~(drv_word (FST(SND(r2:int64#(int64->byte)#int64))) enda = word 0)`, rec_done_tm)) in
  rec_order (tab_rec_static_names @ ["m"; "used"; "r1"; "r2"]) (mk_imp(mk_conj(tab_rec_static_tm, dyn), cncl));;

(* One turn of the loop whose handler FIRES: when ENDW stays 0 the invariant *)
(* holds again (the header or a record); when it is set (END), the run has  *)
(* read a whole stream.                                                      *)
let REC_STEP_TAB = prove(tab_rec_step_goal,
  let r1m = `FST(SND(r1:int64#(int64->byte)#int64))`
  and used1 = `SND(SND(r1:int64#(int64->byte)#int64))`
  and r2 = `r2:int64#(int64->byte)#int64` in
  let dop = `drv_word m0 (word_add ht (word (8 * op)))` in
  let dop_at k = subst [mk_small_numeral k, `op:num`] dop in
  let ns_tuple = end_itlist (curry mk_pair) pl_ns_vars in
  let is_tbl mt th = is_forall(concl th) && can (find_term ((=) `ht:int64`)) (concl th) &&
                     can (find_term ((=) mt)) (concl th) && can (find_term ((=) `m0:int64->byte`)) (concl th) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!d. MEM d ds ==> val(d:int64) + 64 <= 2 EXP 64` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> is_const_app "rec_layout" (concl th))) THEN
    REWRITE_TAC[rec_layout] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the invariant's state *)
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[tab_rec_inv] o check (fun th -> is_const_app "tab_rec_inv" (concl th))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC ([`cw:num->num`] @ RD_NS_VARS @ [`pos:num`]) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
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
  (* slot 60 in the decode's memory *)
  SUBGOAL_THEN `rd_hdr_rel bw (word_sub E (word 312)) (FST(SND(r1:int64#(int64->byte)#int64)))` ASSUME_TAC THENL
   [MATCH_MP_TAC RD_HDR_AGREE THEN EXISTS_TAC `m:int64->byte` THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
      MATCH_MP_TAC(rec_spec ["d", `dd:int64`; "used", `word_add used (word 1):int64`;
                             "rr", `r1:int64#(int64->byte)#int64`] REC_PLAN_HDR) THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* the decode's descriptor, the lookup *)
  SUBGOAL_THEN `!a. (R:int64->bool) a ==> ~rec_stack E a /\ ~drv_in a (word_add dd (word 40)) 24` ASSUME_TAC THENL
   [REC_RFACTS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(dd:int64) + 64 <= 2 EXP 64` ASSUME_TAC THENL [REC_D64_TAC; ALL_TAC] THEN
  MP_TAC(SPEC_ALL REC_LOOKUP_TAB) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `op:num` STRIP_ASSUME_TAC)) THEN
  (* the entry *)
  FIRST_ASSUM(MP_TAC o SPEC `op:num` o check (fun th -> is_forall(concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "tab_rec_entry")) (concl th))) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[tab_rec_entry] THEN STRIP_TAC THEN
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
  (* the table in the handler's memory *)
  SUBGOAL_THEN `!k. k < val(nh:int64)
                    ==> drv_word (FST(SND(r2:int64#(int64->byte)#int64))) (word_add ht (word (8 * k))) =
                        drv_word m0 (word_add ht (word (8 * k)))` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(rec_spec ["d", dop; "m", r1m; "used", used1; "rr", r2] REC_PLAN_TABLE) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (is_tbl r1m)) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* slot 60 in the handler's memory *)
  SUBGOAL_THEN `rd_hdr_rel bw (word_sub E (word 312)) (FST(SND(r2:int64#(int64->byte)#int64)))` ASSUME_TAC THENL
   [MATCH_MP_TAC RD_HDR_AGREE THEN EXISTS_TAC r1m THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
      MATCH_MP_TAC(rec_spec ["d", dop; "m", r1m; "used", used1; "rr", r2] REC_PLAN_HDR) THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `op < 128` ASSUME_TAC THENL
   [UNDISCH_TAC `op < val(nh:int64)` THEN UNDISCH_TAC `val(nh:int64) <= 128` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `op = 127` THENL
   [(* END *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && lhand(concl th) = `127 = 127`)) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(rec_spec ["d", dop_at 127; "m", r1m; "used", used1; "r", r2] REC_END_RECORD_TAB) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th))) THENL
     [REC_HDR_CONTRA_TAC;
      CONJ_TAC THENL
       [PURE_REWRITE_TAC[ASSUME `(enda:int64) = word_add ctl (word (8 * 19))`] THEN DISCH_TAC THEN REC_NEG_CONTRA_TAC;
        DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`pol0:num`; `recs:holr_record list`; ns_tuple] THEN
        REPEAT CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          REWRITE_TAC[holr_stream] THEN
          FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `inp:num list`
                                then GEN_REWRITE_TAC LAND_CONV [th] else failwith "") THEN
          FIRST_ASSUM(fun th -> if is_eq(concl th) && is_const_app "list_of_seq" (lhs(concl th))
                                then PURE_REWRITE_TAC[th] else failwith "") THEN
          FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `(cw:num->num) 17`
                                then PURE_REWRITE_TAC[th] else failwith "") THEN
          REFL_TAC;
          FIRST_ASSUM ACCEPT_TAC]]];
    ALL_TAC] THEN
  ASM_CASES_TAC `op = 72` THENL
   [(* the header *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && lhand(concl th) = `72 = 72`)) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(rec_spec ["d", dop_at 72; "H", mk_comb(`pl:int64->(int64 list)list`, dop_at 72);
                     "m", r1m; "used", used1; "r", r2] REC_HEADER_RECORD_TAB) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC THEN NO_TAC; REFL_TAC]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `s':pstate` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th))) THENL
     [FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o
                    check (fun th -> is_eq(concl th) && is_pair(lhs(concl th)))) THEN
      REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
               mem (lhs(concl th)) (`pos:num` :: pl_ns_vars)))) THEN
      TAB_REC_ENDW0_TAC THEN
      CONJ_TAC THENL [DISCH_TAC; DISCH_TAC THEN REC_NEG_CONTRA_TAC] THEN
      TAB_REC_INV_TAC `0 + LENGTH (holr_body p 0 [])` THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        REC_FRAME_TAC 19 THEN FIRST_ASSUM ACCEPT_TAC;
        REC_FRAME_TAC 22 THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        DISJ2_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY EXISTS_TAC [`p:num`; `[]:holr_record list`] THEN
        REPEAT CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          REWRITE_TAC[LENGTH] THEN REC_FRAME_TAC 17 THEN FIRST_ASSUM ACCEPT_TAC;
          FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `rd_from inp 0`
                                then SUBST1_TAC(MATCH_MP LIST_OF_SEQ_RD_FROM th) else failwith "") THEN
          REWRITE_TAC[list_of_seq; APPEND];
          REWRITE_TAC[tc_path] THEN
          FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `FST(SND(s':pstate))`
                                then REWRITE_TAC[th] else failwith "")]];
      REC_HDR_CONTRA_TAC];
    ALL_TAC] THEN
  (* a record kind *)
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "tab_kind_contract")) (concl th))) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(rec_spec ["d", dop; "H", mk_comb(`pl:int64->(int64 list)list`, dop); "m", r1m; "used", used1; "r", r2]
                  REC_RECORD_TAB) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC THEN NO_TAC; REFL_TAC]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `rec:holr_record` (X_CHOOSE_THEN `s':pstate`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th))) THENL
   [REC_HDR_CONTRA_TAC; ALL_TAC] THEN
  TAB_REC_ENDW0_TAC THEN
  CONJ_TAC THENL [DISCH_TAC; DISCH_TAC THEN REC_NEG_CONTRA_TAC] THEN
  TAB_REC_INV_TAC `pos + LENGTH (holr_rec_enc rec)` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    REC_FRAME_TAC 19 THEN FIRST_ASSUM ACCEPT_TAC;
    REC_FRAME_TAC 22 THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    DISJ2_TAC THEN CONJ_TAC THENL [REC_FRAME_TAC 20 THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`pol0:num`; `APPEND recs [rec:holr_record]`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
      FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `FST(s':pstate) 17`
                            then PURE_REWRITE_TAC[th] else failwith "") THEN
      FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `(cw:num->num) 17`
                            then PURE_REWRITE_TAC[th] else failwith "") THEN
      ARITH_TAC;
      FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `rd_from inp pos`
                            then SUBST1_TAC(MATCH_MP LIST_OF_SEQ_RD_FROM th) else failwith "") THEN
      FIRST_ASSUM(fun th -> if is_eq(concl th) && is_const_app "list_of_seq" (lhs(concl th))
                            then PURE_REWRITE_TAC[th] else failwith "") THEN
      REWRITE_TAC[HOLR_BODY_SNOC];
      MATCH_MP_TAC TC_PATH_SNOC THEN EXISTS_TAC ns_tuple THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]]);;

let tab_rec_induction_goal =
  let run = `rec_run progs bw ctl budget E pl dd ht nh opa enda m used c res` in
  let inner = list_mk_forall([`m:int64->byte`; `used:int64`; `c:num`; `res:int64#num#(int64->byte)#int64`],
                mk_imp(run, mk_imp(`tab_rec_inv L bw ctl nctl E ht nh m0 hpol inp m /\
                                    FST(res:int64#num#(int64->byte)#int64) = word 1`, rec_done_tm))) in
  rec_order tab_rec_static_names (mk_imp(tab_rec_static_tm, inner));;

(* REC_INDUCTION_TAB: from a memory meeting the invariant, a run of the record   *)
(* loop that ends FIRED has read a stream of a policy p <= 2 whose records' *)
(* native steps run from the bootstrap state under the larger policy.       *)
let REC_INDUCTION_TAB = prove(tab_rec_induction_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC rec_run_INDUCT THEN REWRITE_TAC[FST] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[];
    MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[];
    MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
    MP_TAC(SPEC_ALL REC_STEP_TAB) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN FIRST_ASSUM ACCEPT_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) && is_conj(lhand(concl th)) &&
                                                  is_const_app "tab_rec_inv" (lhand(lhand(concl th))))) THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC_ALL REC_STEP_TAB) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC]]);;

(* With NAT_ACCEPTS_BOOT: the stream the run read is accepted under the      *)
(* host's floor.                                                             *)
let REC_ACCEPTS_TAB = prove
 (rec_order (tab_rec_static_names @ ["m"; "used"; "c"; "res"])
   (mk_imp(list_mk_conj [tab_rec_static_tm; `rec_run progs bw ctl budget E pl dd ht nh opa enda m used c res`;
                         `tab_rec_inv L bw ctl nctl E ht nh m0 hpol inp m`;
                         `FST(res:int64#num#(int64->byte)#int64) = word 1`],
           `holr_accepts hpol inp`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL REC_INDUCTION_TAB) THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:int64->byte`; `used:int64`; `c:num`; `res:int64#num#(int64->byte)#int64`]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`pol:num`; `recs:holr_record list`; `ns:nstate`] THEN STRIP_TAC THEN
  MATCH_MP_TAC NAT_ACCEPTS_BOOT THEN
  MAP_EVERY EXISTS_TAC [`pol:num`; `recs:holr_record list`; `ns:nstate`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* The bootstrap state meets HOL's invariant, whatever the policy, for any   *)
(* control words that hold 0..6 at 0..6 and FNVB, with an empty stack.       *)
let HOL_INV_BOOT = prove
 (`!cw hpol. (!n. n <= 6 ==> cw n = n) /\ cw 22 = val fnv_offset /\ cw 7 = hpol
     ==> hol_inv (cw,(hinit_ctxt,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],hpol),[])`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HOL_INV; MEM; PL_INV_BOOT]);;

(* The bootstrap memory meets the invariant: both relations at the bootstrap *)
(* state and cursor 0, the header's constant in slot 60, CNT, ENDW and HDR 0, *)
(* FNVB the offset basis (HOL_INV_BOOT).                                       *)
let REC_BOOT_TAB = prove
 (`!L bw ctl nctl E ht nh m0 hpol inp cw0.
     tab_rel hol_tables L inp bw ctl nctl (word_sub E (word 312)) m0
       (cw0,(hinit_ctxt,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],hpol),[]) /\
     rd_rel bw ctl nctl (word_sub E (word 312)) m0 inp 0 /\ rd_hdr_rel bw (word_sub E (word 312)) m0 /\
     cw0 17 = 0 /\ cw0 19 = 0 /\ cw0 20 = 0 /\ cw0 22 = val fnv_offset /\ cw0 7 = hpol
     ==> tab_rec_inv L bw ctl nctl E ht nh m0 hpol inp m0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tab_rec_inv] THEN
  MAP_EVERY EXISTS_TAC [`cw0:num->num`; `hinit_ctxt`; `nat_boot_nms`; `nat_boot_tys`;
                        `[]:(num#num#num#num#num)list`; `nat_boot_dbs`; `[]:(num#num)list`; `[]:num list`;
                        `[]:num list`; `[]:(num#num)list`; `hpol:num`; `[]:num list`; `0`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOL_INV_BOOT THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_const_app "tab_rel" (concl th))) THEN
  REWRITE_TAC[tab_rel] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The record loop's call, entry to return, with its verdict's meaning: when  *)
(* the loop returns FIRED (RAX = 1), the input it read is a stream HOLR      *)
(* accepts under the host's floor (REC_CORRECT with REC_ACCEPTS_TAB).            *)
(* ------------------------------------------------------------------------- *)

let tab_rec_x86_goal =
  let _, body = strip_forall(concl REC_CORRECT) in
  let prem, ens = dest_imp body in
  let f, frame = dest_comb ens in
  let f2, post = dest_comb f in
  let s, pb = dest_abs post in
  let acc = vsubst [s, `s:x86state`] `read RAX (s:x86state) = word 1 ==> holr_accepts hpol inp` in
  let post' = mk_abs(s, mk_conj(pb, acc)) in
  let ens' = mk_comb(mk_comb(f2, post'), frame) in
  let prems = list_mk_conj [prem; tab_rec_static_tm; `tab_rec_inv L bw ctl nctl E ht nh m0 hpol inp m0`] in
  let tm = mk_imp(prems, ens') in
  list_mk_forall(frees tm, tm);;

let REC_X86_ACCEPTS_TAB = prove(tab_rec_x86_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (let _, body = strip_forall(concl REC_CORRECT) in rand(rator(rand body))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_TAC THEN
      MP_TAC(rec_spec ["m", `m0:int64->byte`; "used", `used0:int64`; "c", `0`;
                       "res", `res:int64#num#(int64->byte)#int64`] REC_ACCEPTS_TAB) THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      ACCEPT_TAC(TRANS (SYM(ASSUME `read RAX (s:x86state) = FST(res:int64#num#(int64->byte)#int64)`))
                       (ASSUME `read RAX (s:x86state) = word 1`))];
    MP_TAC(SPEC_ALL REC_CORRECT) THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]);;

(* Every theorem this file states, for the audits. *)
let rec_induction_tab_theorems =
 ["TAB_REL_READS_TAB", TAB_REL_READS_TAB; "TAB_REL_READS_RD", TAB_REL_READS_RD;
  "REC_DECODE_TAB", REC_DECODE_TAB; "REC_HANDLER_TAB", REC_HANDLER_TAB;
  "REC_HEADER_HANDLER_TAB", REC_HEADER_HANDLER_TAB; "REC_END_HANDLER_TAB", REC_END_HANDLER_TAB;
  "REC_LOOKUP_TAB", REC_LOOKUP_TAB; "REC_RECORD_TAB", REC_RECORD_TAB; "REC_ENDW_TAB", REC_ENDW_TAB;
  "REC_END_RECORD_TAB", REC_END_RECORD_TAB; "REC_HEADER_RECORD_TAB", REC_HEADER_RECORD_TAB;
  "REC_STEP_TAB", REC_STEP_TAB; "REC_INDUCTION_TAB", REC_INDUCTION_TAB; "REC_ACCEPTS_TAB", REC_ACCEPTS_TAB;
  "HOL_INV_BOOT", HOL_INV_BOOT; "REC_BOOT_TAB", REC_BOOT_TAB; "REC_X86_ACCEPTS_TAB", REC_X86_ACCEPTS_TAB];;
