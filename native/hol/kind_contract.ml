(* ========================================================================= *)
(* The kind contract: what the record loop needs of a handler, whatever its  *)
(* operands. A handler H for opcode op, run from a state whose relations    *)
(* hold at the cursor c (the byte after the opcode): when it FIRES, the     *)
(* bytes at c are the rest of some record rec's encoding, whose first byte  *)
(* is op; the header was seen (HDR); the record's nat_step holds; both     *)
(* relations hold after it at the cursor past the record; the count is one *)
(* more and the words 18..23 (OPC, ENDW, HDR, RST, FNVB) are kept. The      *)
(* record loop's induction takes a table of such handlers; each compiled    *)
(* kind meets the contract by its handler theorem and its encoding         *)
(* (kind_contract_of), its unbuilt leaves as premises.                       *)
(*                                                                           *)
(* Loaded after handler_compiler.ml.                                         *)
(* ========================================================================= *)

needs "native/hol/handler_compiler.ml";;
needs "native/hol/reader_hdr.ml";;

let kind_contract = new_definition
 `kind_contract progs bw ctl nctl budget cfr H op <=>
    !m used res cw ns stk inp c.
      drv_sem progs bw ctl budget cfr H 0 m used res /\
      plan_rel bw ctl nctl cfr m (cw,ns,stk) /\ pl_inv (cw,ns,stk) /\
      rd_rel bw ctl nctl cfr m inp c /\ ~(val budget < val used)
      ==> (FST res = word 1
           ==> cw 20 = 1 /\
               ?rec rest s'. holr_rec_enc rec = CONS op (TL (holr_rec_enc rec)) /\
                             rd_from inp c = APPEND (TL (holr_rec_enc rec)) rest /\
                             nat_step ns rec (FST(SND s')) /\ pl_inv s' /\
                             plan_rel bw ctl nctl cfr (FST(SND(SND res))) s' /\
                             rd_rel bw ctl nctl cfr (FST(SND(SND res))) inp
                                    (c + LENGTH (TL (holr_rec_enc rec))) /\
                             FST s' 17 = cw 17 + 1 /\
                             (!j. 18 <= j /\ j < 24 ==> FST s' j = cw j))`;;

(* A handler theorem (HANDLER_<KIND>, kind_handler's normal form) gives its  *)
(* kind's contract: HDR from its prefix, the record is the one its nat_step *)
(* names, its encoding by holr_rec_enc, the words 18..23 from the frame.   *)
let CONTRACT_TAC handler_th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[kind_contract] THEN
  REPEAT GEN_TAC THEN SPEC_TAC(`ns:nstate`,`ns:nstate`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC pl_ns_vars THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL handler_th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC(MP (CONJUNCT1 th) (ASSUME `FST(res:int64#num#(int64->byte)#int64) = word 1`))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [leb_fires] o
                    check (fun th -> is_const_app "leb_fires" (concl th)))) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_const_app "nat_step" (concl th)
                        then EXISTS_TAC (el 1 (snd(strip_comb(concl th)))) else failwith "") THEN
  MAP_EVERY EXISTS_TAC [`rest:num list`; `s':pstate`] THEN
  REWRITE_TAC[holr_rec_enc; TL] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `FST(s':pstate)`)) (concl th)
                        then MP_TAC(SPEC `j:num` th) else failwith "") THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[pl_set] THEN
  ASM_SIMP_TAC[ARITH_RULE `18 <= j ==> ~(j = 8) /\ ~(j = 9) /\ ~(j = 10) /\ ~(j = 11)`;
               ARITH_RULE `j < 24 ==> ~(j = 24)`];;

(* The contract's statement for a compiled handler: the handler theorem's    *)
(* static premises (those that name no state, run or input) outside.        *)
let kind_contract_goal handler_th op =
  let _, body = strip_forall(concl handler_th) in
  let ant, _ = dest_imp body in
  let dyn = [`m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`; `cw:num->num`;
             `stk:num list`; `inp:num list`; `c:num`] @ pl_ns_vars in
  let static = filter (fun p -> not (exists (fun v -> vfree_in v p) dyn)) (conjuncts ant) in
  let drv = find (fun p -> is_const_app "drv_sem" p) (conjuncts ant) in
  let h = el 5 (snd(strip_comb drv)) in
  let cncl = list_mk_icomb "kind_contract" [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`;
                                            `budget:int64`; `cfr:int64`; h; op] in
  let body = mk_imp(list_mk_conj static, cncl) in
  list_mk_forall(filter (fun v -> vfree_in v body)
    [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`; `cfr:int64`], body);;

let kind_contract_of handler_th op = prove(kind_contract_goal handler_th op, CONTRACT_TAC handler_th);;

(* The kinds with handler theorems: REFL (hand-built), ASSUME, TRANS, EQ_MP, *)
(* MK_COMB (compiled; the last three with leaf 7 as premises).              *)
let KC_REFL = kind_contract_of HANDLER_REFL_REL `16`;;
let KC_ASSUME = kind_contract_of HANDLER_ASSUME `21`;;
let KC_TRANS = kind_contract_of HANDLER_TRANS `17`;;
let KC_EQMP = kind_contract_of HANDLER_EQMP `22`;;
let KC_MKCOMB = kind_contract_of HANDLER_MKCOMB `18`;;

let kind_contract_theorems =
 ["KC_REFL", KC_REFL; "KC_ASSUME", KC_ASSUME; "KC_TRANS", KC_TRANS; "KC_EQMP", KC_EQMP;
  "KC_MKCOMB", KC_MKCOMB];;

(* ------------------------------------------------------------------------- *)
(* The header contract: the header's handler H, run from a state whose      *)
(* relations hold at the cursor c (the byte after the opcode 72), with the  *)
(* header's constant in slot 60 (rd_hdr_rel): when it                       *)
(* FIRES, no header was seen (HDR 0); the bytes at c are the rest of the     *)
(* header of a policy p <= 2 (holr_body p 0 [] after its first byte); the  *)
(* native state is the same with the policy raised to p; both relations     *)
(* hold after it at the cursor past the header; HDR is set and the words    *)
(* 17..23 but HDR are kept.                                                  *)
(* ------------------------------------------------------------------------- *)

let header_contract = new_definition
 `header_contract progs bw ctl nctl budget cfr H <=>
    !m used res cw ctx nms tys ntms dbs ths nmap ymap drops pol stk inp c.
      drv_sem progs bw ctl budget cfr H 0 m used res /\
      plan_rel bw ctl nctl cfr m (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
      pl_inv (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk) /\
      rd_rel bw ctl nctl cfr m inp c /\ rd_hdr_rel bw cfr m /\ ~(val budget < val used)
      ==> (FST res = word 1
           ==> cw 20 = 0 /\
               ?p rest s'. p <= 2 /\ rd_from inp c = APPEND (TL (holr_body p 0 [])) rest /\
                           FST(SND s') = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,MAX pol p) /\
                           pl_inv s' /\
                           plan_rel bw ctl nctl cfr (FST(SND(SND res))) s' /\
                           rd_rel bw ctl nctl cfr (FST(SND(SND res))) inp
                                  (c + LENGTH (TL (holr_body p 0 []))) /\
                           FST s' 20 = 1 /\ (!j. 17 <= j /\ j < 24 /\ ~(j = 20) ==> FST s' j = cw j))`;;

(* The header plan meets the header contract (HDR_CONTRACT_FORM). *)
let HC_HDR = prove
 (`!progs bw ctl nctl budget cfr.
     progs 3 = eqw /\ rd_progs_ok progs /\ progs 31 = const_next /\ progs 20 = pol_max /\ 27 < nctl
     ==> header_contract progs bw ctl nctl budget cfr pl_plan_hdr`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[header_contract] THEN
  MATCH_MP_TAC(SPEC_ALL HDR_CONTRACT_FORM) THEN FIRST_ASSUM ACCEPT_TAC);;

let kind_contract_theorems = kind_contract_theorems @ ["HC_HDR", HC_HDR];;
