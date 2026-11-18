needs "native/hol/boot_memory.ml";;

(* ========================================================================= *)
(* The bootstrap tables. From empty tables, the boot plan interns HOL's     *)
(* bootstrap rows with the leaves the record plans use: the names bool,     *)
(* fun, = and A, read from a constant region of their bytes (boot_bytes,    *)
(* bound at slot 62 as fnv's and intern_name's input); then the nine type   *)
(* rows of nat_boot_tys and the de Bruijn nil row, each packed and          *)
(* interned. Every name's offset and length in the boot bytes is one of the *)
(* constant words K0..K6, and every type row names the ids the steps before *)
(* it returned.                                                              *)
(*                                                                           *)
(* A run of the plan FIRES exactly into the bootstrap state, and otherwise   *)
(* stops with a resource outcome (a table too small) at a state whose       *)
(* terms, theorems, maps and drops are still empty; it never REFUSES and    *)
(* writes no control word below the temporaries (BOOT_RUN). Through the     *)
(* driver, from memory related to empty tables, the same holds of the      *)
(* memory it leaves (BOOT_TAB). Memory is related to empty tables when the  *)
(* regions are long enough (hol_boot_lengths), the count words, the names'  *)
(* used-bytes word and every mark word are zero (hol_boot_zero) and slot 62 *)
(* holds the boot bytes (hol_boot_bytes_at): BOOT_FRESH_TAB. The boot       *)
(* layout binds the boot bytes where HOL's full layout binds the input; the *)
(* two relations agree on every other table (BOOT_LAYOUT_SWAP). A boot run  *)
(* that FIRES leaves memory at which the record loop's invariant holds,     *)
(* with the reader at the input's start (BOOT_START).                       *)
(*                                                                           *)
(* Loaded after every_tab.ml.                                                *)
(* ========================================================================= *)

(* "=Aboolfun". *)

let BOOT_BYTES_NAMES = prove
 (`tab_key boot_bytes 2 4 = hname_bytes "bool" /\ tab_key boot_bytes 6 3 = hname_bytes "fun" /\
   tab_key boot_bytes 0 1 = hname_bytes "=" /\ tab_key boot_bytes 1 1 = hname_bytes "A"`,
  REWRITE_TAC[tab_key; boot_bytes; hname_bytes; MAP; hchar_code] THEN
  CONV_TAC(DEPTH_CONV LIST_OF_SEQ_CONV) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* The boot layout: HOL's tables, the boot bytes as the input. *)
let hol_boot_layout = new_definition
 `hol_boot_layout = APPEND hol_layout_old
                      [RowTab 24 26 1; MarkTab 28 24 26 1; RowTab 30 32 1; MarkTab 34 30 32 1;
                       NameTab 44; InTab 62]`;;

let HOL_BOOT_LAYOUT_WF = prove
 (`tab_wf hol_boot_layout`,
  REWRITE_TAC[tab_wf; hol_boot_layout; hol_layout_old; APPEND] THEN CONJ_TAC THENL
   [REWRITE_TAC[tab_slots; ITLIST; tab_dslots; APPEND; PAIRWISE; ALL] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[MEM; injectivity "tabdesc"; distinctness "tabdesc"] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let HOL_BOOT_LAYOUT_MEMS = prove
 (`MEM (KeyTab 0) hol_boot_layout /\ MEM (KeyTab 6) hol_boot_layout /\
   MEM (NameTab 44) hol_boot_layout /\ MEM (InTab 62) hol_boot_layout`,
  REWRITE_TAC[hol_boot_layout; hol_layout_old; APPEND; MEM]);;

(* The plan: four names (fnv of their bytes, then intern_name), then the     *)
(* type rows nil, bool, A, [bool], [A; bool], A->bool, [A->bool],            *)
(* [A; A->bool], A->A->bool (each packed, then interned), then the de       *)
(* Bruijn nil row.                                                           *)
let pl_BOOTIN = [62] and pl_BOOTNAMES = [62; 44; 46; 48; 50];;
pl_begin();;
let _ = let name off len = let h = pl_emit pl_FNV pl_BOOTIN off len [pl_FNVB] in
                           pl_emit pl_INAME pl_BOOTNAMES off len [h] in
        let nb = name 2 4 in let nf = name 6 3 in let _ = name 0 1 in let na = name 1 1 in
        let nil = pl_ity 2 0 0 in
        let bool = pl_ity 1 nb nil in
        let a = pl_ity 0 na 0 in
        let l1 = pl_ity 3 bool nil in
        let l2 = pl_ity 3 a l1 in
        let ab = pl_ity 1 nf l2 in
        let l3 = pl_ity 3 ab nil in
        let l4 = pl_ity 3 a l3 in
        let _ = pl_ity 1 nf l4 in
        pl_idb 5 0 0;;
let pl_plan_boot = new_definition(mk_eq(`pl_plan_boot:(int64 list)list`, pl_plan()));;

let BOOT_BYTES_LENGTH = prove
 (`LENGTH boot_bytes = 9`,
  REWRITE_TAC[boot_bytes; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let HNAME_BYTES_11 = prove
 (`!a b. hname_bytes a = hname_bytes b <=> a = b`,
  MESON_TAC[HOLR_NAME_BYTES]);;

(* Interning a name the table does not hold appends it, or is a resource   *)
(* outcome that keeps the state.                                             *)
let BOOT_INTERN_NAME = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol key k pay s'.
     ~MEM key (MAP hname_bytes nms) /\ ALL (\b. b < 256) key
     ==> (tab_intern hol_trow hol_tn hol_tapp 44 50 (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) key k pay s' <=>
          k = 1 /\ pay = LENGTH nms /\ LENGTH nms + 1 < 2 EXP 60 /\
          s' = (ctx,APPEND nms [holr_name key],tys,ntms,dbs,ths,nmap,ymap,drops,pol) \/
          ~(k = 0) /\ ~(k = 1) /\ s' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tab_intern; hol_trow; hol_tn; hol_tapp] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!i. i < LENGTH (nms:string list) ==> ~(hname_bytes (EL i nms) = key)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `~MEM (key:num list) (MAP hname_bytes nms)` THEN
    REWRITE_TAC[MEM_EXISTS_EL; LENGTH_MAP] THEN EXISTS_TAC `i:num` THEN ASM_SIMP_TAC[EL_MAP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(ASM_ARITH_TAC THEN NO_TAC) THEN ASM_MESON_TAC[]);;

(* Interning a key the canonical rows of a keyed table do not hold. *)
let BOOT_INTERN_KEY_TAC th rows =
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_EL] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun c -> REWRITE_TAC[MATCH_MP th c]) THEN
  REWRITE_TAC[pl_intern; pl_interned] THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST [EXISTS_TAC rows THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         EXISTS_TAC (mk_comb(mk_comb(`APPEND:(num#num#num)list->(num#num#num)list->(num#num#num)list`, rows),
                             `[pl_key a0 a1]`)) THEN
         ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
          [ASM_ARITH_TAC; EXISTS_TAC `[pl_key a0 a1]` THEN REWRITE_TAC[]];
         ASM_MESON_TAC[MEM_EXISTS_EL]];;

let BOOT_INTERN_TY = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol a0 a1 k pay s'.
     ALL (\r:num#num#num. FST r < 8) tys /\ ~MEM (pl_key a0 a1) tys
     ==> (tab_intern hol_trow hol_tn hol_tapp 0 4 (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) [a0; a1] k pay s' <=>
          k = 1 /\ pay = LENGTH tys /\ LENGTH tys + 1 < 2 EXP 60 /\
          s' = (ctx,nms,APPEND tys [pl_key a0 a1],ntms,dbs,ths,nmap,ymap,drops,pol) \/
          ~(k = 0) /\ ~(k = 1) /\ s' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol))`,
  BOOT_INTERN_KEY_TAC TAB_INTERN_HOL_TY `tys:(num#num#num)list`);;

let BOOT_INTERN_DB = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol a0 a1 k pay s'.
     ALL (\r:num#num#num. FST r < 8) dbs /\ ~MEM (pl_key a0 a1) dbs
     ==> (tab_intern hol_trow hol_tn hol_tapp 6 10 (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) [a0; a1] k pay s' <=>
          k = 1 /\ pay = LENGTH dbs /\ LENGTH dbs + 1 < 2 EXP 60 /\
          s' = (ctx,nms,tys,ntms,APPEND dbs [pl_key a0 a1],ths,nmap,ymap,drops,pol) \/
          ~(k = 0) /\ ~(k = 1) /\ s' = (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol))`,
  BOOT_INTERN_KEY_TAC TAB_INTERN_HOL_DB `dbs:(num#num#num)list`);;

(* ------------------------------------------------------------------------- *)
(* The plan's run, step by step over the concrete tables.                    *)
(* ------------------------------------------------------------------------- *)

(* A side condition of the interning lemmas, decided on concrete rows. *)
let BOOT_SIDE_CONV =
  REWRITE_CONV[MEM; MAP; ALL; HNAME_BYTES_11; HNAME_BYTES_LT; pl_key; PAIR_EQ; APPEND; FST] THENC
  NUM_REDUCE_CONV THENC DEPTH_CONV STRING_EQ_CONV THENC REWRITE_CONV[];;

(* tab_intern over concrete rows, by the interning lemmas. *)
let BOOT_INTERN_CONV tm =
  let try_th th =
    let ith = PART_MATCH (lhs o rand) th tm in
    MP ith (EQT_ELIM(BOOT_SIDE_CONV(lhand(concl ith)))) in
  tryfind try_th [BOOT_INTERN_NAME; BOOT_INTERN_TY; BOOT_INTERN_DB];;

(* Concrete rows: appended lists and keys as literals. *)
let BOOT_NORM_CONV =
  REWRITE_CONV[APPEND; LENGTH; HOLR_NAME_BYTES; pl_key] THENC NUM_REDUCE_CONV;;

(* A step's leaf fact over the concrete state, as outcomes. *)
let BOOT_FACT_RULE asl th =
  let cws = filter TAB_CW_EQ (map snd asl) in
  CONV_RULE (REWRITE_CONV cws THENC
             REWRITE_CONV[tab_fnv; tab_name; pl_pack; BOOT_BYTES_LENGTH; WORD_VAL] THENC NUM_REDUCE_CONV THENC
             REWRITE_CONV[BOOT_BYTES_NAMES] THENC
             ONCE_DEPTH_CONV(fun t -> if is_const_app "tab_intern" t then BOOT_INTERN_CONV t
                                      else failwith "") THENC
             BOOT_NORM_CONV THENC REWRITE_CONV[]) th;;

let BOOT_STEP_TAC =
  GEN_REWRITE_TAC LAND_CONV [CONJUNCT2 tab_run] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV(fun t -> if TAB_LEAF_TERM t then TAB_LEAF_CONV t else failwith "TAB_HEAD"))) THEN
  CONV_TAC(LAND_CONV PL_NORM_CONV) THEN REWRITE_TAC[FST; SND; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> W(fun (asl,_) ->
    let fact = BOOT_FACT_RULE asl (CONJUNCT1 th) in
    MP_TAC (CONJUNCT2 th) THEN STRIP_ASSUME_TAC fact)) THEN
  PL_SUBST_ALL_TAC THEN CONV_TAC(LAND_CONV(NUM_REDUCE_CONV THENC REWRITE_CONV[])) THEN
  TRY(FIRST_ASSUM(fun th -> let c = concl th in
        if is_neg c && is_eq(rand c) && rhs(rand c) = `1` then REWRITE_TAC[th] else failwith ""));;

(* The end of a run: its result, and what holds of it. *)
let BOOT_END_TAC =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN PL_SUBST_ALL_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  REPEAT CONJ_TAC THEN
  W(fun (_,w) ->
    if is_forall w then PL_SET_LOW_TAC
    else if is_exists w then REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]
    else REWRITE_TAC[nat_boot_nms; nat_boot_tys; nat_boot_dbs; PAIR_EQ] THEN CONV_TAC NUM_REDUCE_CONV);;

let rec BOOT_RUN_TAC g =
  let w = snd g in
  if not (is_imp w) then ALL_TAC g else
  let a = lhand w in
  if is_const_app "tab_run" a then
    let sts = el 2 (snd(strip_comb a)) in
    if is_const sts && fst(dest_const sts) = "NIL"
    then (GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 tab_run] THEN BOOT_END_TAC) g
    else (BOOT_STEP_TAC THEN BOOT_RUN_TAC) g
  else if is_eq a then BOOT_END_TAC g
  else ALL_TAC g;;

let BOOT_RUN = prove
 (`!cw ctx pol k j cw' ns' stk'.
     (!n. n <= 6 ==> cw n = n) /\ cw 22 = val fnv_offset /\
     tab_run hol_tables boot_bytes pl_plan_boot 0 (cw,(ctx,[],[],[],[],[],[],[],[],pol),[]) (k,j,(cw',ns',stk'))
     ==> ~(k = 0) /\ stk' = [] /\ (!n. n < 24 ==> cw' n = cw n) /\
         (k = 1 ==> ns' = (ctx,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],pol)) /\
         (?nms tys dbs. ns' = (ctx,nms,tys,[],dbs,[],[],[],[],pol))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN DISCH_TAC THEN
  MAP_EVERY (fun n -> ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV
                        (SPEC (mk_small_numeral n) (ASSUME `!n. n <= 6 ==> cw n = n`)))) (0--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN REWRITE_TAC[pl_plan_boot] THEN BOOT_RUN_TAC);;

(* ------------------------------------------------------------------------- *)
(* Through the driver: every step's leaf implements its meaning over the     *)
(* boot layout, and the plan is safe from empty tables.                      *)
(* ------------------------------------------------------------------------- *)

let TAB_BOOT_BRIDGE st =
  let ws = map (fun t -> dest_small_numeral(rand t)) (dest_list st) in
  let leaf = el 0 ws and b1 = el 1 ws and b2 = el 2 ws in
  let h th = ISPECL [`hol_trow`; `hol_tn`; `hol_twd`; `hol_tdrop`; `hol_tapp`; `hol_tput`; `hol_boot_layout`] th in
  let inst th l = INST (map (fun (v,n) -> (mk_small_numeral n, mk_var(v,`:num`))) l) (SPEC_ALL (h th)) in
  match leaf with
    0 -> inst TAB_IMPL_I16 ["j",b1]
  | 1 -> inst TAB_IMPL_PACK []
  | 22 -> inst TAB_IMPL_FNV ["ji",b1]
  | 23 -> inst TAB_IMPL_NAME ["ji",b1; "j",b2]
  | _ -> failwith "TAB_BOOT_BRIDGE: a leaf the boot plan does not use";;

let TAB_BOOT_IMPL_TAC : tactic = fun (asl,w) ->
  (REWRITE_TAC[hol_tables] THEN MATCH_MP_TAC (TAB_BOOT_BRIDGE (rand w)) THEN
   ASM_REWRITE_TAC[HOL_BOOT_LAYOUT_MEMS; HOL_BOOT_LAYOUT_WF; HOL_TB_OK] THEN
   CONV_TAC TAB_REDUCE_CONV THEN REWRITE_TAC[HOL_TAPP_EXISTS]) (asl,w);;

let BOOT_IMPL = prove
 (`!inp progs bw ctl nctl budget cfr.
     hol_progs progs /\ pl_cw_range nctl pl_plan_boot
     ==> !st. MEM st pl_plan_boot
              ==> tab_impl (tab_rel hol_tables hol_boot_layout inp bw ctl nctl cfr) hol_tables inp
                           progs bw ctl budget cfr st`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_progs; pl_progs_ok] THEN STRIP_TAC THEN
  X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!f. 10 <= f /\ f < 18 ==> val(EL f (st:int64 list)) < nctl` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_cw_range]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "MEM" (concl th))) THEN
  REWRITE_TAC[pl_plan_boot; MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `st:int64 list`
                          then SUBST_ALL_TAC th else failwith "") THEN
  TAB_BOOT_IMPL_TAC);;

(* A leaf the boot plan reaches is enabled: intern_name's hash is fnv's. *)
let BOOT_ENABLED_TAC =
  REWRITE_TAC[hol_tables] THEN
  FIRST [MATCH_MP_TAC TAB_EN_TOTAL THEN CONV_TAC TAB_REDUCE_CONV THEN NO_TAC;
         MATCH_MP_TAC TAB_EN_NAME THEN CONV_TAC TAB_REDUCE_CONV THEN
         ASM_REWRITE_TAC[WORD_VAL; BOOT_BYTES_NAMES; BOOT_BYTES_LENGTH] THEN NO_TAC];;

let rec BOOT_SAFE_TAC g =
  let w = snd g in
  if not (is_const_app "tab_safe" w) then ALL_TAC g else
  let sts = el 2 (snd(strip_comb w)) in
  if is_const sts && fst(dest_const sts) = "NIL" then REWRITE_TAC[CONJUNCT1 tab_safe] g else
  (GEN_REWRITE_TAC I [CONJUNCT2 tab_safe] THEN REWRITE_TAC[FST; SND] THEN CONJ_TAC THENL
    [BOOT_ENABLED_TAC;
     REPEAT GEN_TAC THEN
     CONV_TAC(LAND_CONV(LAND_CONV(fun t -> if TAB_LEAF_TERM t then TAB_LEAF_CONV t else failwith "TAB_HEAD"))) THEN
     DISCH_THEN(fun th -> W(fun (asl,_) ->
       let fact = BOOT_FACT_RULE asl (CONJUNCT1 th) in
       ASSUME_TAC(CONJUNCT2 th) THEN STRIP_ASSUME_TAC fact)) THEN
     PL_SUBST_ALL_TAC THEN (TAB_CONTRA_TAC ORELSE BOOT_SAFE_TAC)]) g;;

let BOOT_SAFE = prove
 (`!cw ctx pol.
     (!n. n <= 6 ==> cw n = n) /\ cw 22 = val fnv_offset
     ==> tab_safe hol_tables boot_bytes pl_plan_boot (cw,(ctx,[],[],[],[],[],[],[],[],pol),[])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun n -> ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV
                        (SPEC (mk_small_numeral n) (ASSUME `!n. n <= 6 ==> cw n = n`)))) (0--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN REWRITE_TAC[pl_plan_boot] THEN BOOT_SAFE_TAC);;

(* The boot plan through the driver, from memory related to empty tables:  *)
(* it never REFUSES; the memory it leaves is related, with the control     *)
(* words below the temporaries and the stack kept, to a state whose terms, *)
(* theorems, maps and drops are empty, the bootstrap state when it FIRES.  *)
let BOOT_TAB = prove
 (`!progs bw ctl nctl budget cfr m used res cw ctx pol.
     hol_progs progs /\ pl_cw_range nctl pl_plan_boot /\
     drv_sem progs bw ctl budget cfr pl_plan_boot 0 m used res /\
     tab_rel hol_tables hol_boot_layout boot_bytes bw ctl nctl cfr m (cw,(ctx,[],[],[],[],[],[],[],[],pol),[]) /\
     cw 22 = val fnv_offset /\ ~(val budget < val used)
     ==> ~(FST res = word 0) /\ ~(val budget < val(SND(SND(SND res)))) /\
         ?cw' ns'. tab_rel hol_tables hol_boot_layout boot_bytes bw ctl nctl cfr (FST(SND(SND res))) (cw',ns',[]) /\
                   (!n. n < 24 ==> cw' n = cw n) /\
                   (FST res = word 1 ==> ns' = (ctx,nat_boot_nms,nat_boot_tys,[],nat_boot_dbs,[],[],[],[],pol)) /\
                   (?nms tys dbs. ns' = (ctx,nms,tys,[],dbs,[],[],[],[],pol))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. n <= 6 ==> cw n = n` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_const_app "tab_rel" (concl th)
                          then MP_TAC(GEN_REWRITE_RULE I [tab_rel] th) else failwith "") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tab_rel hol_tables hol_boot_layout boot_bytes bw ctl nctl cfr`; `hol_tables`; `boot_bytes`;
                 `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `cfr:int64`;
                 `pl_plan_boot`; `0`; `m:int64->byte`; `used:int64`; `res:int64#num#(int64->byte)#int64`;
                 `(cw,(ctx,[],[],[],[],[],[],[],[],pol),[]):pstate`] TAB_DRV_BRIDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOOT_IMPL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC BOOT_SAFE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `s':pstate` MP_TAC))) THEN
  SPEC_TAC(`s':pstate`,`s':pstate`) THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN X_GEN_TAC `cw':num->num` THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`ns':nstate`; `stk':num list`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(FST(res:int64#num#(int64->byte)#int64) = word 1 <=> k = 1) /\ (FST res = word 0 <=> k = 0)`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC PL_WORD_SMALL_EQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cw:num->num`; `ctx:(hupdate)list`; `pol:num`; `k:num`; `j:num`; `cw':num->num`; `ns':nstate`;
                `stk':num list`] BOOT_RUN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`cw':num->num`; `ns':nstate`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `stk':num list = []`)) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Empty tables. Memory whose count words, names' used-bytes word and mark  *)
(* regions hold zero is related to empty tables, the regions long enough.   *)
(* The leaf state an interner's relation names is given a frame in the     *)
(* driver's stack window, which no table region meets.                      *)
(* ------------------------------------------------------------------------- *)

(* A state whose frame at f holds the words ws, memory m elsewhere. *)
let TISA_FRAME_EXISTS = prove
 (`!(f:int64) (m:int64->byte) (ws:num->int64) n.
     val f + 8 * n <= 2 EXP 64
     ==> ?t. tregs t 0 = f /\ (!j. j < n ==> tisa_fword t j = ws j) /\
             (!a. ~(val f <= val a /\ val a < val f + 8 * n) ==> tmem t a = m a)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `TState (\j. f) m` THEN REWRITE_TAC[tregs; tmem; LT];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:tisa_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `TState (\j. f) (write (bytes64 (word_add f (word(8 * n)))) (ws n) (tmem t))` THEN
  REWRITE_TAC[tregs; tmem] THEN
  SUBGOAL_THEN `!k. k < 8 * SUC n ==> val(word_add f (word k):int64) = val f + k` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!b. ~(val(word_add f (word(8 * n)):int64) <= val b /\
                      val b < val(word_add f (word(8 * n)):int64) + 8)
                    ==> write (bytes64 (word_add f (word(8 * n)))) (ws n:int64) (tmem t) b = tmem t b`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `8 * n`) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[DRV_FWORD; tregs; tmem] THEN
    ASM_CASES_TAC `j:num = n` THENL [ASM_REWRITE_TAC[DRV_WORD_WRITE_SAME]; ALL_TAC] THEN
    SUBGOAL_THEN `j < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `ws:num->int64`)) (concl th) &&
                               can (find_term (is_const_app "tisa_fword")) (concl th)
                            then (MP_TAC(SPEC `j:num` th)) else failwith "") THEN
    ASM_REWRITE_TAC[DRV_FWORD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `val(word_add (word_add f (word(8 * j))) (word i):int64) = val f + 8 * j + i` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `8 * n`) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    W(fun (asl,w) -> let th = find (fun (_,th) -> is_forall(concl th) &&
                                    can (find_term (is_const_app "write")) (concl th)) asl in
                     MP_TAC(SPEC `a:int64` (snd th))) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `8 * n`) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* The word at a table region's start, read by a leaf state agreeing there. *)
let TAB_FRESH_WORD = prove
 (`!t (m:int64->byte) (b:int64) n k.
     val b + n <= 2 EXP 64 /\ 8 * k + 8 <= n /\
     (!a. drv_in a b n ==> tmem t a = m a)
     ==> tisa_read t (word_add b (word(8 * k))) 8 = drv_word m (word_add b (word(8 * k)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_read; GSYM drv_word] THEN
  MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[drv_in] THEN
  SUBGOAL_THEN `val(word_add (word_add b (word(8 * k))) (word i):int64) = val b + 8 * k + i` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
    MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* A table region's addresses lie outside the frame placed at cfr - 48. *)
let TAB_FRESH_APART = prove
 (`!L bw ctl nctl cfr j a.
     tab_layout L bw ctl nctl cfr /\ MEM j (tab_slots L) /\ drv_in a (bw j) (val(bw(j + 1)))
     ==> ~(val(word_sub cfr (word 48):int64) <= val a /\ val a < val(word_sub cfr (word 48):int64) + 8 * 10)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j:num`]
               TAB_LAYOUT_SLOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  MP_TAC(SPECL [`cfr:int64`; `a:int64`; `bw(j:num):int64`; `val(bw(j + 1):int64)`] DRV_IN_NOT_STACK) THEN
  ASM_REWRITE_TAC[drv_stack] THEN
  SUBGOAL_THEN `val(word_sub cfr (word 48):int64) = val cfr - 48` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[ARITH_RULE `48 <= c ==> 48 <= c`];
    ARITH_TAC]);;

let TAB_FRESH_FRAME_TAC n ws =
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [tab_layout]) THEN
  MP_TAC(ISPECL [`word_sub cfr (word 48):int64`; `m:int64->byte`; ws; mk_small_numeral n] TISA_FRAME_EXISTS) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `val(word_sub cfr (word 48):int64) = val cfr - 48` SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:tisa_state` STRIP_ASSUME_TAC) THEN EXISTS_TAC `t:tisa_state`;;

(* An empty intern16 table: its count word zero. *)
let TAB_KEY_EMPTY = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput L inp bw ctl nctl cfr m s j.
     tab_layout L bw ctl nctl cfr /\ MEM (KeyTab j) L /\
     16 <= val(bw(j + 1)) /\ 8 <= val(bw(j + 3)) /\ 8 <= val(bw(j + 5)) /\
     pl_mw m (bw(j + 4)) 0 = 0 /\ tn (j + 4) s = 0
     ==> tab_mem (trow,tn,twd,tdrop,tapp,tput) inp bw m s (KeyTab j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[tab_mem; LT] THEN
  FIRST_ASSUM(ASSUME_TAC o CONV_RULE(DEPTH_CONV BETA_CONV) o REWRITE_RULE[tab_dslots; ALL] o
              MATCH_MP TAB_DESC_SLOTS) THEN
  TAB_FRESH_FRAME_TAC 6 `\i. (bw:num->int64)(j + i)` THEN
  SUBGOAL_THEN `!r. r < 3 ==> MEM (j + 2 * r) (tab_slots L)` ASSUME_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `!r a. r < 3 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1))) ==> tmem t a = m a`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                                                can (find_term (is_const_app "tmem")) (concl th))) THEN
    MATCH_MP_TAC(ARITH_RULE `~(f <= a /\ a < f + 8 * 10) ==> ~(f <= a /\ a < f + 8 * 6)`) THEN
    MATCH_MP_TAC TAB_FRESH_APART THEN
    MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `j + 2 * r`] THEN
    ASM_SIMP_TAC[GSYM ADD_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r < 3 ==> tisa_base t r = bw(j + 2 * r) /\ tisa_len t r = bw(j + 2 * r + 1)`
    ASSUME_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[tisa_base; tisa_len] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term (is_const_app "tisa_fword")) (concl th)
                          then MP_TAC(SPEC `2 * r + 1` th) THEN MP_TAC(SPEC `2 * r` th) else failwith "") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(intern_count t) = 0` ASSUME_TAC THENL
   [REWRITE_TAC[intern_count] THEN
    FIRST_ASSUM(MP_TAC o SPEC `2` o check (fun th -> is_forall(concl th) &&
                  can (find_term (is_const_app "tisa_base")) (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    MP_TAC(SPECL [`t:tisa_state`; `m:int64->byte`; `bw(j + 4):int64`; `val(bw(j + 5):int64)`; `0`]
                 TAB_FRESH_WORD) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j + 4`]
                     TAB_LAYOUT_SLOT) THEN
        ASM_REWRITE_TAC[ARITH_RULE `(j + 4) + 1 = j + 5`] THEN ARITH_TAC;
        ASM_ARITH_TAC;
        X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
        FIRST_ASSUM(MP_TAC o SPECL [`2`; `a:int64`] o check (fun th -> is_forall(concl th) &&
          can (find_term (is_const_app "tmem")) (concl th) && can (find_term (is_const_app "drv_in")) (concl th))) THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `pl_mw m (bw(j + 4)) 0 = 0` THEN REWRITE_TAC[pl_mw; MULT_CLAUSES; WORD_ADD_0]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[intern_ok; intern_complete; intern_distinct; LT; LE_0]);;

(* An empty names interner: its count and used-bytes words zero. *)
let TAB_NAME_EMPTY = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput L inp bw ctl nctl cfr m s j.
     tab_layout L bw ctl nctl cfr /\ MEM (NameTab j) L /\ 16 <= val(bw(j + 7)) /\
     pl_mw m (bw(j + 6)) 0 = 0 /\ pl_mw m (bw(j + 6)) 1 = 0 /\ tn (j + 6) s = 0
     ==> tab_mem (trow,tn,twd,tdrop,tapp,tput) inp bw m s (NameTab j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[tab_mem; LT] THEN
  FIRST_ASSUM(ASSUME_TAC o CONV_RULE(DEPTH_CONV BETA_CONV) o REWRITE_RULE[tab_dslots; ALL] o
              MATCH_MP TAB_DESC_SLOTS) THEN
  TAB_FRESH_FRAME_TAC 10 `\i. if i < 2 then word 0 else (bw:num->int64)(j + i - 2)` THEN
  SUBGOAL_THEN `!r. r < 4 ==> MEM (j + 2 * r) (tab_slots L)` ASSUME_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `!r a. r < 4 /\ drv_in a (bw(j + 2 * r)) (val(bw(j + 2 * r + 1))) ==> tmem t a = m a`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                                                can (find_term (is_const_app "tmem")) (concl th))) THEN
    MATCH_MP_TAC TAB_FRESH_APART THEN
    MAP_EVERY EXISTS_TAC [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `j + 2 * r`] THEN
    ASM_SIMP_TAC[GSYM ADD_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r < 4 ==> tisa_base t (r + 1) = bw(j + 2 * r) /\ tisa_len t (r + 1) = bw(j + 2 * r + 1)`
    ASSUME_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[tisa_base; tisa_len] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term (is_const_app "tisa_fword")) (concl th)
                          then MP_TAC(SPEC `2 * (r + 1) + 1` th) THEN MP_TAC(SPEC `2 * (r + 1)` th)
                          else failwith "") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ARITH_RULE `~(2 * (r + 1) < 2) /\ ~(2 * (r + 1) + 1 < 2)`;
                ARITH_RULE `2 * (r + 1) - 2 = 2 * r /\ (2 * (r + 1) + 1) - 2 = 2 * r + 1`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `3` o check (fun th -> is_forall(concl th) &&
                can (find_term (is_const_app "tisa_base")) (concl th))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `!k. k < 2 ==> tisa_read t (word_add (bw(j + 6)) (word(8 * k))) 8 =
                              drv_word m (word_add (bw(j + 6)) (word(8 * k)))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TAB_FRESH_WORD THEN EXISTS_TAC `val(bw(j + 7):int64)` THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`L:tabdesc list`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `cfr:int64`; `j + 6`]
                   TAB_LAYOUT_SLOT) THEN
      ASM_REWRITE_TAC[ARITH_RULE `(j + 6) + 1 = j + 7`] THEN ARITH_TAC;
      ASM_ARITH_TAC;
      X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`3`; `a:int64`] o check (fun th -> is_forall(concl th) &&
        can (find_term (is_const_app "tmem")) (concl th) && can (find_term (is_const_app "drv_in")) (concl th))) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(name_count t) = 0 /\ val(name_used t) = 0` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[name_count; name_used] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
                  can (find_term (is_const_app "tisa_read")) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o SPEC `1` o check (fun th -> is_forall(concl th) &&
                  can (find_term (is_const_app "tisa_read")) (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    UNDISCH_TAC `pl_mw m (bw(j + 6)) 0 = 0` THEN UNDISCH_TAC `pl_mw m (bw(j + 6)) 1 = 0` THEN
    REWRITE_TAC[pl_mw] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[name_ok; name_complete; name_distinct; LT; LE_0]);;

(* An empty row table: its count word zero. *)
let TAB_ROW_EMPTY = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput inp bw m s j c wd.
     val(bw(j + 1)) < 8 * wd * 2 EXP 60 /\ 8 <= val(bw(c + 1)) /\ pl_mw m (bw c) 0 = 0 /\ tn c s = 0
     ==> tab_mem (trow,tn,twd,tdrop,tapp,tput) inp bw m s (RowTab j c wd)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[tab_mem; pl_rtab; LT; MULT_CLAUSES; LE_0]);;

(* Empty marks: every mark word zero, no id dropped. *)
let TAB_MARK_EMPTY = prove
 (`!(trow:num->S->num->num list) tn twd tdrop tapp tput inp bw m s jm j c wd.
     val(bw(j + 1)) <= wd * val(bw(jm + 1)) /\ tn c s = 0 /\ (!i. ~tdrop jm s i) /\
     (!i. 8 * i + 8 <= val(bw(jm + 1)) ==> pl_mw m (bw jm) i = 0)
     ==> tab_mem (trow,tn,twd,tdrop,tapp,tput) inp bw m s (MarkTab jm j c wd)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[tab_mem; LT; MULT_CLAUSES; LE_0] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* What the entry establishes before the boot plan: the regions' lengths,   *)
(* zero count words, used-bytes word and marks, and the boot bytes.          *)
(* ------------------------------------------------------------------------- *)

(* The interners' rows, hash slots and counts; each row table's room below  *)
(* 2^60 rows of its width, its count word, marks for every row; the names'  *)
(* header (count and bytes used).                                            *)

(* The count words, the names' count and used-bytes words, every mark word. *)

(* The boot bytes at slot 62. *)

(* Such memory is related to empty tables at the boot layout. *)
let BOOT_FRESH_TAB = prove
 (`!bw ctl nctl cfr m cw ctx pol.
     tab_layout hol_boot_layout bw ctl nctl cfr /\ 7 <= nctl /\ (!k. k <= 6 ==> cw k = k) /\
     pl_cwords ctl nctl m cw /\ hol_boot_lengths bw /\ hol_boot_zero bw m /\ hol_boot_bytes_at bw m
     ==> tab_rel hol_tables hol_boot_layout boot_bytes bw ctl nctl cfr m (cw,(ctx,[],[],[],[],[],[],[],[],pol),[])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_boot_lengths; hol_boot_zero; hol_boot_bytes_at] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[tab_rel; pl_stk; LENGTH; LT; MULT_CLAUSES; LE_0] THEN
  MP_TAC HOL_BOOT_LAYOUT_MEMS THEN
  REWRITE_TAC[hol_boot_layout; hol_layout_old; APPEND; ALL; hol_tables] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC TAB_KEY_EMPTY THEN
    MAP_EVERY EXISTS_TAC [`hol_boot_layout`; `ctl:int64`; `nctl:num`; `cfr:int64`];
    MATCH_MP_TAC TAB_KEY_EMPTY THEN
    MAP_EVERY EXISTS_TAC [`hol_boot_layout`; `ctl:int64`; `nctl:num`; `cfr:int64`];
    MATCH_MP_TAC TAB_ROW_EMPTY;
    MATCH_MP_TAC TAB_MARK_EMPTY;
    MATCH_MP_TAC TAB_ROW_EMPTY;
    MATCH_MP_TAC TAB_MARK_EMPTY;
    MATCH_MP_TAC TAB_ROW_EMPTY;
    MATCH_MP_TAC TAB_MARK_EMPTY;
    MATCH_MP_TAC TAB_ROW_EMPTY;
    MATCH_MP_TAC TAB_MARK_EMPTY;
    MATCH_MP_TAC TAB_NAME_EMPTY THEN
    MAP_EVERY EXISTS_TAC [`hol_boot_layout`; `ctl:int64`; `nctl:num`; `cfr:int64`];
    REWRITE_TAC[tab_mem; BOOT_BYTES_LENGTH]] THEN
  REWRITE_TAC[hol_tn; hol_tdrop; LENGTH; MEM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[hol_boot_layout; hol_layout_old; APPEND] THEN ASM_SIMP_TAC[]);;

(* The boot layout's relation, with the input in slot 54, is the record     *)
(* loop's: the two layouts differ only in the input's table.                 *)
let BOOT_LAYOUT_SWAP = prove
 (`!inp bw ctl nctl cfr m cw (s:nstate) stk.
     tab_rel hol_tables hol_boot_layout boot_bytes bw ctl nctl cfr m (cw,s,stk) /\
     tab_layout hol_layout bw ctl nctl cfr /\
     LENGTH inp = val(bw 55) /\ (!i. i < LENGTH inp ==> val(m(word_add (bw 54) (word i))) = EL i inp)
     ==> tab_rel hol_tables hol_layout inp bw ctl nctl cfr m (cw,s,stk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tab_rel; hol_boot_layout; hol_layout; hol_layout_old; ALL_APPEND; ALL] THEN
  REWRITE_TAC[hol_tables; tab_mem] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* From the boot to the record loop: a boot run that FIRES, from memory the  *)
(* entry prepared, leaves memory at which the record loop's invariant holds  *)
(* at HOL's full layout, with the reader at the input's start (BOOT_START).  *)
(* ------------------------------------------------------------------------- *)

let TAB_SLOTS_BOOT = prove
 (`tab_slots hol_boot_layout =
     [0; 2; 4; 6; 8; 10; 12; 14; 16; 18; 20; 22; 24; 26; 28; 30; 32; 34; 44; 46; 48; 50; 62; 40; 42]`,
  REWRITE_TAC[tab_slots; hol_boot_layout; hol_layout_old; APPEND; ITLIST; tab_dslots] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* The boot plan writes only the boot layout's tables, never the input. *)
let BOOT_RD_PLAN_OK = prove
 (`!progs nctl. hol_progs progs /\ pl_cw_range nctl pl_plan_boot
                ==> tab_rd_plan_ok hol_boot_layout progs nctl pl_plan_boot`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_progs; pl_progs_ok; pl_cw_range; tab_rd_plan_ok] THEN STRIP_TAC THEN
  X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(EL 17 (st:int64 list)) < nctl` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_const_app "MEM" (concl th))) THEN
  REWRITE_TAC[pl_plan_boot; MEM] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC)) THEN TRY(DISCH_THEN SUBST1_TAC) THEN
  CONV_TAC STEP_EL_CONV2 THEN
  ASM_REWRITE_TAC(PL_LEAVES_WF @ PL_LEAVES_RW @ [FNV_LEAF_WF; FNV_RO; NAME_LEAF_WF; NAME_RW]) THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`; FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  CONV_TAC STEP_EL_CONV2 THEN REWRITE_TAC[TAB_SLOTS_BOOT; MEM] THEN CONV_TAC NUM_REDUCE_CONV);;

(* The boot run's end is the record loop's start: the tables hold the     *)
(* bootstrap state at HOL's full layout, the reader its words and the      *)
(* input from its start, given the header's constant kept.                 *)
let BOOT_START = prove
 (`!progs bw ctl nctl budget E m0 used res cw inp hpol ht nh.
     hol_progs progs /\ pl_cw_range nctl pl_plan_boot /\
     drv_sem progs bw ctl budget (word_sub E (word 312)) pl_plan_boot 0 m0 used res /\
     tab_layout hol_boot_layout bw ctl nctl (word_sub E (word 312)) /\
     tab_layout hol_layout bw ctl nctl (word_sub E (word 312)) /\ 7 <= nctl /\
     (!k. k <= 6 ==> cw k = k) /\ cw 17 = 0 /\ cw 19 = 0 /\ cw 20 = 0 /\ cw 22 = val fnv_offset /\ cw 7 = hpol /\
     pl_cwords ctl nctl m0 cw /\ hol_boot_lengths bw /\ hol_boot_zero bw m0 /\ hol_boot_bytes_at bw m0 /\
     rd_rel bw ctl nctl (word_sub E (word 312)) m0 inp 0 /\ rd_tab_apart hol_boot_layout bw /\
     rd_hdr_rel bw (word_sub E (word 312)) (FST(SND(SND res))) /\
     ~(val budget < val used) /\ FST res = word 1
     ==> tab_rec_inv hol_layout bw ctl nctl E ht nh (FST(SND(SND res))) hpol inp (FST(SND(SND res)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                `word_sub E (word 312):int64`; `m0:int64->byte`; `used:int64`;
                `res:int64#num#(int64->byte)#int64`; `cw:num->num`; `hinit_ctxt`; `hpol:num`] BOOT_TAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BOOT_FRESH_TAB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `ns':nstate` &&
                                                  can (find_term ((=) `nat_boot_nms`)) (concl th))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) && is_pair(lhs(concl th))))) THEN
  SUBGOAL_THEN `rd_rel bw ctl nctl (word_sub E (word 312)) (FST(SND(SND(res:int64#num#(int64->byte)#int64)))) inp 0`
    ASSUME_TAC THENL
   [MATCH_MP_TAC TAB_PLAN_KEEPS_RD THEN
    MAP_EVERY EXISTS_TAC [`hol_boot_layout`; `progs:num->tisa_prog`; `budget:int64`; `pl_plan_boot`; `0`;
                          `m0:int64->byte`; `used:int64`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BOOT_RD_PLAN_OK THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REC_BOOT_TAB THEN EXISTS_TAC `cw':num->num` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BOOT_LAYOUT_SWAP THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> if is_const_app "rd_rel" (concl th) &&
                             not(can (find_term ((=) `m0:int64->byte`)) (concl th))
                          then STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [rd_rel] th) else failwith "") THEN
    ASM_REWRITE_TAC[];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `cw':num->num`)) (concl th)
                          then MP_TAC th else failwith "") THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONV_RULE NUM_REDUCE_CONV (SPEC `7` th);
                                   CONV_RULE NUM_REDUCE_CONV (SPEC `17` th);
                                   CONV_RULE NUM_REDUCE_CONV (SPEC `19` th);
                                   CONV_RULE NUM_REDUCE_CONV (SPEC `20` th);
                                   CONV_RULE NUM_REDUCE_CONV (SPEC `22` th)]) THEN
  ASM_REWRITE_TAC[]);;

(* Every theorem this file states, for the audits. *)
let boot_tab_theorems =
 ["BOOT_BYTES_NAMES", BOOT_BYTES_NAMES; "HOL_BOOT_LAYOUT_WF", HOL_BOOT_LAYOUT_WF;
  "HOL_BOOT_LAYOUT_MEMS", HOL_BOOT_LAYOUT_MEMS; "BOOT_BYTES_LENGTH", BOOT_BYTES_LENGTH;
  "HNAME_BYTES_11", HNAME_BYTES_11; "BOOT_INTERN_NAME", BOOT_INTERN_NAME; "BOOT_INTERN_TY", BOOT_INTERN_TY;
  "BOOT_INTERN_DB", BOOT_INTERN_DB; "BOOT_RUN", BOOT_RUN; "BOOT_IMPL", BOOT_IMPL; "BOOT_SAFE", BOOT_SAFE;
  "BOOT_TAB", BOOT_TAB; "TISA_FRAME_EXISTS", TISA_FRAME_EXISTS; "TAB_FRESH_WORD", TAB_FRESH_WORD;
  "TAB_FRESH_APART", TAB_FRESH_APART; "TAB_KEY_EMPTY", TAB_KEY_EMPTY; "TAB_NAME_EMPTY", TAB_NAME_EMPTY;
  "TAB_ROW_EMPTY", TAB_ROW_EMPTY; "TAB_MARK_EMPTY", TAB_MARK_EMPTY; "BOOT_FRESH_TAB", BOOT_FRESH_TAB;
  "BOOT_LAYOUT_SWAP", BOOT_LAYOUT_SWAP; "TAB_SLOTS_BOOT", TAB_SLOTS_BOOT; "BOOT_RD_PLAN_OK", BOOT_RD_PLAN_OK;
  "BOOT_START", BOOT_START];;
