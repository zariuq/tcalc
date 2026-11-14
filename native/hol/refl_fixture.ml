(* ========================================================================= *)
(* The REFL record on the x86 checker, at a concrete memory.                *)
(*                                                                           *)
(* The native state just before the record RRefl t of the control stream    *)
(* (ctl_recs, holr_native.ml) is laid out as the plan driver reads it: the   *)
(* binding slots' regions (two interners, term and theorem rows and marks,   *)
(* the operand stack), the control words with the operand t in word 8, the  *)
(* REFL plan, its descriptor, and the code of the driver and of its seven    *)
(* leaves, all written over an arbitrary background memory. At that memory   *)
(* every premise of DRV_CORRECT and of PL_REFL_REL is proved. Two operands:  *)
(*                                                                           *)
(*   t = 0, the term x: the code returns RAX = 1 (FIRED), and the plan's     *)
(*   final memory represents a native state that nat_step reaches from the   *)
(*   state before the record by RRefl 0, whose one theorem row is |- x = x   *)
(*   (REFL_FIX0_X86, REFL_FIX0_STEP, REFL_FIX0_ROW).                          *)
(*                                                                           *)
(*   t = 4, past the four terms: the code returns RAX = 0 (REFUSED)          *)
(*   (REFL_FIX4_X86, REFL_FIX4_REFUSED).                                     *)
(*                                                                           *)
(* FIRED comes from one run of the plan evaluated in the logic (drv_eval.ml) *)
(* and the driver's determinism up to its stack (DRV_SEM_FUN), since the     *)
(* plan's abstract leaves allow a resource failure in every state.           *)
(*                                                                           *)
(* Loaded in a session on s2n-bignum's base after the files that            *)
(* plans_rel.ml needs.                                                       *)
(* ========================================================================= *)

needs "tisa/hol/tisa_p1_eval.ml";;
needs "native/leaves/pack/pack.hol";;           needs "native/leaves/pack/pack_join.ml";;
needs "native/leaves/unpack/unpack.hol";;       needs "native/leaves/unpack/unpack_join.ml";;
needs "native/leaves/eqw/eqw.hol";;             needs "native/leaves/eqw/eqw_join.ml";;
needs "native/leaves/row_word/row_word.hol";;   needs "native/leaves/row_word/row_word_join.ml";;
needs "native/leaves/live/live.hol";;           needs "native/leaves/live/live_join.ml";;
needs "native/leaves/append_row/append_row.hol";; needs "native/leaves/append_row/append_row_join.ml";;
needs "native/driver/driver_det.ml";;
needs "native/driver/drv_eval.ml";;

(* ------------------------------------------------------------------------- *)
(* The native state before the record: the first 13 records of the control  *)
(* stream, by the proved steps of ctl_path; nat_ok and nat_sim there by      *)
(* NAT_RUN_SIM; canonical, distinct keys.                                    *)
(* ------------------------------------------------------------------------- *)

let fx_plan13 =
   [0, [`[61]`; `[]:string list`; `2`];
    0, [`[65]`; `[]:string list`; `3`];
    1, [`1`; ctl_nil3; ctl_nil3; `2`];
    0, [`[98;111;111;108]`; `[]:string list`; `0`];
    0, [`[102;117;110]`; `[]:string list`; `1`];
    2, [`2`; `[]:num list`; `[]:holtype list`; ctl_nil3; ctl_nil3; `1`];
    2, [`3`; `[0;1]`; mk_list([ctl_A; ctl_bool],`:holtype`); ctl_nil3; ctl_nil3; `5`];
    2, [`3`; `[0;2]`; mk_list([ctl_A; ctl_AB],`:holtype`); ctl_nil3; ctl_nil3; `8`];
    0, [`[120]`; `["x"]`; `4`];
    3, [`4`; `0`; ctl_A; ctl_nil3; `[0,4,2]:(num#num#num)list`; `1`];
    4, [`0`; `3`; ctl_AAB; `HFun (TyVar "A") (HFun (TyVar "A") HBool)`;
        `[]:(holtype#holtype)list`; ctl_nil3; `[2,2,8]:(num#num#num)list`; `2`];
    5, [`1`; `0`; ctl_eq; ctl_x; ctl_AB; ctl_nil3; `[3,2,1]:(num#num#num)list`; `5`; `3`];
    5, [`2`; `0`; ctl_eqx; ctl_x; ctl_bool; ctl_nil3; `[3,3,1]:(num#num#num)list`; `1`; `4`]];;

let fx_run =
  let rec go st acc = function
      [] -> rev acc
    | (k, extra) :: rest -> let th, st' = ctl_step k st extra in go st' ((th, st') :: acc) rest in
  go ctl_state [] fx_plan13;;
let fx_steps13 = map fst fx_run;;
let fx_ns_pre = snd (last fx_run);;

let fx_mk_tuple l = end_itlist (curry mk_pair) l;;
let fx_s0 = fx_mk_tuple ctl_state;;
let fx_s13 = fx_mk_tuple fx_ns_pre;;

let fx_boot =
  REWRITE_RULE[nat_boot_nms; nat_boot_tys; nat_boot_dbs]
    (MP (SPECL [`nat_boot_nms`; `nat_boot_tys`; `nat_boot_dbs`; `pol:num`] NAT_BOOT)
        (CONJ NAT_BOOT_TYS_OK NAT_BOOT_CANON));;
let fx_path =
  let base = prove(list_mk_icomb "tc_path" [`nat_step`; `[]:holr_record list`; fx_s13; fx_s13],
                   REWRITE_TAC[tc_path]) in
  itlist (fun st p -> MATCH_MP (ISPEC `nat_step` TC_PATH_CONS_STEP) (CONJ st p)) fx_steps13 base;;
let fx_recs = rand(rator(rator(concl fx_path)));;
let fx_hr0 = rand(rand(concl fx_boot));;
let REFL_FIX_NAT_PRE = MP (ISPECL [fx_recs; fx_s0; fx_s13; fx_hr0] NAT_RUN_SIM) (CONJ fx_path fx_boot);;

(* v < k (k a numeral) as v = k-1 \/ ... \/ v = 0, one SUC at a time. *)
let rec FX_LT_DISJ_CONV tm =
  match tm with
    Comb(Comb(Const("<",_),v),k) when is_var v && is_numeral k ->
      if dest_small_numeral k = 0 then SPEC v (CONJUNCT1 LT)
      else (RAND_CONV num_CONV THENC REWR_CONV (CONJUNCT2 LT) THENC RAND_CONV FX_LT_DISJ_CONV) tm
  | _ -> failwith "FX_LT_DISJ_CONV";;
let FX_LT_EXPAND_CONV tm =
  (FX_LT_DISJ_CONV THENC PURE_REWRITE_CONV[OR_CLAUSES] THENC ONCE_DEPTH_CONV NUM_SUC_CONV) tm;;

(* A bounded goal !j. j < LENGTH l ==> P j over a concrete l: expand, evaluate each case. *)
let FX_BOUNDED_TAC =
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV FX_LT_EXPAND_CONV) THEN TRY(REWRITE_TAC[] THEN NO_TAC) THEN
  GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC FIBRE_EVAL_CONV THEN REWRITE_TAC[];;

(* keys_distinct of a concrete list, row after row. *)
let fx_keys_distinct tm =
  let els = dest_list tm in
  let ty = type_of (hd els) in
  let base = prove(mk_icomb(`keys_distinct:(num#num#num)list->bool`, mk_list([], ty)),
                   REWRITE_TAC[keys_distinct; LENGTH; LT]) in
  let step th x =
    let l = rand(concl th) in
    let side = prove(mk_forall(`j:num`, mk_imp(mk_binop `(<):num->num->bool` `j:num`
                                                  (mk_icomb(`LENGTH:(num#num#num)list->num`, l)),
                                               mk_neg(mk_eq(mk_icomb(mk_icomb(`EL:num->(num#num#num)list->num#num#num`, `j:num`), l), x)))),
                     FX_BOUNDED_TAC) in
    REWRITE_RULE[APPEND] (MATCH_MP (ISPECL [l; x] KEYS_DISTINCT_SNOC) (CONJ th side)) in
  rev_itlist (fun x th -> step th x) els base;;

let FX_DISTINCT_TYS = fx_keys_distinct (el 2 fx_ns_pre);;
let FX_DISTINCT_DBS = fx_keys_distinct (el 4 fx_ns_pre);;
let FX_KEYS = prove(list_mk_icomb "nat_keys" [el 2 fx_ns_pre; el 4 fx_ns_pre],
  REWRITE_TAC[nat_keys] THEN CONJ_TAC THEN FX_BOUNDED_TAC THEN
  REWRITE_TAC[ty_key_ok; db_key_ok] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The memory map. Addresses are small and page aligned; the stack and the   *)
(* code lie far from the data. The tables are generated by the interner's    *)
(* own rule; nothing generated is trusted, every fact is proved below.      *)
(* ------------------------------------------------------------------------- *)

let fx_d = 0x10000 and fx_plan = 0x11000 and fx_ctl = 0x12000 and fx_bind = 0x12800
and fx_leaves = 0x12C00;;
let fx_nctl = 48 and fx_nbw = 58 and fx_nl = 7;;
let fx_sp = 0x30000;;                         (* the child frame at cfr = sp - 248 *)
let fx_pc = 0x40000;;                         (* the driver's code *)
let fx_lpc j = 0x41000 + 0x1000 * j;;         (* leaf j's code *)
let fx_ret = 0x50000;;                        (* the caller's return address *)

(* intern_hash k0 k1 = z*C xor ((z*C) >>> 29), z = k0 xor k1, C = 11400714819323198485. *)
let fx_hash (k0:Int64.t) (k1:Int64.t) =
  let c = Int64.of_string "-7046029254386353131" in
  let z = Int64.mul (Int64.logxor k0 k1) c in
  Int64.logxor z (Int64.shift_right_logical z 29);;
let fx_key (tag,a,b) = (Int64.of_int (8 * a + tag), Int64.of_int b);;
(* Slots for rows inserted in order: the first empty slot from the hash, probing upwards. *)
let fx_slots nslots rows =
  let s = Array.make nslots 0 in
  let mask = Int64.of_int (nslots - 1) in
  List.iteri (fun j r ->
    let k0, k1 = fx_key r in
    let h = fx_hash k0 k1 in
    let rec probe x =
      if x >= nslots then failwith "fx_slots: table full" else
      let p = Int64.to_int (Int64.logand (Int64.add h (Int64.of_int x)) mask) in
      if s.(p) = 0 then s.(p) <- j + 1 else probe (x + 1) in
    probe 0) rows;
  Array.to_list s;;
let fx_le_bytes (ws:int list) =
  List.concat (List.map (fun w -> List.map (fun i -> (w lsr (8 * i)) land 255) (0--7)) ws);;
let fx_interner cap nslots rows =
  let ws = List.concat (List.map (fun (tag,a,b) -> [8 * a + tag; b]) rows) in
  let pad = Array.to_list (Array.make (2 * cap - List.length ws) 0) in
  (fx_le_bytes (ws @ pad), fx_le_bytes (fx_slots nslots rows), fx_le_bytes [List.length rows]);;
let fx_rows3 tm = map (fun t -> match map dest_small_numeral (strip_tuple t) with
                                  [a;b;c] -> (a,b,c) | _ -> failwith "fx_rows3") (dest_list tm);;
let fx_tys = fx_rows3 (el 2 fx_ns_pre) and fx_dbs = fx_rows3 (el 4 fx_ns_pre);;
let fx_ty_tab = fx_interner 32 64 fx_tys and fx_db_tab = fx_interner 32 64 fx_dbs;;

(* Slot j: (base, length), for the slots of pl_slots; the other binding words name empty regions. *)
let fx_slot_regions =
  [0, (0x13000, 512); 2, (0x13400, 512); 4, (0x13800, 8);      (* type interner *)
   6, (0x13C00, 512); 8, (0x14000, 512); 10, (0x14400, 8);     (* de Bruijn interner *)
   12, (0x14800, 640); 14, (0x14C00, 8); 16, (0x14E00, 128);   (* term rows, count, marks *)
   18, (0x15000, 256); 20, (0x15200, 8); 22, (0x15400, 128);   (* theorem rows, count, marks *)
   40, (0x15800, 512); 42, (0x15C00, 64)];;                    (* operand stack, spare *)
let fx_bw j = if j mod 2 = 0 then (try fst (assoc j fx_slot_regions) with Failure _ -> 0)
              else (try snd (assoc (j - 1) fx_slot_regions) with Failure _ -> 0);;

let fx_ntms = map (fun t -> map dest_small_numeral (strip_tuple t)) (dest_list (el 3 fx_ns_pre));;
let fx_rows_bytes width rows cap =
  let ws = List.concat rows in
  fx_le_bytes (ws @ Array.to_list (Array.make (width * cap - List.length ws) 0));;
let fx_ty_rows, fx_ty_slots, fx_ty_count = fx_ty_tab
and fx_db_rows, fx_db_slots, fx_db_count = fx_db_tab;;
let fx_region_bytes =
  [0x13000, fx_ty_rows; 0x13400, fx_ty_slots; 0x13800, fx_ty_count;
   0x13C00, fx_db_rows; 0x14000, fx_db_slots; 0x14400, fx_db_count;
   0x14800, fx_rows_bytes 5 fx_ntms 16; 0x14C00, fx_le_bytes [length fx_ntms];
   0x14E00, fx_le_bytes (Array.to_list (Array.make 16 0));
   0x15000, fx_le_bytes (Array.to_list (Array.make 32 0)); 0x15200, fx_le_bytes [0];
   0x15400, fx_le_bytes (Array.to_list (Array.make 16 0));
   0x15800, fx_le_bytes (Array.to_list (Array.make 64 0))];;

let fx_plan_words = map (fun st -> map (fun w -> dest_small_numeral (rand w)) (dest_list st))
                        (dest_list (rand(concl pl_plan_refl)));;
let fx_ns = length fx_plan_words;;
let fx_bind_words = map fx_bw (0--(fx_nbw - 1));;
let fx_budget = 1000000 and fx_used0 = 0;;
let fx_desc_words = [fx_plan; fx_plan + 144 * fx_ns; fx_ctl; fx_bind; fx_leaves; fx_budget; fx_used0; 0];;

(* A little-endian byte list as a numeral, and the write chain. *)
let fx_numeral bytes =
  mk_numeral (List.fold_right (fun b acc -> Num.add_num (Num.mult_num acc (Num.num_of_int 256)) (Num.num_of_int b))
                              bytes (Num.num_of_int 0));;
let fx_write (a, bytes) m =
  list_mk_icomb "write" [mk_comb(`bytes:int64#num->(int64->byte,num)component`,
                                 mk_pair(mk_comb(`word:num->int64`, mk_small_numeral a),
                                         mk_small_numeral (length bytes)));
                         fx_numeral bytes; m];;

(* The code (driver and leaves) and the return address, from the code constants' definitions. *)
let fx_def name = find (fun th -> try fst(dest_const(lhs(concl th))) = name with Failure _ -> false) (definitions());;
let fx_mc_bytes name = map (fun w -> dest_small_numeral (rand w)) (dest_list (rhs(concl(fx_def name))));;
let fx_leaf_mcs = ["intern16_mc"; "pack_mc"; "unpack_mc"; "eqw_mc"; "row_word_mc"; "live_mc"; "append_row_mc"];;
let fx_code_writes =
  (fx_pc, fx_mc_bytes "drv_mc") :: (fx_sp, fx_le_bytes [fx_ret]) ::
  map (fun (j, n) -> (fx_lpc j, fx_mc_bytes n)) (zip (0--6) fx_leaf_mcs);;

(* Two frames for the interner witnesses of pl_itab: each holds its interner's three bases and lengths. *)
let fx_fty = 0x16000 and fx_fdb = 0x16100;;

(* The whole memory for control words cw_words. *)
let fx_memory cw_words =
  let data = [fx_d, fx_le_bytes fx_desc_words; fx_plan, fx_le_bytes (List.concat fx_plan_words);
              fx_ctl, fx_le_bytes cw_words; fx_bind, fx_le_bytes fx_bind_words;
              fx_leaves, fx_le_bytes (map fx_lpc (0--(fx_nl - 1)))] @ fx_region_bytes in
  let m = itlist fx_write data `m_bg:int64->byte` in
  let m = itlist fx_write fx_code_writes m in
  itlist fx_write [fx_fty, fx_le_bytes (map fx_bw (0--5)); fx_fdb, fx_le_bytes (map fx_bw (6--11))] m;;

(* The fixture's terms. *)
let fx_word n = mk_comb(`word:num->int64`, mk_small_numeral n);;
let fx_bw_tm = mk_abs(`j:num`, mk_comb(`word:num->int64`,
  list_mk_icomb "EL" [`j:num`; mk_list(map mk_small_numeral fx_bind_words, `:num`)]));;
let fx_ctl_tm = fx_word fx_ctl and fx_cfr_tm = fx_word (fx_sp - 248) and fx_nctl_tm = mk_small_numeral fx_nctl;;
let fx_progs = `\j. EL j [intern16; pack; unpack; eqw; row_word; live; append_row]`;;
let fx_lpc_tm = mk_abs(`j:num`, list_mk_icomb "EL" [`j:num`; mk_list(map (fun j -> mk_small_numeral (fx_lpc j)) (0--6), `:num`)]);;
let fx_lmc = `\j. EL j [intern16_mc; pack_mc; unpack_mc; eqw_mc; row_word_mc; live_mc; append_row_mc]`;;
let fx_pc_tm = mk_small_numeral fx_pc and fx_sp_tm = fx_word fx_sp and fx_d_tm = fx_word fx_d
and fx_plan_tm = fx_word fx_plan and fx_bind_tm = fx_word fx_bind and fx_leaves_tm = fx_word fx_leaves
and fx_budget_tm = fx_word fx_budget and fx_used0_tm = fx_word fx_used0 and fx_ret_tm = fx_word fx_ret;;
let fx_cfr_sub = `word_sub (word 196608) (word 248):int64`;;
let FX_CFR_EQ = WORD_REDUCE_CONV fx_cfr_sub;;

(* ------------------------------------------------------------------------- *)
(* Evaluation tactics: bounded quantifiers expanded linearly, closed         *)
(* subterms evaluated before a case split, arithmetic on words.              *)
(* ------------------------------------------------------------------------- *)

let FX_ARITH_TAC =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC FIBRE_EVAL_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ntm_db; ntm_ty] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

(* 8 * v + 8 <= c (c a multiple of 8) as v < c / 8. *)
let FX_MUL8_CONV tm =
  match tm with
    Comb(Comb(Const("<=",_),Comb(Comb(Const("+",_),Comb(Comb(Const("*",_),e),v)),e')),c)
      when e = `8` && e' = `8` && is_var v && is_numeral c ->
      ARITH_RULE(mk_eq(tm, mk_binop `(<):num->num->bool` v (mk_small_numeral(dest_small_numeral c / 8))))
  | _ -> failwith "FX_MUL8_CONV";;

let FX_CLOSED_CONV conv tm = if frees tm = [] && not (is_numeral tm) then conv tm else failwith "FX_CLOSED_CONV";;
let FX_CLOSEDISH_CONV conv tm =
  if subtract (frees tm) [`m_bg:int64->byte`] = [] && not (is_numeral tm) then conv tm
  else failwith "FX_CLOSEDISH_CONV";;
let FX_CLOSED_EVAL_CONV = FX_CLOSED_CONV (FIBRE_EVAL_CONV THENC WORD_REDUCE_CONV THENC NUM_REDUCE_CONV THENC FIBRE_EVAL_CONV);;

let FX_BOUNDS_TAC tac =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV (FX_CLOSED_CONV (FIBRE_EVAL_CONV THENC WORD_REDUCE_CONV THENC NUM_REDUCE_CONV))) THEN
  CONV_TAC(ONCE_DEPTH_CONV FX_MUL8_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV FX_LT_EXPAND_CONV) THEN REWRITE_TAC[MEM] THEN
  TRY(REWRITE_TAC[] THEN NO_TAC) THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> let c = concl th in
           is_eq c && is_var(lhs c) && is_numeral(rhs c)))) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  tac;;

let FX_ALL2_MEM = prove
 (`!(Q:num->num->bool) l. (!j j'. MEM j l /\ MEM j' l /\ ~(j = j') ==> Q j j') <=>
                          ALL (\j. ALL (\j'. ~(j = j') ==> Q j j') l) l`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;
let FX_ALL_MEM2 = prove
 (`!(A:num->bool) (B:int64 list->num->bool) l.
     (!st f. MEM st l /\ A f ==> B st f) <=> ALL (\st. !f. A f ==> B st f) l`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* What does not depend on the memory: the slots' layout, the driver's      *)
(* layout, its steps, the leaves, the control word range.                    *)
(* ------------------------------------------------------------------------- *)

let REFL_FIX_PL_LAYOUT = time prove(list_mk_icomb "pl_layout" [fx_bw_tm; fx_ctl_tm; fx_nctl_tm; fx_cfr_tm],
  REWRITE_TAC[pl_layout; pl_slots; drv_apart; FX_ALL2_MEM; ALL_MEM] THEN REWRITE_TAC[ALL] THEN
  FX_ARITH_TAC);;

let FX_MC_DEFS = map fx_def ("drv_mc" :: fx_leaf_mcs);;
let fx_mc_length name =
  (REWRITE_CONV[fx_def name] THENC LENGTH_CONV) (mk_icomb(`LENGTH:byte list->num`, mk_const(name, [])));;
let FX_MC_LENGTHS = map fx_mc_length ("drv_mc" :: fx_leaf_mcs);;
let FX_LEAF_TAC = CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV (FX_CLOSED_CONV FIBRE_EVAL_CONV)) THEN REWRITE_TAC FX_MC_LENGTHS THEN FX_ARITH_TAC;;

let REFL_FIX_DRV_LAYOUT = time prove(list_mk_icomb "drv_layout"
    [fx_pc_tm; fx_cfr_sub; fx_d_tm; fx_plan_tm; `20`; fx_ctl_tm; fx_nctl_tm; fx_bind_tm; `58`;
     fx_leaves_tm; `7`; fx_lpc_tm; fx_lmc],
  REWRITE_TAC[drv_layout; drv_apart] THEN REPEAT CONJ_TAC THEN
  TRY(FX_ARITH_TAC THEN NO_TAC) THEN FX_BOUNDS_TAC FX_LEAF_TAC);;

let FX_DECLS = [INTERN16_DECLS; PACK_DECLS; UNPACK_DECLS; EQW_DECLS; ROW_WORD_DECLS; LIVE_DECLS;
                APPEND_ROW_DECLS];;
let FX_CHILD_TAC =
  GEN_TAC THEN DISCH_THEN(fun th ->
    let reg0, rest = CONJ_PAIR th in
    let insts = map (fun r -> MP (SPEC (mk_small_numeral r) rest) (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral r) `9`)))
                    (0--8) in
    MAP_EVERY ASSUME_TAC (reg0 :: map CONJUNCT1 insts @ map CONJUNCT2 insts)) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV FX_CLOSED_EVAL_CONV) THEN
  REWRITE_TAC FX_DECLS THEN REWRITE_TAC[tisa_decls_ok; tisa_pairs_ok; tisa_region_ok; tisa_pair_ok; tisa_frame] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[drv_base; drv_len] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV FX_CLOSED_EVAL_CONV) THEN FX_ARITH_TAC;;

let FX_APART_IN = prove
 (`!a b l c m. drv_apart b l c m /\ drv_in a c m ==> ~drv_in a b l`,
  REWRITE_TAC[drv_apart; drv_in] THEN ARITH_TAC);;
let FX_RW_STATIC = prove
 (`!decls bw st pc cfr d plan ns bind nbw leaves nl lpc lmc.
     (!r. tisa_rw decls r
          ==> drv_apart (drv_base bw st r) (val(drv_len bw st r)) (word pc) 522 /\
              (!j. j < nl ==> drv_apart (drv_base bw st r) (val(drv_len bw st r)) (word(lpc j)) (LENGTH(lmc j))) /\
              drv_apart (drv_base bw st r) (val(drv_len bw st r)) d 64 /\
              drv_apart (drv_base bw st r) (val(drv_len bw st r)) plan (144 * ns) /\
              drv_apart (drv_base bw st r) (val(drv_len bw st r)) bind (8 * nbw) /\
              drv_apart (drv_base bw st r) (val(drv_len bw st r)) leaves (8 * nl) /\
              drv_apart (drv_base bw st r) (val(drv_len bw st r)) (word_add cfr (word 248)) 8)
     ==> !r a. tisa_rw decls r /\ drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a
               ==> ~drv_in a (drv_base bw st r) (val(drv_len bw st r))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun rw -> FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP rw o SPEC `r:num`)) MP_TAC) THEN
  REWRITE_TAC[drv_static] THEN STRIP_TAC THEN ASM_MESON_TAC[FX_APART_IN]);;
let FX_RW_TAC =
  MATCH_MP_TAC FX_RW_STATIC THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV FX_CLOSED_EVAL_CONV) THEN REWRITE_TAC FX_DECLS THEN
  REWRITE_TAC[tisa_rw] THEN
  FX_BOUNDS_TAC (REWRITE_TAC[drv_apart; drv_base; drv_len] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
                 CONV_TAC(ONCE_DEPTH_CONV FX_CLOSED_EVAL_CONV) THEN REWRITE_TAC FX_MC_LENGTHS THEN FX_ARITH_TAC THEN
                 TRY(FX_BOUNDS_TAC (CONV_TAC(ONCE_DEPTH_CONV FX_CLOSED_EVAL_CONV) THEN REWRITE_TAC FX_MC_LENGTHS THEN FX_ARITH_TAC)));;
let FX_READABLE_TAC =
  REWRITE_TAC[tisa_readable; drv_apart; drv_base; drv_len] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV FX_CLOSED_EVAL_CONV) THEN REWRITE_TAC FX_DECLS THEN
  FX_BOUNDS_TAC (CONV_TAC(ONCE_DEPTH_CONV FX_CLOSED_EVAL_CONV) THEN REWRITE_TAC FX_DECLS THEN
                 CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
let FX_STEP_TAC =
  REWRITE_TAC[drv_step_ok] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN REWRITE_TAC[];
    FX_ARITH_TAC;
    FX_BOUNDS_TAC FX_ARITH_TAC;
    FX_BOUNDS_TAC FX_ARITH_TAC;
    FX_CHILD_TAC;
    FX_READABLE_TAC;
    FX_RW_TAC];;
let fx_step_ok_f = list_mk_icomb "drv_step_ok"
  [fx_progs; fx_pc_tm; fx_cfr_sub; fx_d_tm; fx_plan_tm; `20`; fx_nctl_tm; fx_bind_tm; `58`; fx_leaves_tm;
   `7`; fx_lpc_tm; fx_lmc; fx_bw_tm];;
let REFL_FIX_DRV_STEPS = time prove(list_mk_icomb "ALL" [fx_step_ok_f; `pl_plan_refl`],
  REWRITE_TAC[pl_plan_refl; ALL] THEN REPEAT CONJ_TAC THEN FX_STEP_TAC);;

let FX_LEAF_WFS = [INTERN16_LEAF_WF; PACK_LEAF_WF; UNPACK_LEAF_WF; EQW_LEAF_WF; ROW_WORD_LEAF_WF;
                   LIVE_LEAF_WF; APPEND_ROW_LEAF_WF];;
let FX_LEAF_SPECS = [INTERN16_LEAF_SPEC; PACK_LEAF_SPEC; UNPACK_LEAF_SPEC; EQW_LEAF_SPEC; ROW_WORD_LEAF_SPEC;
                     LIVE_LEAF_SPEC; APPEND_ROW_LEAF_SPEC];;
let REFL_FIX_LEAVES = time prove(
  mk_forall(`j:num`, mk_imp(`j < 7`, mk_conj(mk_icomb(`tisa_leaf_wf`, mk_comb(fx_progs, `j:num`)),
    list_mk_icomb "tisa_leaf_spec" [mk_comb(fx_progs, `j:num`); mk_comb(fx_lmc, `j:num`); mk_comb(fx_lpc_tm, `j:num`)]))),
  FX_BOUNDS_TAC (CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV FX_CLOSED_EVAL_CONV) THEN
                 REWRITE_TAC (FX_LEAF_WFS @ FX_LEAF_SPECS)));;

let REFL_FIX_PROGS_OK = prove(mk_icomb(`pl_progs_ok`, fx_progs),
  REWRITE_TAC[pl_progs_ok] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC FIBRE_EVAL_CONV THEN REWRITE_TAC[]);;
let REFL_FIX_CW_RANGE = time prove(`pl_cw_range 48 pl_plan_refl`,
  REWRITE_TAC[pl_cw_range; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[FX_ALL_MEM2] THEN REWRITE_TAC[pl_plan_refl; ALL] THEN REPEAT CONJ_TAC THEN
  FX_BOUNDS_TAC FX_ARITH_TAC);;

let FX_DRV_CODE_BYTES = prove
 (`!(m:int64->byte) p mc. read (bytes(word p, LENGTH mc)) m = num_of_bytelist mc ==> drv_code m p mc`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[drv_code; bytelist; READ_COMPONENT_COMPOSE; through; read] THEN
  ASM_REWRITE_TAC[BYTELIST_OF_NUM_OF_BYTELIST]);;

(* ------------------------------------------------------------------------- *)
(* One instance: control word 8 holds t; the memory is the constant name    *)
(* applied to the background m_bg, so goals carry a small atom and only     *)
(* reads unfold it. Every premise of DRV_CORRECT and of PL_REFL_REL.         *)
(* ------------------------------------------------------------------------- *)

type refl_fix =
  { rf_cw : term; rf_pre : term; rf_mem : term; rf_memdef : thm; rf_inv : thm; rf_plan_rel : thm;
    rf_code : thm; rf_holds : thm; rf_drv : thm; rf_at : thm };;

let refl_fixture name t =
  let cw = subst [mk_small_numeral t, `t0:num`] `\k:num. if k <= 6 then k else if k = 8 then t0 else 0` in
  let cw_words = map (fun k -> if k <= 6 then k else if k = 8 then t else 0) (0--(fx_nctl - 1)) in
  let pre = mk_pair(cw, mk_pair(fx_s13, `[]:num list`)) in
  let inv = prove(mk_icomb(`pl_inv`, pre),
    REWRITE_TAC[pl_inv; FX_KEYS; FX_DISTINCT_TYS; FX_DISTINCT_DBS] THEN
    CONJ_TAC THENL [ACCEPT_TAC(CONJUNCT1 REFL_FIX_NAT_PRE); ALL_TAC] THEN
    CONJ_TAC THENL [MP_TAC(CONJUNCT2 REFL_FIX_NAT_PRE) THEN MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LENGTH; LT] THEN CONV_TAC FIBRE_EVAL_CONV) in
  let mdef = new_definition(mk_eq(mk_comb(mk_var(name, `:(int64->byte)->int64->byte`), `m_bg:int64->byte`),
                                  fx_memory cw_words)) in
  let m0 = lhs(concl(SPEC_ALL mdef)) in
  (* reading the memory *)
  let mem_conv = REWRITE_CONV[pl_mw; drv_word; mdef] THENC TISA_EVAL_CONV in
  let read_conv tm =
    match strip_comb tm with
      Const("read",_), [_; Comb(Const(c,_),_)] when c = name -> (REWRITE_CONV[mdef] THENC TISA_EVAL_CONV) tm
    | _ -> failwith "read_conv" in
  let plmw_conv tm =
    match strip_comb tm with
      Const("pl_mw",_), [_;_;_] -> mem_conv tm
    | _ -> failwith "plmw_conv" in
  let reads_tac = CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC FIBRE_EVAL_CONV THEN
                  CONV_TAC(ONCE_DEPTH_CONV plmw_conv) THEN FX_ARITH_TAC in
  (* plan_rel, conjunct by conjunct *)
  let fx_ntms_tm = el 3 fx_ns_pre and fx_ths_tm = el 5 fx_ns_pre and fx_drops_tm = el 8 fx_ns_pre in
  let cwords = time prove(list_mk_icomb "pl_cwords" [fx_ctl_tm; fx_nctl_tm; m0; cw],
    REWRITE_TAC[pl_cwords] THEN FX_BOUNDS_TAC reads_tac) in
  let rtab_tm = time prove(list_mk_icomb "pl_rtab"
      [fx_bw_tm; `12`; `14`; `5`; m0; mk_abs(`i:num`, mk_abs(`w:num`,
         list_mk_icomb "pl_f5" [list_mk_icomb "EL" [`i:num`; fx_ntms_tm]; `w:num`]));
       mk_icomb(`LENGTH:(num#num#num#num#num)list->num`, fx_ntms_tm)],
    REWRITE_TAC[pl_rtab] THEN REPEAT CONJ_TAC THEN TRY(reads_tac THEN NO_TAC) THEN
    FX_BOUNDS_TAC (REWRITE_TAC[pl_f5] THEN reads_tac)) in
  let rtab_th = time prove(list_mk_icomb "pl_rtab"
      [fx_bw_tm; `18`; `20`; `2`; m0; mk_abs(`i:num`, mk_abs(`w:num`,
         list_mk_icomb "pl_f2" [list_mk_icomb "EL" [`i:num`; fx_ths_tm]; `w:num`]));
       mk_icomb(`LENGTH:(num#num)list->num`, fx_ths_tm)],
    REWRITE_TAC[pl_rtab; LENGTH] THEN REPEAT CONJ_TAC THEN TRY(reads_tac THEN NO_TAC) THEN
    FX_BOUNDS_TAC reads_tac) in
  let marks spc n jm = list_mk_icomb "pl_marks" [fx_bw_tm; mk_small_numeral jm; m0; mk_small_numeral spc; n; fx_drops_tm] in
  let marks_tm = time prove(marks 2 (mk_icomb(`LENGTH:(num#num#num#num#num)list->num`, fx_ntms_tm)) 16,
    REWRITE_TAC[pl_marks; LENGTH; MEM] THEN REPEAT CONJ_TAC THEN
    TRY(reads_tac THEN NO_TAC) THEN FX_BOUNDS_TAC reads_tac) in
  let marks_th = time prove(marks 3 (mk_icomb(`LENGTH:(num#num)list->num`, fx_ths_tm)) 22,
    REWRITE_TAC[pl_marks; LENGTH; MEM] THEN REPEAT CONJ_TAC THEN
    TRY(reads_tac THEN NO_TAC) THEN FX_BOUNDS_TAC reads_tac) in
  let stk = prove(list_mk_icomb "pl_stk" [fx_bw_tm; m0; `[]:num list`],
    REWRITE_TAC[pl_stk; LENGTH; LT] THEN FX_ARITH_TAC) in
  (* the interners: a witness state with register 0 at the interner's frame and this memory *)
  let probe_dists nslots rows =
    let slots = Array.of_list (fx_slots nslots rows) and mask = nslots - 1 in
    List.mapi (fun j r ->
      let k0, k1 = fx_key r in
      let h = Int64.to_int (Int64.logand (fx_hash k0 k1) (Int64.of_int mask)) in
      let rec find x = if x >= nslots then failwith "probe_dists" else
                       if slots.((h + x) land mask) = j + 1 then x else find (x + 1) in
      find 0) rows in
  let tstate frame = list_mk_icomb "TState"
    [mk_abs(`r:num`, mk_cond(`r = 0`, mk_comb(`word:num->int64`, mk_small_numeral frame), `word 0:int64`)); m0] in
  let tisa_defs = [intern_ok; intern_complete; intern_distinct; intern_has; intern_count; intern_word;
                   intern_slots; intern_pos; intern_slot; intern_hash; tisa_read; tisa_base; tisa_len;
                   tisa_fword; tisa_frame; tregs; tmem] in
  let eval_tac =
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV (FX_CLOSEDISH_CONV read_conv)) THEN
    CONV_TAC(ONCE_DEPTH_CONV (FX_CLOSED_CONV (FIBRE_EVAL_CONV THENC WORD_REDUCE_CONV THENC NUM_REDUCE_CONV))) THEN
    REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] in
  let pre_tac = REWRITE_TAC tisa_defs THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV (FX_CLOSEDISH_CONV read_conv)) THEN
    CONV_TAC(ONCE_DEPTH_CONV (FX_CLOSED_CONV (FIBRE_EVAL_CONV THENC WORD_REDUCE_CONV THENC NUM_REDUCE_CONV))) in
  let itab_tac frame dists =
    REWRITE_TAC[pl_itab] THEN EXISTS_TAC (tstate frame) THEN
    REWRITE_TAC[tmem] THEN REPEAT CONJ_TAC THENL
     [FX_BOUNDS_TAC (pre_tac THEN eval_tac);
      pre_tac THEN REPEAT CONJ_TAC THENL
       [eval_tac;
        GEN_TAC THEN DISCH_TAC THEN
        EXISTS_TAC (list_mk_icomb "EL" [`i:num`; mk_list(map mk_small_numeral dists, `:num`)]) THEN
        POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
        FX_BOUNDS_TAC (FX_BOUNDS_TAC eval_tac);
        FX_BOUNDS_TAC eval_tac];
      pre_tac THEN eval_tac;
      FX_BOUNDS_TAC (pre_tac THEN eval_tac)] in
  let itab j rows = list_mk_icomb "pl_itab" [fx_bw_tm; mk_small_numeral j; m0; rows] in
  let itab_db = time prove(itab 6 (el 4 fx_ns_pre), itab_tac fx_fdb (probe_dists 64 fx_dbs)) in
  let itab_ty = time prove(itab 0 (el 2 fx_ns_pre), itab_tac fx_fty (probe_dists 64 fx_tys)) in
  let rel = time prove(list_mk_icomb "plan_rel" [fx_bw_tm; fx_ctl_tm; fx_nctl_tm; fx_cfr_tm; m0; pre],
    REWRITE_TAC[plan_rel] THEN
    REWRITE_TAC[REFL_FIX_PL_LAYOUT; cwords; itab_ty; itab_db; rtab_tm; marks_tm; rtab_th; marks_th; stk] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]) in
  (* the code and the driver's descriptor in memory *)
  let code_tac =
    MATCH_MP_TAC FX_DRV_CODE_BYTES THEN REWRITE_TAC FX_MC_DEFS THEN
    CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV (FX_CLOSEDISH_CONV read_conv)) THEN
    REWRITE_TAC[num_of_bytelist] THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV in
  let code = time prove(mk_conj(list_mk_icomb "drv_code" [m0; fx_pc_tm; `drv_mc`],
      mk_forall(`j:num`, mk_imp(`j < 7`, list_mk_icomb "drv_code" [m0; mk_comb(fx_lpc_tm, `j:num`); mk_comb(fx_lmc, `j:num`)]))),
    CONJ_TAC THENL [code_tac;
                    FX_BOUNDS_TAC (CONV_TAC(ONCE_DEPTH_CONV (FX_CLOSED_CONV FIBRE_EVAL_CONV)) THEN code_tac)]) in
  let drvw_tac = REWRITE_TAC[drv_word] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV (FX_CLOSEDISH_CONV read_conv)) THEN FX_ARITH_TAC in
  let holds = time prove(list_mk_icomb "drv_holds"
      [m0; fx_d_tm; fx_plan_tm; `20`; fx_ctl_tm; fx_bind_tm; fx_leaves_tm; fx_budget_tm; fx_used0_tm;
       `pl_plan_refl`; fx_bw_tm; `58`; fx_lpc_tm; `7`],
    REWRITE_TAC[drv_holds; pl_plan_refl] THEN REPEAT CONJ_TAC THEN
    TRY(CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(drvw_tac THEN NO_TAC) THEN FX_BOUNDS_TAC drvw_tac) in
  (* DRV_CORRECT and PL_REFL_REL at the instance *)
  let drv = MP (SPEC_ALL (ISPECL [fx_progs; fx_lpc_tm; fx_lmc; `7`; fx_pc_tm; fx_sp_tm; fx_d_tm; fx_plan_tm; `20`;
                                  fx_ctl_tm; fx_nctl_tm; fx_bind_tm; `58`; fx_leaves_tm; fx_bw_tm; `pl_plan_refl`;
                                  fx_budget_tm; fx_used0_tm; m0; fx_ret_tm] DRV_CORRECT))
               (end_itlist CONJ [REFL_FIX_LEAVES; REFL_FIX_DRV_LAYOUT; REFL_FIX_DRV_STEPS; holds;
                                 CONJUNCT1 code; CONJUNCT2 code]) in
  let at =
    let th = ISPECL ([fx_progs; fx_bw_tm; fx_ctl_tm; fx_nctl_tm; fx_budget_tm; fx_cfr_tm; m0; fx_used0_tm;
                      `res:int64#num#(int64->byte)#int64`; cw] @ fx_ns_pre @ [`[]:num list`; mk_small_numeral t])
                    PL_REFL_REL in
    let ant = lhand(concl th) in
    let sem = find (fun c -> try fst(dest_const(fst(strip_comb c))) = "drv_sem" with Failure _ -> false) (conjuncts ant) in
    let rest = prove(mk_imp(sem, ant),
      DISCH_TAC THEN ASM_REWRITE_TAC[REFL_FIX_PROGS_OK; REFL_FIX_CW_RANGE; rel; inv] THEN
      CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]) in
    GEN `res:int64#num#(int64->byte)#int64` (IMP_TRANS rest th) in
  { rf_cw = cw; rf_pre = pre; rf_mem = m0; rf_memdef = mdef; rf_inv = inv; rf_plan_rel = rel;
    rf_code = code; rf_holds = holds; rf_drv = REWRITE_RULE[FX_CFR_EQ] drv; rf_at = at };;

(* ensures x86 P Q C, with Q s = ... ?res. drv_sem ... res /\ read RAX s = FST res ..., and         *)
(* |- !res. drv_sem ... res ==> E (FST res): ensures x86 P (\s. Q s /\ extra s) C.                    *)
let fx_ensures_rax drv_th lemma extra =
  let f, args = strip_comb (concl drv_th) in
  let q = el 2 args in
  let s = mk_var("s", fst(dest_fun_ty(type_of q))) in
  let qs = rhs(concl(BETA_CONV(mk_comb(q, s)))) in
  let q' = mk_abs(s, mk_conj(qs, extra s)) in
  let goal = list_mk_comb(f, [el 0 args; el 1 args; q'; el 3 args]) in
  prove(goal,
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC q THEN REWRITE_TAC[drv_th] THEN
    GEN_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN(fun th -> CONJ_TAC THENL [ACCEPT_TAC th; STRIP_ASSUME_TAC th]) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP lemma) THEN ASM_REWRITE_TAC[]);;
let fx_rax v s = mk_eq(mk_comb(`read RAX`, s), mk_comb(`word:num->int64`, mk_small_numeral v));;
let fx_res = `res:int64#num#(int64->byte)#int64`;;

(* ------------------------------------------------------------------------- *)
(* Operand 4: REFUSED.                                                       *)
(* ------------------------------------------------------------------------- *)

let REFL_FIX4 = refl_fixture "refl_fix_mem4" 4;;
let REFL_FIX4_NOT_LIVE =
  let eq = SPEC `4` (MATCH_MP PL_REFL_GUARDS REFL_FIX4.rf_inv) in
  prove(mk_neg(lhs(concl eq)), REWRITE_TAC[eq; holr_live; LENGTH; MEM] THEN CONV_TAC NUM_REDUCE_CONV);;
let REFL_FIX4_REFUSED = prove(mk_forall(fx_res, mk_imp(lhand(concl(SPEC fx_res REFL_FIX4.rf_at)),
                                                       `FST(res:int64#num#(int64->byte)#int64) = word 0`)),
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REFL_FIX4.rf_at) THEN REWRITE_TAC[REFL_FIX4_NOT_LIVE] THEN SIMP_TAC[]);;
let REFL_FIX4_X86 = fx_ensures_rax REFL_FIX4.rf_drv REFL_FIX4_REFUSED (fx_rax 0);;

(* ------------------------------------------------------------------------- *)
(* Operand 0: FIRED. One run of the plan from the fixture memory, evaluated  *)
(* step by step, ends FIRED; by DRV_SEM_FUN so does every run of drv_sem    *)
(* from it; with PL_REFL_REL its final memory represents a native state     *)
(* that nat_step reaches by RRefl 0.                                         *)
(* ------------------------------------------------------------------------- *)

let REFL_FIX0 = refl_fixture "refl_fix_mem0" 0;;
let FX_LEAF_TERMS = [PACK_TERM; UNPACK_TERM; EQW_TERM; ROW_WORD_TERM; LIVE_TERM; APPEND_ROW_TERM;
                     intern16; intern16_prologue; intern16_body];;
let fx_eval_conv = Compute.CBV_CONV (drv_eval_compset (FX_LEAF_TERMS @ [REFL_FIX0.rf_memdef]));;
let REFL_FIX0_RUN = time (drv_run_eval fx_eval_conv fx_progs fx_bw_tm fx_ctl_tm fx_budget_tm fx_cfr_tm
                            (dest_list (rand(concl pl_plan_refl))) REFL_FIX0.rf_mem) fx_used0_tm;;
let REFL_FIX0_RUN' = REWRITE_RULE[GSYM pl_plan_refl] REFL_FIX0_RUN;;
let fx_sem0 = lhand(concl(SPEC fx_res REFL_FIX0.rf_at));;
let REFL_FIX0_FIRED = prove(mk_forall(fx_res, mk_imp(fx_sem0, `FST(res:int64#num#(int64->byte)#int64) = word 1`)),
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP DRV_SEM_FUN (end_itlist CONJ
    [REWRITE_RULE[FX_CFR_EQ] REFL_FIX_DRV_LAYOUT;
     prove(mk_forall(`j:num`, mk_imp(`j < 7`, mk_icomb(`tisa_leaf_wf`, mk_comb(fx_progs, `j:num`)))),
           MESON_TAC[REFL_FIX_LEAVES]);
     REWRITE_RULE[FX_CFR_EQ] REFL_FIX_DRV_STEPS;
     prove(mk_forall(`a:int64`, mk_imp(mk_neg(list_mk_icomb "drv_stack" [fx_cfr_tm; `a:int64`]),
                                       mk_eq(mk_comb(REFL_FIX0.rf_mem, `a:int64`), mk_comb(REFL_FIX0.rf_mem, `a:int64`)))),
           REWRITE_TAC[]);
     REFL_FIX0_RUN'; ASSUME fx_sem0])) THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN REWRITE_TAC[FST]);;
let REFL_FIX0_STEP = prove(mk_forall(fx_res,
    mk_imp(fx_sem0, mk_conj(`FST(res:int64#num#(int64->byte)#int64) = word 1`,
                            rand(lhand(rand(concl(SPEC fx_res REFL_FIX0.rf_at))))))),
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REFL_FIX0_FIRED) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP REFL_FIX0.rf_at) THEN ASM_SIMP_TAC[]);;
let REFL_FIX0_X86 = fx_ensures_rax REFL_FIX0.rf_drv REFL_FIX0_FIRED (fx_rax 1);;

(* ------------------------------------------------------------------------- *)
(* The new theorem row. RRefl t appends one row (e,k): e decodes to no      *)
(* hypotheses and k to the equation tm = tm of term t. At the fixture term 0 *)
(* decodes to x, so the FIRED run's final memory represents |- x = x.        *)
(* ------------------------------------------------------------------------- *)

let NAT_STEP_REFL_ROW = prove
 (`!ctx nms tys ntms dbs ths nmap ymap drops pol t s'.
     nat_step (ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol) (RRefl t) s'
     ==> ?tm mt md e k.
           fdtm nms tys ntms t tm /\
           fddbs nms (APPEND tys mt) (APPEND dbs md) e [] /\
           fddb nms (APPEND tys mt) (APPEND dbs md) k (hdb (tm =:= tm)) /\
           s' = (ctx,nms,APPEND tys mt,ntms,APPEND dbs md,APPEND ths [(e,k)],nmap,ymap,drops,pol)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[nat_step_CASES] THEN
  REWRITE_TAC[HOLR_RECORD_DISTINCT; HOLR_RECORD_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

let FX_FDTM0 = fdtm_thm (el 1 fx_ns_pre) (el 2 fx_ns_pre) (el 3 fx_ns_pre) 0;;
let fx_x = rand(concl FX_FDTM0);;
let FX_ROW_INST = REWRITE_RULE[CONJUNCT1 APPEND] (ISPECL (fx_ns_pre @ [`0`]) NAT_STEP_REFL_ROW);;
let fx_ns_after, fx_row_ex = dest_forall(concl FX_ROW_INST);;
let fx_row_body = let tmv, b = dest_exists(rand fx_row_ex) in subst [fx_x, tmv] b;;

let REFL_FIX0_ROW =
  let ex = rand(rand(concl(SPEC fx_res REFL_FIX0_STEP))) in
  let p', b = dest_exists ex in
  let goal = mk_forall(fx_res, mk_imp(fx_sem0,
    mk_conj(`FST(res:int64#num#(int64->byte)#int64) = word 1`,
            mk_exists(p', list_mk_conj [rand(lhand b); rand b;
              subst [list_mk_icomb "FST" [list_mk_icomb "SND" [p']], fx_ns_after] fx_row_body])))) in
  prove(goal,
    GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REFL_FIX0_STEP) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN p' STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC p' THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP FX_ROW_INST o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "nat_step")) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `tm:holterm` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (mk_eq(`tm:holterm`, fx_x)) SUBST_ALL_TAC THENL
     [MP_TAC(SPECL [el 1 fx_ns_pre; el 2 fx_ns_pre; el 3 fx_ns_pre; `0`; `tm:holterm`] FDTM_FUNCTIONAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ACCEPT_TAC FX_FDTM0;
      ALL_TAC] THEN
    ASM_MESON_TAC[]);;

let fx_report name th =
  Printf.printf "REFL_FIX %s: hypotheses %d\n%!" name (length (hyp th));;
do_list (uncurry fx_report)
  ["REFL_FIX_NAT_PRE", REFL_FIX_NAT_PRE; "REFL_FIX_DRV_LAYOUT", REFL_FIX_DRV_LAYOUT;
   "REFL_FIX_DRV_STEPS", REFL_FIX_DRV_STEPS; "REFL_FIX_LEAVES", REFL_FIX_LEAVES;
   "REFL_FIX4 plan_rel", REFL_FIX4.rf_plan_rel; "REFL_FIX4_REFUSED", REFL_FIX4_REFUSED;
   "REFL_FIX4_X86", REFL_FIX4_X86;
   "REFL_FIX0 plan_rel", REFL_FIX0.rf_plan_rel; "REFL_FIX0_RUN", REFL_FIX0_RUN';
   "REFL_FIX0_FIRED", REFL_FIX0_FIRED; "REFL_FIX0_STEP", REFL_FIX0_STEP; "REFL_FIX0_X86", REFL_FIX0_X86;
   "NAT_STEP_REFL_ROW", NAT_STEP_REFL_ROW; "REFL_FIX0_ROW", REFL_FIX0_ROW];;
Printf.printf "REFL_FIX axioms %d\n%!" (length (axioms()));;
