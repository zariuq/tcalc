(* ========================================================================= *)
(* The generator's case for hoisted count loops (tisa_x86_hoist.ml): the     *)
(* template copy as for any count loop; the entry test, proved to establish  *)
(* H, the facts its ranges give; the fast copy's body, proved whole under H  *)
(* and j < nv; then the join.                                                *)
(* ========================================================================= *)

needs "tisa/hol/tisa_x86_hoist.ml";;
needs "tisa/hol/tisa_x86_hoist_fund.ml";;
needs "tisa/hol/tisa_x86_hoist_early_fund.ml";;

(* Loop path -> (ranges (region, base, k, lo, hi), FUND units), from the
   tisa_hoist record of the image being proved. *)
let tisa_loop_ranges = ref ([] : (string * ((int * int * int * int * int) list * int)) list);;

(* H as facts text: at least one iteration, and per range the lower and upper
   bound the entry test checked, for q = b - base(r) (0 for the region's own
   base): q + lo >= 0, and q + k * (nv - 1) + hi <= len. *)
let tisa_hoist_facts nvn ranges =
  let range (r, b, k, lo, hi) =
    let bv = if b = 254 then None else Some b in
    let lower = if lo >= 0 then [] else
      [match bv with
       | Some b -> Printf.sprintf "val (B%d:int64) + %d <= val(tregs t %d)" r (-lo) b
       | None -> Printf.sprintf "%d <= 0" (-lo)] in
    let upper = match bv, hi >= 0 with
      | Some b, true -> Printf.sprintf "val(tregs t %d) + %d * %s + %d <= val (B%d:int64) + val (L%d:int64) + %d" b k nvn hi r r k
      | Some b, false -> Printf.sprintf "val(tregs t %d) + %d * %s <= val (B%d:int64) + val (L%d:int64) + %d" b k nvn r r (k - hi)
      | None, true -> Printf.sprintf "%d * %s + %d <= val (L%d:int64) + %d" k nvn hi r k
      | None, false -> Printf.sprintf "%d * %s <= val (L%d:int64) + %d" k nvn r (k - hi) in
    lower @ [upper] in
  (Printf.sprintf "1 <= %s" nvn) :: List.concat (map range ranges);;

let tisa_text_conj facts = "(\\t:tisa_state. " ^ String.concat " /\\ " facts ^ ")";;

(* A facts text with more conjuncts. *)
let tisa_facts_plus text extra =
  if extra = [] then text
  else String.sub text 0 (String.length text - 1) ^
       String.concat "" (map (fun e -> " /\\ " ^ e) extra) ^ ")";;

let TISA_RUNSF_STRENGTHEN_PRE = prove
 (`!mc pc oa oe epi (P:tisa_state->bool) P' Q f C.
        (!t. P' t ==> P t) /\ tisa_x86_runsf mc pc oa oe epi P Q f C
        ==> tisa_x86_runsf mc pc oa oe epi P' Q f C`,
  REWRITE_TAC[tisa_x86_runsf] THEN MESON_TAC[]);;

(* A product of words in value arithmetic, exact unless it wraps (the entry
   test's F * n, with n at most the loop cap). *)
let TISA_VAL_WORD_MUL_CASES = prove
 (`!x y:int64. val(word_mul x y) =
      if val x * val y < 2 EXP 64 then val x * val y else (val x * val y) MOD 2 EXP 64`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_MUL; DIMINDEX_64] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MOD_LT]);;

(* The test's "at most" (CF or ZF): ZF as a word equation, which the
   arithmetic reads only as values. *)
let TISA_WORD_SUB_EQ_0_VAL = prove
 (`!x y:int64. word_sub x y = word 0 <=> val x = val y`,
  REWRITE_TAC[WORD_SUB_EQ_0; VAL_EQ]);;

(* The entry test, per instance. *)
let TISA_HOIST_TEST_TAC execth stops =
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[tisa_x86_hoist_test] THEN X_GEN_TAC `t:tisa_state` THEN BETA_TAC THEN
  REWRITE_TAC[tisa_x86_rel; tisa_fword; tisa_read; tisa_frame; tregs; tmem] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0; INT_ADD_RID] THEN
  TISA_NAME_STATE_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `v0:int64 = fr`)) THEN
  RULE_ASSUM_TAC TISA_HIDE_MREAD_RULE THEN
  REWRITE_TAC[SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  TISA_RUN_TAC execth `pc:num` stops 1 THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC (TISA_HIDE_MREAD_RULE o TISA_MEM_NORM_RULE) THEN
  CONV_TAC(TOP_DEPTH_CONV(GEN_REWRITE_CONV I [GSYM tisa_mread])) THEN
  TISA_FRAME_EQS_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV o REWRITE_RULE[TISA_VAL_WORD_MUL_CASES; TISA_WORD_SUB_EQ_0_VAL]) THEN
  TRY(DISJ2_TAC THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TISA_ARITH_GOAL_TAC);;

(* The fast latch, per instance. *)
let TISA_FAST_LATCH_TAC execth stops =
  REWRITE_TAC[tisa_x86_fast_latch; tisa_x86_rel; tisa_setreg; tregs; tmem] THEN
  X_GEN_TAC `t:tisa_state` THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  TISA_NAME_STATE_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN TISA_RUN_TAC execth `pc:num` stops 1 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN TISA_ARITH_GOAL_TAC;;

(* Products with the numeral first, as x86 addressing writes scaled indices. *)
let TISA_MULT_NUMERAL_LEFT_CONV tm =
  match tm with
  | Comb(Comb(Const("*",_),a),k) when type_of tm = `:num` && is_numeral k && not (is_numeral a) ->
      REWR_CONV MULT_SYM tm
  | _ -> failwith "TISA_MULT_NUMERAL_LEFT_CONV";;

let TISA_WORD_ADD_LCANCEL = WORD_RULE `!x y z:int64. word_add x y = word_add x z <=> y = z`;;

let TISA_FAST_FINISH_TAC =
  CONV_TAC(TOP_DEPTH_CONV TISA_MULT_NUMERAL_LEFT_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV TISA_MULT_NUMERAL_LEFT_CONV)) THEN
  TRY(REWRITE_TAC[TISA_WORD_ADD_LCANCEL]) THEN TISA_WORD_FINISH_TAC;;

(* A whole body at once: its statements in sequence are run through
   tisa_then, which the per-statement templates never meet. *)
let TISA_THEN_COND = prove
 (`!c (a:tisa_result) b f. tisa_then (if c then a else b) f = if c then tisa_then a f else tisa_then b f`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* An effective address from a register plus an integer sum: the register
   plus the word of the sum (so that every access has the shape
   word_add x (word n) that the arithmetic reads). *)
let TISA_IWORD_VAL_ADD_INT = prove
 (`!(x:int64) e. iword(&(val x) + e) = word_add x (iword e)`,
  REWRITE_TAC[IWORD_INT_ADD; TISA_IWORD_VAL]);;

let TISA_BODY_SETUP_TAC =
  REWRITE_TAC[tisa_x86_runs] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  X_GEN_TAC `t:tisa_state` THEN BETA_TAC THEN
  REWRITE_TAC[tisa_exec; tisa_instr; tisa_fund; tisa_fail; tisa_finish] THEN
  REPEAT(CHANGED_TAC(REWRITE_TAC[tisa_then; TISA_THEN_COND] THEN CONV_TAC(DEPTH_CONV BETA_CONV))) THEN
  REWRITE_TAC[TISA_X86_POSTF_COND] THEN
  REWRITE_TAC[tisa_x86_postf] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[tisa_x86_rel; tisa_setfword; tisa_store; tisa_setreg;
              tisa_inside; tisa_ea; tisa_addr_mid; tisa_index; tisa_base; tisa_len;
              tisa_fword; tisa_read; tisa_frame; tisa_norm; tisa_bool; tisa_rhs;
              tisa_compare; tisa_compare_at; tisa_narrow; tisa_binop; tisa_shift; tisa_shift32;
              tisa_shift64; tisa_extract; tregs; tmem] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0; INT_ADD_RID] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_MUL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV TISA_MULT_NUMERAL_LEFT_CONV) THEN
  REWRITE_TAC[GSYM INT_ADD_ASSOC] THEN REWRITE_TAC[TISA_IWORD_VAL_ADD_INT] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; GSYM WORD_IWORD; MULT_CLAUSES] THEN
  TISA_IWORD_NORM_TAC THEN
  TISA_NAME_STATE_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `v0:int64 = fr`)) THEN
  RULE_ASSUM_TAC TISA_HIDE_MREAD_RULE THEN
  REWRITE_TAC[SOME_FLAGS] THEN ENSURES_INIT_TAC "s0";;

(* What the fast body's leaves leave: reads of one address in two shapes
   (base + ((j + c) + d) against (base + (j + c)) + d), and branches the
   facts refute once reads through the writes are resolved (after the
   leaf's first refutation attempt). *)
(* A negative displacement folded into a numeral (lea's word (a + 2^64 - n)),
   as the subtraction it is, so that its value is linear arithmetic with
   cases rather than a value modulo 2^64. *)
let TISA_WORD_NEG_DISP = prove
 (`!a n. n <= 2 EXP 64 ==> word (a + (2 EXP 64 - n)):int64 = word_sub (word a) (word n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_IWORD; GSYM IWORD_INT_SUB] THEN
  REWRITE_TAC[IWORD_EQ; DIMINDEX_64] THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_SUB] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_POW] THEN CONV_TAC INTEGER_RULE);;

let TISA_NEG_DISP_CONV tm =
  match tm with
  | Comb(Const("word",_), Comb(Comb(Const("+",_),a), nn)) when is_numeral nn && type_of tm = `:int64` ->
      let big = rhs(concl(NUM_REDUCE_CONV (mk_binop `(<=):num->num->bool` `9223372036854775808` nn))) in
      if big <> `T` then failwith "TISA_NEG_DISP_CONV: not negative" else
      let n = rhs(concl(NUM_REDUCE_CONV (mk_binop `(-):num->num->num` `2 EXP 64` nn))) in
      let th = MP (SPECL [a; n] TISA_WORD_NEG_DISP)
                  (EQT_ELIM(NUM_REDUCE_CONV (mk_binop `(<=):num->num->bool` n `2 EXP 64`))) in
      let th' = CONV_RULE (LAND_CONV (RAND_CONV (RAND_CONV NUM_REDUCE_CONV))) th in
      if lhs(concl th') = tm then th' else failwith "TISA_NEG_DISP_CONV: shape"
  | _ -> failwith "TISA_NEG_DISP_CONV";;

let TISA_NEG_DISP_TAC =
  CONV_TAC(TOP_DEPTH_CONV TISA_NEG_DISP_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV TISA_NEG_DISP_CONV));;

(* A frame word read through a write to another frame word (two constant
   offsets from fr, the frame not wrapping): the read before the write. *)
let TISA_WORD_SUB_FRAME = WORD_RULE
 `(!x y z:int64. word_sub (word_add x y) (word_add x z) = word_sub y z) /\
  (!x z:int64. word_sub x (word_add x z) = word_neg z) /\
  (!x y:int64. word_sub (word_add x y) x = y)`;;

let tisa_frame_addr t = match t with
  | Var("fr",_) -> true
  | Comb(Comb(Const("word_add",_),Var("fr",_)),Comb(Const("word",_),n)) -> is_numeral n
  | _ -> false;;

let TISA_FRAME_THROUGH_CONV tm =
  match tm with
  | Comb(Comb(Const("tisa_mread",_),Comb(Const("bytes",_),ak)),
         Comb(Comb(Comb(Const("write",_),Comb(Const("bytes",_),cj)),n),m)) ->
      let a,k = dest_pair ak and c,j = dest_pair cj in
      if not (tisa_frame_addr a && tisa_frame_addr c) || a = c then failwith "TISA_FRAME_THROUGH_CONV" else
      let th = ISPECL [a; k; c; j; n; m] TISA_MREAD_OUTSIDE in
      let side = (REWRITE_CONV[TISA_WORD_SUB_FRAME] THENC WORD_REDUCE_CONV THENC
                  REWRITE_CONV[VAL_WORD; DIMINDEX_64] THENC NUM_REDUCE_CONV) (lhand(concl th)) in
      MP th (EQT_ELIM side)
  | _ -> failwith "TISA_FRAME_THROUGH_CONV";;

(* FUND words in the fast copy: the budget read through the payment's write
   of the used word, and a word made from a value modulo 2^64. *)
let TISA_WRITE_SAME_SIMPS =
  [TISA_MREAD_WRITE_SAME; ARITH_RULE `8 <= 2 EXP 64 /\ 4 <= 2 EXP 64 /\ 1 <= 2 EXP 64`];;

let TISA_FAST_NORM_TAC =
  TISA_NEG_DISP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV TISA_FRAME_THROUGH_CONV) o REWRITE_RULE[TISA_WORD_VAL_MOD]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TISA_WORD_VAL_MOD] o CONV_RULE NUM_REDUCE_CONV o SIMP_RULE TISA_WRITE_SAME_SIMPS) THEN
  CONV_TAC(TOP_DEPTH_CONV TISA_FRAME_THROUGH_CONV) THEN
  SIMP_TAC TISA_WRITE_SAME_SIMPS THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[TISA_WORD_VAL_MOD];;

(* Branches of the fast copy that turn on a signed or 32-bit comparison (a
   CMP's setcc byte tested later in the body): refuted by WORD_ARITH over the
   facts about ival and 32-bit values, each setcc byte written as its
   condition and zero-extended values generalized first. *)
let TISA_IVAL_REFUTE_TAC (asl,w) =
  let wanted c = tisa_has_ival c || tisa_has_narrow c in
  let rel = filter (fun th -> let c = concl th in wanted c &&
                     not (exists (fun v -> type_of v = `:x86state`) (frees c))) (map snd asl) in
  if rel = [] then FAIL_TAC "TISA_IVAL_REFUTE_TAC: no ival facts" (asl,w) else
  (SUBGOAL_THEN `F` (fun th -> CONTR_TAC th) THEN
   MAP_EVERY MP_TAC rel THEN REWRITE_TAC[TISA_SETCC_ZX; TISA_SETCC_ZX_DECIDED] THEN
   CONV_TAC WORD_REDUCE_CONV THEN TISA_GEN_ZX_TAC THEN CONV_TAC WORD_ARITH) (asl,w);;

let TISA_FAST_CLOSE_TAC =
  TRY(REWRITE_TAC[MULT_CLAUSES; WORD_SHL_WORD; GSYM WORD_MUL; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(TOP_DEPTH_CONV TISA_MULT_NUMERAL_LEFT_CONV) THEN NO_TAC) THEN
  TISA_FAST_NORM_TAC THEN
  TRY(REWRITE_TAC[MULT_CLAUSES; WORD_SHL_WORD; GSYM WORD_MUL; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(TOP_DEPTH_CONV TISA_MULT_NUMERAL_LEFT_CONV) THEN NO_TAC) THEN
  TRY TISA_REFUTE_TAC THEN TRY TISA_IVAL_REFUTE_TAC THEN
  (* the path that runs: the frame words, then each conjunct by itself *)
  TRY(TISA_FRAME_EQS_TAC THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      (REFL_TAC ORELSE FIRST_ASSUM ACCEPT_TAC ORELSE TISA_ARITH_GOAL_TAC) THEN NO_TAC);;

(* Stores in the fast copy. A store's base register may be written earlier in
   the same body (by the ADDR's lea), so its address is read from the x86 state
   at the store, and shown apart from the code from the region's bounds (the
   range facts), as the template store does from its checks. *)
let tisa_vreg_regs = [`RDI`; `RSI`; `RDX`; `RCX`; `R8`; `R9`; `R10`; `R11`; `RAX`; `RBX`; `R12`; `R13`];;

(* The last store bounds goal that the arithmetic did not prove. *)
let tisa_store_safe_failed = ref (([],`T`) : goal);;

let TISA_STORE_BOUNDS_TAC (asl,w) =
  try (TISA_NEG_DISP_TAC THEN TISA_ARITH_GOAL_TAC) (asl,w)
  with Failure m -> (tisa_store_safe_failed := (asl,w); failwith ("store bounds: " ^ m));;

let TISA_FAST_STORE_SAFE_TAC r p off w mclen (asl,g) =
  let s = rand g in
  let rd = list_mk_icomb "read" [el p tisa_vreg_regs; s] in
  let base = try rhs(concl(snd(find (fun (_,th) -> let c = concl th in is_eq c && lhs c = rd) asl)))
             with Failure _ -> failwith "TISA_FAST_STORE_SAFE_TAC: the base register's value is unknown" in
  let addr = if off = 0 then base
             else mk_comb(mk_comb(`word_add:int64->int64->int64`,base), tisa_offset_word off) in
  let b = mk_var("B"^string_of_int r, `:int64`) and l = mk_var("L"^string_of_int r, `:int64`) in
  let goal = list_mk_icomb "nonoverlapping"
               [mk_pair(addr, mk_small_numeral w); mk_pair(`word pc:int64`, mk_small_numeral mclen)] in
  (SUBGOAL_THEN goal ASSUME_TAC THENL
    [MATCH_MP_TAC (ISPECL [b; mk_comb(`val:int64->num`,l)] TISA_NONOVERLAP_INSIDE) THEN
     CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; TISA_STORE_BOUNDS_TAC];
     ALL_TAC]) (asl,g);;

(* Run the fast copy from store to store; stores: (instruction offset,
   (region, base vreg, offset, width)) in code order. *)
let rec TISA_FAST_RUN_TAC execth pcv stores ends mclen n =
  match stores with
  | [] -> TISA_RUN_TAC execth pcv ends n
  | (at,(r,p,off,w))::rest ->
      TISA_RUN_TAC execth pcv (at :: ends) n THEN
      W(fun (asl,g) ->
          let s = rand g in
          match (try Some(snd(find (tisa_rip_fact s o snd) asl)) with Failure _ -> None) with
          | Some rip when tisa_rip_offset pcv (rhs(concl rip)) = Some at ->
              TISA_FAST_STORE_SAFE_TAC r p off w mclen THEN
              TISA_FAST_RUN_TAC execth pcv rest ends mclen (n + 100)
          | _ -> ALL_TAC);;

(* The statement at a path below a node (TSeq 0/1, TIf 1/2, a loop's body 0). *)
let rec tisa_stmt_at node rel =
  if rel = "" then node else
  let k, rest = match String.index_opt rel '.' with
    | Some i -> int_of_string (String.sub rel 0 i), String.sub rel (i+1) (String.length rel - i - 1)
    | None -> int_of_string rel, "" in
  let c, args = strip_comb node in
  let child = match fst(dest_const c), k with
    | "TSeq", 0 -> el 0 args | "TSeq", 1 -> el 1 args
    | "TIf", 1 -> el 1 args | "TIf", 2 -> el 2 args
    | ("TCountLoop" | "TEarlyLoop"), 0 -> last args
    | _ -> failwith ("tisa_stmt_at: no child " ^ string_of_int k) in
  tisa_stmt_at child rest;;

(* The fast copy's stores of the loop at path (node the loop statement). *)
let tisa_fast_stores ctx path node =
  let pre = "F" ^ path ^ "." in
  let n = String.length pre in
  let found = Hashtbl.fold (fun p (off,len,tm) acc ->
      (* STORE-H: the store without its check; STORE: a store the hoisting did
         not cover, whose passed check is among the facts at the store *)
      if (tm = "STORE-H" || tm = "STORE") && String.length p > n && String.sub p 0 n = pre then
        let st = tisa_stmt_at node (String.sub p n (String.length p - n)) in
        let _,[w;r;bp;disp;_] = strip_comb (rand st) in
        (tisa_last_instr ctx.execth off len, (tisa_num r, tisa_num bp, tisa_int disp, tisa_num w)) :: acc
      else acc) ctx.spans [] in
  sort (fun (a,_) (b,_) -> a < b) found;;

(* The last fast body attempted: its goal and its stages, to step through
   when one stalls. *)
let tisa_fast_parts = ref (`T`, ([] : (string * tactic) list));;

let tisa_fast_body_tac name g parts =
  tisa_fast_parts := (g, parts);
  itlist (fun (_,t) acc -> t THEN acc) parts ALL_TAC;;

(* time_prove with the refuter splitting val (word n) by cases. *)
let tisa_prove_with_word_cases name g tac =
  tisa_val_word_cases := true;
  try let th = time_prove name g tac in tisa_val_word_cases := false; th
  with e -> (tisa_val_word_cases := false; raise e);;

(* val (word j) = j, from j < nv and an assumption val v = nv. *)
let TISA_INDEX_VAL_TAC jv nvv (asl,w) =
  let (_,th) = find (fun (_,th) -> let c = concl th in
                       is_eq c && rhs c = nvv &&
                       (match lhs c with Comb(Const("val",_),_) -> true | _ -> false)) asl in
  let x = rand(lhs(concl th)) in
  (SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`, mk_comb(`word:num->int64`, jv)), jv)) ASSUME_TAC THENL
    [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
     MP_TAC(ISPEC x VAL_BOUND_64) THEN MP_TAC th THEN
     UNDISCH_TAC (mk_binary "<" (jv, nvv)) THEN ARITH_TAC;
     ALL_TAC]) (asl,w);;

let tisa_prove_hoisted_count_loop_unguarded ctx node path f cursor =
  let mc = ctx.mc and epi = ctx.epi in
  let _,[x;n;cap;body] = strip_comb node in
  let xi = tisa_num x and ni = tisa_num n in
  let spans = tisa_span ctx path in
  let find_span name = match filter (fun (_,_,tm) -> tm = name) spans with
    | [s] -> s | _ -> failwith ("hoisted loop: no single " ^ name ^ " at " ^ path) in
  let (oe0,_,_) = find_span "LOOP-ENTRY" and (ot,lt,_) = find_span "HOIST-TEST"
  and (ofl,_,_) = find_span "FAST-LATCH" and (oh,lh,_) = find_span "LOOP-HEAD"
  and (ol,ll,_) = find_span "LOOP-LATCH" in
  let ofast = ot + lt and ob = oh + lh and oend = ol + ll in
  if oe0 <> cursor then failwith ("loop entry not at the cursor at " ^ path);
  let ranges, fund = (try assoc path !tisa_loop_ranges
                      with Failure _ -> failwith ("no hoisting record for the loop at " ^ path)) in
  let depth = length !tisa_extra_facts in
  let jn = "j" ^ string_of_int depth and nvn = "nv" ^ string_of_int depth in
  let jv = mk_var(jn, `:num`) and nvv = mk_var(nvn, `:num`) in
  let inv = tisa_loop_invariant node f in
  let saved = !tisa_extra_facts in
  let nfact = Printf.sprintf "val(tregs t %d) = %s" ni nvn in
  let xfact j = Printf.sprintf "tregs t %d = word %s" xi j in
  let hfacts = tisa_hoist_facts nvn ranges in
  (* FUND: the test gives F * nv <= allowance at entry; each iteration then
     starts with F * (nv - j) left and ends with F * (nv - (j + 1)). *)
  let allowance = "val(word_sub (tisa_fword t 20) (tisa_fword t 21))" in
  let hfund = if fund = 0 then [] else [Printf.sprintf "%d * %s <= %s" fund nvn allowance] in
  let ffacts j = if fund = 0 then [] else [Printf.sprintf "%d * (%s - %s) <= %s" fund nvn j allowance] in
  (* after the entry, the bound is at most the cap: the entry test's
     arithmetic needs it (n - 1 scaled does not wrap) *)
  let capfact = Printf.sprintf "%s <= %s" nvn (string_of_term cap) in
  tisa_extra_facts := saved @ [nfact];
  let p_nv = tisa_facts_text ctx.nregions f in
  tisa_extra_facts := saved @ [xfact "0"; nfact; capfact];
  let p_0 = tisa_facts_text ctx.nregions inv in
  tisa_extra_facts := saved @ [xfact jn; nfact; capfact];
  let pj = tisa_facts_text ctx.nregions inv in
  (* the template copy's body, as in any count loop *)
  let thb,sb,eb,fb = tisa_prove_stmt ctx body (tisa_child path 0) inv ob in
  let qb = tisa_facts_text ctx.nregions fb in
  tisa_extra_facts := saved;
  let p_entry = tisa_facts_text ctx.nregions f and r_exit = tisa_facts_text ctx.nregions inv in
  if sb <> ob || eb <> ol then failwith ("loop body not between head and latch at " ^ path);
  let thb = if qb = pj then thb else MATCH_MP TISA_RUNS_WEAKEN (CONJ (tisa_imp_facts qb pj) thb) in
  let pcv = `pc:num` and frame = tisa_frame_tm () in
  (* the template iterations from x = 0 *)
  let hth = time_prove (path ^ " head") (tisa_head_goal mc oh xi ni ob oend) (TISA_HEAD_TAC ctx.execth [ob; oend]) in
  let lth = time_prove (path ^ " latch") (tisa_latch_goal mc ol xi oh) (TISA_LATCH_TAC ctx.execth [oh]) in
  let lem = BETA_RULE (ISPECL [parse_term mc; pcv; mk_small_numeral oh; mk_small_numeral ob; mk_small_numeral ol;
                               mk_small_numeral oend; mk_small_numeral epi; x; n; tisa_facts_fun jn pj; body;
                               frame; nvv] TISA_COUNT_ITER_RUNSF) in
  let ants = conjuncts(lhand(concl lem)) in
  let idx = tisa_side_prove (path ^ " index") (el 1 ants, REPEAT GEN_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC) in
  let pres = tisa_side_prove (path ^ " preserve") (el 2 ants, TISA_PRESERVE_TAC) in
  let bodyth = GEN jv (DISCH (mk_binary "<" (jv, nvv)) thb) in
  let ith = MP lem (end_itlist CONJ [TISA_FRAME_IDEMPOT; idx; pres; hth; lth;
                                     CONV_RULE (ONCE_DEPTH_CONV (ALPHA_CONV `j:num`)) bodyth]) in
  let ith = MP (SPECL [nvv; `0`] ith) (ARITH_RULE (mk_eq(mk_binary "+" (`0`, nvv), nvv))) in
  let ith = BETA_RULE (INST [`0`, jv] ith) in
  (* the fast copy: its body whole, under H and j < nv *)
  let pjh = tisa_facts_plus pj (hfacts @ ffacts jn) in
  let qjh = tisa_facts_plus pj (hfacts @ ffacts ("(" ^ jn ^ " + 1)")) in
  let fbg = mk_imp(mk_binary "<" (jv, nvv),
                   vsubst [body, `tisa_stmt_here:tisa_stmt`]
                     (tisa_runs_goal mc ctx.mclen ctx.decls epi "tisa_stmt_here" ofast (ofl - ofast) pjh qjh)) in
  let fbth = tisa_prove_with_word_cases (path ^ " fast body") fbg
               (tisa_fast_body_tac (path ^ " fast body") fbg
                 [("setup", DISCH_TAC THEN TISA_BODY_SETUP_TAC THEN TISA_INDEX_VAL_TAC jv nvv);
                  ("run", TISA_FAST_RUN_TAC ctx.execth pcv (tisa_fast_stores ctx path node) [ofl; epi] ctx.mclen 1);
                  ("products", CONV_TAC(TOP_DEPTH_CONV TISA_MULT_NUMERAL_LEFT_CONV) THEN
                               RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV TISA_MULT_NUMERAL_LEFT_CONV)));
                  ("leaf", TISA_RUNS_LEAF_TAC);
                  ("close", TISA_FAST_CLOSE_TAC);
                  ("finish", TISA_FAST_FINISH_TAC);
                  ("close again", TISA_FAST_CLOSE_TAC)]) in
  let fbth = GEN jv (DISCH (mk_binary "<" (jv, nvv)) (tisa_cut_global ctx (UNDISCH fbth))) in
  let flth = time_prove (path ^ " fast latch")
               (parse_term (Printf.sprintf "tisa_x86_fast_latch %s pc %d %d %d %d %d (%s)"
                              mc ofl xi ni ofast oend tisa_frame_str))
               (TISA_FAST_LATCH_TAC ctx.execth [ofast; oend]) in
  let flem = BETA_RULE (ISPECL [parse_term mc; pcv; mk_small_numeral ofast; mk_small_numeral ofl;
                                mk_small_numeral oend; mk_small_numeral epi; x; n; tisa_facts_fun jn pjh;
                                tisa_facts_fun jn qjh; body; frame; nvv] TISA_FAST_LOOP_RUNSF2) in
  let fants = conjuncts(lhand(concl flem)) in
  let fidx = tisa_side_prove (path ^ " fast index") (el 1 fants, REPEAT GEN_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC) in
  let fqidx = tisa_side_prove (path ^ " fast index after") (el 2 fants, REPEAT GEN_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC) in
  let fpres = tisa_side_prove (path ^ " fast preserve") (el 3 fants, TISA_PRESERVE_TAC) in
  let fone = tisa_side_prove (path ^ " one iteration") (el 6 fants, GEN_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC) in
  let fth = MP flem (end_itlist CONJ [TISA_FRAME_IDEMPOT; fidx; fqidx; fpres; flth;
                                      CONV_RULE (ONCE_DEPTH_CONV (ALPHA_CONV `j:num`)) fbth; fone]) in
  (* the test *)
  let hterm = parse_term (tisa_text_conj (hfacts @ hfund)) in
  let tg = mk_imp(ctx.global,
                  parse_term (Printf.sprintf "tisa_x86_hoist_test %s pc %d %d %d %s %s (%s)"
                                mc ot oh ofast p_0 ("(" ^ string_of_term hterm ^ ")") tisa_frame_str)) in
  let tth = tisa_cut_global ctx (time_prove (path ^ " hoist test") tg (TISA_HOIST_TEST_TAC ctx.execth [oh; ofast])) in
  (* the join: the fast copy's facts as P and H, its end as the template's *)
  let runsf_pre c = lhand(rator(rator c)) and runsf_post c = lhand(rator c) and runsf_fun c = lhand c in
  let p0tm = runsf_pre (concl ith) and qtm = runsf_post (concl ith) in
  let jl = BETA_RULE (ISPECL [parse_term mc; pcv; mk_small_numeral ot; mk_small_numeral oh; mk_small_numeral ofast;
                               mk_small_numeral oend; mk_small_numeral epi; p0tm; qtm; hterm;
                               runsf_fun (concl ith); frame] TISA_HOIST_JOIN) in
  let jants = conjuncts(lhand(concl jl)) in
  let fpre = runsf_pre (el 3 jants) in
  let fth' = MATCH_MP TISA_RUNSF_STRENGTHEN_PRE
               (CONJ (tisa_side_prove (path ^ " fast entry facts")
                            (mk_forall(`t:tisa_state`, mk_imp(mk_comb(fpre, `t:tisa_state`),
                                        mk_comb(runsf_pre (concl fth), `t:tisa_state`))),
                             GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN REWRITE_TAC[SUB_0] THEN TISA_FACTS_CLOSE_TAC)) fth) in
  let fth'' = MATCH_MP TISA_RUNSF_WEAKEN_POST
                (CONJ (tisa_side_prove (path ^ " fast exit facts")
                             (mk_forall(`t:tisa_state`, mk_imp(mk_comb(runsf_post (concl fth'), `t:tisa_state`),
                                         mk_comb(qtm, `t:tisa_state`))),
                              GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC)) fth') in
  let jth = MP jl (end_itlist CONJ [TISA_FRAME_IDEMPOT; tth; ith; fth'']) in
  (* the entry, then the join; the loop statement; the bound forgotten *)
  let eg = parse_term (Printf.sprintf "tisa_x86_runsf %s pc %d %d %d %s %s (\\t. tisa_loop_entry %d %d %s t) (%s)"
                         mc oe0 ot epi p_nv p_0 xi ni (string_of_term cap) tisa_frame_str) in
  let eth = time_prove (path ^ " entry") (mk_imp(ctx.global, eg))
              (REWRITE_TAC[tisa_x86_runsf; tisa_loop_entry] THEN TISA_RUNS_TAC ctx.execth [ot; epi]) in
  let eth = tisa_cut_global ctx eth in
  let cth = BETA_RULE (MATCH_MP TISA_THEN_RUNSF (CONJ TISA_FRAME_IDEMPOT (CONJ eth jth))) in
  let lth2 = MATCH_MP TISA_COUNT_LOOP_RUNS_OF
               (CONJ (tisa_side_prove (path ^ " bound")
                            (parse_term (Printf.sprintf "!t:tisa_state. %s t ==> val(tregs t %d) = %s" p_nv ni nvn),
                             GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC)) cth) in
  let pnfun = mk_abs(nvv, parse_term p_nv) and qfun = mk_abs(nvv, parse_term (
                 (tisa_extra_facts := saved @ [xfact nvn; nfact; capfact];
                  let s = tisa_facts_text ctx.nregions inv in tisa_extra_facts := saved; s))) in
  let plem = BETA_RULE (ISPECL [parse_term mc; pcv; mk_small_numeral oe0; mk_small_numeral oend;
                                mk_small_numeral epi; parse_term p_entry; pnfun; qfun; parse_term r_exit;
                                node; frame] TISA_RUNS_PARAM) in
  let pants = conjuncts(lhand(concl plem)) in
  let ex = tisa_side_prove (path ^ " exists") (el 1 pants, GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC (mk_comb(`val:int64->num`, mk_comb(mk_comb(`tregs`, `t:tisa_state`), n))) THEN TISA_FACTS_CLOSE_TAC) in
  let wk = tisa_side_prove (path ^ " weaken") (el 2 pants, REPEAT GEN_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC) in
  let th = MP plem (end_itlist CONJ [GEN nvv lth2; ex; wk]) in
  (th, oe0, oend, inv);;

let tisa_prove_hoisted_count_loop = tisa_guard_extras tisa_prove_hoisted_count_loop_unguarded;;

(* Early-exit loops: the test leaves for the end when k is 0, and the fast
   latch tests k first. *)
let TISA_HOIST_TEST_EARLY_TAC execth stops =
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[tisa_x86_hoist_test_early] THEN X_GEN_TAC `t:tisa_state` THEN BETA_TAC THEN
  REWRITE_TAC[tisa_x86_rel; tisa_fword; tisa_read; tisa_frame; tregs; tmem] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0; INT_ADD_RID] THEN
  TISA_NAME_STATE_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `v0:int64 = fr`)) THEN
  RULE_ASSUM_TAC TISA_HIDE_MREAD_RULE THEN
  REWRITE_TAC[SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  TISA_RUN_TAC execth `pc:num` stops 1 THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC (TISA_HIDE_MREAD_RULE o TISA_MEM_NORM_RULE) THEN
  CONV_TAC(TOP_DEPTH_CONV(GEN_REWRITE_CONV I [GSYM tisa_mread])) THEN
  TISA_FRAME_EQS_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV o REWRITE_RULE[TISA_VAL_WORD_MUL_CASES; WORD_AND_REFL; VAL_EQ_0]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TISA_WORD_SUB_EQ_0_VAL]) THEN
  ASM_REWRITE_TAC[] THEN
  TRY(DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(DISJ2_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TISA_ARITH_GOAL_TAC) THEN
  (* k known not 0: the end's disjunct is gone, the fast copy's is the second *)
  TRY(DISJ2_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN REPEAT CONJ_TAC THEN TISA_ARITH_GOAL_TAC);;

let TISA_EARLY_FAST_LATCH_TAC execth stops =
  REWRITE_TAC[tisa_x86_early_fast_latch; tisa_x86_rel; tisa_setreg; tregs; tmem; tisa_bool] THEN
  X_GEN_TAC `t:tisa_state` THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  TISA_NAME_STATE_TAC THEN DISCH_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN TISA_RUN_TAC execth `pc:num` stops 1 THEN
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_REFL; VAL_EQ_0]) THEN ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN TISA_ARITH_GOAL_TAC;;

let tisa_prove_hoisted_early_loop_unguarded ctx node path f cursor =
  let mc = ctx.mc and epi = ctx.epi in
  let _,[x;n;k;cap;body] = strip_comb node in
  let xi = tisa_num x and ni = tisa_num n and ki = tisa_num k in
  let spans = tisa_span ctx path in
  let find_span name = match filter (fun (_,_,tm) -> tm = name) spans with
    | [s] -> s | _ -> failwith ("hoisted loop: no single " ^ name ^ " at " ^ path) in
  let (oe0,_,_) = find_span "LOOP-ENTRY" and (ot,lt,_) = find_span "HOIST-TEST"
  and (ofl,_,_) = find_span "EARLY-FAST-LATCH" and (oh,lh,_) = find_span "EARLY-LOOP-HEAD"
  and (ol,ll,_) = find_span "EARLY-LOOP-LATCH" in
  let ofast = ot + lt and ob = oh + lh and oend = ol + ll in
  if oe0 <> cursor then failwith ("loop entry not at the cursor at " ^ path);
  let ranges, fund = (try assoc path !tisa_loop_ranges
                      with Failure _ -> failwith ("no hoisting record for the loop at " ^ path)) in
  let depth = length !tisa_extra_facts in
  let jn = "j" ^ string_of_int depth and nvn = "nv" ^ string_of_int depth in
  let jv = mk_var(jn, `:num`) and nvv = mk_var(nvn, `:num`) in
  let inv = tisa_loop_invariant node f in
  (match inv with None -> () | Some(_,bs) when mem ki bs -> () | _ -> failwith ("loop continuation not known Boolean at " ^ path));
  let saved = !tisa_extra_facts in
  let nfact = Printf.sprintf "val(tregs t %d) = %s" ni nvn in
  let xfact j = Printf.sprintf "tregs t %d = word %s" xi j in
  let hfacts = tisa_hoist_facts nvn ranges in
  (* FUND, as for counted loops: F * nv <= allowance from the test; each
     iteration starts with F * (nv - j) left and ends with F * (nv - (j + 1)) *)
  let allowance = "val(word_sub (tisa_fword t 20) (tisa_fword t 21))" in
  let hfund = if fund = 0 then [] else [Printf.sprintf "%d * %s <= %s" fund nvn allowance] in
  let ffacts j = if fund = 0 then [] else [Printf.sprintf "%d * (%s - %s) <= %s" fund nvn j allowance] in
  let capfact = Printf.sprintf "%s <= %s" nvn (string_of_term cap) in
  tisa_extra_facts := saved @ [nfact];
  let p_nv = tisa_facts_text ctx.nregions f in
  tisa_extra_facts := saved @ [xfact "0"; nfact; capfact];
  let p_0 = tisa_facts_text ctx.nregions inv in
  tisa_extra_facts := saved @ [xfact jn; nfact; capfact];
  let pj = tisa_facts_text ctx.nregions inv in
  let thb,sb,eb,fb = tisa_prove_stmt ctx body (tisa_child path 0) inv ob in
  let qb = tisa_facts_text ctx.nregions fb in
  tisa_extra_facts := saved;
  let p_entry = tisa_facts_text ctx.nregions f and r_exit = tisa_facts_text ctx.nregions inv in
  if sb <> ob || eb <> ol then failwith ("loop body not between head and latch at " ^ path);
  let thb = if qb = pj then thb else MATCH_MP TISA_RUNS_WEAKEN (CONJ (tisa_imp_facts qb pj) thb) in
  let pcv = `pc:num` and frame = tisa_frame_tm () in
  (* the template iterations from x = 0 *)
  let hth = time_prove (path ^ " early head") (tisa_early_head_goal mc oh xi ni ki ob oend)
              (TISA_EARLY_HEAD_TAC ctx.execth [ob; oend]) in
  let lth = time_prove (path ^ " early latch") (tisa_early_latch_goal mc ol xi ki oh oend)
              (TISA_EARLY_LATCH_TAC ctx.execth [oh; oend]) in
  let lem = BETA_RULE (ISPECL [parse_term mc; pcv; mk_small_numeral oh; mk_small_numeral ob; mk_small_numeral ol;
                               mk_small_numeral oend; mk_small_numeral epi; x; n; k; parse_term r_exit;
                               tisa_facts_fun jn pj; body; frame; nvv] TISA_EARLY_ITER_RUNSF) in
  let ants = conjuncts(lhand(concl lem)) in
  let idx = tisa_side_prove (path ^ " index") (el 1 ants, REPEAT GEN_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC) in
  let pres = tisa_side_prove (path ^ " preserve") (el 2 ants, TISA_PRESERVE_TAC) in
  let bodyth = GEN jv (DISCH (mk_binary "<" (jv, nvv)) thb) in
  let ith = MP lem (end_itlist CONJ [TISA_FRAME_IDEMPOT; idx; pres; hth; lth;
                                     CONV_RULE (ONCE_DEPTH_CONV (ALPHA_CONV `j:num`)) bodyth]) in
  let ith = MP (SPECL [nvv; `0`] ith) (ARITH_RULE (mk_eq(mk_binary "+" (`0`, nvv), nvv))) in
  let ith = BETA_RULE (INST [`0`, jv] ith) in
  (* the fast copy, its body whole under H and j < nv *)
  let pjh = tisa_facts_plus pj (hfacts @ ffacts jn) in
  let qjh = tisa_facts_plus pj (hfacts @ ffacts ("(" ^ jn ^ " + 1)")) in
  let fbg = mk_imp(mk_binary "<" (jv, nvv),
                   vsubst [body, `tisa_stmt_here:tisa_stmt`]
                     (tisa_runs_goal mc ctx.mclen ctx.decls epi "tisa_stmt_here" ofast (ofl - ofast) pjh qjh)) in
  let fbth = tisa_prove_with_word_cases (path ^ " fast body") fbg
               (tisa_fast_body_tac (path ^ " fast body") fbg
                 [("setup", DISCH_TAC THEN TISA_BODY_SETUP_TAC THEN TISA_INDEX_VAL_TAC jv nvv);
                  ("run", TISA_FAST_RUN_TAC ctx.execth pcv (tisa_fast_stores ctx path node) [ofl; epi] ctx.mclen 1);
                  ("products", CONV_TAC(TOP_DEPTH_CONV TISA_MULT_NUMERAL_LEFT_CONV) THEN
                               RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV TISA_MULT_NUMERAL_LEFT_CONV)));
                  ("leaf", TISA_RUNS_LEAF_TAC);
                  ("close", TISA_FAST_CLOSE_TAC);
                  ("finish", TISA_FAST_FINISH_TAC);
                  ("close again", TISA_FAST_CLOSE_TAC)]) in
  let fbth = GEN jv (DISCH (mk_binary "<" (jv, nvv)) (tisa_cut_global ctx (UNDISCH fbth))) in
  let flth = time_prove (path ^ " early fast latch")
               (parse_term (Printf.sprintf "tisa_x86_early_fast_latch %s pc %d %d %d %d %d %d (%s)"
                              mc ofl xi ni ki ofast oend tisa_frame_str))
               (TISA_EARLY_FAST_LATCH_TAC ctx.execth [ofast; oend]) in
  let flem = BETA_RULE (ISPECL [parse_term mc; pcv; mk_small_numeral ofast; mk_small_numeral ofl;
                                mk_small_numeral oend; mk_small_numeral epi; x; n; k; parse_term r_exit;
                                tisa_facts_fun jn pjh; tisa_facts_fun jn qjh; body; frame; nvv]
                              TISA_EARLY_FAST_LOOP_RUNSF2) in
  let fants = conjuncts(lhand(concl flem)) in
  let fkx = tisa_side_prove (path ^ " k apart from x") (el 1 fants, CONV_TAC NUM_REDUCE_CONV) in
  let fidx = tisa_side_prove (path ^ " fast index") (el 2 fants, REPEAT GEN_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC) in
  let fqidx = tisa_side_prove (path ^ " fast index after") (el 3 fants, REPEAT GEN_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC) in
  let fpres = tisa_side_prove (path ^ " fast preserve") (el 4 fants, TISA_PRESERVE_TAC) in
  let fone = tisa_side_prove (path ^ " one iteration") (el 7 fants, GEN_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC) in
  let fth = MP flem (end_itlist CONJ [TISA_FRAME_IDEMPOT; fkx; fidx; fqidx; fpres; flth;
                                      CONV_RULE (ONCE_DEPTH_CONV (ALPHA_CONV `j:num`)) fbth; fone]) in
  (* the test *)
  let hterm = parse_term (tisa_text_conj (hfacts @ hfund)) in
  let tg = mk_imp(ctx.global,
                  parse_term (Printf.sprintf "tisa_x86_hoist_test_early %s pc %d %d %d %d %d %s %s (%s)"
                                mc ot oh oend ofast ki p_0 ("(" ^ string_of_term hterm ^ ")") tisa_frame_str)) in
  let tth = tisa_cut_global ctx (time_prove (path ^ " hoist test") tg
              (TISA_HOIST_TEST_EARLY_TAC ctx.execth [oh; oend; ofast])) in
  (* the join *)
  let runsf_pre c = lhand(rator(rator c)) and runsf_post c = lhand(rator c) and runsf_fun c = lhand c in
  let p0tm = runsf_pre (concl ith) and qtm = runsf_post (concl ith) and ftm = runsf_fun (concl ith) in
  let jl = BETA_RULE (ISPECL [parse_term mc; pcv; mk_small_numeral ot; mk_small_numeral oh; mk_small_numeral oend;
                               mk_small_numeral ofast; mk_small_numeral epi; p0tm; qtm; hterm; k; ftm; frame]
                              TISA_HOIST_JOIN_EARLY) in
  let jants = conjuncts(lhand(concl jl)) in
  let subth = tisa_side_prove (path ^ " subsumed") (el 1 jants, SUBSUMED_ID_MAYCHANGE_TAC) in
  let k0th = tisa_side_prove (path ^ " k zero") (el 4 jants,
                   GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
                    [MATCH_MP_TAC TISA_EARLY_ITER_K0 THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]) in
  let fpre = runsf_pre (el 5 jants) in
  let fth' = MATCH_MP TISA_RUNSF_STRENGTHEN_PRE
               (CONJ (tisa_side_prove (path ^ " fast entry facts")
                            (mk_forall(`t:tisa_state`, mk_imp(mk_comb(fpre, `t:tisa_state`),
                                        mk_comb(runsf_pre (concl fth), `t:tisa_state`))),
                             GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN REWRITE_TAC[SUB_0] THEN TISA_FACTS_CLOSE_TAC)) fth) in
  let jth = MP jl (end_itlist CONJ [TISA_FRAME_IDEMPOT; subth; tth; ith; k0th; fth']) in
  (* the entry, then the join; the loop statement; the bound forgotten *)
  let eg = parse_term (Printf.sprintf "tisa_x86_runsf %s pc %d %d %d %s %s (\\t. tisa_loop_entry %d %d %s t) (%s)"
                         mc oe0 ot epi p_nv p_0 xi ni (string_of_term cap) tisa_frame_str) in
  let eth = time_prove (path ^ " entry") (mk_imp(ctx.global, eg))
              (REWRITE_TAC[tisa_x86_runsf; tisa_loop_entry] THEN TISA_RUNS_TAC ctx.execth [ot; epi]) in
  let eth = tisa_cut_global ctx eth in
  let cth = BETA_RULE (MATCH_MP TISA_THEN_RUNSF (CONJ TISA_FRAME_IDEMPOT (CONJ eth jth))) in
  let lth2 = MATCH_MP TISA_EARLY_LOOP_RUNS_OF
               (CONJ (tisa_side_prove (path ^ " bound")
                            (parse_term (Printf.sprintf "!t:tisa_state. %s t ==> val(tregs t %d) = %s" p_nv ni nvn),
                             GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN TISA_FACTS_CLOSE_TAC)) cth) in
  let pnfun = mk_abs(nvv, parse_term p_nv) and qfun = mk_abs(nvv, parse_term r_exit) in
  let plem = BETA_RULE (ISPECL [parse_term mc; pcv; mk_small_numeral oe0; mk_small_numeral oend;
                                mk_small_numeral epi; parse_term p_entry; pnfun; qfun; parse_term r_exit;
                                node; frame] TISA_RUNS_PARAM) in
  let pants = conjuncts(lhand(concl plem)) in
  let ex = tisa_side_prove (path ^ " exists") (el 1 pants, GEN_TAC THEN STRIP_TAC THEN
                   EXISTS_TAC (mk_comb(`val:int64->num`, mk_comb(mk_comb(`tregs`, `t:tisa_state`), n))) THEN
                   TISA_FACTS_CLOSE_TAC) in
  let wk = tisa_side_prove (path ^ " weaken") (el 2 pants, REPEAT GEN_TAC THEN REWRITE_TAC[]) in
  let th = MP plem (end_itlist CONJ [GEN nvv lth2; ex; wk]) in
  (th, oe0, oend, inv);;

let tisa_prove_hoisted_early_loop = tisa_guard_extras tisa_prove_hoisted_early_loop_unguarded;;

let tisa_plain_loop_hook = !tisa_loop_hook;;
let () = tisa_loop_hook := (fun ctx node path f cursor ->
  if exists (fun (_,_,tm) -> tm = "HOIST-TEST") (tisa_span ctx path) then
    (match tisa_cname node with
     | "TCountLoop" -> tisa_prove_hoisted_count_loop ctx node path f cursor
     | "TEarlyLoop" -> tisa_prove_hoisted_early_loop ctx node path f cursor
     | k -> failwith ("hoisted loop of kind " ^ k ^ " at " ^ path))
  else tisa_plain_loop_hook ctx node path f cursor);;

(* Hoisted images wait for their tisa_hoist record, which follows them. *)
let tisa_pending = ref ([] : (string * (term * string * (int * int * string * string) list)) list);;
let tisa_image_now = tisa_image;;
let tisa_image name prog hex spanlist =
  if exists (fun (_,_,tm,_) -> tm = "HOIST-TEST") spanlist
  then tisa_pending := (name, (prog, hex, spanlist)) :: !tisa_pending
  else tisa_image_now name prog hex spanlist;;
let tisa_hoist name loops =
  let prog, hex, spanlist = assoc name !tisa_pending in
  tisa_loop_ranges := map (fun (p, rs, fund) -> (p, (rs, fund))) loops;
  tisa_image_now name prog hex spanlist;;
