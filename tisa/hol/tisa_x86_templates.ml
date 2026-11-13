(* ========================================================================= *)
(* Template theorems for images emitted by tcalc/tisa/tisa_x86.c.            *)
(*                                                                           *)
(* A template theorem says that the bytes of one statement's template, at    *)
(* its offset in an image, take any native state realizing a t-ISA state t   *)
(* to the native state realizing the statement's result: the next template   *)
(* with the continued state, or the epilogue with a stopped run's memory and *)
(* its return value in rax. One tactic proves every instance: it expands the *)
(* statement's semantics, runs every native path to its end (splitting at    *)
(* conditional jumps), and settles each path's semantic tests from the path  *)
(* conditions by arithmetic.                                                  *)
(* ========================================================================= *)

needs "tisa/hol/tisa_x86_rel.ml";;
needs "tisa/hol/tisa_x86_decide.ml";;

(* ------------------------------------------------------------------------- *)
(* Unfolding a statement's result into its tests and its effects.            *)
(* ------------------------------------------------------------------------- *)

let TISA_X86_POST_COND = prove
 (`!n e b x y s. tisa_x86_post n e (if b then x else y) s =
                 if b then tisa_x86_post n e x s else tisa_x86_post n e y s`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let TISA_POST_EXPAND_TAC =
  REWRITE_TAC[tisa_exec; tisa_instr; tisa_fail; tisa_finish] THEN
  REWRITE_TAC[TISA_X86_POST_COND] THEN
  REWRITE_TAC[tisa_x86_post; tisa_x86_rel; tisa_setfword; tisa_store; tisa_setreg;
              tisa_inside; tisa_ea; tisa_addr_mid; tisa_index; tisa_base; tisa_len;
              tisa_fword; tisa_read; tisa_frame; tisa_norm; tisa_bool; tisa_rhs;
              tisa_compare; tisa_compare_at; tisa_narrow; tisa_binop; tisa_shift; tisa_shift32; tisa_shift64;
              tisa_extract; tregs; tmem] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0; INT_ADD_RID];;

let TISA_TY_DISTINCT =
  let d = CONJUNCTS(prove_constructors_distinct tisa_ty_RECURSION) in d @ map GSYM d;;

(* Name v0..v11 and the memory: s2n-bignum's overlap reasoning wants atoms. *)
let TISA_NAME_STATE_TAC =
  let t = `t:tisa_state` in
  MAP_EVERY (fun i -> ABBREV_TAC (mk_eq(mk_var("v"^string_of_int i,`:int64`),
                                        mk_comb(mk_comb(`tregs`,t),mk_small_numeral i)))) (0--11) THEN
  ABBREV_TAC (mk_eq(`m:int64->byte`, mk_comb(`tmem`,t)));;

(* Memory-function reads in one form, word(tisa_mread (bytes(a,k)) m), which
   the old-state cleanup leaves alone. *)
let TISA_MEM_NORM_RULE =
  REWRITE_RULE[TISA_MREAD_BYTES64; TISA_MREAD_BYTES32; TISA_MREAD_BYTES8;
               TISA_WRITE_BYTES64; TISA_WRITE_BYTES32; TISA_WRITE_BYTES8] o
  REWRITE_RULE[];;

let TISA_HIDE_MREAD_RULE = GEN_REWRITE_RULE (TOP_DEPTH_CONV) [GSYM tisa_mread];;

(* Effective addresses in the semantics, as the words the x86 computes. *)
let TISA_IWORD_NORM_TAC =
  REWRITE_TAC(TISA_TY_DISTINCT @ [TISA_IWORD_VAL; TISA_IWORD_VAL_ADD]) THEN
  CONV_TAC(TOP_DEPTH_CONV TISA_IWORD_VAL_NEG_CONV);;

let TISA_SETUP_TAC =
  REPEAT GEN_TAC THEN TISA_POST_EXPAND_TAC THEN
  TISA_IWORD_NORM_TAC THEN
  TISA_NAME_STATE_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC TISA_HIDE_MREAD_RULE THEN
  REWRITE_TAC[SOME_FLAGS] THEN ENSURES_INIT_TAC "s0";;

(* ------------------------------------------------------------------------- *)
(* Settling a path's end.                                                    *)
(* ------------------------------------------------------------------------- *)

let TISA_MREAD_WRITE_SAME = prove
 (`!(a:int64) k n m. k <= 2 EXP 64 ==>
     tisa_mread (bytes(a,k)) (write (bytes(a,k)) n m) = n MOD 2 EXP (8 * k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_mread] THEN
  MATCH_MP_TAC READ_WRITE_BYTES THEN ASM_REWRITE_TAC[DIMINDEX_64]);;

let list_mk_imp (l,c) = itlist (fun a b -> mk_imp(a,b)) l c;;

let tisa_is_arith_fact th =
  let c = concl th in
  not (exists (fun v -> type_of v = `:x86state`) (frees c)) &&
  not (can (find_term (fun t -> is_const t &&
         mem (fst(dest_const t)) ["nonoverlapping"; "tregs"; "tmem"; "bytes_loaded"; "MAYCHANGE"])) c) &&
  (can (find_term (fun t -> is_const t && fst(dest_const t) = "val")) c ||
   exists (fun v -> type_of v = `:num` && fst(dest_var v) <> "pc") (frees c));;

(* The facts' frame words, as equations word(tisa_mread ...) = Br. *)
let tisa_frame_eqs asl =
  filter (fun th -> let c = concl th in is_eq c && is_var(rhs c) &&
            (match lhs c with Comb(Const("word",_),Comb(Comb(Const("tisa_mread",_),_),_)) -> true
                            | _ -> false)) (map snd asl);;

(* The arithmetic facts of a goal, in one normal form. *)
let tisa_arith_facts asl =
  let eqs = tisa_frame_eqs asl in
  map (REWRITE_RULE eqs o TISA_HIDE_MREAD_RULE o TISA_MEM_NORM_RULE)
      (filter tisa_is_arith_fact (map snd asl));;

(* The facts that share 64-bit variables with the seed, transitively: the
   arithmetic splits on every conditional it is given, so it gets only these
   first. *)
(* The variables that link arithmetic facts: words and numbers (such as a
   loop's bound parameter), but not the code address pc. *)
let tisa_int64_vars tm =
  filter (fun v -> type_of v = `:int64` || (type_of v = `:num` && fst(dest_var v) <> "pc")) (frees tm);;

let tisa_relevant seed facts =
  let rec grow vs fs =
    let picked,rest = partition (fun th -> exists (fun v -> mem v vs) (tisa_int64_vars (concl th))) fs in
    if picked = [] then []
    else picked @ grow (itlist (union o tisa_int64_vars o concl) picked vs) rest in
  grow seed facts;;

(* Shifts in value arithmetic: a right shift is zero exactly when the value
   is below the shifted-out power; a left shift is exact unless it overflows. *)
let TISA_DIV_EXP_EQ_0 = prove
 (`!m k. m DIV 2 EXP k = 0 <=> m < 2 EXP k`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC DIV_EQ_0 THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ]);;

let TISA_VAL_WORD_SHL_CASES = prove
 (`!(x:int64) n. val(word_shl x n) =
      if 2 EXP n * val x < 2 EXP 64 then 2 EXP n * val x else (2 EXP n * val x) MOD 2 EXP 64`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SHL; DIMINDEX_64] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MOD_LT]);;

(* Integer comparisons of value sums (the semantics' address bounds) as
   natural-number comparisons, negative offsets moved across first. *)
let TISA_INT_NEG_LE = INT_ARITH
  `!a b c:int. (a + --c <= b <=> a <= b + c) /\ (b <= a + --c <=> b + c <= a) /\
               (a + --c < b <=> a < b + c) /\ (b < a + --c <=> b + c < a)`;;

(* A word made from a number is that number unless it wraps. *)
let TISA_VAL_WORD_CASES = prove
 (`!n. val(word n:int64) = if n < 2 EXP 64 then n else n MOD 2 EXP 64`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MOD_LT]);;

let TISA_ARITH_NORM = [VAL_WORD_SUB_CASES; VAL_WORD_ADD_CASES; DIMINDEX_64; VAL_WORD_USHR; TISA_DIV_EXP_EQ_0;
  TISA_VAL_WORD_SHL_CASES; TISA_INT_NEG_LE; INT_OF_NUM_POW; INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_LE;
  INT_OF_NUM_LT; INT_OF_NUM_EQ];;

(* Whether the refuter splits val (word n) by cases: only where words are
   made from index arithmetic (the hoisted fast copy); elsewhere the extra
   cases only cost time. *)
let tisa_val_word_cases = ref false;;

(* Whether the refuter settles conditionals from the plain facts before it
   splits (TISA_COND_DECIDE_TAC), rather than splitting on every one (false:
   the plain split, kept for comparison). *)
let tisa_decide_conds = ref true;;

(* The value of a word from a number, by cases, but not of a numeral (which
   NUM_REDUCE_CONV settles) and not of j itself where val (word j) = j is
   known: rewriting those would only add cases. *)
let TISA_VAL_WORD_CASES_CONV tm =
  match tm with
  | Comb(Const("val",_),Comb(Const("word",_),n)) when not (is_numeral n) && not (is_var n) ->
      REWR_CONV TISA_VAL_WORD_CASES tm
  | _ -> failwith "TISA_VAL_WORD_CASES_CONV";;

(* A k-byte read is below 2^(8k), so reducing it modulo a larger power of
   two leaves it unchanged (a byte loaded into a wider register). *)
let TISA_MREAD_MOD = prove
 (`!(a:int64) k m N. 2 EXP (8 * k) <= N ==> tisa_mread (bytes(a,k)) m MOD N = tisa_mread (bytes(a,k)) m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP (8 * k)` THEN
  ASM_REWRITE_TAC[tisa_mread; READ_BYTES_BOUND]);;

(* A k-byte read's bound, for the arithmetic (as VAL_BOUND_64 for a value). *)
let TISA_MREAD_BOUND = prove
 (`!(a:int64) k m. tisa_mread (bytes(a,k)) m < 2 EXP (8 * k)`,
  REWRITE_TAC[tisa_mread; READ_BYTES_BOUND]);;

let TISA_MREAD_MOD_CONV tm =
  match tm with
  | Comb(Comb(Const("MOD",_),Comb(Comb(Const("tisa_mread",_),Comb(Const("bytes",_),pr)),m)),nN)
      when is_numeral nN ->
      let a,k = dest_pair pr in
      let th = ISPECL [a; k; m; nN] TISA_MREAD_MOD in
      MP th (EQT_ELIM (NUM_REDUCE_CONV (lhand(concl th))))
  | _ -> failwith "TISA_MREAD_MOD_CONV";;

(* The value of a k-byte read seen through words at least 8k bits wide, as
   zero-extended or not: the read itself. The semantics and the x86 state a
   loaded byte through different words (val (word r) and
   val (word_zx (word_zx (word r)))); reduced, the arithmetic sees one atom. *)
let tisa_has_mread tm =
  can (find_term (fun t -> match t with
                    Comb(Comb(Const("tisa_mread",_),Comb(Const("bytes",_),_)),_) -> true | _ -> false)) tm;;

let TISA_VAL_MREAD_CONV tm =
  match tm with
  | Comb(Const("val",_),x) when tisa_has_mread x ->
      let th = (REWRITE_CONV[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64] THENC
                REWRITE_CONV[MOD_MOD_EXP_MIN] THENC NUM_REDUCE_CONV THENC
                TOP_DEPTH_CONV TISA_MREAD_MOD_CONV) tm in
      (match rhs(concl th) with
       | Comb(Comb(Const("tisa_mread",_),_),_) -> th
       | _ -> failwith "TISA_VAL_MREAD_CONV: not reduced to the read")
  | _ -> failwith "TISA_VAL_MREAD_CONV";;

let tisa_arith_prove facts goal =
  let tm = list_mk_imp (map concl facts, goal) in
  let th = prove(tm,
    CONV_TAC(TOP_DEPTH_CONV TISA_VAL_MREAD_CONV) THEN
    REWRITE_TAC TISA_ARITH_NORM THEN
    (* the normal form makes new val terms (val (word_sub x y) gives val x) *)
    CONV_TAC(TOP_DEPTH_CONV TISA_VAL_MREAD_CONV) THEN
    (if !tisa_val_word_cases then CONV_TAC(TOP_DEPTH_CONV TISA_VAL_WORD_CASES_CONV) else ALL_TAC) THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    W(fun (_,g) ->
       let atoms = setify (find_terms (fun t -> match t with
          | Comb(Const("val",_),x) ->
              not (is_comb x && (match x with
                                 | Comb(Comb(Const(("word_sub"|"word_add"),_),_),_) -> true
                                 | _ -> false))
          | _ -> false) g) in
       MAP_EVERY (fun a -> MP_TAC (ISPEC (rand a) VAL_BOUND_64)) atoms) THEN
    (* reads that TISA_VAL_MREAD_CONV took out of their words keep a bound *)
    W(fun (_,g) ->
       let reads = setify (find_terms (fun t -> match t with
          | Comb(Comb(Const("tisa_mread",_),Comb(Const("bytes",_),_)),m) -> is_var m
          | _ -> false) g) in
       MAP_EVERY (fun r -> let (a,k) = dest_pair(rand(rand(rator r))) in
                           MP_TAC (ISPECL [a; k; rand r] TISA_MREAD_BOUND)) reads) THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    (if !tisa_decide_conds then REPEAT DISCH_TAC THEN TISA_COND_DECIDE_TAC
     else REPEAT COND_CASES_TAC) THEN
    ASM_ARITH_TAC) in
  rev_itlist (fun f th -> MP th f) facts th;;

(* A path whose conditions contradict the branch of the semantics at hand:
   derive F from the arithmetic facts alone, as a separate theorem. *)
let tisa_is_linear th =
  not (can (find_term (fun t -> match t with
                         | Comb(Comb(Const(("word_sub"|"word_add"),_),_),_) -> true
                         | _ -> false)) (concl th));;

(* Linear facts first, then every relevant fact. *)
(* Relevance that does not spread through hubs: the frame base and the stack
   pointer occur in every region's placement fact, so growing through them
   brings in every region at once (and their disjunctions multiply the cases).
   The closure grows through the other variables only, and keeps the facts
   whose variables all lie in it or are hubs. *)
let tisa_hubs = [`fr:int64`; `stackpointer:int64`];;

let tisa_hub_closure seed facts =
  let nonhub vs = filter (fun v -> not (mem v tisa_hubs)) vs in
  let rec grow cs =
    let cs' = itlist (fun th acc ->
        let vs = nonhub (tisa_int64_vars (concl th)) in
        if exists (fun v -> mem v cs) vs then union vs acc else acc) facts cs in
    if length cs' = length cs then cs else grow cs' in
  let cs = grow (nonhub seed) in
  filter (fun th -> forall (fun v -> mem v cs || mem v tisa_hubs) (tisa_int64_vars (concl th))) facts;;

(* Linear relevant facts first (cheap); then the hub closure, when it is
   smaller and has few disjunctions; then every relevant fact. *)
let tisa_arith_attempts seed facts goal =
  let rel = tisa_relevant seed facts in
  try tisa_arith_prove (filter tisa_is_linear rel) goal with Failure _ ->
  let hub = tisa_hub_closure seed facts in
  let ndisj l = length (filter (fun th -> can (find_term is_disj) (concl th)) l) in
  try (if length hub < length rel && ndisj hub <= 6 then tisa_arith_prove hub goal
       else failwith "hub set not smaller")
  with Failure _ -> tisa_arith_prove rel goal;;

(* A loop's index facts name a register's value (v9 = word j0, from the loop
   prover's tregs t 9 = word j0). The simulation states the x86 flags with
   word j0 and other facts with v9 (val v9 = nv2, when an inner loop's bound
   is the outer index); substituted, the arithmetic sees one atom. *)
let TISA_SUBST_INDEX_TAC =
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let c = concl th in
    is_eq c && is_var(lhs c) && type_of(lhs c) = `:int64` &&
    (match rhs c with Comb(Const("word",_),n) -> is_var n | _ -> false))));;

let TISA_REFUTE_CORE_TAC (asl,w) =
  let facts = tisa_arith_facts asl in
  let seed = match asl with (_,th)::_ -> tisa_int64_vars (concl th) | [] -> [] in
  CONTR_TAC (tisa_arith_attempts seed facts `F`) (asl,w);;

let TISA_REFUTE_TAC = TISA_SUBST_INDEX_TAC THEN TISA_REFUTE_CORE_TAC;;

(* Inside loops the facts also name a bound: val v9 = nv0. The semantics'
   index arithmetic gets rewritten to nv0 where the x86 side keeps v9; with
   nv0 replaced by val v9 everywhere (and an index v9 by word j0), one name
   remains for each value. *)
let TISA_SUBST_LOOP_NAMES_TAC =
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    let c = concl th in
    is_eq c && is_var(rhs c) && type_of(rhs c) = `:num` &&
    (match lhs c with Comb(Const("val",_),v) -> is_var v && type_of v = `:int64` | _ -> false)))) THEN
  TISA_SUBST_INDEX_TAC;;

let TISA_BYTE_MOD = prove
 (`!x:int64. word(val x MOD 256):byte = word_zx x`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; word_zx; GSYM DIMINDEX_8; WORD_MOD_SIZE]);;

(* setcc writes a byte, then movzx widens it. *)
let TISA_SETCC_ZX = prove
 (`!(h:56 word) b.
     word_zx(word_zx(word(val(word_join h (if b then word 1 else word 0:byte):int64) MOD 256):byte):int32):int64 =
     if b then word 1 else word 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TISA_BYTE_MOD] THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN CONV_TAC WORD_BLAST);;

(* The same when the flags have already decided the byte (a register
   compared with itself). *)
let TISA_SETCC_ZX_DECIDED = prove
 (`!(h:56 word).
     word_zx(word_zx(word(val(word_join h (word 0:byte):int64) MOD 256):byte):int32):int64 = word 0 /\
     word_zx(word_zx(word(val(word_join h (word 1:byte):int64) MOD 256):byte):int32):int64 = word 1`,
  GEN_TAC THEN REWRITE_TAC[TISA_BYTE_MOD] THEN CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let TISA_WORD_VAL_MOD = prove
 (`!x:int64. word(val x MOD 18446744073709551616) = x /\ word(val x MOD 2 EXP 64) = x`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP 64`] THEN
  REWRITE_TAC[GSYM DIMINDEX_64; WORD_MOD_SIZE; WORD_VAL]);;

(* A 32- or 8-bit store writes the low bytes of the register (the model
   states them as word_zx x, or as word (n MOD 2^k)). *)
let TISA_WRITE_ZX = prove
 (`(!(a:int64) (x:int64) m. write (bytes(a,4)) (val(word_zx x:int32)) m = write (bytes(a,4)) (val x) m) /\
   (!(a:int64) (x:int64) m. write (bytes(a,1)) (val(word_zx x:byte)) m = write (bytes(a,1)) (val x) m) /\
   (!(a:int64) n m. write (bytes(a,4)) (val(word(n MOD 4294967296):int32)) m = write (bytes(a,4)) n m) /\
   (!(a:int64) n m. write (bytes(a,1)) (val(word(n MOD 256):byte)) m = write (bytes(a,1)) n m)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WRITE_BYTES_RESTRICT] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_8; ARITH_RULE `8 * 4 = 32 /\ 8 * 1 = 8`;
              ARITH_RULE `256 = 2 EXP 8 /\ 4294967296 = 2 EXP 32`; MOD_MOD_REFL]);;

let TISA_CLOSE_RW = [TISA_SETCC_ZX; TISA_SETCC_ZX_DECIDED; VAL_EQ_0; WORD_SUB_EQ_0; TISA_WORD_VAL_MOD; TISA_WRITE_ZX];;

let TISA_DECIDE_TAC =
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_LE; INT_OF_NUM_LT] THEN
  SIMP_TAC[TISA_MREAD_WRITE_SAME; ARITH_RULE `8 <= 2 EXP 64 /\ 4 <= 2 EXP 64 /\ 1 <= 2 EXP 64`] THEN
  RULE_ASSUM_TAC(CONV_RULE(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV)) THEN
  CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) THEN
  REPEAT COND_CASES_TAC THEN
  FIRST [TISA_REFUTE_TAC; ASM_REWRITE_TAC TISA_CLOSE_RW THEN NO_TAC; ASM_REWRITE_TAC TISA_CLOSE_RW];;

let TISA_LEAF_TAC =
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC (TISA_HIDE_MREAD_RULE o TISA_MEM_NORM_RULE) THEN
  CONV_TAC(TOP_DEPTH_CONV(GEN_REWRITE_CONV I [GSYM tisa_mread])) THEN
  TISA_SUBST_LOOP_NAMES_TAC THEN TISA_DECIDE_TAC;;

(* An address ADDR computes, as an integer e inside region (b,l), is the word
   iword e, and that word lies in the region. *)
let TISA_IWORD_INSIDE = prove
 (`!(e:int) (b:int64) (l:int64).
      &(val b) <= e /\ e <= &(val b + val l) /\ val b + val l < 2 EXP 64
      ==> val b <= val(iword e:int64) /\ val(iword e:int64) <= val b + val l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&(val(iword e:int64)):int = e` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_VAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_INT_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC]);;

(* A goal about val (iword e): its region is read off the assumption that
   bounds e above by &(val b + val l). *)
let TISA_IWORD_TAC (asl,w) =
  let ts = find_terms (fun t -> match t with
             Comb(Const("val",_),Comb(Const("iword",_),_)) -> true | _ -> false) w in
  if ts = [] then FAIL_TAC "TISA_IWORD_TAC: no iword" (asl,w) else
  let e = rand(rand(hd ts)) in
  let ups = find_terms (fun t -> match t with
      Comb(Comb(Const("int_le",_),x),Comb(Const("int_of_num",_),
           Comb(Comb(Const("+",_),Comb(Const("val",_),_)),Comb(Const("val",_),_)))) -> x = e
    | _ -> false) (list_mk_conj (`T` :: map (concl o snd) asl)) in
  match ups with
  | [] -> FAIL_TAC "TISA_IWORD_TAC: no bound" (asl,w)
  | u::_ ->
      let sm = rand(rand u) in
      let b = rand(lhand sm) and l = rand(rand sm) in
      (MP_TAC(SPECL [e; b; l] TISA_IWORD_INSIDE) THEN
       ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]) (asl,w);;

(* The last goal the targeted arithmetic gave up on, for inspection. *)
let tisa_arith_failed = ref (([], `T`) : goal);;

(* Arithmetic from the facts relevant to the goal, in widening rings: those
   whose atoms all occur in the goal, then those sharing an atom with it, then
   one more ring. Atoms are val terms and num variables (pc excepted). A goal
   without atoms (F, or a branch whose own facts contradict) takes its atoms
   from the newest assumptions. Arithmetic splits on every disjunction, so a
   ring with more than eight disjunctive facts is not tried. *)
let TISA_TARGET_ARITH_TAC (asl,w) =
  let atoms tm = setify (find_terms (fun t -> match t with
                           Comb(Const("val",_),_) -> true
                         | Var(n,ty) -> ty = `:num` && n <> "pc"
                         | _ -> false) tm) in
  let usable th = let c = concl th in
    not (exists (fun v -> type_of v = `:x86state`) (frees c)) &&
    not (can (find_term (fun t -> try
      let n = fst(dest_const t) in
      n = "nonoverlapping" || n = "ensures" || n = "tisa_entry_ok" || n = "tisa_keeps" || n = "tisa_apart"
      with Failure _ -> false)) c) in
  let ths = filter usable (map snd asl) in
  let ga = match atoms w with
           | [] -> itlist (union o atoms o concl o snd) (fst(chop_list (min 4 (length asl)) asl)) []
           | l -> l in
  let touches a th = exists (fun x -> mem x a) (atoms (concl th)) in
  let s1 = filter (fun th -> let a = atoms (concl th) in a <> [] && subset a ga) ths in
  let s2 = filter (touches ga) ths in
  let s3 = filter (touches (itlist (union o atoms o concl) s2 ga)) ths in
  let rings = s1 :: (if length s2 > length s1 then [s2] else []) @
              (if length s3 > length s2 then [s3] else []) in
  let ndisj l = length (filter (fun th -> can (find_term is_disj) (concl th)) l) in
  let attempt l = if ndisj l > 8 then FAIL_TAC "TISA_TARGET_ARITH_TAC: too many cases"
                  else MAP_EVERY MP_TAC l THEN ARITH_TAC in
  try FIRST (map attempt rings) (asl,w)
  with Failure s -> (tisa_arith_failed := (asl,w); failwith s);;

(* A leaf whose sides differ by conditions on values (flags against a
   comparison): split on each condition, state its word equalities as value
   equalities, and decide by arithmetic. *)
let TISA_COND_FINISH_TAC =
  REPEAT(COND_CASES_TAC THEN
         FIRST_X_ASSUM(ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV o
                       REWRITE_RULE[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64])) THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN TISA_TARGET_ARITH_TAC;;

(* Boolean operations keep words Boolean (BIN on BOOL). *)
let TISA_BOOL_WORD_OPS = prove
 (`!x y:int64. val x <= 1 /\ val y <= 1
               ==> val(word_and x y) <= 1 /\ val(word_or x y) <= 1 /\ val(word_xor x y) <= 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `n <= 1 <=> n = 0 \/ n = 1`] THEN
  REWRITE_TAC[VAL_EQ_0; MESON[VAL_WORD_1; VAL_EQ] `val (x:int64) = 1 <=> x = word 1`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

let TISA_BOOL_OPS_TAC =
  let ths = map (fun i -> GEN_ALL(DISCH_ALL(el i (CONJUNCTS(UNDISCH(SPEC_ALL TISA_BOOL_WORD_OPS))))))
                [0; 1; 2] in
  FIRST (map (fun th -> MATCH_MP_TAC th THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC) ths);;

(* A compare's leaf that the value arithmetic does not decide: signed
   compares (setl/setle read SF and OF, which the model states with ival; for
   an immediate the simulation has already evaluated ival of it) and compares
   of 32-bit values (the value arithmetic is 64-bit). Split the byte's
   condition, then decide each branch by WORD_ARITH over the facts that
   mention ival or a 32-bit value, with zero-extended values generalized to
   variables first (WORD_ARITH does not see through word_zx; the generalized
   goal is stronger). *)
let tisa_has_ival tm =
  can (find_term (fun t -> match t with Comb(Const("ival",_),_) -> true | _ -> false)) tm;;

let tisa_has_narrow tm =
  can (find_term (fun t -> match t with
                    Comb(Const("word_zx",_),_) -> type_of t = `:int32` | _ -> false)) tm;;

let TISA_GEN_ZX_TAC (asl,w) =
  let size t = length (find_terms (fun _ -> true) t) in
  let zx = setify (find_terms (fun t -> match t with Comb(Const("word_zx",_),_) -> true | _ -> false) w) in
  let zx = map snd (sort (fun (a,_) (b,_) -> a > b) (map (fun t -> (size t, t)) zx)) in
  MAP_EVERY (fun t -> SPEC_TAC(t, genvar(type_of t))) zx (asl,w);;

let TISA_FLAGS_FINISH_TAC (asl,w) =
  let wanted c = tisa_has_ival c || tisa_has_narrow c in
  if not (wanted w) then FAIL_TAC "TISA_FLAGS_FINISH_TAC: no ival or 32-bit value" (asl,w) else
  (REPEAT COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
   (fun (asl,w) ->
      let rel = filter (fun th -> let c = concl th in wanted c &&
                         not (exists (fun v -> type_of v = `:x86state`) (frees c))) (map snd asl) in
      (MAP_EVERY MP_TAC rel THEN TISA_GEN_ZX_TAC THEN CONV_TAC WORD_ARITH) (asl,w))) (asl,w);;

(* A read of at most three bytes is below 2^31, so its 32-bit word is
   non-negative and sign-extends as it zero-extends (a byte loaded into a
   TyI32S register: the x86 zero-extends it, the semantics sign-extends). *)
let TISA_MREAD_LT = prove
 (`!(a:int64) k m N. 2 EXP (8 * k) <= N ==> tisa_mread (bytes(a,k)) m < N`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP (8 * k)` THEN
  ASM_REWRITE_TAC[tisa_mread; READ_BYTES_BOUND]);;

let TISA_SX_SMALL = prove
 (`!r. r < 2147483648 ==> word_sx (word r:int32):int64 = word r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_sx; ival; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `r MOD 4294967296 = r` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[GSYM WORD_IWORD]]);;

let TISA_SX_MREAD_CONV tm =
  match tm with
  | Comb(Const("word_sx",_),(Comb(Const("word",_),
         (Comb(Comb(Const("tisa_mread",_),Comb(Const("bytes",_),pr)),m) as r)) as w))
      when type_of w = `:int32` && type_of tm = `:int64` ->
      let a,k = dest_pair pr in
      let side = mk_binop `(<=):num->num->bool`
                   (mk_binop `(EXP):num->num->num` `2` (mk_binop `( * ):num->num->num` `8` k)) `2147483648` in
      let lt = MP (ISPECL [a; k; m; `2147483648`] TISA_MREAD_LT) (EQT_ELIM (NUM_REDUCE_CONV side)) in
      MP (SPEC r TISA_SX_SMALL) lt
  | _ -> failwith "TISA_SX_MREAD_CONV";;

(* The low 32 or 8 bits of a 64-bit word made from a number: the narrower
   word made from it (a 4-byte load sign-extended from either). *)
let TISA_WORD_ZX_WORD = prove
 (`(!n. word_zx (word n:int64):int32 = word n) /\ (!n. word_zx (word n:int64):byte = word n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_64; DIMINDEX_32; DIMINDEX_8; MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* What is left at a leaf: word identities, first by value arithmetic, then
   per conjunct the addresses ADDR computes, Boolean operations, then
   bit-blasting (not for products, whose blasting is costly). *)
let TISA_WORD_FINISH_TAC =
  TRY(REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(TOP_DEPTH_CONV TISA_MREAD_MOD_CONV) THEN REWRITE_TAC[] THEN NO_TAC) THEN
  REPEAT CONJ_TAC THEN TRY(REWRITE_TAC[TISA_WORD_ZX_WORD] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[TISA_WORD_ZX_WORD] THEN CONV_TAC(TOP_DEPTH_CONV TISA_SX_MREAD_CONV) THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(TOP_DEPTH_CONV TISA_MREAD_MOD_CONV) THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[WORD_MUL_SYM] THEN NO_TAC) THEN
  (* sign-extended on both sides: equal 32-bit words suffice *)
  TRY(AP_TERM_TAC THEN REWRITE_TAC[TISA_WORD_ZX_WORD] THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(TOP_DEPTH_CONV TISA_MREAD_MOD_CONV) THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY TISA_IWORD_TAC THEN TRY TISA_BOOL_OPS_TAC THEN
  TRY(TISA_COND_FINISH_TAC THEN NO_TAC) THEN
  TRY(TISA_FLAGS_FINISH_TAC THEN NO_TAC) THEN
  TRY(W(fun (_,w) ->
        if can (find_term (fun t -> is_const t && fst(dest_const t) = "word_mul")) w then NO_TAC
        else CONV_TAC WORD_BLAST));;

let TISA_TEMPLATE_TAC execth stops =
  TISA_SETUP_TAC THEN TISA_RUN_TAC execth `pc:num` stops 1 THEN
  TISA_LEAF_TAC THEN TISA_WORD_FINISH_TAC;;

(* ------------------------------------------------------------------------- *)
(* The theorem for one template instance: statement stmt at offset off,      *)
(* length len, of image mc (mclen bytes) whose epilogue is at epi.           *)
(* ------------------------------------------------------------------------- *)

let tisa_template_goal mc mclen epi stmt off len pre =
  parse_term (Printf.sprintf
   "!pc t. nonoverlapping (tregs t 0,192) (word pc,%d)%s ==> ensures x86 (\\s. bytes_loaded s (word pc) %s /\\ read RIP s = word(pc + %d) /\\ tisa_x86_rel t s) (\\s. tisa_x86_post (pc + %d) (pc + %d) (tisa_exec %s t) s) (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RSI; R8; R9; R10; R11; R12; R13; R14; R15] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory])"
   mclen pre mc off (off + len) epi stmt);;

(* p points into region r, which does not wrap. *)
let tisa_ptr_pre r p = Printf.sprintf
  " /\\ val(tisa_base t %d) <= val(tregs t %d) /\\ val(tregs t %d) <= val(tisa_base t %d) + val(tisa_len t %d) /\\ val(tisa_base t %d) + val(tisa_len t %d) < 2 EXP 64"
  r p p r r r r;;

(* ... and region r, which a STORE writes, is apart from the code. *)
let tisa_store_pre r p mclen = tisa_ptr_pre r p ^ Printf.sprintf
  " /\\ nonoverlapping (tisa_base t %d, val(tisa_len t %d)) (word pc,%d)" r r mclen;;

(* The goal and tactic of the last proof that failed, for inspection. *)
let tisa_failed_goal = ref (`T`, ALL_TAC);;

let time_prove name g tac =
  let t0 = Sys.time() in
  let th = (try prove(g,tac) with Failure m -> (tisa_failed_goal := (g,tac); failwith (name ^ ": " ^ m))) in
  Printf.printf "PROVED %s in %.1fs\n%!" name (Sys.time() -. t0); th;;

(* A side proof: on failure, keep the goal and name the step. *)
let tisa_side_prove name (g,tac) =
  try prove(g,tac) with Failure m -> (tisa_failed_goal := (g,tac); failwith (name ^ ": " ^ m));;

(* ------------------------------------------------------------------------- *)
(* STORE: the store's bytes lie in its region, which is apart from the code. *)
(* ------------------------------------------------------------------------- *)

let TISA_NONOVERLAP_INSIDE = prove
 (`!(b:int64) l (a:int64) w (c:int64) k.
        nonoverlapping (b,l) (c,k) /\ val b <= val a /\ val a + w <= val b + l
        ==> nonoverlapping (a,w) (c,k)`,
  REWRITE_TAC[nonoverlapping] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SUBREGIONS THEN
  MAP_EVERY EXISTS_TAC [`val(b:int64)`; `l:num`; `val(c:int64)`; `k:num`] THEN
  ASM_REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL] THEN
  REWRITE_TAC[contained_modulo] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  EXISTS_TAC `val(a:int64) - val(b:int64) + i` THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(NUMBER_RULE `x = y ==> (x == y) (mod n)`) THEN ASM_ARITH_TAC);;

(* Prove an arithmetic goal from the arithmetic facts alone. *)
let TISA_ARITH_GOAL_TAC (asl,w) =
  let facts = tisa_arith_facts asl in
  let th = try tisa_arith_attempts (tisa_int64_vars w) facts w
           with Failure _ -> tisa_arith_prove facts w in
  ACCEPT_TAC th (asl,w);;



let tisa_frame_word_term i =
  if i = 0 then `word (tisa_mread (bytes (v0:int64,8)) m):int64`
  else mk_comb(`word:num->int64`,
         list_mk_icomb "tisa_mread"
           [mk_icomb(`bytes:int64#num->((int64->byte),num)component`,
                     mk_pair(mk_comb(mk_comb(`word_add:int64->int64->int64`,`v0:int64`),
                                     mk_comb(`word:num->int64`,mk_small_numeral(8 * i))),
                             `8`));
            `m:int64->byte`]);;

(* At the store instruction: its range (p + off, w) misses the code. *)
(* A displacement as the word the x86 adds: a negative one is its two's
   complement, as the decoder sign-extends it. *)
let tisa_offset_word off =
  if off >= 0 then mk_comb(`word:num->int64`, mk_small_numeral off)
  else mk_comb(`word:num->int64`,
               rhs(concl(NUM_REDUCE_CONV (mk_binop `(-):num->num->num` `2 EXP 64` (mk_small_numeral (-off))))));;

let TISA_STORE_SAFE_TAC r p off w mclen (asl,g) =
  let vp = mk_var("v"^string_of_int p,`:int64`) in
  let addr = if off = 0 then vp else mk_comb(mk_comb(`word_add:int64->int64->int64`,vp), tisa_offset_word off) in
  let b = tisa_frame_word_term (2 * r) and l = tisa_frame_word_term (2 * r + 1) in
  let code = `(word pc:int64, n:num)` in
  let goal = vsubst [mk_small_numeral mclen, `n:num`]
    (list_mk_icomb "nonoverlapping" [mk_pair(addr, mk_small_numeral w); code]) in
  (SUBGOAL_THEN goal ASSUME_TAC THENL
    [MATCH_MP_TAC (ISPECL [b; mk_comb(`val:int64->num`,l)] TISA_NONOVERLAP_INSIDE) THEN
     CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; TISA_ARITH_GOAL_TAC];
     ALL_TAC]) (asl,g);;

let tisa_last_instr execth off len =
  let arr = snd execth in
  let ks = filter (fun k -> match arr.(k) with Some _ -> true | None -> false) (off--(off+len-1)) in
  last ks;;

let TISA_STORE_TEMPLATE_TAC execth (off,len) epi (r,p,disp,w) mclen =
  let at = tisa_last_instr execth off len in
  TISA_SETUP_TAC THEN
  TISA_RUN_TAC execth `pc:num` [at; off + len; epi] 1 THEN
  W(fun (asl,g) ->
      let s = rand g in
      let rip = snd(find (tisa_rip_fact s o snd) asl) in
      if tisa_rip_offset `pc:num` (rhs(concl rip)) = Some at
      then TISA_STORE_SAFE_TAC r p disp w mclen THEN
           TISA_RUN_TAC execth `pc:num` [off + len; epi] 100
      else ALL_TAC) THEN
  TISA_LEAF_TAC THEN TISA_WORD_FINISH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Template theorems with the facts of their program points.                 *)
(* ------------------------------------------------------------------------- *)

needs "tisa/hol/tisa_x86_compose.ml";;

let TISA_X86_POSTF_COND = prove
 (`!n e Q b x y s. tisa_x86_postf n e Q (if b then x else y) s =
                   if b then tisa_x86_postf n e Q x s else tisa_x86_postf n e Q y s`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* Everything a statement's code may change, flags spelled out. *)
let tisa_frame_str =
  "MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RSI; R8; R9; R10; R11; R12; R13; R14; R15] ,, MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory]";;

let TISA_FRAME_IDEMPOT = prove
 (parse_term ("(" ^ tisa_frame_str ^ ") ,, (" ^ tisa_frame_str ^ ") = " ^ tisa_frame_str),
  MAYCHANGE_IDEMPOT_TAC);;

let TISA_FRAME_REFL = prove
 (parse_term ("!s:x86state. (" ^ tisa_frame_str ^ ") s s"),
  GEN_TAC THEN ASSUME_TAC(ISPEC `s:x86state` MAYCHANGE_STARTER) THEN
  MONOTONE_MAYCHANGE_TAC);;

(* Facts of a program point: the frame at F, region r's words Br and Lr,
   pointer registers inside their regions, Boolean registers. *)
let tisa_facts_str nregions ptrs bools =
  let regs = String.concat "" (map (fun r ->
      Printf.sprintf " /\\ tisa_fword t %d = B%d /\\ tisa_fword t %d = L%d" (2*r) r (2*r+1) r) (0--(nregions-1))) in
  let ps = String.concat "" (map (fun (p,r) ->
      Printf.sprintf " /\\ val B%d <= val(tregs t %d) /\\ val(tregs t %d) <= val B%d + val L%d" r p p r r) ptrs) in
  let bs = String.concat "" (map (fun b -> Printf.sprintf " /\\ tisa_bool (tregs t %d)" b) bools) in
  "(\\t:tisa_state. tregs t 0 = fr" ^ regs ^ ps ^ bs ^ ")";;

let tisa_nofacts_str = "(\\t:tisa_state. F)";;

(* What holds of the whole run: the code apart from the frame and from every
   writable region, the frame apart from those regions, nothing wraps. *)
(* What the images assume of their surroundings: the frame does not wrap and
   lies apart from the code; accessible regions do not wrap; read-write
   regions lie apart from the code, and, when not empty, from the frame
   (entry validation requires the last two of the program's state). *)
let tisa_global_str mclen decls =
  let rs = String.concat "" (List.mapi (fun r mode ->
      (if mode <> 0 then Printf.sprintf " /\\ val (B%d:int64) + val (L%d:int64) < 2 EXP 64" r r else "") ^
      (if mode = 2 then Printf.sprintf
         " /\\ nonoverlapping (B%d:int64, val (L%d:int64)) (word pc,%d) /\\ (val L%d = 0 \\/ val B%d + val L%d <= val fr \\/ val fr + 192 <= val B%d)"
         r r mclen r r r r else "")) decls) in
  Printf.sprintf "nonoverlapping (fr:int64,192) (word pc,%d) /\\ val fr + 192 <= 2 EXP 64" mclen ^ rs;;

let tisa_runs_goal mc mclen decls epi stmt off len pfacts qfacts =
  parse_term (Printf.sprintf "%s ==> tisa_x86_runs %s pc %d %d %d %s %s %s (%s)"
    (tisa_global_str mclen decls) mc off (off + len) epi pfacts qfacts stmt tisa_frame_str);;

let TISA_MREAD_OUTSIDE = prove
 (`!(a:int64) k c j n m.
        j <= val(word_sub a c) /\ val(word_sub a c) + k <= 2 EXP 64
        ==> tisa_mread (bytes(a,k)) (write (bytes(c,j)) n m) = tisa_mread (bytes(a,k)) m`,
  REWRITE_TAC[tisa_mread] THEN MESON_TAC[TISA_READ_OUTSIDE_WRITE]);;

(* A read of the frame through a store elsewhere: settle it if the store is
   outside the read, by arithmetic. *)
let rec TISA_MREAD_THROUGH_TAC (asl,w) =
  let is_through t = match t with
    | Comb(Comb(Const("tisa_mread",_),Comb(Const("bytes",_),_)),
           Comb(Comb(Comb(Const("write",_),Comb(Const("bytes",_),_)),_),_)) -> true
    | _ -> false in
  match find_terms is_through w with
  | [] -> ALL_TAC (asl,w)
  | tm::_ ->
      let a,k = dest_pair(rand(rand(rator tm))) in
      let wr = rand tm in
      let c,j = dest_pair(rand(rand(rator(rator wr)))) in
      if a = c && k = j then failwith "same range" else
      let cond = list_mk_conj
        [mk_binop `(<=):num->num->bool` j (mk_comb(`val:int64->num`,
           mk_comb(mk_comb(`word_sub:int64->int64->int64`,a),c)));
         mk_binop `(<=):num->num->bool`
           (mk_binop `(+):num->num->num` (mk_comb(`val:int64->num`,
              mk_comb(mk_comb(`word_sub:int64->int64->int64`,a),c))) k) `2 EXP 64`] in
      (SUBGOAL_THEN cond ASSUME_TAC THENL
        [TISA_ARITH_GOAL_TAC;
         ASM_SIMP_TAC[TISA_MREAD_OUTSIDE] THEN TISA_MREAD_THROUGH_TAC]) (asl,w);;

(* The facts' frame words, as equations word(tisa_mread ...) = Br, rewrite
   everything else. *)
let TISA_FRAME_EQS_TAC (asl,w) =
  let eqs = tisa_frame_eqs asl in
  (RULE_ASSUM_TAC(fun th -> if mem th eqs then th else REWRITE_RULE eqs th) THEN
   REWRITE_TAC eqs) (asl,w);;

let TISA_RUNS_SETUP_TAC =
  REWRITE_TAC[tisa_x86_runs] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  X_GEN_TAC `t:tisa_state` THEN BETA_TAC THEN
  REWRITE_TAC[tisa_exec; tisa_instr; tisa_fund; tisa_fail; tisa_finish] THEN
  REWRITE_TAC[TISA_X86_POSTF_COND] THEN
  REWRITE_TAC[tisa_x86_postf] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[tisa_x86_rel; tisa_setfword; tisa_store; tisa_setreg;
              tisa_inside; tisa_ea; tisa_addr_mid; tisa_index; tisa_base; tisa_len;
              tisa_fword; tisa_read; tisa_frame; tisa_norm; tisa_bool; tisa_rhs;
              tisa_compare; tisa_compare_at; tisa_narrow; tisa_binop; tisa_shift; tisa_shift32;
              tisa_shift64; tisa_extract; tregs; tmem] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0; INT_ADD_RID] THEN
  TISA_IWORD_NORM_TAC THEN
  TISA_NAME_STATE_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `v0:int64 = fr`)) THEN
  RULE_ASSUM_TAC TISA_HIDE_MREAD_RULE THEN
  REWRITE_TAC[SOME_FLAGS] THEN ENSURES_INIT_TAC "s0";;

(* A path's end: decide the semantics' tests first (refuting the branches
   the path contradicts), then settle frame reads through stores with the
   branch's own facts. *)
let TISA_RUNS_LEAF_TAC =
  ENSURES_FINAL_STATE_TAC THEN
  RULE_ASSUM_TAC (TISA_HIDE_MREAD_RULE o TISA_MEM_NORM_RULE) THEN
  CONV_TAC(TOP_DEPTH_CONV(GEN_REWRITE_CONV I [GSYM tisa_mread])) THEN
  TISA_SUBST_LOOP_NAMES_TAC THEN
  TISA_FRAME_EQS_TAC THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_LE; INT_OF_NUM_LT] THEN
  SIMP_TAC[TISA_MREAD_WRITE_SAME; ARITH_RULE `8 <= 2 EXP 64 /\ 4 <= 2 EXP 64 /\ 1 <= 2 EXP 64`] THEN
  RULE_ASSUM_TAC(CONV_RULE(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV)) THEN
  CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) THEN
  REPEAT COND_CASES_TAC THEN
  FIRST [TISA_REFUTE_TAC;
         TRY TISA_MREAD_THROUGH_TAC THEN TISA_FRAME_EQS_TAC THEN
         ASM_REWRITE_TAC TISA_CLOSE_RW];;

let TISA_RUNS_TAC execth stops =
  TISA_RUNS_SETUP_TAC THEN TISA_RUN_TAC execth `pc:num` stops 1 THEN
  TISA_RUNS_LEAF_TAC THEN TISA_WORD_FINISH_TAC;;

(* STORE with the facts: the store's range lies in region r, whose bounds the
   facts name Br and Lr, and which is apart from the code. *)
let TISA_RUNS_STORE_SAFE_TAC r p off w mclen (asl,g) =
  let vp = mk_var("v"^string_of_int p,`:int64`) in
  let addr = if off = 0 then vp else mk_comb(mk_comb(`word_add:int64->int64->int64`,vp), tisa_offset_word off) in
  let b = mk_var("B"^string_of_int r,`:int64`) and l = mk_var("L"^string_of_int r,`:int64`) in
  let goal = list_mk_icomb "nonoverlapping"
               [mk_pair(addr, mk_small_numeral w); mk_pair(`word pc:int64`, mk_small_numeral mclen)] in
  (SUBGOAL_THEN goal ASSUME_TAC THENL
    [MATCH_MP_TAC (ISPECL [b; mk_comb(`val:int64->num`,l)] TISA_NONOVERLAP_INSIDE) THEN
     CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; TISA_ARITH_GOAL_TAC];
     ALL_TAC]) (asl,g);;

let TISA_RUNS_STORE_TAC execth (off,len) epi (r,p,disp,w) mclen =
  let at = tisa_last_instr execth off len in
  TISA_RUNS_SETUP_TAC THEN
  TISA_RUN_TAC execth `pc:num` [at; off + len; epi] 1 THEN
  W(fun (asl,g) ->
      let s = rand g in
      let rip = snd(find (tisa_rip_fact s o snd) asl) in
      if tisa_rip_offset `pc:num` (rhs(concl rip)) = Some at
      then TISA_RUNS_STORE_SAFE_TAC r p disp w mclen THEN
           TISA_RUN_TAC execth `pc:num` [off + len; epi] 100
      else ALL_TAC) THEN
  TISA_RUNS_LEAF_TAC THEN TISA_WORD_FINISH_TAC;;
