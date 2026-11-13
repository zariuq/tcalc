(* ========================================================================= *)
(* Weakest preconditions for t-ISA p1 statements, and a forward generator    *)
(* that runs a statement symbolically on an entry state, splitting only the  *)
(* conditions the assumptions do not decide.                                 *)
(*                                                                           *)
(* tisa_wp S Q R st: every run of S from st that continues ends in Q, and   *)
(* every run that stops with outcome k ends in R k. A specification is a   *)
(* weakest-precondition statement for every state satisfying P.            *)
(*                                                                           *)
(* The generator's state normal form (revised 2026-11-12 for intern16's     *)
(* completeness proof; the laws above the generator are unchanged):          *)
(*  - addresses: a computed address iword(base + index * 2^s + off) and an   *)
(*    effective address iword(val p + off) become word_add base (word k),    *)
(*    nested offsets combined; val (word_ushr x n) becomes val x DIV 2^n.    *)
(*  - memory: frame words, region bases and lengths and region checks read   *)
(*    through a store that lies outside the frame; an 8-byte read through   *)
(*    an 8-byte store gives the stored value when the two addresses have    *)
(*    one value and the older read when the ranges lie apart; frame words   *)
(*    and reads away from the frame pass through the finish (tisa_finst).   *)
(*  - decisions: a condition is stripped of its negation, then proved,      *)
(*    refuted, or split on; arithmetic conditions are decided over the      *)
(*    assumptions and, failing that, with facts about the values of the     *)
(*    word operations in them (word_and bounds, exact add, sub, shl and     *)
(*    word n when nothing wraps, each side condition proved first, inner     *)
(*    terms before outer ones). Conditions that are not arithmetic skip the *)
(*    arithmetic.                                                           *)
(*  - BOOL operations (revised 2026-11-12 for the reader's leb128): AND, OR *)
(*    and XOR of two comparison results are the comparison result of their  *)
(*    conjunction, disjunction and difference (TISA_COND01_AND, _OR, _XOR), *)
(*    so a BOOL operation's check passes and an IF on its result splits on  *)
(*    the combined condition. Without them the generator could not decide   *)
(*    tisa_bool of such a result and left a failure leaf for it.            *)
(*  - byte-range writes and reads of any width (revised 2026-11-12 for      *)
(*    intern_name's copy of a name into its arena): tisa_bwrite a n x st    *)
(*    writes the n bytes of the number x at a, as a copy loop leaves memory *)
(*    (the n bytes of a source range, read as one number). Frame words,     *)
(*    region bases and lengths and region checks read through such a write *)
(*    outside the frame (TISA_BWRITE_FRAME_TAC); a read of any width        *)
(*    through a store of any width or through such a write gives the older *)
(*    read when the two ranges lie apart (TISA_APART_READ_TAC); a read of   *)
(*    any width other than 8 passes through the finish when it lies apart   *)
(*    from the status and return words (TISA_FINST_READ_W_TAC). Reads       *)
(*    inside a byte-range write are left to the proof that knows the bytes *)
(*    (TISA_READ_BWRITE_BYTE, LIMB_READ_BYTES).                             *)
(*  - focused arithmetic (revised 2026-11-12 for intern_name's five         *)
(*    regions): entry validation gives one disjunction per pair of regions  *)
(*    and per region against the frame, fifteen for five regions, and the   *)
(*    arithmetic's case split over all that bear on a goal grows as 2^15.   *)
(*    With tisa_arith_focus set, the decisions (TISA_ARITH_DECIDE_TAC and   *)
(*    the side conditions of the value facts) use the facts without         *)
(*    disjunctions, then those with one disjunctive fact that bears on the  *)
(*    goal, each in turn: a separation is one disjunction; facts that are  *)
(*    not comparisons of numbers stay out; value facts are added for the   *)
(*    word operations under val in the arithmetic assumptions as well as in *)
(*    the goal (TISA_VAL_FACTS_ALL_TAC). The default                        *)
(*    (unset) keeps the earlier selection, TISA_ARITH_TAC's.                *)
(*  - frame words fold to the bases and lengths of all nine regions, not of *)
(*    regions 0..3 only (TISA_FRAME_FOLDS; revised 2026-11-12).             *)
(* ========================================================================= *)

needs "native/hol/tisa_symex.ml";;

let tisa_rwp = new_definition
 `tisa_rwp (r:tisa_result) (Q:tisa_state->bool) (R:num->tisa_state->bool) <=>
    (!s. r = TCont s ==> Q s) /\ (!k s. r = TStop k s ==> R k s)`;;

let tisa_wp = new_definition
 `tisa_wp S (Q:tisa_state->bool) (R:num->tisa_state->bool) st <=>
    tisa_rwp (tisa_exec S st) Q R`;;

let TISA_SPEC_WP = prove
 (`!P S Q R. tisa_spec P S Q R <=> !st. P st ==> tisa_wp S Q R st`,
  REWRITE_TAC[tisa_spec; tisa_wp; tisa_rwp]);;

(* ------------------------------------------------------------------------- *)
(* Results.                                                                  *)
(* ------------------------------------------------------------------------- *)

let TISA_RWP_CONT = prove
 (`!s Q R. tisa_rwp (TCont s) Q R <=> Q s`,
  REWRITE_TAC[tisa_rwp; TISA_RESULT_DISTINCT; TISA_RESULT_INJ] THEN MESON_TAC[]);;

let TISA_RWP_STOP = prove
 (`!k s Q R. tisa_rwp (TStop k s) Q R <=> R k s`,
  REWRITE_TAC[tisa_rwp; TISA_RESULT_DISTINCT; TISA_RESULT_INJ] THEN MESON_TAC[]);;

let TISA_RWP_COND = prove
 (`!b r1 r2 Q R. tisa_rwp (if b then r1 else r2) Q R <=>
                 if b then tisa_rwp r1 Q R else tisa_rwp r2 Q R`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let TISA_RWP_THEN = prove
 (`!r f Q R. tisa_rwp (tisa_then r f) Q R <=> tisa_rwp r (\s. tisa_rwp (f s) Q R) R`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `r:tisa_result` TISA_RESULT_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[tisa_then; TISA_RWP_CONT; TISA_RWP_STOP]);;

let TISA_RWP_MONO = prove
 (`!r Q R Q' R'. (!s. Q s ==> Q' s) /\ (!k s. R k s ==> R' k s) /\ tisa_rwp r Q R
                 ==> tisa_rwp r Q' R'`,
  REWRITE_TAC[tisa_rwp] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Statements.                                                               *)
(* ------------------------------------------------------------------------- *)

let TISA_WP_SKIP = prove
 (`!Q R st. tisa_wp TSkip Q R st <=> Q st`,
  REWRITE_TAC[tisa_wp; tisa_exec; TISA_RWP_CONT]);;

let TISA_WP_SEQ = prove
 (`!a b Q R st. tisa_wp (TSeq a b) Q R st <=> tisa_wp a (\s. tisa_wp b Q R s) R st`,
  REWRITE_TAC[tisa_wp; tisa_exec; TISA_RWP_THEN]);;

let TISA_WP_INSTR = prove
 (`!i Q R st. tisa_wp (TInstr i) Q R st <=> tisa_rwp (tisa_instr i st) Q R`,
  REWRITE_TAC[tisa_wp; tisa_exec]);;

let TISA_WP_IF = prove
 (`!c a b Q R st.
     tisa_wp (TIf c a b) Q R st <=>
     if ~tisa_bool (tregs st c) then R 3 (tisa_failst 3 st)
     else if tregs st c = word 0 then tisa_wp b Q R st else tisa_wp a Q R st`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_wp; tisa_exec] THEN
  ASM_CASES_TAC `tisa_bool (tregs st c)` THEN
  ASM_REWRITE_TAC[TISA_FAIL_STOP; TISA_RWP_STOP] THEN
  ASM_CASES_TAC `tregs st c = word 0` THEN ASM_REWRITE_TAC[]);;

let TISA_WP_RETURN = prove
 (`!out r Q R st. tisa_wp (TReturn out r) Q R st <=>
                  R out (tisa_finst out (tregs st r) st)`,
  REWRITE_TAC[tisa_wp; tisa_exec; TISA_FINISH_STOP; TISA_RWP_STOP]);;

let TISA_WP_MONO = prove
 (`!S Q R Q' R' st. (!s. Q s ==> Q' s) /\ (!k s. R k s ==> R' k s) /\ tisa_wp S Q R st
                    ==> tisa_wp S Q' R' st`,
  REWRITE_TAC[tisa_wp] THEN MESON_TAC[TISA_RWP_MONO]);;

(* A block whose specification is proved is used through it. *)
let TISA_WP_BY_SPEC = prove
 (`!P S Q0 R0 Q R st.
     tisa_spec P S Q0 R0 /\ P st /\ (!s. Q0 s ==> Q s) /\ (!k s. R0 k s ==> R k s)
     ==> tisa_wp S Q R st`,
  REWRITE_TAC[TISA_SPEC_WP] THEN MESON_TAC[TISA_WP_MONO]);;

(* A counted loop, by an invariant Inv N j over the iteration index. *)
let TISA_WP_COUNT_LOOP = prove
 (`!(Inv:num->num->tisa_state->bool) x n cap body Q R st.
     (cap < val(tregs st n) ==> R 2 (tisa_failst 2 st)) /\
     (~(cap < val(tregs st n)) ==> Inv (val(tregs st n)) 0 st) /\
     (!N j s0. j < N /\ Inv N j s0
               ==> tisa_wp body (Inv N (j + 1)) R (tisa_setreg x (word j) s0)) /\
     (!N s. Inv N N s ==> Q (tisa_setreg x (word N) s))
     ==> tisa_wp (TCountLoop x n cap body) Q R st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\s:tisa_state. s = st`; `Q:tisa_state->bool`; `R:num->tisa_state->bool`;
                 `Inv:num->num->tisa_state->bool`; `x:num`; `n:num`; `cap:num`;
                 `body:tisa_stmt`] TISA_SPEC_COUNT_LOOP) THEN
  REWRITE_TAC[TISA_SPEC_WP] THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC; ASM_MESON_TAC[]] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `s:tisa_state` THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:tisa_state` STRIP_ASSUME_TAC) THEN
  ASM_MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The forward generator. On a goal tisa_wp S Q R st it unfolds S in order,  *)
(* evaluates each instruction on the symbolic state, and splits a condition *)
(* only when neither it nor its negation follows from the assumptions by    *)
(* rewriting and targeted arithmetic. It stops at the leaves: a goal Q s or *)
(* R k s, and at loops, which take an invariant through TISA_WP_COUNT_LOOP. *)
(* ------------------------------------------------------------------------- *)

(* Comparison results as BOOL words. *)
let TISA_BOOL_COND01 = prove
 (`!b. tisa_bool (if b then word 1 else word 0:int64)`,
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[tisa_bool; VAL_WORD_0; VAL_WORD_1] THEN
  ARITH_TAC);;

let TISA_COND01_EQ_0 = prove
 (`!b. (if b then word 1 else word 0:int64) = word 0 <=> ~b`,
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

(* BOOL AND, OR and XOR of comparison results are comparison results.        *)
let TISA_COND01_AND = prove
 (`!p q. word_and (if p then word 1 else word 0) (if q then word 1 else word 0):int64 =
         if p /\ q then word 1 else word 0`,
  REPEAT GEN_TAC THEN MAP_EVERY BOOL_CASES_TAC [`p:bool`; `q:bool`] THEN
  REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

let TISA_COND01_OR = prove
 (`!p q. word_or (if p then word 1 else word 0) (if q then word 1 else word 0):int64 =
         if p \/ q then word 1 else word 0`,
  REPEAT GEN_TAC THEN MAP_EVERY BOOL_CASES_TAC [`p:bool`; `q:bool`] THEN
  REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

let TISA_COND01_XOR = prove
 (`!p q. word_xor (if p then word 1 else word 0) (if q then word 1 else word 0):int64 =
         if ~(p <=> q) then word 1 else word 0`,
  REPEAT GEN_TAC THEN MAP_EVERY BOOL_CASES_TAC [`p:bool`; `q:bool`] THEN
  REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

(* Two writes to one register: the second wins. *)
let TISA_SETREG_SETREG = prove
 (`!d (v:int64) w st. tisa_setreg d v (tisa_setreg d w st) = tisa_setreg d v st`,
  REWRITE_TAC[tisa_setreg; tregs; tmem] THEN REPEAT GEN_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* Addresses as a base plus an offset word, nested offsets combined. *)
let TISA_WORD_ADD_VAL = prove
 (`!(b:int64) n. word_add b (word n) = word(val b + n)`,
  REWRITE_TAC[WORD_ADD; WORD_VAL]);;

let TISA_IWORD_OFFSET = prove
 (`!(b:int64) n. iword(&(val b) + &n) = word_add b (word n):int64`,
  REWRITE_TAC[TISA_WORD_ADD_VAL; INT_OF_NUM_ADD; GSYM WORD_IWORD]);;

let TISA_ADDR_WORD_OFFSET = prove
 (`!(b:int64) (x:int64) s n.
     iword((&(val b) + &(val x) * &2 pow s) + &n) =
     word_add b (word(2 EXP s * val x + n)):int64`,
  REWRITE_TAC[TISA_WORD_ADD_VAL; INT_OF_NUM_POW; INT_OF_NUM_MUL; INT_OF_NUM_ADD;
              GSYM WORD_IWORD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let TISA_WORD_ADD_OFFSETS = prove
 (`!(b:int64) m n. word_add (word_add b (word m)) (word n) = word_add b (word(m + n))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let TISA_ADDR_REWRS =
  [TISA_ADDR_WORD; TISA_ADDR_WORD_OFFSET; TISA_IWORD_OFFSET; TISA_WORD_ADD_OFFSETS;
   INT_MUL_LZERO; VAL_WORD_USHR];;

(* The finish keeps the registers. *)
let TISA_TREGS_FINST = prove
 (`!out (v:int64) st. tregs (tisa_finst out v st) = tregs st`,
  REWRITE_TAC[tisa_finst; tisa_setfword; TISA_TREGS_STORE]);;

(* A write of the n bytes of the number x at a, keeping the registers: what *)
(* a loop that copies n bytes leaves.                                        *)
let tisa_bwrite = new_definition
 `tisa_bwrite (a:int64) n x st = TState (tregs st) (write (bytes(a,n)) x (tmem st))`;;

let TISA_TREGS_BWRITE = prove
 (`!(a:int64) n x st. tregs (tisa_bwrite a n x st) = tregs st`,
  REWRITE_TAC[tisa_bwrite; tregs]);;

let TISA_TMEM_BWRITE = prove
 (`!(a:int64) n x st. tmem (tisa_bwrite a n x st) = write (bytes(a,n)) x (tmem st)`,
  REWRITE_TAC[tisa_bwrite; tmem]);;

(* Instruction meanings and register reads: unconditional rewrites.          *)
let TISA_INSTR_REWRS =
  [tisa_norm; tisa_shift; tisa_narrow; tisa_shift64; tisa_compare; tisa_compare_at;
   tisa_rhs; tisa_index; tisa_binop; TISA_TY_DISTINCT_ALL; TISA_FAIL_STOP; tisa_ea;
   tisa_addr_mid; INT_ADD_RID; TISA_BOOL_COND01; TISA_COND01_EQ_0;
   TISA_COND01_AND; TISA_COND01_OR; TISA_COND01_XOR; TISA_TREGS_SETREG;
   TISA_TMEM_SETREG; TISA_TREGS_STORE; TISA_TMEM_STORE; TISA_READ_SETREG;
   TISA_SETREG_SETREG; TISA_TREGS_FINST; TISA_TREGS_BWRITE] @ TISA_ADDR_REWRS;;

(* Frame, region and bounds reads through register writes: conditional.     *)
let TISA_STATE_SIMPS =
  [TISA_FWORD_SETREG; TISA_BASE_SETREG; TISA_LEN_SETREG; TISA_INSIDE_SETREG;
   TISA_FRAME_SETREG; GSYM WORD_IWORD; WORD_VAL; ARITH_EQ];;

(* Frame words 0..17 as the bases and lengths of regions 0..8 (all nine     *)
(* regions p1 allows; revised 2026-11-12, intern_name has five).             *)
let TISA_FRAME_FOLDS =
  map (fun r -> CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
                  (GSYM(SPECL [`st:tisa_state`; mk_small_numeral r] tisa_base)))
      [0;1;2;3;4;5;6;7;8] @
  map (fun r -> CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
                  (GSYM(SPECL [`st:tisa_state`; mk_small_numeral r] tisa_len)))
      [0;1;2;3;4;5;6;7;8];;

(* Rewrite with the assumptions that give a register, the memory, a read, a  *)
(* frame word, or a region's base or length of a named state.               *)
let TISA_ASM_STATE_TAC : tactic = fun (asl,w) ->
  let heads = [`tregs`; `tmem`; `tisa_read`; `tisa_fword`; `tisa_base`; `tisa_len`] in
  let ok th = let c = concl(SPEC_ALL th) in
    is_eq c && (let h,args = strip_comb(lhand c) in
                mem h heads && args <> [] && is_var(hd args)) in
  REWRITE_TAC (filter ok (map snd asl)) (asl,w);;

(* Unconditional rewriting and the conditional state reads are kept apart:  *)
(* one simplifier pass over both recursed without bound on comparison steps.*)
let TISA_STATE_NORM_BASE_TAC =
  REWRITE_TAC TISA_INSTR_REWRS THEN CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN
  SIMP_TAC TISA_STATE_SIMPS THEN REWRITE_TAC TISA_INSTR_REWRS THEN
  CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN TISA_ASM_STATE_TAC THEN
  REWRITE_TAC TISA_FRAME_FOLDS;;

(* Region bounds as arithmetic on numbers. *)
let TISA_INSIDE_NUM = prove
 (`!st r (e:num) w.
     tisa_inside st r (&e) w <=>
     val(tisa_base st r) <= e /\ e + w <= val(tisa_base st r) + val(tisa_len st r)`,
  REWRITE_TAC[tisa_inside; INT_OF_NUM_ADD; INT_OF_NUM_LE]);;

let TISA_ARITH_SIMPS = [TISA_INSIDE_NUM; INT_OF_NUM_ADD; INT_OF_NUM_LE; INT_OF_NUM_LT;
                        INT_OF_NUM_EQ; INT_OF_NUM_MUL; INT_OF_NUM_POW];;

(* ------------------------------------------------------------------------- *)
(* Values of word operations, exact when nothing wraps, as facts for the     *)
(* arithmetic: the val atoms of a goal and the atoms they speak of, inner    *)
(* ones first, so a side condition can use the facts about its parts.        *)
(* ------------------------------------------------------------------------- *)

(* Focused arithmetic (see the header): the facts without disjunctions, then *)
(* with one disjunctive fact that bears on the goal, each in turn.           *)
let tisa_arith_focus = ref false;;

(* Formulas built from comparisons of numbers (as tisa_is_arith_fm below). *)
let rec tisa_focus_arith_fm t =
  if t = `T` || t = `F` then true
  else if is_neg t then tisa_focus_arith_fm (dest_neg t)
  else if is_conj t || is_disj t || is_imp t then
    tisa_focus_arith_fm (lhand t) && tisa_focus_arith_fm (rand t)
  else if is_eq t then
    (type_of(lhand t) = bool_ty && tisa_focus_arith_fm (lhand t) && tisa_focus_arith_fm (rand t)) ||
    type_of(lhand t) = `:num`
  else
    let h,args = strip_comb t in
    (try mem (fst(dest_const h)) ["<"; "<="; ">"; ">="] with Failure _ -> false) &&
    length args = 2 && type_of(hd args) = `:num`;;

let TISA_FOCUS_ARITH_TAC : tactic =
  let bad = ["tisa_inside"; "tisa_bool"; "tisa_store"; "tisa_setreg"; "tisa_exec"; "tisa_bwrite"] in
  let is_val t = is_comb t && (try fst(dest_const(rator t)) = "val" with Failure _ -> false) in
  let atoms tm = setify(find_terms is_val tm) in
  fun (asl,w) ->
    let ok th = let c = concl th in
      not (is_forall c) && tisa_focus_arith_fm c &&
      not (can (find_term (fun t -> is_const t && mem (fst(dest_const t)) bad)) c) &&
      can (find_term is_val) c in
    let cands = filter (fun (_,th) -> ok th) asl in
    let plain = filter (fun (_,th) -> not (can (find_term is_disj) (concl th))) cands
    and disj = filter (fun (_,th) -> can (find_term is_disj) (concl th)) cands in
    let g0 = atoms w in
    let g1 = itlist (fun (_,th) acc -> let a = atoms (concl th) in
                       if intersect a g0 <> [] then union a acc else acc) plain g0 in
    let score (_,th) = length (intersect (atoms (concl th)) g1) in
    let rel = map snd (sort (fun (a,_) (b,_) -> a > b)
                (map (fun d -> score d, d) (filter (fun d -> score d > 0) disj))) in
    let attempt ds = (MAP_EVERY (fun (_,th) -> MP_TAC th) (plain @ ds) THEN ARITH_TAC) (asl,w) in
    try attempt [] with Failure _ -> tryfind (fun d -> attempt [d]) rel;;

let TISA_WP_ARITH_TAC : tactic = fun g ->
  if !tisa_arith_focus then TISA_FOCUS_ARITH_TAC g else TISA_ARITH_TAC g;;

let TISA_VAL_WORD_EXACT = prove
 (`!n. n < 2 EXP 64 ==> val(word n:int64) = n`,
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64]);;

let TISA_VAL_ADD_EXACT = prove
 (`!x y:int64. val x + val y < 2 EXP 64 ==> val(word_add x y) = val x + val y`,
  SIMP_TAC[VAL_WORD_ADD; DIMINDEX_64; MOD_LT]);;

let TISA_VAL_SUB_EXACT = prove
 (`!x y:int64. val y <= val x ==> val(word_sub x y) = val x - val y`,
  SIMP_TAC[VAL_WORD_SUB_CASES]);;

let TISA_VAL_SHL_EXACT = prove
 (`!(x:int64) n. 2 EXP n * val x < 2 EXP 64 ==> val(word_shl x n) = 2 EXP n * val x`,
  SIMP_TAC[VAL_WORD_SHL; DIMINDEX_64; MOD_LT]);;

let tisa_val64 = `val:int64->num`;;
let tisa_is_val64 t = is_comb t && rator t = tisa_val64;;
let tisa_const_name t = try fst(dest_const t) with Failure _ -> "";;

let tisa_val_children t =
  let h,args = strip_comb(rand t) in
  match tisa_const_name h, args with
    ("word_and"|"word_add"|"word_sub"), [x;y] -> [mk_comb(tisa_val64,x); mk_comb(tisa_val64,y)]
  | ("word_ushr"|"word_shl"), [x;_] -> [mk_comb(tisa_val64,x)]
  | "word", [n] -> find_terms tisa_is_val64 n
  | _ -> [];;

(* A fact under a side condition is kept when arithmetic proves the side. *)
let TISA_COND_FACT_TAC th =
  let ante = lhand(concl th) in
  TRY(SUBGOAL_THEN ante (fun a -> ASSUME_TAC(MP th a)) THENL [TISA_WP_ARITH_TAC; ALL_TAC]);;

let TISA_VAL_FACT_TAC t =
  let u = rand t in
  let h,args = strip_comb u in
  match tisa_const_name h, args with
    "word_and", [x;y] ->
      ASSUME_TAC(ISPECL [x;y] (CONJUNCT1 VAL_WORD_AND_LE)) THEN
      ASSUME_TAC(ISPECL [x;y] (CONJUNCT2 VAL_WORD_AND_LE))
  | "word_ushr", [x;n] when is_numeral n ->
      ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV (ISPECL [x;n] VAL_WORD_USHR))
  | "word", [n] when is_numeral n ->
      ASSUME_TAC((REWRITE_CONV[VAL_WORD; DIMINDEX_64] THENC NUM_REDUCE_CONV) t)
  | "word_add", [x;y] -> TISA_COND_FACT_TAC(ISPECL [x;y] TISA_VAL_ADD_EXACT)
  | "word_sub", [x;y] -> TISA_COND_FACT_TAC(ISPECL [x;y] TISA_VAL_SUB_EXACT)
  | "word_shl", [x;n] when is_numeral n ->
      TISA_COND_FACT_TAC(CONV_RULE NUM_REDUCE_CONV (ISPECL [x;n] TISA_VAL_SHL_EXACT))
  | "word", [n] -> TISA_COND_FACT_TAC(ISPEC n TISA_VAL_WORD_EXACT)
  | _ -> ASSUME_TAC(ISPEC u VAL_BOUND_64);;

let TISA_VAL_FACTS_TAC : tactic = fun (asl,w) ->
  let seen = ref [] and order = ref [] in
  let rec visit t =
    if mem t !seen then () else
    (seen := t :: !seen; List.iter visit (tisa_val_children t); order := t :: !order) in
  List.iter visit (find_terms tisa_is_val64 w);
  MAP_EVERY TISA_VAL_FACT_TAC (rev !order) (asl,w);;

(* With focused arithmetic, value facts also for the word operations under  *)
(* val in the arithmetic assumptions (path conditions name values the goal   *)
(* reaches only through them).                                               *)
let TISA_VAL_FACTS_ALL_TAC : tactic = fun (asl,w) ->
  let seen = ref [] and order = ref [] in
  let rec visit t =
    if mem t !seen then () else
    (seen := t :: !seen; List.iter visit (tisa_val_children t); order := t :: !order) in
  let wordop t = mem (tisa_const_name (fst(strip_comb(rand t))))
                   ["word_and"; "word_add"; "word_sub"; "word_ushr"; "word_shl"; "word"] in
  (* the assumptions' terms first: a fact about the goal can need theirs *)
  List.iter (fun (_,th) -> if tisa_focus_arith_fm (concl th)
                           then List.iter visit (filter wordop (find_terms tisa_is_val64 (concl th))))
            asl;
  List.iter visit (find_terms tisa_is_val64 w);
  MAP_EVERY TISA_VAL_FACT_TAC (rev !order) (asl,w);;

let TISA_WP_VAL_FACTS_TAC : tactic = fun g ->
  if !tisa_arith_focus then TISA_VAL_FACTS_ALL_TAC g else TISA_VAL_FACTS_TAC g;;

(* Formulas built from comparisons of numbers. *)
let tisa_num_ty = `:num`;;
let rec tisa_is_arith_fm t =
  if t = `T` || t = `F` then true
  else if is_neg t then tisa_is_arith_fm (dest_neg t)
  else if is_conj t || is_disj t || is_imp t then
    tisa_is_arith_fm (lhand t) && tisa_is_arith_fm (rand t)
  else if is_eq t then
    (type_of(lhand t) = bool_ty && tisa_is_arith_fm (lhand t) && tisa_is_arith_fm (rand t)) ||
    type_of(lhand t) = tisa_num_ty
  else
    let h,args = strip_comb t in
    mem (tisa_const_name h) ["<"; "<="; ">"; ">="] && length args = 2 &&
    type_of(hd args) = tisa_num_ty;;

(* Arithmetic decision of a normalized condition. *)
let TISA_ARITH_DECIDE_TAC =
  SIMP_TAC TISA_ARITH_SIMPS THEN TISA_ASM_STATE_TAC THEN
  (fun (asl,w) ->
     if tisa_is_arith_fm w
     then (TISA_WP_ARITH_TAC ORELSE (TISA_WP_VAL_FACTS_TAC THEN TISA_WP_ARITH_TAC)) (asl,w)
     else failwith "TISA_ARITH_DECIDE_TAC: not arithmetic");;

(* ------------------------------------------------------------------------- *)
(* Reads through stores and through the finish.                              *)
(* ------------------------------------------------------------------------- *)

(* Frame words, region words and region checks through a store outside the  *)
(* frame.                                                                    *)
let TISA_STORE_KEEPS_FRAME = prove
 (`!(a:int64) w (v:int64) st.
     val(tregs st 0) + 192 <= 2 EXP 64 /\ val a + w <= 2 EXP 64 /\
     (val a + w <= val(tregs st 0) \/ val(tregs st 0) + 192 <= val a)
     ==> (!i. i < 24 ==> tisa_fword (tisa_store a w v st) i = tisa_fword st i) /\
         (!r. r < 12 ==> tisa_base (tisa_store a w v st) r = tisa_base st r) /\
         (!r. r < 12 ==> tisa_len (tisa_store a w v st) r = tisa_len st r) /\
         (!r e w'. r < 12 ==> (tisa_inside (tisa_store a w v st) r e w' <=>
                               tisa_inside st r e w'))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i. i < 24 ==> tisa_fword (tisa_store a w v st) i = tisa_fword st i`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_FWORD_STORE_OUTSIDE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[tisa_base; tisa_len; tisa_inside;
               ARITH_RULE `r < 12 ==> 2 * r < 24 /\ 2 * r + 1 < 24`]);;

(* An 8-byte read through an 8-byte store. *)
let TISA_READ_STORE_SAME = prove
 (`!(a:int64) (v:int64) st b.
     val a + 8 <= 2 EXP 64 /\ val b = val a
     ==> tisa_read (tisa_store a 8 v st) b 8 = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `b:int64 = a` SUBST1_TAC THENL [ASM_REWRITE_TAC[GSYM VAL_EQ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:int64`; `v:int64`; `st:tisa_state`; `a:int64`] TISA_READ_STORE) THEN
  ASM_REWRITE_TAC[]);;

let TISA_READ_STORE_APART = prove
 (`!(a:int64) (v:int64) st b.
     val a + 8 <= 2 EXP 64 /\ val b + 8 <= 2 EXP 64 /\
     (val a + 8 <= val b \/ val b + 8 <= val a)
     ==> tisa_read (tisa_store a 8 v st) b 8 = tisa_read st b 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `v:int64`; `st:tisa_state`; `b:int64`] TISA_READ_STORE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `~(a:int64 = b)` (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN ASM_ARITH_TAC);;

(* Frame words and reads away from the frame through the finish. *)
let TISA_FINST_VIEW = prove
 (`!out (v:int64) st.
     val(tregs st 0) + 192 <= 2 EXP 64
     ==> (!i. i < 24 ==> tisa_fword (tisa_finst out v st) i =
                         if i = 19 then v else if i = 18 then word out else tisa_fword st i) /\
         (!r. r < 9 ==> tisa_base (tisa_finst out v st) r = tisa_base st r) /\
         (!r. r < 9 ==> tisa_len (tisa_finst out v st) r = tisa_len st r) /\
         (!a. val a + 8 <= 2 EXP 64 /\
              (val a + 8 <= val(tregs st 0) \/ val(tregs st 0) + 192 <= val a)
              ==> tisa_read (tisa_finst out v st) a 8 = tisa_read st a 8)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i. i < 24 ==> tisa_fword (tisa_finst out v st) i =
                    if i = 19 then v else if i = 18 then word out else tisa_fword st i`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_FWORD_FINST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_base] THEN
    ASM_SIMP_TAC[ARITH_RULE `r < 9 ==> 2 * r < 24 /\ ~(2 * r = 19) /\ ~(2 * r = 18)`];
    REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_len] THEN
    ASM_SIMP_TAC[ARITH_RULE `r < 9 ==> 2 * r + 1 < 24 /\ ~(2 * r + 1 = 19) /\ ~(2 * r + 1 = 18)`];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_READ_FINST THEN ASM_REWRITE_TAC[]]);;

let tisa_read_tm = `tisa_read` and tisa_store_tm = `tisa_store`
and tisa_finst_tm = `tisa_finst` and tisa_eight_tm = `8`
and tisa_fword_tm = `tisa_fword` and tisa_base_tm = `tisa_base`
and tisa_len_tm = `tisa_len` and tisa_inside_tm = `tisa_inside`
and tisa_lt_tm = `(<):num->num->bool`;;

let tisa_numeral_lt k n = EQT_ELIM(NUM_REDUCE_CONV(mk_comb(mk_comb(tisa_lt_tm,k),mk_small_numeral n)));;

(* A tactic that fails when it changes nothing. *)
let TISA_PROGRESS_TAC (tac:tactic) : tactic = fun (asl,w) ->
  (tac THEN (fun (asl',w') -> if w' = w then failwith "TISA_PROGRESS_TAC" else ALL_TAC (asl',w')))
  (asl,w);;

let tisa_store_frame_reads w =
  find_terms (fun t -> let h,args = strip_comb t in
     (h = tisa_fword_tm || h = tisa_base_tm || h = tisa_len_tm || h = tisa_inside_tm) &&
     args <> [] &&
     (let sh,sargs = strip_comb (hd args) in sh = tisa_store_tm && length sargs = 4)) w;;

let tisa_store_frame_eq thS t =
  let h,args = strip_comb t in
  let k = el 1 args in
  match CONJUNCTS thS with
    [fw;bs;ln;ins] ->
      if h = tisa_fword_tm then MP (SPEC k fw) (tisa_numeral_lt k 24)
      else if h = tisa_base_tm then MP (SPEC k bs) (tisa_numeral_lt k 12)
      else if h = tisa_len_tm then MP (SPEC k ln) (tisa_numeral_lt k 12)
      else MP (SPECL [k; el 2 args; el 3 args] ins) (tisa_numeral_lt k 12)
  | _ -> failwith "tisa_store_frame_eq";;

let TISA_STORE_FRAME_TAC : tactic = fun (asl,w) ->
  let targets = tisa_store_frame_reads w in
  if targets = [] then failwith "TISA_STORE_FRAME_TAC: no frame read through a store" else
  let stores = setify (map (fun t -> hd(snd(strip_comb t))) targets) in
  let step s =
    let _,sargs = strip_comb s in
    let ts = filter (fun t -> hd(snd(strip_comb t)) = s) targets in
    MP_TAC(ISPECL sargs TISA_STORE_KEEPS_FRAME) THEN ANTS_TAC THENL
     [TISA_STATE_NORM_BASE_TAC THEN REPEAT CONJ_TAC THEN TISA_ARITH_DECIDE_TAC;
      DISCH_THEN(fun thS -> REWRITE_TAC(mapfilter (tisa_store_frame_eq thS) ts))] in
  TISA_PROGRESS_TAC (MAP_EVERY (fun s -> TRY(step s)) stores) (asl,w);;

let tisa_store_mem_reads w =
  find_terms (fun t -> let h,args = strip_comb t in
     h = tisa_read_tm && length args = 3 && el 2 args = tisa_eight_tm &&
     (let sh,sargs = strip_comb (hd args) in
      sh = tisa_store_tm && length sargs = 4 && el 1 sargs = tisa_eight_tm)) w;;

let TISA_STORE_READ_TAC : tactic = fun (asl,w) ->
  let targets = tisa_store_mem_reads w in
  if targets = [] then failwith "TISA_STORE_READ_TAC: no read through a store" else
  let step t =
    let _,targs = strip_comb t in
    let s = el 0 targs and b = el 1 targs in
    let _,sargs = strip_comb s in
    let a = el 0 sargs and v = el 2 sargs and s0 = el 3 sargs in
    let by th = MP_TAC(ISPECL [a;v;s0;b] th) THEN ANTS_TAC THENL
                 [TISA_STATE_NORM_BASE_TAC THEN REPEAT CONJ_TAC THEN TISA_ARITH_DECIDE_TAC;
                  DISCH_THEN(fun th -> REWRITE_TAC[th])] in
    if a = b then TRY(by TISA_READ_STORE_SAME)
    else TRY(by TISA_READ_STORE_APART ORELSE by TISA_READ_STORE_SAME) in
  TISA_PROGRESS_TAC (MAP_EVERY step targets) (asl,w);;

let tisa_finst_reads w =
  find_terms (fun t -> let h,args = strip_comb t in
     (h = tisa_fword_tm || h = tisa_base_tm || h = tisa_len_tm ||
      (h = tisa_read_tm && length args = 3 && el 2 args = tisa_eight_tm)) &&
     args <> [] &&
     (let sh,sargs = strip_comb (hd args) in sh = tisa_finst_tm && length sargs = 3)) w;;

let tisa_finst_frame_eq thF t =
  let h,args = strip_comb t in
  let k = el 1 args in
  match CONJUNCTS thF with
    [fw;bs;ln;_] ->
      if h = tisa_fword_tm then MP (SPEC k fw) (tisa_numeral_lt k 24)
      else if h = tisa_base_tm then MP (SPEC k bs) (tisa_numeral_lt k 9)
      else if h = tisa_len_tm then MP (SPEC k ln) (tisa_numeral_lt k 9)
      else failwith "tisa_finst_frame_eq"
  | _ -> failwith "tisa_finst_frame_eq";;

let TISA_FINST_TAC : tactic = fun (asl,w) ->
  let targets = tisa_finst_reads w in
  if targets = [] then failwith "TISA_FINST_TAC: no read through a finish" else
  let fins = setify (map (fun t -> hd(snd(strip_comb t))) targets) in
  let step f =
    let _,fargs = strip_comb f in
    let ts = filter (fun t -> hd(snd(strip_comb t)) = f) targets in
    let reads = filter (fun t -> fst(strip_comb t) = tisa_read_tm) ts in
    MP_TAC(ISPECL fargs TISA_FINST_VIEW) THEN ANTS_TAC THENL
     [TISA_STATE_NORM_BASE_TAC THEN TISA_ARITH_DECIDE_TAC;
      DISCH_THEN(fun thF ->
        REWRITE_TAC(mapfilter (tisa_finst_frame_eq thF) ts) THEN
        CONV_TAC(TRY_CONV NUM_REDUCE_CONV) THEN
        MAP_EVERY (fun t ->
          let a = el 1 (snd(strip_comb t)) in
          TRY(MP_TAC(SPEC a (el 3 (CONJUNCTS thF))) THEN ANTS_TAC THENL
                [TISA_STATE_NORM_BASE_TAC THEN REPEAT CONJ_TAC THEN TISA_ARITH_DECIDE_TAC;
                 DISCH_THEN(fun th -> REWRITE_TAC[th])])) reads)] in
  TISA_PROGRESS_TAC (MAP_EVERY (fun f -> TRY(step f)) fins) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Byte-range writes, and reads of any width (see the header).               *)
(* ------------------------------------------------------------------------- *)

(* A read of w bytes at b through a write of n bytes at a, the two apart. *)
let TISA_READ_WRITE_APART = prove
 (`!(a:int64) n x (m:int64->byte) (b:int64) w.
     val a + n <= 2 EXP 64 /\ val b + w <= 2 EXP 64 /\
     (val a + n <= val b \/ val b + w <= val a)
     ==> read (bytes(b,w)) (write (bytes(a,n)) x m) = read (bytes(b,w)) m`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `w = 0` THEN
  ASM_REWRITE_TAC[READ_BYTES_TRIVIAL] THEN
  MATCH_MP_TAC TISA_READ_DISJOINT_WRITE THEN ASM_REWRITE_TAC[]);;

let TISA_READ_BWRITE_APART = prove
 (`!(a:int64) n x st (b:int64) w.
     val a + n <= 2 EXP 64 /\ val b + w <= 2 EXP 64 /\
     (val a + n <= val b \/ val b + w <= val a)
     ==> tisa_read (tisa_bwrite a n x st) b w = tisa_read st b w`,
  REWRITE_TAC[tisa_read; TISA_TMEM_BWRITE] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC TISA_READ_WRITE_APART THEN ASM_REWRITE_TAC[]);;

let TISA_READ_STORE_APART_W = prove
 (`!(a:int64) w (v:int64) st (b:int64) w'.
     val a + w <= 2 EXP 64 /\ val b + w' <= 2 EXP 64 /\
     (val a + w <= val b \/ val b + w' <= val a)
     ==> tisa_read (tisa_store a w v st) b w' = tisa_read st b w'`,
  REWRITE_TAC[tisa_read; TISA_TMEM_STORE] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC TISA_READ_WRITE_APART THEN ASM_REWRITE_TAC[]);;

(* Frame words, region words and region checks through a byte-range write  *)
(* outside the frame.                                                        *)
let TISA_BWRITE_KEEPS_FRAME = prove
 (`!(a:int64) n x st.
     val(tregs st 0) + 192 <= 2 EXP 64 /\ val a + n <= 2 EXP 64 /\
     (val a + n <= val(tregs st 0) \/ val(tregs st 0) + 192 <= val a)
     ==> (!i. i < 24 ==> tisa_fword (tisa_bwrite a n x st) i = tisa_fword st i) /\
         (!r. r < 12 ==> tisa_base (tisa_bwrite a n x st) r = tisa_base st r) /\
         (!r. r < 12 ==> tisa_len (tisa_bwrite a n x st) r = tisa_len st r) /\
         (!r e w'. r < 12 ==> (tisa_inside (tisa_bwrite a n x st) r e w' <=>
                               tisa_inside st r e w'))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i. i < 24 ==> tisa_fword (tisa_bwrite a n x st) i = tisa_fword st i`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[tisa_fword; tisa_frame; TISA_TREGS_BWRITE] THEN
    MATCH_MP_TAC TISA_READ_BWRITE_APART THEN
    SUBGOAL_THEN `val(word_add (tregs st 0) (word(8 * i)):int64) = val(tregs st 0) + 8 * i`
     SUBST1_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[tisa_base; tisa_len; tisa_inside;
               ARITH_RULE `r < 12 ==> 2 * r < 24 /\ 2 * r + 1 < 24`]);;

(* Reads of any width through the finish, apart from its two words. *)
let TISA_READ_FINST_W = prove
 (`!out (v:int64) st (a:int64) w.
     val(tregs st 0) + 192 <= 2 EXP 64 /\ val a + w <= 2 EXP 64 /\
     (val a + w <= val(tregs st 0) + 144 \/ val(tregs st 0) + 160 <= val a)
     ==> tisa_read (tisa_finst out v st) a w = tisa_read st a w`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[tisa_finst; tisa_setfword; tisa_frame; TISA_TREGS_STORE] THEN
  SUBGOAL_THEN `!k. k < 24 ==> val(word_add (tregs st 0) (word(8 * k)):int64) = val(tregs st 0) + 8 * k`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) TISA_READ_STORE_APART_W (lhand w))) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `19 < 24`] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC TISA_READ_STORE_APART_W THEN
  ASM_SIMP_TAC[ARITH_RULE `18 < 24`] THEN ASM_ARITH_TAC);;

(* A byte inside a byte-range write, and the bytes of a range read as one   *)
(* number.                                                                   *)
let TISA_READ_BWRITE_BYTE = prove
 (`!(a:int64) n x st (b:int64).
     val a + n <= 2 EXP 64 /\ val a <= val b /\ val b < val a + n
     ==> tisa_read (tisa_bwrite a n x st) b 1 = word(limb 8 x (val b - val a))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[tisa_read; TISA_TMEM_BWRITE; READ_BYTES_1; WRITE_BYTES] THEN BETA_TAC THEN
  SUBGOAL_THEN `val(word_sub b a:int64) = val b - val a` SUBST1_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD_SUB_CASES]; ALL_TAC] THEN
  SUBGOAL_THEN `val(b:int64) - val(a:int64) < n` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[LIMB_BOUND]);;

let LIMB_READ_BYTES = prove
 (`!(a:int64) n (m:int64->byte) k.
     limb 8 (read (bytes(a,n)) m) k = if k < n then val(m(word_add a (word k))) else 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_BYTES] THEN
  MATCH_MP_TAC LIMB_DIGITSUM THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(m:int64->byte) (word_add a (word i))` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8]);;

let tisa_bwrite_tm = `tisa_bwrite`;;

let tisa_bwrite_frame_reads w =
  find_terms (fun t -> let h,args = strip_comb t in
     (h = tisa_fword_tm || h = tisa_base_tm || h = tisa_len_tm || h = tisa_inside_tm) &&
     args <> [] &&
     (let sh,sargs = strip_comb (hd args) in sh = tisa_bwrite_tm && length sargs = 4)) w;;

let TISA_BWRITE_FRAME_TAC : tactic = fun (asl,w) ->
  let targets = tisa_bwrite_frame_reads w in
  if targets = [] then failwith "TISA_BWRITE_FRAME_TAC: no frame read through a byte write" else
  let writes = setify (map (fun t -> hd(snd(strip_comb t))) targets) in
  let step s =
    let _,sargs = strip_comb s in
    let ts = filter (fun t -> hd(snd(strip_comb t)) = s) targets in
    MP_TAC(ISPECL sargs TISA_BWRITE_KEEPS_FRAME) THEN ANTS_TAC THENL
     [TISA_STATE_NORM_BASE_TAC THEN REPEAT CONJ_TAC THEN TISA_ARITH_DECIDE_TAC;
      DISCH_THEN(fun thS -> REWRITE_TAC(mapfilter (tisa_store_frame_eq thS) ts))] in
  TISA_PROGRESS_TAC (MAP_EVERY (fun s -> TRY(step s)) writes) (asl,w);;

(* Reads through a byte-range write, and reads through a store when a width *)
(* is not 8 (TISA_STORE_READ_TAC takes 8-byte reads through 8-byte stores). *)
let tisa_apart_reads w =
  find_terms (fun t -> let h,args = strip_comb t in
     h = tisa_read_tm && length args = 3 &&
     (let sh,sargs = strip_comb (hd args) in
      length sargs = 4 &&
      (sh = tisa_bwrite_tm ||
       (sh = tisa_store_tm && not(el 2 args = tisa_eight_tm && el 1 sargs = tisa_eight_tm))))) w;;

let TISA_APART_READ_TAC : tactic = fun (asl,w) ->
  let targets = tisa_apart_reads w in
  if targets = [] then failwith "TISA_APART_READ_TAC: no read through a write" else
  let step t =
    let _,targs = strip_comb t in
    let s = el 0 targs and b = el 1 targs and wd = el 2 targs in
    let sh,sargs = strip_comb s in
    let th = if sh = tisa_store_tm then TISA_READ_STORE_APART_W else TISA_READ_BWRITE_APART in
    TRY(MP_TAC(ISPECL (sargs @ [b; wd]) th) THEN ANTS_TAC THENL
          [TISA_STATE_NORM_BASE_TAC THEN REPEAT CONJ_TAC THEN TISA_ARITH_DECIDE_TAC;
           DISCH_THEN(fun th -> REWRITE_TAC[th])]) in
  TISA_PROGRESS_TAC (MAP_EVERY step targets) (asl,w);;

(* Reads of a width other than 8 through the finish. *)
let tisa_finst_w_reads w =
  find_terms (fun t -> let h,args = strip_comb t in
     h = tisa_read_tm && length args = 3 && not(el 2 args = tisa_eight_tm) &&
     (let sh,sargs = strip_comb (hd args) in sh = tisa_finst_tm && length sargs = 3)) w;;

let TISA_FINST_READ_W_TAC : tactic = fun (asl,w) ->
  let targets = tisa_finst_w_reads w in
  if targets = [] then failwith "TISA_FINST_READ_W_TAC: no narrow read through a finish" else
  let step t =
    let _,targs = strip_comb t in
    let _,fargs = strip_comb (el 0 targs) in
    TRY(MP_TAC(ISPECL (fargs @ [el 1 targs; el 2 targs]) TISA_READ_FINST_W) THEN ANTS_TAC THENL
          [TISA_STATE_NORM_BASE_TAC THEN REPEAT CONJ_TAC THEN TISA_ARITH_DECIDE_TAC;
           DISCH_THEN(fun th -> REWRITE_TAC[th])]) in
  TISA_PROGRESS_TAC (MAP_EVERY step targets) (asl,w);;

let TISA_MEM_STEP_TAC =
  TISA_STORE_FRAME_TAC ORELSE TISA_STORE_READ_TAC ORELSE TISA_FINST_TAC ORELSE
  TISA_BWRITE_FRAME_TAC ORELSE TISA_APART_READ_TAC ORELSE TISA_FINST_READ_W_TAC;;

(* The state normal form. *)
let TISA_STATE_NORM_TAC =
  TISA_STATE_NORM_BASE_TAC THEN REPEAT(TISA_MEM_STEP_TAC THEN TISA_STATE_NORM_BASE_TAC);;

let TISA_WP_SIMPS = TISA_INSTR_REWRS @ TISA_STATE_SIMPS;;

(* ------------------------------------------------------------------------- *)
(* Deciding conditions, and the generator's steps.                           *)
(* ------------------------------------------------------------------------- *)

(* Prove a condition from the assumptions: simplification first, then        *)
(* arithmetic on the numbers it leaves.                                      *)
let TISA_PROVE_COND_TAC =
  TISA_STATE_NORM_TAC THEN ((ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE TISA_ARITH_DECIDE_TAC);;

(* Decide a condition, stripped of its negation, from the assumptions, or    *)
(* split on it, keeping the case as an assumption.                          *)
let TISA_DECIDE_TAC c =
  let c0 = if is_neg c then dest_neg c else c in
  (SUBGOAL_THEN c0 (fun th -> REWRITE_TAC[th]) THENL [TISA_PROVE_COND_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_neg c0) (fun th -> REWRITE_TAC[th]) THENL [TISA_PROVE_COND_TAC; ALL_TAC]) ORELSE
  (ASM_CASES_TAC c0 THEN POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th));;

let rec TISA_WP_STEP_TAC : tactic = fun (asl,w) ->
  let h,args = strip_comb w in
  if h = `tisa_wp` then
    let sh,_ = strip_comb (hd args) in
    if sh = `TSeq` then (GEN_REWRITE_TAC I [TISA_WP_SEQ] THEN TISA_WP_STEP_TAC) (asl,w)
    else if sh = `TSkip` then
      (GEN_REWRITE_TAC I [TISA_WP_SKIP] THEN BETA_TAC THEN TISA_WP_STEP_TAC) (asl,w)
    else if sh = `TReturn` then (GEN_REWRITE_TAC I [TISA_WP_RETURN] THEN BETA_TAC) (asl,w)
    else if sh = `TIf` then
      (GEN_REWRITE_TAC I [TISA_WP_IF] THEN TISA_STATE_NORM_TAC THEN
       TISA_COND_TAC) (asl,w)
    else if sh = `TInstr` then
      (GEN_REWRITE_TAC I [TISA_WP_INSTR] THEN REWRITE_TAC[tisa_instr] THEN
       REWRITE_TAC[TISA_RWP_COND; TISA_RWP_CONT; TISA_RWP_STOP; TISA_FAIL_STOP] THEN
       BETA_TAC THEN TISA_STATE_NORM_TAC THEN TISA_COND_TAC) (asl,w)
    else ALL_TAC (asl,w)
  else ALL_TAC (asl,w)

(* Decide or split the outermost condition of an if-then-else goal, then go *)
(* on with the statement that remains.                                       *)
and TISA_COND_TAC : tactic = fun (asl,w) ->
  if is_cond w then
    let c = fst(dest_cond w) in
    (TISA_DECIDE_TAC c THEN BETA_TAC THEN TISA_COND_TAC) (asl,w)
  else TISA_WP_STEP_TAC (asl,w);;

(* Run the generator, then close the leaves that are numeral facts. *)
let TISA_VCG_TAC =
  TISA_WP_STEP_TAC THEN BETA_TAC THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) THEN
  TRY(TISA_STATE_NORM_TAC THEN NO_TAC);;
