(* ========================================================================= *)
(* The image as a subroutine. The prologue pushes rbx r12 r13 r14 r15 into   *)
(* the 40 bytes below the caller's stack pointer, the body runs the program  *)
(* from there, and the epilogue pops them and returns.                       *)
(*                                                                           *)
(* The body runs from the caller's state patched with those 40 bytes. A run  *)
(* touches only its accessible regions and its frame                         *)
(* (tisa_p1_noninterference.ml), and writes only its read-write regions and  *)
(* frame words (tisa_p1_frame.ml); the stack lies apart from both. So the    *)
(* run from the patched state is the patched run from the caller's state,   *)
(* the pops read back what was pushed, and ret reads the caller's return     *)
(* address.                                                                  *)
(* ========================================================================= *)

needs "tisa/hol/tisa_x86_image.ml";;
needs "tisa/hol/tisa_p1_noninterference.ml";;

(* The 40 bytes below the stack pointer stackpointer. *)
let tisa_saved = new_definition
 `tisa_saved (stackpointer:int64) (a:int64) <=> val stackpointer <= val a + 40 /\ val a < val stackpointer`;;

(* What a call assumes of its stack: 40 bytes below stackpointer and the return
   address at stackpointer, which do not wrap and lie apart from the code, the frame and
   every accessible region. *)
let tisa_stack_str mclen decls =
  let rs = String.concat "" (List.mapi (fun r mode ->
      if mode <> 0 then
        Printf.sprintf " /\\ (val L%d = 0 \\/ val B%d + val L%d <= val stackpointer - 40 \\/ val stackpointer + 8 <= val B%d)" r r r r
      else "") decls) in
  Printf.sprintf
    "40 <= val (stackpointer:int64) /\\ val stackpointer + 8 <= 2 EXP 64 /\\ nonoverlapping (word_sub stackpointer (word 40):int64,48) (word pc,%d) /\\ (val fr + 192 <= val stackpointer - 40 \\/ val stackpointer + 8 <= val fr)%s"
    mclen rs;;

(* What a call of the image establishes, for an entry state t meeting the
   image's entry facts: it returns to returnaddress with RSP restored, rbx r12 r13 r14 r15
   restored, ret_val in rax, and every byte outside the 40 saved bytes equal
   to the run's final memory. *)
let tisa_call_frame_str =
  "MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; R8; R9; R10; R11; R12; R13; R14; R15] ,, MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory]";;

let tisa_wrapper_goal ctx root pfacts =
  let s = Printf.sprintf
    "%s /\\ %s /\\ %s t ==> ensures x86 (\\s. bytes_loaded s (word pc) %s /\\ read RIP s = word pc /\\ read RSP s = stackpointer /\\ read (memory :> bytes64 stackpointer) s = returnaddress /\\ tisa_x86_rel t s /\\ read R14 s = r14v /\\ read R15 s = r15v) (\\s. read RIP s = returnaddress /\\ read RSP s = word_add stackpointer (word 8) /\\ read RBX s = tregs t 9 /\\ read R12 s = tregs t 10 /\\ read R13 s = tregs t 11 /\\ read R14 s = r14v /\\ read R15 s = r15v /\\ (?k u. tisa_exec tisa_root_here t = TStop k u /\\ read RAX s = tisa_fword u 19 /\\ !a. ~tisa_saved stackpointer a ==> read memory s a = tmem u a)) (%s)"
    (tisa_global_str ctx.mclen ctx.decls) (tisa_stack_str ctx.mclen ctx.decls) pfacts ctx.mc tisa_call_frame_str in
  vsubst [root, `tisa_root_here:tisa_stmt`] (parse_term s);;

(* ------------------------------------------------------------------------- *)
(* Reading a patched memory.                                                 *)
(* ------------------------------------------------------------------------- *)

let TISA_PATCH_READ_INSIDE = prove
 (`!(P:int64->bool) g m (a:int64) w.
        val a + w <= 2 EXP 64 /\ (!b. val a <= val b /\ val b < val a + w ==> P b)
        ==> read (bytes(a,w)) (\x. if P x then g x else m x) = read (bytes(a,w)) g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[READ_BYTES_EQ] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `(P:int64->bool)(word_add a (word k))` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `val(word_add a (word k):int64) = val a + k` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let TISA_PATCH_READ_OUTSIDE = prove
 (`!(P:int64->bool) g m (a:int64) w.
        val a + w <= 2 EXP 64 /\ (!b. val a <= val b /\ val b < val a + w ==> ~P b)
        ==> read (bytes(a,w)) (\x. if P x then g x else m x) = read (bytes(a,w)) m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[READ_BYTES_EQ] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `~((P:int64->bool)(word_add a (word k)))` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `val(word_add a (word k):int64) = val a + k` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

(* The saved bytes below stackpointer, as offsets. *)
let TISA_VAL_SP_SUB = prove
 (`!(stackpointer:int64) n. n <= val stackpointer ==> val(word_sub stackpointer (word n)) = val stackpointer - n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `n MOD 2 EXP 64 = n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `stackpointer:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* The pushes' addresses, in normal form. *)
let TISA_SP_SUB_NORM = prove
 (`!s:int64.
     word_sub (word_sub (word_sub (word_sub (word_sub s (word 8)) (word 8)) (word 8)) (word 8)) (word 8) =
       word_sub s (word 40) /\
     word_sub (word_sub (word_sub (word_sub s (word 8)) (word 8)) (word 8)) (word 8) = word_sub s (word 32) /\
     word_sub (word_sub (word_sub s (word 8)) (word 8)) (word 8) = word_sub s (word 24) /\
     word_sub (word_sub s (word 8)) (word 8) = word_sub s (word 16)`,
  GEN_TAC THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE);;

(* A pushed word lies inside the saved bytes, so bytes outside them keep
   their values. *)
let TISA_WRITE64_SP_OUTSIDE = prove
 (`!(stackpointer:int64) n (v:int64) m x.
        8 <= n /\ n <= 40 /\ 40 <= val stackpointer /\ ~tisa_saved stackpointer x
        ==> write (bytes64 (word_sub stackpointer (word n))) v m x = m x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tisa_saved] THEN STRIP_TAC THEN
  REWRITE_TAC[TISA_WRITE_BYTES64] THEN MATCH_MP_TAC TISA_WRITE_BYTES_OUTSIDE THEN
  SUBGOAL_THEN `val(word_sub stackpointer (word n):int64) = val stackpointer - n` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_SP_SUB THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `stackpointer:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC);;

(* Reading back a pushed word. *)
let TISA_READ_WRITE64_SAME = prove
 (`!(a:int64) (v:int64) m. read (bytes(a,8)) (write (bytes64 a) v m) = val v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TISA_WRITE_BYTES64] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) READ_WRITE_BYTES o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_64] THEN ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * 8 = 64`] THEN MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[VAL_BOUND_64]);;

(* ------------------------------------------------------------------------- *)
(* A big step through a block whose frame includes the whole memory. The     *)
(* block's postcondition states bytes_loaded itself, so this omits the       *)
(* non-self-modification check that s2n-bignum's X86_BIGSTEP_TAC needs a     *)
(* memory-free frame for; facts about the old state are carried over by the  *)
(* frame as usual.                                                           *)
(* ------------------------------------------------------------------------- *)

let TISA_BIGSTEP_TAC =
  let lemma = prove
   (`P s /\ (!s':S. Q s' /\ C s s' ==> eventually step R s')
     ==> ensures step P Q C ==> eventually step R s`,
    STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [ensures] THEN
    DISCH_THEN(MP_TAC o SPEC `s:S`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[]
     `(!s:S. eventually step P s ==> eventually step Q s)
      ==> eventually step P s ==> eventually step Q s`) THEN
    GEN_REWRITE_TAC I [EVENTUALLY_IMP_EVENTUALLY] THEN
    ASM_REWRITE_TAC[]) in
  fun sname (asl,w) ->
    let sv = mk_var(sname,type_of(rand(rand w))) in
    (MATCH_MP_TAC lemma THEN CONJ_TAC THENL
      [BETA_TAC THEN ASM_REWRITE_TAC[];
       BETA_TAC THEN X_GEN_TAC sv THEN
       REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
       REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
       ASSUMPTION_STATE_UPDATE_TAC THEN
       MAYCHANGE_STATE_UPDATE_TAC THEN
       DISCH_THEN(K ALL_TAC) THEN
       DISCARD_OLDSTATE_TAC sname]) (asl,w);;

(* The pops' addresses, after the pushes' are normalized. *)
let TISA_SP_POP_NORM = prove
 (`!s:int64.
     word_add (word_sub s (word 40)) (word 8) = word_sub s (word 32) /\
     word_add (word_sub s (word 40)) (word 16) = word_sub s (word 24) /\
     word_add (word_sub s (word 40)) (word 24) = word_sub s (word 16) /\
     word_add (word_sub s (word 40)) (word 32) = word_sub s (word 8) /\
     word_add (word_sub s (word 40)) (word 40) = s /\
     word_add (word_sub s (word 40)) (word 48) = word_add s (word 8)`,
  GEN_TAC THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE);;

(* A saved slot reads the pushed memory; the return slot reads the run's. *)
let TISA_SAVED_SLOT_READ = prove
 (`!(stackpointer:int64) k g m.
        8 <= k /\ k <= 40 /\ 40 <= val stackpointer
        ==> read (bytes(word_sub stackpointer (word k),8))
                 (\a. if tisa_saved stackpointer a then g a else m a) =
            read (bytes(word_sub stackpointer (word k),8)) g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_PATCH_READ_INSIDE THEN
  SUBGOAL_THEN `val(word_sub stackpointer (word k):int64) = val stackpointer - k` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_SP_SUB THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[tisa_saved] THEN MP_TAC(ISPEC `stackpointer:int64` VAL_BOUND_64) THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let TISA_RET_SLOT_READ = prove
 (`!(stackpointer:int64) g m.
        val stackpointer + 8 <= 2 EXP 64
        ==> read (bytes(stackpointer,8))
                 (\a. if tisa_saved stackpointer a then g a else m a) =
            read (bytes(stackpointer,8)) m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_PATCH_READ_OUTSIDE THEN
  ASM_REWRITE_TAC[tisa_saved] THEN ARITH_TAC);;

(* The slot reads in the tisa_mread form the stepping produces. *)
let TISA_MREAD_SAVED_SLOT = prove
 (`!(stackpointer:int64) k g u.
        8 <= k /\ k <= 40 /\ 40 <= val stackpointer
        ==> tisa_mread (bytes64 (word_sub stackpointer (word k)))
                       (tmem (tisa_patch (tisa_saved stackpointer) g u)) =
            tisa_mread (bytes64 (word_sub stackpointer (word k))) g`,
  SIMP_TAC[TISA_MREAD_BYTES64; TISA_PATCH_MEM; TISA_SAVED_SLOT_READ]);;

let TISA_MREAD_RET_SLOT = prove
 (`!(stackpointer:int64) g u.
        val stackpointer + 8 <= 2 EXP 64
        ==> tisa_mread (bytes64 stackpointer)
                       (tmem (tisa_patch (tisa_saved stackpointer) g u)) =
            tisa_mread (bytes64 stackpointer) (tmem u)`,
  SIMP_TAC[TISA_MREAD_BYTES64; TISA_PATCH_MEM; TISA_RET_SLOT_READ; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Deciding facts about a concrete program's region declarations.           *)
(* ------------------------------------------------------------------------- *)

let TISA_EL_CONS = prove
 (`!n h t. EL n (CONS h t) = if n = 0 then h else EL (n - 1) t`,
  INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; NOT_SUC; SUC_SUB1]);;

let TISA_DECLS_CONV =
  REWRITE_CONV[tisa_stmt_ok; tisa_instr_ok; tisa_rw; tisa_readable; LENGTH] THENC
  NUM_REDUCE_CONV THENC
  REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV(REWR_CONV TISA_EL_CONS) THENC NUM_REDUCE_CONV THENC
                       REWRITE_CONV[])) THENC
  REWRITE_CONV[FST] THENC NUM_REDUCE_CONV;;

let TISA_DECIDE_REGIONS_CONV =
  REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV(REWR_CONV TISA_EL_CONS) THENC NUM_REDUCE_CONV THENC
                       REWRITE_CONV[FST])) THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[];;

(* (!r. r < n ==> P r) <=> P 0 /\ ... /\ P (n - 1); for n = 0 (a program with no regions) the
   right-hand side is T. *)
let tisa_forall_lt n =
  let r = `r:num` and p = `P:num->bool` in
  let lhs = mk_forall(r, mk_imp(mk_binary "<" (r, mk_small_numeral n), mk_comb(p, r))) in
  if n = 0 then prove(mk_forall(p, mk_iff(lhs, `T`)), REWRITE_TAC[LT]) else
  let rhs = list_mk_conj (map (fun i -> mk_comb(p, mk_small_numeral i)) (0--(n-1))) in
  let disj = list_mk_disj (map (fun i -> mk_eq(r, mk_small_numeral i)) (0--(n-1))) in
  let lt = ARITH_RULE (mk_iff(mk_binary "<" (r, mk_small_numeral n), disj)) in
  prove(mk_forall(p, mk_iff(lhs, rhs)), GEN_TAC THEN REWRITE_TAC[lt] THEN MESON_TAC[]);;

(* Facts read (memory :> c) s = v about state s become facts of its memory,
   kept as tisa_mread so that old-state cleanup does not take them for reads
   of a state. *)
let TISA_MEMFACTS_TAC sname (asl,w) =
  let s = mk_var(sname, `:x86state`) in
  let memth = snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = mk_comb(tisa_rmem, s)) asl) in
  let compose = MATCH_MP TISA_READ_MEMORY_COMPOSE memth in
  let facts = mapfilter (fun (_,th) ->
      let c = concl th in
      if not (is_eq c) then failwith "" else
      match lhs c with
      | Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),comp)),s') when s' = s ->
          TRANS (SYM(ISPEC comp compose)) th
      | _ -> failwith "") asl in
  MAP_EVERY ASSUME_TAC facts (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The call theorem of an image, from its body theorem.                      *)
(* ------------------------------------------------------------------------- *)

let TISA_WRAPPER_TAC ctx root decls body =
  let execth = ctx.execth and n = ctx.nregions in
  let fl = tisa_forall_lt n in
  let ok = EQT_ELIM(TISA_DECLS_CONV
             (list_mk_comb(`tisa_stmt_ok:(num#num#num)list->tisa_stmt->bool`, [decls; root]))) in
  let texec = mk_comb(mk_comb(`tisa_exec`, root), `t:tisa_state`) in
  let regions_tac =
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[fl] THEN CONV_TAC TISA_DECIDE_REGIONS_CONV THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REPEAT STRIP_TAC THEN TISA_TARGET_ARITH_TAC in
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th -> if is_comb(concl th) && is_abs(rator(concl th))
                          then STRIP_ASSUME_TAC(BETA_RULE th) else failwith "") THEN
  REWRITE_TAC[tisa_x86_rel] THEN ENSURES_INIT_TAC "s0" THEN
  TISA_MEMFACTS_TAC "s0" THEN
  (* the prologue *)
  TISA_STEPS_TAC execth (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TISA_SP_SUB_NORM]) THEN
  TISA_MEMFACTS_TAC "s5" THEN
  W(fun (asl,w) ->
    let m5 = rhs(concl(snd(find (fun (_,th) -> is_eq(concl th) &&
                                   lhs(concl th) = `read memory (s5:x86state)`) asl))) in
    let t1 = mk_icomb(mk_icomb(mk_icomb(`tisa_patch:(int64->bool)->(int64->byte)->tisa_state->tisa_state`,
                                         `tisa_saved stackpointer`), m5), `t:tisa_state`) in
    (* the body starts from the caller's state patched with the saved bytes *)
    SUBGOAL_THEN (mk_comb(mk_comb(`tisa_x86_rel`, t1), `s5:x86state`)) ASSUME_TAC THENL
     [REWRITE_TAC[tisa_x86_rel; TISA_PATCH_REGS; TISA_PATCH_MEM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:int64` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[TISA_WRITE64_SP_OUTSIDE; ARITH];
      ALL_TAC] THEN
    SUBGOAL_THEN `tisa_fapart (tisa_saved stackpointer) t` ASSUME_TAC THENL
     [REWRITE_TAC[tisa_fapart; tisa_saved] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      REPEAT GEN_TAC THEN TRY DISCH_TAC THEN TISA_TARGET_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN (list_mk_comb(`tisa_frame_sep:(num#num#num)list->tisa_state->bool`, [decls; `t:tisa_state`]))
    ASSUME_TAC THENL
     [REWRITE_TAC[tisa_frame_sep; tisa_readable; tisa_rw; LENGTH; tisa_base; tisa_len; IMP_CONJ] THEN regions_tac;
      ALL_TAC] THEN
    SUBGOAL_THEN (list_mk_comb(`tisa_apart:(num#num#num)list->(int64->bool)->tisa_state->bool`,
                               [decls; `tisa_saved stackpointer`; `t:tisa_state`])) ASSUME_TAC THENL
     [REWRITE_TAC[tisa_apart; tisa_touch; tisa_saved; tisa_readable; LENGTH; tisa_base; tisa_len] THEN
      CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
      REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`; IMP_CONJ] THEN regions_tac;
      ALL_TAC] THEN
    (* the body *)
    MP_TAC(DISCH_ALL body) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[tisa_x86_runs] THEN DISCH_THEN(MP_TAC o SPEC t1) THEN
    ANTS_TAC THENL [BETA_TAC THEN ASM_SIMP_TAC[TISA_PATCH_REGS; TISA_FWORD_PATCH; ARITH]; ALL_TAC] THEN
    TISA_BIGSTEP_TAC "s6" THEN
    (* the patched run is the caller's run, patched *)
    MP_TAC(SPECL [root; decls; `tisa_saved stackpointer`; m5; `t:tisa_state`] TISA_EXEC_PATCH) THEN
    ASM_REWRITE_TAC[ok] THEN DISCH_THEN(fun eq -> RULE_ASSUM_TAC(REWRITE_RULE[eq])) THEN
    MP_TAC(ISPEC texec TISA_RESULT_CASES) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = texec
                            then RULE_ASSUM_TAC(REWRITE_RULE[th; tisa_rpatch; tisa_x86_postf]) THEN
                                 ASSUME_TAC th
                            else failwith "") THENL
     [FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`)); ALL_TAC] THEN
    (* the run stopped with state a1: the epilogue *)
    FIRST_X_ASSUM(fun th -> if is_conj(concl th) && can (find_term ((=) `RIP`)) (concl th)
                            then STRIP_ASSUME_TAC th else failwith "") THEN
    TISA_STEPS_TAC execth (7--12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TISA_SP_SUB_NORM; TISA_SP_POP_NORM]) THEN
    SUBGOAL_THEN (list_mk_comb(`tisa_keeps:(num#num#num)list->tisa_state->tisa_state->bool`,
                               [decls; `t:tisa_state`; `a1:tisa_state`])) ASSUME_TAC THENL
     [MP_TAC(SPECL [root; decls; `t:tisa_state`] TISA_KEEPS_EXEC) THEN
      ASM_REWRITE_TAC[ok; tisa_state_of];
      ALL_TAC] THEN
    (* the return address is in bytes the run keeps *)
    SUBGOAL_THEN `tisa_mread (bytes64 stackpointer) (tmem a1) = tisa_mread (bytes64 stackpointer) (tmem t)`
    ASSUME_TAC THENL
     [REWRITE_TAC[TISA_MREAD_BYTES64] THEN AP_TERM_TAC THEN REWRITE_TAC[READ_BYTES_EQ] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o REWRITE_RULE[tisa_keeps] o
                  check (fun th -> can (find_term ((=) `tisa_keeps`)) (concl th))) THEN
      REWRITE_TAC[tisa_writable; tisa_rw; LENGTH; tisa_base; tisa_len; DE_MORGAN_THM; NOT_EXISTS_THM;
                  TAUT `~(p /\ q) <=> p ==> ~q`; IMP_CONJ] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[fl] THEN CONV_TAC TISA_DECIDE_REGIONS_CONV THEN
      SUBGOAL_THEN `val(word_add stackpointer (word i):int64) = val stackpointer + i` SUBST1_TAC THENL
       [MATCH_MP_TAC TISA_VAL_OFFSET THEN TISA_TARGET_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN TISA_TARGET_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `tisa_fapart (tisa_saved stackpointer) a1` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[tisa_keeps] o
                  check (fun th -> can (find_term ((=) `tisa_keeps`)) (concl th))) THEN
      FIRST_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `tisa_fapart`)) (concl th))) THEN
      REWRITE_TAC[tisa_fapart] THEN MESON_TAC[];
      ALL_TAC] THEN
    (* the final state *)
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[TISA_MREAD_SAVED_SLOT; TISA_MREAD_RET_SLOT; ARITH] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`a0:num`; `a1:tisa_state`] THEN
    ASM_SIMP_TAC[TISA_FWORD_PATCH; ARITH; TISA_PATCH_MEM]);;

(* The call theorems proved, by image name. *)
let tisa_calls = ref ([] : (string * thm) list);;

let tisa_prove_call name =
  let (ctx, prog, pf, body) = assoc name !tisa_images in
  let _,[decls;_;root] = strip_comb prog in
  let t0 = Sys.time() in
  let th = prove(tisa_wrapper_goal ctx root pf, TISA_WRAPPER_TAC ctx root decls body) in
  Printf.printf "CALL %s: %.1fs\n%!" name (Sys.time() -. t0);
  tisa_calls := (name, th) :: !tisa_calls;
  th;;

(* ------------------------------------------------------------------------- *)
(* The image theorem. For every entry state that entry validation accepts,   *)
(* with the code, the frame, the regions and the stack placed apart, a call  *)
(* returns as the call theorem says, with the result of tisa_run.            *)
(* ------------------------------------------------------------------------- *)

let TISA_ENTRY_EXPAND_CONV =
  REWRITE_CONV[tisa_entry_ok; tisa_decls_ok; tisa_pairs_ok; tisa_init_ok; tisa_region_ok;
               tisa_pair_ok; tisa_canonical; tisa_norm; tisa_base; tisa_len; tisa_frame; FST; SND;
               distinctness "tisa_ty"] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[];;

(* The names the image hypotheses use, as frame words of the entry state. *)
let tisa_names_subst n =
  (`tregs t 0`, `fr:int64`) ::
  List.concat (map (fun r ->
    [(mk_comb(mk_comb(`tisa_fword`, `t:tisa_state`), mk_small_numeral(2*r)), mk_var("B"^string_of_int r, `:int64`));
     (mk_comb(mk_comb(`tisa_fword`, `t:tisa_state`), mk_small_numeral(2*r+1)), mk_var("L"^string_of_int r, `:int64`))])
    (0--(n-1)));;

(* What only the caller's placement can provide: code apart from the frame and
   the writable regions, and the stack. *)
(* Parses hypothesis text whose names are 64-bit words. *)
let tisa_parse_named ctx text =
  let names = "fr" :: List.concat (map (fun r -> [Printf.sprintf "B%d" r; Printf.sprintf "L%d" r])
                                       (0--(ctx.nregions-1))) in
  let ann = String.concat " /\\ " (map (fun v -> Printf.sprintf "(%s:int64) = %s" v v) names) in
  let cs = conjuncts(parse_term (ann ^ " /\\ (" ^ text ^ ")")) in
  snd(chop_list (length names) cs);;

let tisa_place_term ctx =
  let g = tisa_parse_named ctx (tisa_global_str ctx.mclen ctx.decls) in
  let st = tisa_parse_named ctx (tisa_stack_str ctx.mclen ctx.decls) in
  let code = filter (fun c -> try fst(dest_const(fst(strip_comb c))) = "nonoverlapping" with _ -> false) g in
  vsubst (tisa_names_subst ctx.nregions) (list_mk_conj (code @ st));;

let tisa_entry_goal ctx prog =
  let s = Printf.sprintf
    "tisa_entry_ok tisa_prog_here t /\\ tisa_place_here ==> ensures x86 (\\s. bytes_loaded s (word pc) %s /\\ read RIP s = word pc /\\ read RSP s = stackpointer /\\ read (memory :> bytes64 stackpointer) s = returnaddress /\\ tisa_x86_rel t s /\\ read R14 s = r14v /\\ read R15 s = r15v) (\\s. read RIP s = returnaddress /\\ read RSP s = word_add stackpointer (word 8) /\\ read RBX s = tregs t 9 /\\ read R12 s = tregs t 10 /\\ read R13 s = tregs t 11 /\\ read R14 s = r14v /\\ read R15 s = r15v /\\ (?k u. tisa_run tisa_prog_here t = TStop k u /\\ read RAX s = tisa_fword u 19 /\\ !a. ~tisa_saved stackpointer a ==> read memory s a = tmem u a)) (%s)"
    ctx.mc tisa_call_frame_str in
  vsubst [prog, `tisa_prog_here:tisa_prog`; tisa_place_term ctx, `tisa_place_here:bool`] (parse_term s);;

let TISA_POST_WEAKEN_TAC (asl,w) =
  let th = snd(find (fun (_,th) -> try fst(dest_const(fst(strip_comb(concl th)))) = "ensures"
                                   with Failure _ -> false) asl) in
  (MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC (rand(rator(concl th))) THEN
   CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC th]) (asl,w);;

(* Arithmetic from the facts that mention the goal's val atoms directly and
   split into no cases; all facts only if that fails. *)
let TISA_ENTRY_ARITH_TAC (asl,w) =
  let atoms tm = setify (find_terms (fun t -> match t with
                           Comb(Const("val",_),_) -> true | _ -> false) tm) in
  let ga = atoms w in
  let plain th = let c = concl th in
    not (can (find_term is_disj) c) && not (can (find_term (fun t -> try
      let n = fst(dest_const t) in n = "nonoverlapping" || n = "ensures" || n = "tisa_entry_ok"
      with Failure _ -> false)) c) in
  let facts = filter (fun th -> plain th && exists (fun a -> mem a ga) (atoms (concl th))) (map snd asl) in
  (FIRST [MAP_EVERY MP_TAC facts THEN ARITH_TAC; TISA_TARGET_ARITH_TAC]) (asl,w);;

let TISA_ENTRY_TAC ctx prog call_th =
  let th = INST (tisa_names_subst ctx.nregions) call_th in
  DISCH_THEN(CONJUNCTS_THEN2
    (fun eth -> ASSUME_TAC eth THEN
                MAP_EVERY ASSUME_TAC (CONJUNCTS(CONV_RULE TISA_ENTRY_EXPAND_CONV eth)))
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC th THEN ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN BETA_TAC THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TISA_ENTRY_ARITH_TAC;
    DISCH_TAC] THEN
  TISA_POST_WEAKEN_TAC THEN X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`k:num`; `u:tisa_state`] THEN
  ASM_REWRITE_TAC[tisa_run; tisa_root; tisa_then];;

let tisa_entry_thms = ref ([] : (string * thm) list);;

let tisa_prove_entry name =
  let (ctx, prog, _, _) = assoc name !tisa_images in
  let call_th = assoc name !tisa_calls in
  let t0 = Sys.time() in
  let th = prove(tisa_entry_goal ctx prog, TISA_ENTRY_TAC ctx prog call_th) in
  Printf.printf "ENTRY %s: %.1fs\n%!" name (Sys.time() -. t0);
  tisa_entry_thms := (name, th) :: !tisa_entry_thms;
  th;;
