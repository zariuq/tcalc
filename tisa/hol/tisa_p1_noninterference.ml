(* ========================================================================= *)
(* What a run reads: only its accessible regions and its frame. Changing     *)
(* memory anywhere else commutes with the run, so the run neither sees nor   *)
(* disturbs it. A subroutine call relies on this for the registers it saves  *)
(* below the stack pointer.                                                  *)
(* ========================================================================= *)

needs "tisa/hol/tisa_p1_frame.ml";;

(* Bytes a run may read or write, for state t. *)
let tisa_touch = new_definition
 `tisa_touch decls t (a:int64) <=>
    (?r. tisa_readable decls r /\ val(tisa_base t r) <= val a /\
         val a < val(tisa_base t r) + val(tisa_len t r)) \/
    (val(tregs t 0) <= val a /\ val a < val(tregs t 0) + 192)`;;

(* Memory changed to g on the addresses P. *)
let tisa_patch = new_definition
 `tisa_patch (P:int64->bool) (g:int64->byte) t =
    TState (tregs t) (\a. if P a then g a else tmem t a)`;;

let tisa_rpatch = define
 `(tisa_rpatch P g (TCont t) = TCont (tisa_patch P g t)) /\
  (tisa_rpatch P g (TStop k t) = TStop k (tisa_patch P g t))`;;

(* P lies apart from every byte the run of t may touch. *)
let tisa_apart = new_definition
 `tisa_apart decls (P:int64->bool) t <=> !a. P a ==> ~tisa_touch decls t a`;;

(* P lies apart from the frame, which does not wrap. *)
let tisa_fapart = new_definition
 `tisa_fapart (P:int64->bool) t <=>
    val(tregs t 0) + 192 <= 2 EXP 64 /\
    !a. P a ==> ~(val(tregs t 0) <= val a /\ val a < val(tregs t 0) + 192)`;;

let TISA_PATCH_REGS = prove
 (`!P g t. tregs (tisa_patch P g t) = tregs t`,
  REWRITE_TAC[tisa_patch; tregs]);;

let TISA_PATCH_MEM = prove
 (`!P g t. tmem (tisa_patch P g t) = \a. if P a then g a else tmem t a`,
  REWRITE_TAC[tisa_patch; tmem]);;

let TISA_SETFWORD_REGS = prove
 (`!j v t. tregs (tisa_setfword j v t) = tregs t`,
  REWRITE_TAC[tisa_setfword; tisa_store; tregs]);;

let TISA_FAPART_SETFWORD = prove
 (`!P j v t. tisa_fapart P (tisa_setfword j v t) <=> tisa_fapart P t`,
  REWRITE_TAC[tisa_fapart; TISA_SETFWORD_REGS]);;

let TISA_APART_FAPART = prove
 (`!decls P t. tisa_frame_sep decls t /\ tisa_apart decls P t ==> tisa_fapart P t`,
  REWRITE_TAC[tisa_frame_sep; tisa_apart; tisa_fapart; tisa_touch] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Reads and writes apart from the patch.                                    *)
(* ------------------------------------------------------------------------- *)

let TISA_READ_PATCH = prove
 (`!P g t (a:int64) w.
        val a + w <= 2 EXP 64 /\ (!b. val a <= val b /\ val b < val a + w ==> ~P b)
        ==> tisa_read (tisa_patch P g t) a w = tisa_read t a w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_read; TISA_PATCH_MEM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[READ_BYTES_EQ] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `~(P(word_add a (word k):int64))` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `val(word_add a (word k):int64) = val a + k` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let TISA_STORE_PATCH = prove
 (`!P g t (a:int64) w v.
        val a + w <= 2 EXP 64 /\ (!b. val a <= val b /\ val b < val a + w ==> ~P b)
        ==> tisa_store a w v (tisa_patch P g t) = tisa_patch P g (tisa_store a w v t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[tisa_store; tisa_patch; tregs; tmem; injectivity "tisa_state"; FUN_EQ_THM] THEN
  X_GEN_TAC `b:int64` THEN BETA_TAC THEN
  ASM_CASES_TAC `(P:int64->bool) b` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(val(a:int64) <= val(b:int64) /\ val b < val a + w)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[TISA_WRITE_BYTES_OUTSIDE];
    REWRITE_TAC[WRITE_BYTES] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

let TISA_SETREG_PATCH = prove
 (`!P g t d v. tisa_setreg d v (tisa_patch P g t) = tisa_patch P g (tisa_setreg d v t)`,
  REWRITE_TAC[tisa_setreg; tisa_patch; tregs; tmem]);;

(* Frame word i, for i below 24, lies in the frame. *)
let TISA_FRAME_WORD_RANGE = prove
 (`!P t i b. tisa_fapart P t /\ i < 24 /\
             val(word_add (tregs t 0) (word(8 * i)):int64) <= val b /\
             val b < val(word_add (tregs t 0) (word(8 * i)):int64) + 8
             ==> ~P b`,
  REWRITE_TAC[tisa_fapart] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add (tregs t 0) (word(8 * i)):int64) = val(tregs t 0) + 8 * i`
  ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:int64` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let TISA_FWORD_PATCH = prove
 (`!P g t i. tisa_fapart P t /\ i < 24
             ==> tisa_fword (tisa_patch P g t) i = tisa_fword t i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_fword; tisa_frame; TISA_PATCH_REGS] THEN
  MATCH_MP_TAC TISA_READ_PATCH THEN CONJ_TAC THENL
   [SUBGOAL_THEN `val(word_add (tregs t 0) (word(8 * i)):int64) = val(tregs t 0) + 8 * i`
    SUBST1_TAC THENL
     [MATCH_MP_TAC TISA_VAL_OFFSET THEN RULE_ASSUM_TAC(REWRITE_RULE[tisa_fapart]) THEN ASM_ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[tisa_fapart]) THEN ASM_ARITH_TAC];
    ASM_MESON_TAC[TISA_FRAME_WORD_RANGE]]);;

let TISA_SETFWORD_PATCH = prove
 (`!P g t j v. tisa_fapart P t /\ j < 24
               ==> tisa_setfword j v (tisa_patch P g t) = tisa_patch P g (tisa_setfword j v t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_setfword; tisa_frame; TISA_PATCH_REGS] THEN
  MATCH_MP_TAC TISA_STORE_PATCH THEN CONJ_TAC THENL
   [SUBGOAL_THEN `val(word_add (tregs t 0) (word(8 * j)):int64) = val(tregs t 0) + 8 * j`
    SUBST1_TAC THENL
     [MATCH_MP_TAC TISA_VAL_OFFSET THEN RULE_ASSUM_TAC(REWRITE_RULE[tisa_fapart]) THEN ASM_ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[tisa_fapart]) THEN ASM_ARITH_TAC];
    ASM_MESON_TAC[TISA_FRAME_WORD_RANGE]]);;

let TISA_FAIL_PATCH = prove
 (`!P g t k. tisa_fapart P t
             ==> tisa_fail k (tisa_patch P g t) = tisa_rpatch P g (tisa_fail k t)`,
  SIMP_TAC[tisa_fail; tisa_rpatch; TISA_SETFWORD_PATCH; TISA_FAPART_SETFWORD;
           ARITH_RULE `18 < 24 /\ 19 < 24`]);;

let TISA_FINISH_PATCH = prove
 (`!P g t out v. tisa_fapart P t
                 ==> tisa_finish out v (tisa_patch P g t) = tisa_rpatch P g (tisa_finish out v t)`,
  SIMP_TAC[tisa_finish; tisa_rpatch; TISA_SETFWORD_PATCH; TISA_FAPART_SETFWORD;
           ARITH_RULE `18 < 24 /\ 19 < 24`]);;

let TISA_FUND_PATCH = prove
 (`!P g t u. tisa_fapart P t
             ==> tisa_fund u (tisa_patch P g t) = tisa_rpatch P g (tisa_fund u t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_fund] THEN
  ASM_SIMP_TAC[TISA_FWORD_PATCH; ARITH_RULE `20 < 24 /\ 21 < 24`] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[TISA_FAIL_PATCH; TISA_SETFWORD_PATCH; tisa_rpatch; ARITH_RULE `21 < 24`]);;

(* ------------------------------------------------------------------------- *)
(* Region bounds, apartness and keeping.                                     *)
(* ------------------------------------------------------------------------- *)

(* A region's bounds are frame words 2r and 2r + 1. *)
let TISA_BOUNDS_PATCH = prove
 (`!P g t r. tisa_fapart P t /\ r < 12
             ==> tisa_base (tisa_patch P g t) r = tisa_base t r /\
                 tisa_len (tisa_patch P g t) r = tisa_len t r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_base; tisa_len] THEN
  MATCH_MP_TAC TISA_FWORD_PATCH THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let TISA_READABLE_SMALL = prove
 (`!decls t r. tisa_frame_sep decls t /\ tisa_readable decls r ==> r < 12`,
  REWRITE_TAC[tisa_frame_sep; tisa_readable] THEN ARITH_TAC);;

(* Bytes inside an accessible region lie apart from the patch. *)
let TISA_REGION_APART = prove
 (`!decls P t r b.
        tisa_apart decls P t /\ tisa_readable decls r /\
        val(tisa_base t r) <= val b /\ val b < val(tisa_base t r) + val(tisa_len t r)
        ==> ~P b`,
  REWRITE_TAC[tisa_apart; tisa_touch] THEN MESON_TAC[]);;

(* Keeping preserves apartness: v0 and every region's words are kept. *)
let TISA_KEEPS_APART = prove
 (`!decls P t t'.
        tisa_frame_sep decls t /\ tisa_keeps decls t t' /\ tisa_apart decls P t
        ==> tisa_apart decls P t'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `tregs t' 0 = tregs t 0 /\
                !r. tisa_readable decls r
                    ==> tisa_base t' r = tisa_base t r /\ tisa_len t' r = tisa_len t r`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[tisa_keeps; TISA_KEEPS_REGIONS]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tisa_apart; tisa_touch]) THEN
  REWRITE_TAC[tisa_apart; tisa_touch] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Instructions.                                                             *)
(* ------------------------------------------------------------------------- *)

let TISA_RHS_PATCH = prove
 (`!P g t rhs. tisa_rhs (tisa_patch P g t) rhs = tisa_rhs t rhs`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC tisa_operand_INDUCT THEN
  REWRITE_TAC[tisa_rhs; TISA_PATCH_REGS]);;

let TISA_INDEX_PATCH = prove
 (`!P g t i. tisa_index (tisa_patch P g t) i = tisa_index t i`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[tisa_index; TISA_PATCH_REGS]);;

(* An access inside an accessible region lies apart from the patch. *)
let TISA_INSIDE_APART = prove
 (`!decls P t r e w.
        tisa_frame_sep decls t /\ tisa_apart decls P t /\ tisa_readable decls r /\
        tisa_inside t r e w
        ==> val(iword e:int64) + w <= 2 EXP 64 /\
            !b. val(iword e:int64) <= val b /\ val b < val(iword e:int64) + w ==> ~P b`,
  REWRITE_TAC[tisa_inside] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:int`; `w:num`; `tisa_base t r`; `tisa_len t r`] TISA_IWORD_RANGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[TISA_SEP_BOUND]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:int64` THEN DISCH_TAC THEN
  MATCH_MP_TAC(SPECL [`decls:(num#num#num)list`; `P:int64->bool`; `t:tisa_state`; `r:num`]
                     TISA_REGION_APART) THEN
  ASM_MESON_TAC[]);;

let TISA_INSIDE_PATCH = prove
 (`!P g t r e w. tisa_fapart P t /\ r < 12
                 ==> (tisa_inside (tisa_patch P g t) r e w <=> tisa_inside t r e w)`,
  SIMP_TAC[tisa_inside; TISA_BOUNDS_PATCH]);;

let TISA_EA_PATCH = prove
 (`!P g t p off. tisa_ea (tisa_patch P g t) p off = tisa_ea t p off`,
  REWRITE_TAC[tisa_ea; TISA_PATCH_REGS]);;

let TISA_ADDR_MID_PATCH = prove
 (`!P g t p i s. tisa_addr_mid (tisa_patch P g t) p i s = tisa_addr_mid t p i s`,
  REWRITE_TAC[tisa_addr_mid; TISA_PATCH_REGS; TISA_INDEX_PATCH]);;

let TISA_READ_INSIDE_PATCH = prove
 (`!decls P g t r e w.
        tisa_frame_sep decls t /\ tisa_apart decls P t /\ tisa_readable decls r /\
        tisa_inside t r e w
        ==> tisa_read (tisa_patch P g t) (iword e) w = tisa_read t (iword e) w`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_READ_PATCH THEN
  MATCH_MP_TAC TISA_INSIDE_APART THEN ASM_MESON_TAC[]);;

let TISA_STORE_INSIDE_PATCH = prove
 (`!decls P g t r e w v.
        tisa_frame_sep decls t /\ tisa_apart decls P t /\ tisa_readable decls r /\
        tisa_inside t r e w
        ==> tisa_store (iword e) w v (tisa_patch P g t) =
            tisa_patch P g (tisa_store (iword e) w v t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_STORE_PATCH THEN
  MATCH_MP_TAC TISA_INSIDE_APART THEN ASM_MESON_TAC[]);;

(* For each region the instruction names, r < 12; for each in-bounds access
   assumed, rewrite patched reads and stores there. *)
let TISA_SMALL_TAC (asl,w) =
  let rs = mapfilter (fun (_,th) ->
      let f,args = strip_comb(concl th) in
      let n = fst(dest_const f) in
      if n = "tisa_readable" || n = "tisa_rw" then el 1 args else failwith "") asl in
  MAP_EVERY (fun r ->
      SUBGOAL_THEN (mk_binary "<" (r, `12`)) ASSUME_TAC THENL
       [ASM_MESON_TAC[TISA_READABLE_SMALL; TISA_RW_READABLE]; ALL_TAC]) rs (asl,w);;

let TISA_ACCESS_PATCH_TAC (asl,w) =
  let ins = mapfilter (fun (_,th) ->
      let f,args = strip_comb(concl th) in
      if fst(dest_const f) = "tisa_inside" then args else failwith "") asl in
  MAP_EVERY (fun args ->
      let [st;r;e;wd] = args in
      let tac th = MP_TAC(SPECL [`decls:(num#num#num)list`; `P:int64->bool`; `g:int64->byte`; st; r; e; wd] th) THEN
                   ASM_SIMP_TAC[TISA_RW_READABLE] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) in
      TRY(tac TISA_READ_INSIDE_PATCH) THEN TRY(tac TISA_STORE_INSIDE_PATCH)) ins (asl,w);;

let TISA_INSTR_PATCH = prove
 (`!decls i t P g.
        tisa_instr_ok decls i /\ tisa_frame_sep decls t /\ tisa_apart decls P t
        ==> tisa_instr i (tisa_patch P g t) = tisa_rpatch P g (tisa_instr i t)`,
  GEN_TAC THEN MATCH_MP_TAC tisa_instr_INDUCT THEN
  REWRITE_TAC[tisa_instr_ok] THEN REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `tisa_fapart (P:int64->bool) t` ASSUME_TAC THENL
    [ASM_MESON_TAC[TISA_APART_FAPART]; ALL_TAC]) THEN
  TISA_SMALL_TAC THEN REWRITE_TAC[tisa_instr] THEN
  ASM_SIMP_TAC[TISA_PATCH_REGS; TISA_RHS_PATCH; TISA_EA_PATCH; TISA_ADDR_MID_PATCH;
               TISA_INSIDE_PATCH; TISA_FWORD_PATCH] THEN
  REPEAT(COND_CASES_TAC THEN TRY TISA_ACCESS_PATCH_TAC) THEN
  ASM_SIMP_TAC[TISA_SETREG_PATCH; TISA_FAIL_PATCH; tisa_rpatch] THEN
  (* splitting a condition already decided leaves contradictory branches *)
  FIRST_ASSUM(CONTR_TAC o REWRITE_RULE[]));;

(* ------------------------------------------------------------------------- *)
(* Statements and loops.                                                     *)
(* ------------------------------------------------------------------------- *)

let TISA_THEN_PATCH = prove
 (`!P g r f.
        (!u. r = TCont u ==> f (tisa_patch P g u) = tisa_rpatch P g (f u))
        ==> tisa_then (tisa_rpatch P g r) f = tisa_rpatch P g (tisa_then r f)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:tisa_result` TISA_RESULT_CASES) THEN
  REWRITE_TAC[tisa_rpatch; tisa_then; injectivity "tisa_result"; distinctness "tisa_result"] THEN
  MESON_TAC[]);;

(* After a step that keeps t, the result state still has t's separation and
   apartness. *)
let TISA_KEEPS_SEP_APART = prove
 (`!decls P t u.
        tisa_frame_sep decls t /\ tisa_apart decls P t /\ tisa_keeps decls t u
        ==> tisa_frame_sep decls u /\ tisa_apart decls P u`,
  MESON_TAC[TISA_KEEPS_WRITABLE; TISA_KEEPS_APART]);;

let TISA_COUNT_ITER_PATCH = prove
 (`!m decls P g f x j t.
        ~(x = 0) /\ tisa_frame_sep decls t /\ tisa_apart decls P t /\
        (!u. tisa_frame_sep decls u ==> tisa_keeps decls u (tisa_state_of (f u))) /\
        (!u. tisa_frame_sep decls u /\ tisa_apart decls P u
             ==> f (tisa_patch P g u) = tisa_rpatch P g (f u))
        ==> tisa_count_iter m f x j (tisa_patch P g t) =
            tisa_rpatch P g (tisa_count_iter m f x j t)`,
  INDUCT_TAC THEN REWRITE_TAC[tisa_count_iter; TISA_SETREG_PATCH] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[tisa_rpatch]; ALL_TAC] THEN
  ABBREV_TAC `t1 = tisa_setreg x (word j) t` THEN
  SUBGOAL_THEN `tisa_frame_sep decls t1 /\ tisa_apart decls P t1` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_KEEPS_SEP_APART THEN EXISTS_TAC `t:tisa_state` THEN
    EXPAND_TAC "t1" THEN ASM_SIMP_TAC[TISA_KEEPS_SETREG];
    ALL_TAC] THEN
  SUBGOAL_THEN `f (tisa_patch P g t1) = tisa_rpatch P g (f t1)` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC TISA_THEN_PATCH THEN X_GEN_TAC `u:tisa_state` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `tisa_frame_sep decls u /\ tisa_apart decls P u` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_KEEPS_SEP_APART THEN EXISTS_TAC `t1:tisa_state` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t1:tisa_state` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_keeps`)) (concl th) &&
      not (can (find_term ((=) `tisa_count_iter`)) (concl th)) &&
      not (can (find_term ((=) `tisa_early_iter`)) (concl th)))) THEN
    ASM_REWRITE_TAC[tisa_state_of];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                  can (find_term ((=) `tisa_count_iter`)) (concl th))) THEN
  EXISTS_TAC `decls:(num#num#num)list` THEN ASM_REWRITE_TAC[]);;

let TISA_EARLY_CHECK_PATCH = prove
 (`!P g k t h.
        tisa_fapart P t /\
        (tisa_bool (tregs t k) /\ ~(tregs t k = word 0)
         ==> h (tisa_patch P g t) = tisa_rpatch P g (h t))
        ==> tisa_early_check k (tisa_patch P g t) h = tisa_rpatch P g (tisa_early_check k t h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tisa_early_check; TISA_PATCH_REGS] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[TISA_FAIL_PATCH; tisa_rpatch] THEN
  FIRST_ASSUM(CONTR_TAC o REWRITE_RULE[]));;

let TISA_EARLY_ITER_PATCH = prove
 (`!m decls P g f x k j t.
        ~(x = 0) /\ tisa_frame_sep decls t /\ tisa_apart decls P t /\
        (!u. tisa_frame_sep decls u ==> tisa_keeps decls u (tisa_state_of (f u))) /\
        (!u. tisa_frame_sep decls u /\ tisa_apart decls P u
             ==> f (tisa_patch P g u) = tisa_rpatch P g (f u))
        ==> tisa_early_iter m f x k j (tisa_patch P g t) =
            tisa_rpatch P g (tisa_early_iter m f x k j t)`,
  INDUCT_TAC THEN REWRITE_TAC[tisa_early_iter; TISA_SETREG_PATCH] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[tisa_rpatch]; ALL_TAC] THEN
  ABBREV_TAC `t1 = tisa_setreg x (word j) t` THEN
  SUBGOAL_THEN `tisa_frame_sep decls t1 /\ tisa_apart decls P t1` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_KEEPS_SEP_APART THEN EXISTS_TAC `t:tisa_state` THEN
    EXPAND_TAC "t1" THEN ASM_SIMP_TAC[TISA_KEEPS_SETREG];
    ALL_TAC] THEN
  MATCH_MP_TAC TISA_EARLY_CHECK_PATCH THEN
  CONJ_TAC THENL [ASM_MESON_TAC[TISA_APART_FAPART]; DISCH_TAC] THEN BETA_TAC THEN
  SUBGOAL_THEN `f (tisa_patch P g t1) = tisa_rpatch P g (f t1)` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC TISA_THEN_PATCH THEN X_GEN_TAC `u:tisa_state` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `tisa_frame_sep decls u /\ tisa_apart decls P u` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_KEEPS_SEP_APART THEN EXISTS_TAC `t1:tisa_state` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t1:tisa_state` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_keeps`)) (concl th) &&
      not (can (find_term ((=) `tisa_count_iter`)) (concl th)) &&
      not (can (find_term ((=) `tisa_early_iter`)) (concl th)))) THEN
    ASM_REWRITE_TAC[tisa_state_of];
    ALL_TAC] THEN
  MATCH_MP_TAC TISA_EARLY_CHECK_PATCH THEN
  CONJ_TAC THENL [ASM_MESON_TAC[TISA_APART_FAPART]; DISCH_TAC] THEN BETA_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                  can (find_term ((=) `tisa_early_iter`)) (concl th))) THEN
  EXISTS_TAC `decls:(num#num#num)list` THEN ASM_REWRITE_TAC[]);;

(* Applies an induction hypothesis whose decls occurs only in its premises. *)
let TISA_IH_TAC =
  FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN EXISTS_TAC `decls:(num#num#num)list` THEN
                        ASM_REWRITE_TAC[] THEN NO_TAC);;

(* A run commutes with any change to memory apart from what it touches. *)
let TISA_EXEC_PATCH = prove
 (`!S decls P g t.
        tisa_stmt_ok decls S /\ tisa_frame_sep decls t /\ tisa_apart decls P t
        ==> tisa_exec S (tisa_patch P g t) = tisa_rpatch P g (tisa_exec S t)`,
  MATCH_MP_TAC tisa_stmt_INDUCT THEN REWRITE_TAC[tisa_stmt_ok; tisa_exec] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[tisa_rpatch];
    MESON_TAC[TISA_INSTR_PATCH];
    (* SEQ a0 a1 *)
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`decls:(num#num#num)list`; `P:int64->bool`; `g:int64->byte`; `t:tisa_state`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `a0:tisa_stmt`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC TISA_THEN_PATCH THEN X_GEN_TAC `u:tisa_state` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `tisa_frame_sep decls u /\ tisa_apart decls P u` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC TISA_KEEPS_SEP_APART THEN EXISTS_TAC `t:tisa_state` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`a0:tisa_stmt`; `decls:(num#num#num)list`; `t:tisa_state`] TISA_KEEPS_EXEC) THEN
      ASM_REWRITE_TAC[tisa_state_of];
      ALL_TAC] THEN
    TISA_IH_TAC;
    (* IF *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[TISA_PATCH_REGS] THEN
    SUBGOAL_THEN `tisa_fapart (P:int64->bool) t` ASSUME_TAC THENL
     [ASM_MESON_TAC[TISA_APART_FAPART]; ALL_TAC] THEN
    REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[TISA_FAIL_PATCH] THEN
    (TISA_IH_TAC ORELSE FIRST_ASSUM(CONTR_TAC o REWRITE_RULE[]));
    (* COUNT_LOOP *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[TISA_PATCH_REGS] THEN
    SUBGOAL_THEN `tisa_fapart (P:int64->bool) t` ASSUME_TAC THENL
     [ASM_MESON_TAC[TISA_APART_FAPART]; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[TISA_FAIL_PATCH] THEN
    MATCH_MP_TAC TISA_COUNT_ITER_PATCH THEN EXISTS_TAC `decls:(num#num#num)list` THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[TISA_KEEPS_EXEC]; REPEAT STRIP_TAC THEN TISA_IH_TAC];
    (* EARLY_EXIT_LOOP *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[TISA_PATCH_REGS] THEN
    SUBGOAL_THEN `tisa_fapart (P:int64->bool) t` ASSUME_TAC THENL
     [ASM_MESON_TAC[TISA_APART_FAPART]; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[TISA_FAIL_PATCH] THEN
    MATCH_MP_TAC TISA_EARLY_ITER_PATCH THEN EXISTS_TAC `decls:(num#num#num)list` THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[TISA_KEEPS_EXEC]; REPEAT STRIP_TAC THEN TISA_IH_TAC];
    (* RETURN *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[TISA_PATCH_REGS] THEN
    MATCH_MP_TAC TISA_FINISH_PATCH THEN ASM_MESON_TAC[TISA_APART_FAPART];
    (* FUND *)
    REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_FUND_PATCH THEN ASM_MESON_TAC[TISA_APART_FAPART]]);;
