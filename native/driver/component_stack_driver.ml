(* Component call-site setup for a declared private callee stack bound. *)
needs "native/driver/stack_driver_loop_tactics.ml";;

let stack_component_drv_sem = define
 `(stack_component_drv_sem reserve (progs:num->native_component) bw ctl budget cfr [] i m used
           (res:int64#num#(int64->byte)#int64) <=>
     res = (word 1, i, m, used)) /\
  (stack_component_drv_sem reserve progs bw ctl budget cfr (CONS st sts) i m used res <=>
     if val budget < val used then res = (word 3, i, m, used)
     else ?t k u. stack_drv_child reserve bw ctl budget cfr st m used t /\
                  component_entry (progs (val(EL 0 st))) t /\
                  component_run (progs (val(EL 0 st))) t = TStop k u /\
                  (if tisa_fword u 18 = word 1
                   then stack_component_drv_sem reserve progs bw ctl budget cfr sts (i + 1) (drv_after ctl st u)
                                (tisa_fword u 21) res
                   else res = (tisa_fword u 18, i, drv_after ctl st u, tisa_fword u 21)))`;;

(* The memory the caller sees: the plan's, with the receipt and the step
   that ended the plan written back to the descriptor. *)

let stack_component_step_ok = new_definition
 `stack_component_step_ok reserve (progs:num->native_component) pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw
              (st:int64 list) <=>
    LENGTH st = 18 /\ val(EL 0 st) < nl /\
    (!r. r < 9 ==> val(EL (1 + r) st) + 1 < nbw) /\
    (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\
    (!t. tregs t 0 = cfr /\
         (!r. r < 9 ==> tisa_base t r = drv_base bw st r /\ tisa_len t r = drv_len bw st r)
         ==> tisa_decls_ok t 0 (component_decls (progs (val(EL 0 st))))) /\
    (!r. tisa_readable (component_decls (progs (val(EL 0 st)))) r
         ==> stack_drv_apart reserve cfr (drv_base bw st r) (val(drv_len bw st r))) /\
    (!r a. tisa_rw (component_decls (progs (val(EL 0 st)))) r /\
           drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a
           ==> ~drv_in a (drv_base bw st r) (val(drv_len bw st r)))`;;

(* The descriptor, the plan, the binding words and the leaf table. *)

let stack_component_child_goal =
  let frame = map (fun j ->
      let x = if j = 0 then `cfr:int64` else wadd `cfr:int64` (w64n (8 * j)) in
      let v = mk_comb(list_mk_comb(`drv_fw (bw:num->int64) (ctl:int64) (budget:int64) (used:int64) (h:int64 list)`,
                                   [`M:int64->byte`]), mk_small_numeral j) in
      mk_eq(subst [x, `x:int64`] `read (memory :> bytes64 x) s`, v)) (0--23) in
  let regs = [`read RDI s = cfr`;
              `read RSI s = drv_cw ctl M (EL 12 h)`; `read RDX s = drv_cw ctl M (EL 13 h)`;
              `read RCX s = drv_cw ctl M (EL 14 h)`; `read R8 s = drv_cw ctl M (EL 15 h)`;
              `read R9 s = drv_cw ctl M (EL 16 h)`; `read RAX s = word 0`; `read RBX s = word 0`;
              `read R10 s = word 0`; `read R11 s = word 0`; `read R12 s = word 0`; `read R13 s = word 0`] in
  let hyps = [`component_ok (progs (val(EL 0 (h:int64 list))))`;
              `stack_drv_layout reserve pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc`;
              `stack_component_step_ok reserve progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw h`;
              `!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a ==> (M:int64->byte) a = m0 a`;
              `drv_code m0 (lpc(val(EL 0 (h:int64 list)))) (lmc(val(EL 0 h)))`;
              `~(val(budget:int64) < val(used:int64))`;
              `!a. ~stack_drv_stack reserve cfr a ==> read memory s a = (M:int64->byte) a`] @ regs @ frame in
  let t = `TState (drv_regs cfr ctl h M) (read memory s)` in
  let concl = list_mk_conj
    [mk_comb(mk_comb(`tisa_x86_rel`, t), `s:x86state`);
     list_mk_comb(`stack_drv_child reserve bw ctl budget cfr h M used`, [t]);
     mk_comb(`component_entry (progs (val(EL 0 (h:int64 list))))`, t);
     list_mk_comb(`component_stack_place reserve (progs (val(EL 0 (h:int64 list)))) (lmc(val(EL 0 h))) (lpc(val(EL 0 h)))`,
                  [t; `word_sub cfr (word 8):int64`]);
     `bytes_loaded s (word(lpc(val(EL 0 (h:int64 list)))):int64) (lmc(val(EL 0 h)))`] in
  list_mk_forall(
    [`reserve:num`; `progs:num->native_component`; `pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`;
     `nctl:num`; `bind:int64`; `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`;
     `lmc:num->byte list`; `bw:num->int64`; `budget:int64`; `used:int64`; `m0:int64->byte`;
     `M:int64->byte`; `h:int64 list`; `s:x86state`],
    mk_imp(list_mk_conj hyps, concl));;

if frees stack_component_child_goal <> [] then failwith "stack_component_child_goal: free variables";;

let STACK_COMPONENT_DRV_CHILD_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc`
  ASSUME_TAC THENL [ASM_MESON_TAC[STACK_DRV_LAYOUT_LEGACY];ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [stack_drv_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [stack_component_step_ok]) THEN
  ABBREV_TAC `t = TState (drv_regs cfr ctl h M) (read memory s)` THEN
  SUBGOAL_THEN `tregs t = drv_regs cfr ctl h M /\ tmem t = read memory s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[tregs; tmem]; ALL_TAC] THEN
  SUBGOAL_THEN `tregs t 0 = cfr` ASSUME_TAC THENL [ASM_REWRITE_TAC[drv_regs]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. j < 24 ==> tisa_fword t j = drv_fw bw ctl budget used h M j` ASSUME_TAC THENL
   [REWRITE_TAC[DRV_FWORD] THEN
    FIRST_ASSUM(fun th -> if concl th = `tregs t 0 = cfr` then REWRITE_TAC[th] else failwith "") THEN
    FIRST_ASSUM(fun th -> if concl th = `tmem t = read memory s` then REWRITE_TAC[th] else failwith "") THEN
    REWRITE_TAC[GSYM DRV_READ64] THEN CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[WORD_ADD_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r < 9 ==> tisa_base t r = drv_base bw h r /\ tisa_len t r = drv_len bw h r` ASSUME_TAC THENL
   [REWRITE_TAC[tisa_base; tisa_len] THEN CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[ARITH] THEN REWRITE_TAC[drv_fw; drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `tisa_fword t 20 = budget /\ tisa_fword t 21 = used` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `drv_fw`)) (concl th) &&
                             can (find_term ((=) `tisa_fword`)) (concl th)
                          then (fun g -> (W(fun (_,w) -> MP_TAC(SPEC (rand(lhs w)) th))) g) else failwith "") THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[drv_fw] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `tisa_decls_ok t 0 (component_decls (progs (val(EL 0 (h:int64 list)))))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                    can (find_term ((=) `tisa_decls_ok`)) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub cfr (word 8):int64) = val cfr - 8 /\ val(word_sub cfr (word(reserve + 8)):int64) = val cfr - (reserve + 8) /\
                word_sub (word_sub cfr (word 8)) (word reserve):int64 = word_sub cfr (word(reserve + 8))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC TISA_VAL_SP_SUB; MATCH_MP_TAC TISA_VAL_SP_SUB; CONV_TAC WORD_RULE] THEN
    MP_TAC(ASSUME `reserve + 8 <= val(cfr:int64)`) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lpc(val(EL 0 (h:int64 list))) + LENGTH(lmc(val(EL 0 h)):byte list) <= 2 EXP 64 /\
                stack_drv_apart reserve cfr (word(lpc(val(EL 0 h)))) (LENGTH(lmc(val(EL 0 h)):byte list))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
       (can (find_term ((=) `stack_drv_apart reserve cfr`)) (concl th) || can (find_term ((=) `(<=):num->num->bool`)) (concl th)) &&
       can (find_term ((=) `lmc:num->byte list`)) (concl th) && not (can (find_term ((=) `ctl:int64`)) (concl th)) &&
       not (can (find_term ((=) `d:int64`)) (concl th)))) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let STACK_COMPONENT_DRV_CHILD_MAIN_TAC =
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[tisa_x86_rel] THEN ASM_REWRITE_TAC[drv_regs] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[stack_drv_child] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[component_entry; tisa_frame] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY MP_TAC [ASSUME `val(cfr:int64) + 256 <= 2 EXP 64`] THEN ARITH_TAC;
      MAP_EVERY MP_TAC [ASSUME `~(val(budget:int64) < val(used:int64))`] THEN ARITH_TAC;
      MATCH_MP_TAC TISA_INIT_U64 THEN
      FIRST_ASSUM(fun th -> if can (find_term ((=) `component_ok`)) (concl th)
                            then MP_TAC(REWRITE_RULE[component_ok] th) else failwith "") THEN
      SIMP_TAC[]];
    ALL_TAC; ALL_TAC];;

let STACK_COMPONENT_DRV_CHILD_PLACE_TAC =
  REWRITE_TAC[component_stack_place] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN MATCH_MP_TAC STACK_DRV_CODE_NONOVERLAP THEN
    MAP_EVERY EXISTS_TAC [`reserve:num`;`cfr:int64`;`reserve + 8`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `r < 9` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if can (find_term ((=) `component_ok`)) (concl th)
                            then MP_TAC(CONJUNCT1(REWRITE_RULE[component_ok] th)) else failwith "") THEN
      UNDISCH_TAC `tisa_rw (component_decls (progs (val (EL 0 (h:int64 list))))) r` THEN
      REWRITE_TAC[tisa_rw] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC DRV_REGION_CODE THEN
    MAP_EVERY EXISTS_TAC [`pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `bind:int64`;
                          `nbw:num`; `leaves:int64`; `nl:num`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term ((=) `drv_in`)) (concl th) && can (find_term ((=) `tisa_rw`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`component_decls (progs (val(EL 0 (h:int64 list))))`; `0`; `t:tisa_state`] TISA_DECLS_OK_REGION) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `r:num`) THEN
      FIRST_ASSUM(fun th -> if concl th = `tisa_rw (component_decls (progs (val (EL 0 (h:int64 list))))) r`
                            then MP_TAC(REWRITE_RULE[tisa_rw] th) else failwith "") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; ARITH_EQ] THEN
      SUBGOAL_THEN `tisa_base t r = drv_base bw h r /\ tisa_len t r = drv_len bw h r`
         (fun th -> REWRITE_TAC[th]) THENL
       [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
           can (find_term ((=) `drv_base`)) (concl th) && can (find_term ((=) `tisa_base`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[tisa_region_ok] THEN ARITH_TAC]];
    MP_TAC(ASSUME `reserve + 8 <= val(cfr:int64)`) THEN ARITH_TAC;
    MP_TAC(ASSUME `val(cfr:int64) + 256 <= 2 EXP 64`) THEN ARITH_TAC;
    ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN MATCH_MP_TAC STACK_DRV_CODE_NONOVERLAP THEN
    MAP_EVERY EXISTS_TAC [`reserve:num`;`cfr:int64`;`0`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `reserve + 8 <= val(cfr:int64)`) THEN ARITH_TAC;
    MP_TAC(ASSUME `48 <= val(cfr:int64)`) THEN ARITH_TAC;
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `r < 9` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if can (find_term ((=) `component_ok`)) (concl th)
                            then MP_TAC(CONJUNCT1(REWRITE_RULE[component_ok] th)) else failwith "") THEN
      UNDISCH_TAC `tisa_readable (component_decls (progs (val (EL 0 (h:int64 list))))) r` THEN
      REWRITE_TAC[tisa_readable] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
       can (find_term ((=) `stack_drv_apart reserve cfr`)) (concl th) && can (find_term ((=) `tisa_readable`)) (concl th))) THEN
    ASM_REWRITE_TAC[stack_drv_apart;drv_apart] THEN
    MP_TAC(ASSUME `reserve + 8 <= val(cfr:int64)`) THEN ARITH_TAC];;

let STACK_DRV_CHILD_LOADED_TAC =
  MATCH_MP_TAC DRV_LOADED_CODE THEN EXISTS_TAC `m0:int64->byte` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~stack_drv_stack reserve cfr a` ASSUME_TAC THENL
   [MATCH_MP_TAC STACK_DRV_IN_NOT_STACK THEN
    MAP_EVERY EXISTS_TAC [`word(lpc(val(EL 0 (h:int64 list)))):int64`;
                          `LENGTH(lmc(val(EL 0 (h:int64 list))):byte list)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
     can (find_term ((=) `drv_static`)) (concl th) && can (find_term ((=) `m0:int64->byte`)) (concl th))) THEN
  REWRITE_TAC[drv_static] THEN DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `val(EL 0 (h:int64 list))` THEN
  ASM_REWRITE_TAC[];;

let STACK_COMPONENT_DRV_CHILD_OK = prove(stack_component_child_goal,
  STACK_COMPONENT_DRV_CHILD_SETUP_TAC THEN STACK_COMPONENT_DRV_CHILD_MAIN_TAC THENL [STACK_COMPONENT_DRV_CHILD_PLACE_TAC; STACK_DRV_CHILD_LOADED_TAC]);;

let stack_component_loop_goal = `!reserve progs lpc lmc nl pc cfr d plan ns ctl nctl bind nbw leaves bw stepl budget used0 m0
    rbxv rbpv r12v r13v r14v r15v.
     (!j. j < nl ==> component_ok (progs j) /\ component_stack_image reserve (progs j) (lmc j) (lpc j)) /\
     stack_drv_layout reserve pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     ALL (stack_component_step_ok reserve progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw) stepl /\
     drv_holds m0 d plan ns ctl bind leaves budget used0 stepl bw nbw lpc nl /\
     drv_code m0 pc drv_mc /\
     (!j. j < nl ==> drv_code m0 (lpc j) (lmc j))
     ==> !sts i M used.
           LENGTH sts + i = ns /\ (!j. j < LENGTH sts ==> EL j sts = EL (i + j) stepl) /\
           (!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a ==> M a = m0 a)
           ==> ensures x86
                (\s. read RIP s = word(pc + 35) /\ read RSP s = cfr /\ read R14 s = d /\
                     read RBP s = word_add plan (word(144 * i)) /\
                     read (memory :> bytes64 (word_add cfr (word 168))) s = used /\
                     read (memory :> bytes64 (word_add cfr (word 240))) s = rbxv /\
                     read (memory :> bytes64 (word_add cfr (word 232))) s = rbpv /\
                     read (memory :> bytes64 (word_add cfr (word 224))) s = r12v /\
                     read (memory :> bytes64 (word_add cfr (word 216))) s = r13v /\
                     read (memory :> bytes64 (word_add cfr (word 208))) s = r14v /\
                     read (memory :> bytes64 (word_add cfr (word 200))) s = r15v /\
                     (!a. ~stack_drv_stack reserve cfr a ==> read memory s a = M a))
                (\s. read RIP s = word(pc + 485) /\ read RSP s = cfr /\ read R14 s = d /\
                     read (memory :> bytes64 (word_add cfr (word 240))) s = rbxv /\
                     read (memory :> bytes64 (word_add cfr (word 232))) s = rbpv /\
                     read (memory :> bytes64 (word_add cfr (word 224))) s = r12v /\
                     read (memory :> bytes64 (word_add cfr (word 216))) s = r13v /\
                     read (memory :> bytes64 (word_add cfr (word 208))) s = r14v /\
                     read (memory :> bytes64 (word_add cfr (word 200))) s = r15v /\
                     ?res. stack_component_drv_sem reserve progs bw ctl budget cfr sts i M used res /\
                           read RAX s = FST res /\
                           read RBP s = word_add plan (word(144 * FST(SND res))) /\
                           read (memory :> bytes64 (word_add cfr (word 168))) s =
                             SND(SND(SND res)) /\
                           (!a. ~stack_drv_stack reserve cfr a ==> read memory s a = FST(SND(SND res)) a) /\
                           (!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a
                                ==> FST(SND(SND res)) a = m0 a))
                (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                            R12; R13; R14; R15; RBP] ,,
                 MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`;;


(* Instantiate the assumption whose conclusion is tm at the numerals ks,
   reducing numeral arithmetic, as new assumptions. *)

let STACK_COMPONENT_DRV_BASE_TAC =
  REWRITE_TAC[LENGTH; ADD_CLAUSES; CONJUNCT1 LT] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  STACK_DRV_LOADED_TAC "s0" `pc:num` `drv_mc` `522` THEN
  STACK_DRV_STATIC_READ_TAC "s0" `word_add (d:int64) (word 8)` `d:int64` `64` `8` THEN
  X86_STEPS_TAC DRV_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC] THEN
  EXISTS_TAC `(word 1:int64, ns:num, M:int64->byte, used:int64)` THEN
  ASM_REWRITE_TAC[stack_component_drv_sem];;

let STACK_COMPONENT_DRV_CONS_SETUP_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH] THEN STRIP_TAC THEN
  SUBGOAL_THEN `EL i stepl = h:int64 list /\ i < ns` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[EL; HD; ADD_CLAUSES; LT_0] THEN
      DISCH_THEN(ACCEPT_TAC o SYM);
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `stack_component_step_ok reserve progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw h`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `i:num` o GEN_REWRITE_RULE I [GSYM ALL_EL] o
      check (fun th -> can (find_term ((=) `ALL:(int64 list->bool)->(int64 list)list->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [stack_component_step_ok]) THEN
  SUBGOAL_THEN `component_ok (progs (val(EL 0 (h:int64 list)))) /\
                component_stack_image reserve (progs (val(EL 0 h))) (lmc (val(EL 0 h))) (lpc (val(EL 0 h)))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `component_stack_image reserve`)) (concl th) &&
                                                   is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val(word_sub (word_add (plan:int64) (word(144 * i))) (word_add plan (word(144 * ns)))) = 0)`
  ASSUME_TAC THENL [MATCH_MP_TAC DRV_NOT_END THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let stack_component_child_inst =
  [`reserve:num`; `progs:num->native_component`; `pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`;
   `nctl:num`; `bind:int64`; `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`;
   `lmc:num->byte list`; `bw:num->int64`; `budget:int64`; `used:int64`; `m0:int64->byte`;
   `M:int64->byte`; `h:int64 list`; `s6:x86state`];;

let STACK_COMPONENT_DRV_M3_TAC =
  SUBGOAL_THEN `!a. ~stack_drv_stack reserve cfr a ==> read memory s6 a = (M:int64->byte) a` ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    W(fun (asl,w) ->
      let th1 = find (fun th -> let c = concl th in is_forall c && can (find_term ((=) `s6:x86state`)) c &&
                                  can (find_term ((=) `mh:int64->byte`)) c) (map snd asl)
      and th2 = find (fun th -> let c = concl th in is_forall c && can (find_term ((=) `mh:int64->byte`)) c &&
                                  can (find_term ((=) `M:int64->byte`)) c) (map snd asl) in
      ASM_MESON_TAC[th1; th2; STACK_DRV_STACK_LEGACY]);
    ALL_TAC] THEN
  SUBGOAL_THEN `drv_code m0 (lpc(val(EL 0 (h:int64 list)))) (lmc(val(EL 0 h)))` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "drv_code")) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(CONV_RULE (REWRITE_CONV[drv_fw; drv_cw] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES])
                   (SPECL stack_component_child_inst STACK_COMPONENT_DRV_CHILD_OK)) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN NO_TAC; STRIP_TAC] THEN
  (* the child state, by name, before s6's facts go *)
  MAP_EVERY (fun (x,v) ->
    SUBGOAL_THEN (mk_eq(mk_comb(mk_comb(`drv_word`, `read memory s6`), x), v)) ASSUME_TAC THENL
     [REWRITE_TAC[GSYM DRV_READ64] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) drv_pushed_words THEN
  ABBREV_TAC `tc = TState (drv_regs cfr ctl h M) (read memory s6)` THEN
  SUBGOAL_THEN `tregs tc = drv_regs cfr ctl h M /\ tmem tc = read memory s6` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tc" THEN REWRITE_TAC[tregs; tmem]; ALL_TAC] THEN
  SUBGOAL_THEN `tregs tc 0 = cfr /\ tregs tc 9 = word 0 /\ tregs tc 10 = word 0 /\ tregs tc 11 = word 0`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[drv_regs] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MAP_EVERY (fun (x,v) ->
    SUBGOAL_THEN (mk_eq(mk_comb(mk_comb(`drv_word`, `tmem tc`), x), v)) ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC]) drv_pushed_words THEN
  FIRST_X_ASSUM(MP_TAC o
    SPECL [`tc:tisa_state`; `word_sub cfr (word 8):int64`;
           `word(pc + 424):int64`; `d:int64`; `word(lpc(val(EL 0 (h:int64 list)))):int64`] o
    REWRITE_RULE[component_stack_image] o
    check (fun th -> can (find_term ((=) `component_stack_image reserve`)) (concl th) && not (is_forall(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN TISA_BIGSTEP_TAC "s7";;

let STACK_COMPONENT_DRV_AFTER_STATIC_TAC x b len k =
  W(fun (asl,w) ->
    let goal = subst [x, `x:int64`] `read (memory :> bytes64 x) s7 = drv_word m0 x` in
    SUBGOAL_THEN goal ASSUME_TAC THENL
     [MATCH_MP_TAC STACK_DRV_AFTER_STATIC THEN
      MAP_EVERY EXISTS_TAC [`reserve:num`; `tc:tisa_state`; `u:tisa_state`; `component_decls (progs (val(EL 0 (h:int64 list))))`;
                            `cfr:int64`; `bw:num->int64`; `h:int64 list`; `M:int64->byte`; static_P] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MP_TAC(ISPECL [`reserve:num`; `cfr:int64`; b; len; x; k; static_P] STACK_DRV_AREA_BYTES) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN
        FIRST [FIRST_ASSUM ACCEPT_TAC; FIRST (map MATCH_ACCEPT_TAC DRV_STATIC_AREA_THS);
               MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC; DRV_ARITH_TAC];
        SIMP_TAC[]];
      ALL_TAC]);;

let STACK_COMPONENT_DRV_M4_TAC =
  SUBGOAL_THEN `tisa_keeps (component_decls (progs (val(EL 0 (h:int64 list))))) tc u` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPONENT_RUN_KEEPS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `tregs u 0 = cfr` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [tisa_keeps] o
      check (fun th -> can (find_term ((=) `tisa_keeps`)) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [stack_drv_child] o
    check (fun th -> can (find_term ((=) `stack_drv_child reserve`)) (concl th) && not(is_forall(concl th)))) THEN
  SUBGOAL_THEN `!r. r < 9 ==> tisa_base tc r = drv_base bw h r /\ tisa_len tc r = drv_len bw h r` ASSUME_TAC THENL
   [REWRITE_TAC[tisa_base; tisa_len] THEN CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[ARITH] THEN REWRITE_TAC[drv_fw; drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (component_decls (progs (val(EL 0 (h:int64 list))))) <= 9` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if can (find_term ((=) `component_ok`)) (concl th) && not(is_forall(concl th))
                          then ACCEPT_TAC(CONJUNCT1(REWRITE_RULE[component_ok] th)) else failwith "");
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_add (word_sub cfr (word 8)) (word 8):int64 = cfr`]) THEN
  STACK_COMPONENT_DRV_AFTER_STATIC_TAC `word_add (d:int64) (word 16)` `d:int64` `64` `16` THEN
  STACK_COMPONENT_DRV_AFTER_STATIC_TAC `word_add (plan:int64) (word(144 * i + 136))` `plan:int64` `144 * ns` `144 * i + 136` THEN
  W(fun (asl,w) ->
    let stp_eq = find_assum `word_add plan (word(144 * i)):int64 = stp` asl in
    FIRST_X_ASSUM(ASSUME_TAC o CONV_RULE (REWRITE_CONV[GSYM DRV_ADDR_ASSOC] THENC REWRITE_CONV[stp_eq]) o
      check (fun th -> can (find_term ((=) `word_add (plan:int64) (word(144 * i + 136))`)) (concl th) &&
                       can (find_term ((=) `s7:x86state`)) (concl th)))) THEN
  MAP_EVERY (fun j ->
    MP_TAC(SPECL [`reserve:num`; `s7:x86state`; `u:tisa_state`; `cfr:int64`; mk_small_numeral j] STACK_DRV_AFTER_FRAME) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN CONV_TAC NUM_REDUCE_CONV;
      DISCH_THEN(ASSUME_TAC o CONV_RULE(DEPTH_CONV NUM_MULT_CONV))]) [18; 19] THEN
  SUBGOAL_THEN `nonoverlapping (word pc:int64,522) (word_add ctl (word(8 * val(EL 17 (h:int64 list)))),8)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN MATCH_MP_TAC DRV_SUB_NONOVERLAP THEN
    MAP_EVERY EXISTS_TAC [`ctl:int64`; `8 * nctl`; `8 * val(EL 17 (h:int64 list))`] THEN
    SUBGOAL_THEN `val(word pc:int64) = pc` SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN DRV_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(MATCH_MP_TAC TISA_VAL_OFFSET) THEN DRV_ARITH_TAC;
    ALL_TAC];;

let STACK_COMPONENT_DRV_M5_TAC =
  W(fun (asl,w) ->
    let hp = find_assum holds_plan_tm asl and ilt = find_assum `i < ns` asl
    and hi = find_assum `EL i stepl = h:int64 list` asl
    and stp_eq = find_assum `word_add plan (word(144 * i)):int64 = stp` asl in
    let v = MP (SPECL [`i:num`; `17`] hp) (CONJ ilt (EQT_ELIM(NUM_REDUCE_CONV `17 < 18`))) in
    let v = CONV_RULE (NUM_REDUCE_CONV THENC REWRITE_CONV[hi; GSYM DRV_ADDR_ASSOC] THENC REWRITE_CONV[stp_eq]) v in
    ASSUME_TAC v) THEN
  SUBGOAL_THEN `bytes_loaded s7 (word pc) drv_mc` ASSUME_TAC THENL
   [MATCH_MP_TAC DRV_LOADED_CODE THEN EXISTS_TAC `m0:int64->byte` THEN
    REWRITE_TAC[COMPUTE_LENGTH_RULE drv_mc] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `a:int64` THEN DISCH_TAC THEN MATCH_MP_TAC STACK_DRV_AFTER_BYTE THEN
    MAP_EVERY EXISTS_TAC [`reserve:num`; `tc:tisa_state`; `u:tisa_state`; `component_decls (progs (val(EL 0 (h:int64 list))))`;
                          `cfr:int64`; `bw:num->int64`; `h:int64 list`; `M:int64->byte`; static_P] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[drv_static] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC STACK_DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [`word pc:int64`; `522`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY (fun (x,v) ->
    let k = rand(rand x) in
    SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`, x), mk_binop `(+):num->num->num` `val(cfr:int64)` k))
      ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (mk_eq(subst [x, `x:int64`] `read (memory :> bytes64 x) s7`, v)) ASSUME_TAC THENL
     [MATCH_MP_TAC STACK_DRV_AFTER_PUSHED THEN
      MAP_EVERY EXISTS_TAC [`reserve:num`; `tc:tisa_state`; `u:tisa_state`; `component_decls (progs (val(EL 0 (h:int64 list))))`;
                            `cfr:int64`; `bw:num->int64`; `h:int64 list`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN DRV_ARITH_TAC;
      ALL_TAC]) drv_pushed_words THEN
  MP_TAC(SPECL [`reserve:num`; `s7:x86state`; `u:tisa_state`; `cfr:int64`; `21`] STACK_DRV_AFTER_FRAME) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN(ASSUME_TAC o CONV_RULE(DEPTH_CONV NUM_MULT_CONV))] THEN
  SUBGOAL_THEN (subst [drv_cx, `x:int64`] `nonoverlapping (x:int64,8) (cfr,248)`) ASSUME_TAC THENL
   [MATCH_MP_TAC STACK_DRV_OUT_NONOVERLAP248 THEN EXISTS_TAC `reserve:num` THEN
    MP_TAC(ISPECL [`reserve:num`; `cfr:int64`; `ctl:int64`; `8 * nctl`; drv_cx; `8 * val(EL 17 (h:int64 list))`;
                   `\a:int64. T`] STACK_DRV_AREA_BYTES) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      FIRST [MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC; DRV_ARITH_TAC];
      SIMP_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `m1 = read memory s7` THEN
  SUBGOAL_THEN `!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a ==> m1 a = (m0:int64->byte) a`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if concl th = `read memory s7 = (m1:int64->byte)` then REWRITE_TAC[SYM th]
                          else failwith "") THEN
    MATCH_MP_TAC STACK_DRV_AFTER_BYTE THEN
    MAP_EVERY EXISTS_TAC [`reserve:num`; `tc:tisa_state`; `u:tisa_state`; `component_decls (progs (val(EL 0 (h:int64 list))))`;
                          `cfr:int64`; `bw:num->int64`; `h:int64 list`; `M:int64->byte`; static_P] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> if concl th = `read memory s7 = (m1:int64->byte)` then REWRITE_TAC[th]
                          else failwith "") THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC STACK_DRV_STATIC_NOT_STACK THEN
    MAP_EVERY EXISTS_TAC [`pc:num`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`; `nctl:num`; `bind:int64`;
                          `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`pc:num`; `cfr:int64`; `d:int64`; `stp:int64`; `ctl:int64`; `EL 17 (h:int64 list)`;
                `tisa_fword u 19`; `tisa_fword u 18`; `m1:int64->byte`; `tisa_fword u 21`;
                `rbxv:int64`; `rbpv:int64`; `r12v:int64`; `r13v:int64`; `r14v:int64`; `r15v:int64`]
               (REWRITE_RULE[SOME_FLAGS] DRV_POST)) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  TISA_BIGSTEP_TAC "s8";;

let STACK_COMPONENT_DRV_SEM_STEP_TAC =
  REWRITE_TAC[stack_component_drv_sem] THEN
  FIRST_ASSUM(fun th -> if concl th = `~(val(budget:int64) < val(used:int64))` then REWRITE_TAC[th]
                        else failwith "") THEN
  MAP_EVERY EXISTS_TAC [`tc:tisa_state`; `k:num`; `u:tisa_state`] THEN ASM_REWRITE_TAC[];;

let STACK_COMPONENT_DRV_NOTFIRED_TAC =
  DRV_COND_TAC `~(tisa_fword u 18 = word 1)` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC) THEN
  EXISTS_TAC `(tisa_fword u 18, i:num, drv_after ctl (h:int64 list) u, tisa_fword u 21)` THEN
  ASM_REWRITE_TAC[] THEN STACK_COMPONENT_DRV_SEM_STEP_TAC;;

let STACK_COMPONENT_DRV_FIRED_TAC =
  DRV_COND_TAC `tisa_fword u 18 = word 1` THEN
  SUBGOAL_THEN `word_add stp (word 144):int64 = word_add plan (word(144 * (i + 1)))` ASSUME_TAC THENL
   [EXPAND_TAC "stp" THEN REWRITE_TAC[DRV_ADDR_ASSOC] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `read RBP s8 = word_add stp (word 144)`
                          then ASSUME_TAC(REWRITE_RULE[ASSUME `word_add stp (word 144):int64 = word_add plan (word(144 * (i + 1)))`] th)
                          else failwith "") THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`; `drv_after ctl (h:int64 list) u`; `tisa_fword u 21`] o
    check (fun th -> is_forall(concl th) &&
             can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) (concl th))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ASSUME `SUC (LENGTH (t:(int64 list)list)) + i = ns`) THEN ARITH_TAC;
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `SUC j` o check (fun th -> is_forall(concl th) &&
         can (find_term ((=) `CONS (h:int64 list) t`)) (concl th))) THEN
      REWRITE_TAC[LT_SUC; EL; TL; ARITH_RULE `i + SUC j = (i + 1) + j`] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN TISA_BIGSTEP_TAC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC) THEN
  EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN ASM_REWRITE_TAC[] THEN STACK_COMPONENT_DRV_SEM_STEP_TAC;;

let STACK_COMPONENT_DRV_REFUSE_TAC =
  ENSURES_INIT_TAC "s0" THEN
  STACK_DRV_LOADED_TAC "s0" `pc:num` `drv_mc` `522` THEN
  STACK_DRV_STATIC_READ_TAC "s0" `word_add (d:int64) (word 8)` `d:int64` `64` `8` THEN
  STACK_DRV_STATIC_READ_TAC "s0" `word_add (d:int64) (word 40)` `d:int64` `64` `40` THEN
  SUBGOAL_THEN `~(val (used:int64) < val (budget:int64) \/ val(word_sub used budget) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DRV_FUEL_COND]; ALL_TAC] THEN
  X86_STEPS_TAC DRV_EXEC (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC) THEN
  EXISTS_TAC `(word 3:int64, i:num, M:int64->byte, used:int64)` THEN
  ASM_REWRITE_TAC[stack_component_drv_sem];;

let STACK_COMPONENT_DRV_LOOP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc`
  ASSUME_TAC THENL [ASM_MESON_TAC[STACK_DRV_LAYOUT_LEGACY];ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [stack_drv_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_holds]) THEN
  LIST_INDUCT_TAC THENL
   [STACK_COMPONENT_DRV_BASE_TAC;
    STACK_COMPONENT_DRV_CONS_SETUP_TAC THEN
    ASM_CASES_TAC `val(budget:int64) < val(used:int64)` THENL
     [STACK_COMPONENT_DRV_REFUSE_TAC;
      STACK_DRV_M1_TAC THEN DRV_M2_TAC THEN STACK_COMPONENT_DRV_M3_TAC THEN STACK_COMPONENT_DRV_M4_TAC THEN STACK_COMPONENT_DRV_M5_TAC THEN
      STACK_DRV_M6_COMMON_TAC THEN
      ASM_CASES_TAC `tisa_fword u 18 = word 1` THENL [STACK_COMPONENT_DRV_FIRED_TAC; STACK_COMPONENT_DRV_NOTFIRED_TAC]]];;

let STACK_COMPONENT_DRV_LOOP = prove(stack_component_loop_goal, STACK_COMPONENT_DRV_LOOP_TAC);;



let stack_component_correct_frame_goal = `!reserve progs lpc lmc nl pc cfr d plan ns ctl nctl bind nbw leaves bw stepl budget used0 m0
    ret rbxv rbpv r12v r13v r14v r15v.
     (!j. j < nl ==> component_ok (progs j) /\ component_stack_image reserve (progs j) (lmc j) (lpc j)) /\
     stack_drv_layout reserve pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     ALL (stack_component_step_ok reserve progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw) stepl /\
     drv_holds m0 d plan ns ctl bind leaves budget used0 stepl bw nbw lpc nl /\
     drv_code m0 pc drv_mc /\
     (!j. j < nl ==> drv_code m0 (lpc j) (lmc j))
     ==> ensures x86
          (\s. read RIP s = word pc /\ read RSP s = word_add cfr (word 248) /\ read RDI s = d /\
               read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
               read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
               read memory s = m0 /\
               read (memory :> bytes64 (word_add cfr (word 248))) s = ret)
          (\s. read RIP s = ret /\ read RSP s = word_add cfr (word 256) /\
               read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
               read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
               ?res. stack_component_drv_sem reserve progs bw ctl budget cfr stepl 0 m0 used0 res /\
                     read RAX s = FST res /\
                     (!a. ~stack_drv_stack reserve cfr a ==> read memory s a = drv_final d plan res a) /\
                     (!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a /\
                          ~drv_in a (word_add d (word 48)) 16
                          ==> read memory s a = m0 a))
          (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                      R12; R13; R14; R15; RBP] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`;;

let STACK_COMPONENT_DRV_TOP_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc`
  ASSUME_TAC THENL [ASM_MESON_TAC[STACK_DRV_LAYOUT_LEGACY];ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [stack_drv_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_holds]) THEN
  ASM_CASES_TAC `drv_word m0 (word_add cfr (word 248)) = (ret:int64)` THENL
   [ALL_TAC;
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `\s:x86state. F` THEN
    REWRITE_TAC[ENSURES_TRIVIAL] THEN X_GEN_TAC `s:x86state` THEN
    REWRITE_TAC[DRV_READ64] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `read memory s = (m0:int64->byte)`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
                                            can (find_term ((=) `ret:int64`)) (concl th))) THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `val(word_sub cfr (word 48):int64) = val cfr - 48` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_SP_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word pc:int64) = pc` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN DRV_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add d (word 48):int64) = val d + 48 /\
                val(word_add d (word 56):int64) = val d + 56` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`reserve:num`; `progs:num->native_component`; `lpc:num->num`; `lmc:num->byte list`; `nl:num`; `pc:num`;
                `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`; `nctl:num`; `bind:int64`;
                `nbw:num`; `leaves:int64`; `bw:num->int64`; `stepl:(int64 list)list`; `budget:int64`;
                `used0:int64`; `m0:int64->byte`; `rbxv:int64`; `rbpv:int64`; `r12v:int64`; `r13v:int64`;
                `r14v:int64`; `r15v:int64`] STACK_COMPONENT_DRV_LOOP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`stepl:(int64 list)list`; `0`; `m0:int64->byte`; `used0:int64`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ADD_CLAUSES]; DISCH_TAC];;

let STACK_COMPONENT_DRV_TOP_EPI_TAC =
  MATCH_MP_TAC(INST_TYPE [`:(int64#num#(int64->byte)#int64)#(int64->byte)`,`:B`] DRV_ENSURES_GHOST) THEN
  EXISTS_TAC
   `\(g:(int64#num#(int64->byte)#int64)#(int64->byte)) (s:x86state).
      (stack_component_drv_sem reserve progs bw ctl budget cfr stepl 0 m0 used0 (FST g) /\
       (!a. ~stack_drv_stack reserve cfr a ==> SND g a = FST(SND(SND(FST g))) a) /\
       (!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a
            ==> FST(SND(SND(FST g))) a = m0 a)) /\
      read RIP s = word(pc + 485) /\ read RSP s = cfr /\ read R14 s = d /\
      read RBP s = word_add plan (word(144 * FST(SND(FST g)))) /\ read RAX s = FST(FST g) /\
      read memory s = SND g /\
      read (memory :> bytes64 (word_add cfr (word 168))) s = SND(SND(SND(FST g))) /\
      read (memory :> bytes64 (word_add cfr (word 240))) s = rbxv /\
      read (memory :> bytes64 (word_add cfr (word 232))) s = rbpv /\
      read (memory :> bytes64 (word_add cfr (word 224))) s = r12v /\
      read (memory :> bytes64 (word_add cfr (word 216))) s = r13v /\
      read (memory :> bytes64 (word_add cfr (word 208))) s = r14v /\
      read (memory :> bytes64 (word_add cfr (word 200))) s = r15v` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN
    EXISTS_TAC `(res:int64#num#(int64->byte)#int64, read memory s)` THEN
    REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`res:int64#num#(int64->byte)#int64`; `m:int64->byte`] THEN
  BETA_TAC THEN REWRITE_TAC[FST; SND] THEN
  MATCH_MP_TAC DRV_ENSURES_PURE THEN STRIP_TAC THEN
  MP_TAC(SPECL [`pc:num`; `cfr:int64`; `d:int64`;
                `word_add plan (word(144 * FST(SND(res:int64#num#(int64->byte)#int64)))):int64`;
                `FST(res:int64#num#(int64->byte)#int64)`;
                `SND(SND(SND(res:int64#num#(int64->byte)#int64)))`;
                `rbxv:int64`; `rbpv:int64`; `r12v:int64`; `r13v:int64`; `r14v:int64`; `r15v:int64`;
                `ret:int64`; `m:int64->byte`] DRV_EPILOGUE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DRV_APART_TAC `d:int64` `64` `word pc:int64` `522` `48` `0`;
      DRV_APART_TAC `d:int64` `64` `word pc:int64` `522` `56` `0`;
      DRV_APART_TAC `word_sub cfr (word 48):int64` `304` `d:int64` `64` `48` `48`;
      DRV_APART_TAC `word_sub cfr (word 48):int64` `304` `d:int64` `64` `48` `56`];
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP DRV_ENSURES_WEAKEN)] THEN
  REPEAT CONJ_TAC THENL
   [STACK_DRV_TOP_EPI_PRE_TAC;
    STACK_DRV_TOP_EPI_POST_TAC;
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

let STACK_COMPONENT_DRV_CORRECT_FRAME = prove(stack_component_correct_frame_goal,
  STACK_COMPONENT_DRV_TOP_SETUP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN W(fun g -> EXISTS_TAC (ensures_arg 2 g)) THEN
  CONJ_TAC THENL [REWRITE_TAC[SOME_FLAGS] THEN MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN W(fun g -> EXISTS_TAC (ensures_arg 1 g)) THEN
    CONJ_TAC THENL [REWRITE_TAC[SOME_FLAGS] THEN MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [STACK_DRV_TOP_PRO_TAC; FIRST_ASSUM ACCEPT_TAC];
    STACK_COMPONENT_DRV_TOP_EPI_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The footprint. A step's leaf runs on a state whose region words are the  *)
(* step's bindings (STACK_DRV_CHILD_REGIONS); a plan changes the memory outside    *)
(* the driver's stack only in its steps' writable regions and payload words *)
(* (STACK_COMPONENT_DRV_SEM_KEEPS).                                                          *)
(* ------------------------------------------------------------------------- *)

let STACK_COMPONENT_DRV_STEP_KEEPS = prove
 (`!reserve prog bw ctl nctl budget cfr st m used t k u a.
     stack_drv_child reserve bw ctl budget cfr st m used t /\ component_ok prog /\ component_entry prog t /\
     component_run prog t = TStop k u /\
     val ctl + 8 * nctl <= 2 EXP 64 /\ val(EL 17 st) < nctl /\
     ~stack_drv_stack reserve cfr a /\
     (!r. tisa_rw (component_decls prog) r ==> ~drv_in a (drv_base bw st r) (val(drv_len bw st r))) /\
     ~drv_in a (word_add ctl (word(8 * val(EL 17 st)))) 8
     ==> drv_after ctl st u a = m a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STACK_DRV_CHILD_REGIONS) THEN
  SUBGOAL_THEN `tisa_keeps (component_decls prog) t u` MP_TAC THENL
   [MATCH_MP_TAC COMPONENT_RUN_KEEPS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[tisa_keeps] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add ctl (word(8 * val(EL 17 (st:int64 list)))):int64) =
                val ctl + 8 * val(EL 17 st)` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN
    UNDISCH_TAC `val(ctl:int64) + 8 * nctl <= 2 EXP 64` THEN UNDISCH_TAC `val(EL 17 (st:int64 list)) < nctl` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[drv_after] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `~drv_in a (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8` THEN
    ASM_REWRITE_TAC[drv_in] THEN
    UNDISCH_TAC `val(ctl:int64) + 8 * nctl <= 2 EXP 64` THEN UNDISCH_TAC `val(EL 17 (st:int64 list)) < nctl` THEN
    ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `tmem u a = tmem t a` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_writable`)) (concl th))) THEN
    MATCH_MP_TAC DRV_NOT_WRITABLE THEN
    MAP_EVERY EXISTS_TAC [`cfr:int64`; `bw:num->int64`; `st:int64 list`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ACCEPT_TAC(CONJUNCT1(REWRITE_RULE[component_ok] (ASSUME `component_ok prog`)));
      UNDISCH_TAC `~stack_drv_stack reserve cfr a` THEN REWRITE_TAC[stack_drv_stack] THEN ARITH_TAC];
    FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [stack_drv_child] o
      check (fun th -> can (find_term ((=) `stack_drv_child reserve`)) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let STACK_COMPONENT_DRV_SEM_KEEPS = prove
 (`!reserve progs bw ctl nctl budget cfr sts i m used res.
     stack_component_drv_sem reserve progs bw ctl budget cfr sts i m used res /\
     val ctl + 8 * nctl <= 2 EXP 64 /\
     (!st. MEM st sts ==> component_ok (progs (val(EL 0 st))) /\ val(EL 17 st) < nctl)
     ==> !a. ~stack_drv_stack reserve cfr a /\
             (!st r. MEM st sts /\ tisa_rw (component_decls (progs (val(EL 0 st)))) r
                     ==> ~drv_in a (drv_base bw st r) (val(drv_len bw st r))) /\
             (!st. MEM st sts ==> ~drv_in a (word_add ctl (word(8 * val(EL 17 st)))) 8)
             ==> FST(SND(SND res)) a = m a`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[stack_component_drv_sem] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_component_drv_sem; MEM] THEN
  COND_CASES_TAC THENL [STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `tc:tisa_state` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u:tisa_state` STRIP_ASSUME_TAC)))
    STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
  SUBGOAL_THEN `drv_after ctl h u a = (m:int64->byte) a` ASSUME_TAC THENL
   [MATCH_MP_TAC STACK_COMPONENT_DRV_STEP_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`reserve:num`; `progs (val(EL 0 (h:int64 list))):native_component`; `bw:num->int64`; `nctl:num`;
                          `budget:int64`; `cfr:int64`; `used:int64`; `tc:tisa_state`; `k:num`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`; `drv_after ctl h u`; `tisa_fword u 21`;
                                  `res:int64#num#(int64->byte)#int64`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `stack_component_drv_sem reserve`)) (concl th))) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a:int64`) THEN ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Two steps that both FIRED, unfolded.                                      *)
(* ------------------------------------------------------------------------- *)

let STACK_COMPONENT_DRV_SEM_TWO_FIRED = prove
 (`!reserve progs bw ctl budget cfr st1 st2 m used res.
     stack_component_drv_sem reserve progs bw ctl budget cfr [st1; st2] 0 m used res /\ FST res = word 1
     ==> ?t1 k1 u1 t2 k2 u2.
           stack_drv_child reserve bw ctl budget cfr st1 m used t1 /\
           component_entry (progs (val(EL 0 st1))) t1 /\
           component_run (progs (val(EL 0 st1))) t1 = TStop k1 u1 /\ tisa_fword u1 18 = word 1 /\
           stack_drv_child reserve bw ctl budget cfr st2 (drv_after ctl st1 u1) (tisa_fword u1 21) t2 /\
           component_entry (progs (val(EL 0 st2))) t2 /\
           component_run (progs (val(EL 0 st2))) t2 = TStop k2 u2 /\ tisa_fword u2 18 = word 1 /\
           res = (word 1, 2, drv_after ctl st2 u2, tisa_fword u2 21)`,
  let NOT_FIRED_TAC =
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `res:int64#num#(int64->byte)#int64`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `FST:int64#num#(int64->byte)#int64->int64`))
                                                 (concl th))) THEN
    ASM_REWRITE_TAC[FST] THEN CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[] in
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_component_drv_sem] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `val(budget:int64) < val(used:int64)` THEN ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN NOT_FIRED_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
       STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  ASM_CASES_TAC `tisa_fword u1 18 = word 1` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; DISCH_TAC THEN NOT_FIRED_TAC] THEN
  ASM_CASES_TAC `val(budget:int64) < val(tisa_fword u1 21)` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN NOT_FIRED_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
       STRIP_ASSUME_TAC))) THEN
  ASM_CASES_TAC `tisa_fword u2 18 = word 1` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THENL [ALL_TAC; NOT_FIRED_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t1:tisa_state`; `k1:num`; `u1:tisa_state`;
                        `t2:tisa_state`; `k2:num`; `u2:tisa_state`] THEN
  ASM_REWRITE_TAC[]);;

let STACK_COMPONENT_DRV_CORRECT = prove
 (`!reserve progs lpc lmc nl pc stackpointer d plan ns ctl nctl bind nbw leaves bw stepl budget used0 m0
    ret rbxv rbpv r12v r13v r14v r15v.
     (!j. j < nl ==> component_ok (progs j) /\ component_stack_image reserve (progs j) (lmc j) (lpc j)) /\
     stack_drv_layout reserve pc (word_sub stackpointer (word 248)) d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     ALL (stack_component_step_ok reserve progs pc (word_sub stackpointer (word 248)) d plan ns nctl bind nbw leaves nl lpc lmc bw)
         stepl /\
     drv_holds m0 d plan ns ctl bind leaves budget used0 stepl bw nbw lpc nl /\
     drv_code m0 pc drv_mc /\
     (!j. j < nl ==> drv_code m0 (lpc j) (lmc j))
     ==> ensures x86
          (\s. read RIP s = word pc /\ read RSP s = stackpointer /\ read RDI s = d /\
               read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
               read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
               read memory s = m0 /\ read (memory :> bytes64 stackpointer) s = ret)
          (\s. read RIP s = ret /\ read RSP s = word_add stackpointer (word 8) /\
               read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
               read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
               ?res. stack_component_drv_sem reserve progs bw ctl budget (word_sub stackpointer (word 248)) stepl 0 m0 used0 res /\
                     read RAX s = FST res /\
                     (!a. ~stack_drv_stack reserve (word_sub stackpointer (word 248)) a
                          ==> read memory s a = drv_final d plan res a) /\
                     (!a. drv_static pc (word_sub stackpointer (word 248)) d plan ns bind nbw leaves nl lpc lmc a /\
                          ~drv_in a (word_add d (word 48)) 16
                          ==> read memory s a = m0 a) /\
                     (!a. ~stack_drv_stack reserve (word_sub stackpointer (word 248)) a /\
                          ~drv_in a (word_add d (word 48)) 16 /\
                          (!st r. MEM st stepl /\ tisa_rw (component_decls (progs (val(EL 0 st)))) r
                                  ==> ~drv_in a (drv_base bw st r) (val(drv_len bw st r))) /\
                          (!st. MEM st stepl
                                ==> ~drv_in a (word_add ctl (word(8 * val(EL 17 st)))) 8)
                          ==> read memory s a = m0 a))
          (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                      R12; R13; R14; R15; RBP] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`reserve:num`; `progs:num->native_component`; `lpc:num->num`; `lmc:num->byte list`; `nl:num`; `pc:num`;
                `word_sub stackpointer (word 248):int64`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`;
                `nctl:num`; `bind:int64`; `nbw:num`; `leaves:int64`; `bw:num->int64`;
                `stepl:(int64 list)list`; `budget:int64`; `used0:int64`; `m0:int64->byte`; `ret:int64`;
                `rbxv:int64`; `rbpv:int64`; `r12v:int64`; `r13v:int64`; `r14v:int64`; `r15v:int64`]
               STACK_COMPONENT_DRV_CORRECT_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_sub stackpointer (word 248)) (word 248):int64 = stackpointer`;
              WORD_RULE `word_add (word_sub stackpointer (word 248)) (word 256):int64 = word_add stackpointer (word 8)`] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP DRV_ENSURES_WEAKEN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [stack_drv_layout]) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
    SUBGOAL_THEN `val(word_add d (word 48):int64) = val d + 48 /\
                  val(word_add d (word 56):int64) = val d + 56` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(a:int64) < val(d:int64) + 48 \/ val d + 64 <= val a` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
                                              can (find_term ((=) `drv_in`)) (concl th) &&
                                              can (find_term ((=) `word_add d (word 48):int64`)) (concl th))) THEN
      REWRITE_TAC[drv_in] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `drv_final`)) (concl th)
                            then REWRITE_TAC[MATCH_MP th (ASSUME `~stack_drv_stack reserve (word_sub stackpointer (word 248)) a`)]
                            else failwith "") THEN
    REWRITE_TAC[drv_final] THEN
    REPEAT(W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
           ANTS_TAC THENL
            [ASM_REWRITE_TAC[] THEN
             FIRST_ASSUM(MP_TAC o check (fun th -> is_disj(concl th) &&
                                                   can (find_term ((=) `val(a:int64)`)) (concl th))) THEN
             DRV_ARITH_TAC;
             DISCH_THEN SUBST1_TAC]) THEN
    MP_TAC(SPECL [`reserve:num`; `progs:num->native_component`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                  `word_sub stackpointer (word 248):int64`; `stepl:(int64 list)list`; `0`; `m0:int64->byte`;
                  `used0:int64`; `res:int64#num#(int64->byte)#int64`] STACK_COMPONENT_DRV_SEM_KEEPS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
      SUBGOAL_THEN `stack_component_step_ok reserve progs pc (word_sub stackpointer (word 248)) d plan ns nctl bind nbw leaves nl lpc lmc bw st`
      MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM ALL_MEM] o
          check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "ALL")) (concl th))) THEN
        DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[stack_component_step_ok] THEN STRIP_TAC THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `val(EL 0 (st:int64 list))` o
          check (fun th -> is_forall(concl th) && can (find_term ((=) `component_stack_image reserve`)) (concl th))) THEN
        ASM_SIMP_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `17` o
          check (fun th -> is_forall(concl th) && can (find_term ((=) `nctl:num`)) (concl th) &&
                           can (find_term ((=) `10`)) (concl th))) THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]];
      DISCH_THEN(MATCH_MP_TAC) THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC]);;


let component_stack_driver_theorems =
 ["STACK_COMPONENT_DRV_CHILD_OK",STACK_COMPONENT_DRV_CHILD_OK;
  "STACK_COMPONENT_DRV_LOOP",STACK_COMPONENT_DRV_LOOP;
  "STACK_COMPONENT_DRV_CORRECT_FRAME",STACK_COMPONENT_DRV_CORRECT_FRAME;
  "STACK_COMPONENT_DRV_STEP_KEEPS",STACK_COMPONENT_DRV_STEP_KEEPS;
  "STACK_COMPONENT_DRV_SEM_KEEPS",STACK_COMPONENT_DRV_SEM_KEEPS;
  "STACK_COMPONENT_DRV_SEM_TWO_FIRED",STACK_COMPONENT_DRV_SEM_TWO_FIRED;
  "STACK_COMPONENT_DRV_CORRECT",STACK_COMPONENT_DRV_CORRECT];;
