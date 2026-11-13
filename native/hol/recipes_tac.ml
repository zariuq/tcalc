(* ========================================================================= *)
(* The symbolic run of recipes (after recipes.ml): plans_abs.ml's executor   *)
(* for leaf steps; at a call, the callee's frame certificate (the shape of   *)
(* the store after the call), a case on the callee's outcome, and in the     *)
(* FIRED case its contract (a theorem, or an induction hypothesis kept out   *)
(* of the simplifier's reach under rc_hide).                                 *)
(* ========================================================================= *)

let rc_hide = new_definition `rc_hide (p:bool) <=> p`;;
let RC_HIDE th = EQ_MP (SYM(SPEC (concl th) rc_hide)) th;;
let RC_SHOW th = EQ_MP (SPEC (rand(concl th)) rc_hide) th;;
let rc_has name tm = can (find_term (fun t -> is_const t && fst(dest_const t) = name)) tm;;
let rc_is_cert tm = is_forall tm && rc_has "rc_call" tm;;
let RC_HIDE_IH_TAC =
  REPEAT(FIRST_X_ASSUM(fun th -> if rc_is_cert(concl th) then ASSUME_TAC(RC_HIDE th) else failwith "ih"));;

let RC_SEMS = pl_relw :: PL_SEMS;;
let RC_LEAF_CONV =
  GEN_REWRITE_CONV I [rc_leaf] THENC
  LAND_CONV PL_LEAF_CONV THENC
  RAND_CONV(REWRITE_CONV[pl_set] THENC DEPTH_CONV BETA_CONV THENC PL_NORM_CONV) THENC
  REWRITE_CONV[];;

(* A branch whose order facts contradict each other is closed. *)
let rc_is_order_lit tm =
  let a = if is_neg tm then dest_neg tm else tm in
  let ok t = is_var t || is_numeral t in
  try let op,args = strip_comb a in
      length args = 2 && type_of(hd args) = `:num` && ok(hd args) && ok(el 1 args) &&
      mem (fst(dest_const op)) ["<"; "<="; "="; ">"; ">="]
  with Failure _ -> false;;
let RC_PRUNE_TAC (asl,w as g) =
  let lits = filter (rc_is_order_lit o concl) (map snd asl) in
  if length lits < 2 then ALL_TAC g else
  try let th = ARITH_RULE(mk_imp(list_mk_conj(map concl lits), `F`)) in
      CONTR_TAC(MP th (end_itlist CONJ lits)) g
  with Failure _ -> ALL_TAC g;;

let RC_AFTER_TAC =
  PL_SUBST_ALL_TAC THEN REWRITE_TAC[ARITH_EQ; RC_OUTC] THEN PL_NEG_EQ_TAC THEN RC_PRUNE_TAC;;

(* Forward facts: lemmas  A1 /\ .. /\ An ==> C  whose premises match facts *)
(* of the branch give C (numerals reduced, as the executor leaves facts).  *)
let RC_FORWARDS = ref ([]:thm list);;
let RC_FORWARD_TAC (asl,w as g) =
  let asms = filter (fun th -> not(is_const_app "rc_hide" (concl th))) (map snd asl) in
  let rec go th =
    if not(is_imp(snd(strip_forall(concl th)))) then [th] else
    flat(mapfilter (fun asm -> go (MATCH_MP th asm)) asms) in
  let news = flat(map (fun l -> go (GEN_ALL(CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[IMP_CONJ] (SPEC_ALL l)))))
                  (!RC_FORWARDS)) in
  let known = map concl asms in
  let rec uniq l = match l with [] -> [] | th::t ->
     if exists (aconv (concl th)) known || exists (fun u -> aconv (concl u) (concl th)) t then uniq t
     else th :: uniq t in
  MAP_EVERY STRIP_ASSUME_TAC (uniq news) g;;

(* Modus ponens among the facts of the branch. *)
let RC_MP_ASM_TAC (asl,w as g) =
  let asms = map snd asl in
  let known = map concl asms in
  let news = mapfilter (fun th ->
     let c = concl th in
     if is_imp c && exists (aconv (lhand c)) known && not(exists (aconv (rand c)) known)
     then MP th (find (fun a -> aconv (concl a) (lhand c)) asms) else failwith "") asms in
  MAP_EVERY STRIP_ASSUME_TAC news g;;

let RC_LEAFSTEP_TAC =
  GEN_REWRITE_TAC LAND_CONV [RC_EXEC_STEP] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV(fun t -> if is_const_app "rc_leaf" t then RC_LEAF_CONV t else failwith "leaf"))) THEN
  CONV_TAC(LAND_CONV PL_NORM_CONV) THEN
  REWRITE_TAC[FST; SND; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let raw = CONV_RULE (REWRITE_CONV RC_SEMS THENC PL_NORM_CONV) (CONJUNCT1 th) in
    PL_BOUNDS_TAC (concl raw) THEN
    W(fun (asl,_) ->
      let leaf = CONV_RULE (SIMP_CONV (!PL_SIMPS @ map snd asl) THENC PL_NORM_CONV THENC
                            REWRITE_CONV[PL_COND_DISJ; DE_MORGAN_THM]) raw in
      MP_TAC(CONJUNCT2 th) THEN PL_ASM_TCL leaf)) THEN
  RC_AFTER_TAC THEN RC_FORWARD_TAC;;

(* The frame of a clause: the argument words and the constants 0..6. *)
let RC_FRAME_TAC th =
  let th' = CONV_RULE(REWRITE_CONV[rc_frame] THENC DEPTH_CONV EL_CONV) th in
  let low = CONJUNCT1 th' in
  let lows = map (fun n -> let s = SPEC (mk_small_numeral n) low in
                            MP s (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl s))))) [0;1;2;3;4;5;6] in
  MAP_EVERY ASSUME_TAC (CONJUNCTS th' @ lows);;

let RC_CALL_CONS_TAC =
  GEN_REWRITE_TAC LAND_CONV [RC_CALL_CONS] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 RC_FRAME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC I [IMP_CONJ];;

(* A callee's entry frame facts are dropped once nothing else mentions the *)
(* frame (a plan's own control words, which its invariant names, stay).    *)
let rc_is_frame_fact tm =
  let is_fv t = is_var t && type_of t = `:num->num` in
  (is_eq tm && is_comb(lhs tm) && is_fv(rator(lhs tm)) && is_numeral(rand(lhs tm))) ||
  (is_forall tm && (let _,b = dest_forall tm in
                    is_imp b && is_eq(rand b) && is_comb(lhs(rand b)) && is_fv(rator(lhs(rand b)))));;
let RC_DROP_FRAMES_TAC (asl,w as g) =
  let ths = map snd asl in
  let others = filter (fun th -> not(rc_is_frame_fact(concl th))) ths in
  let live v = vfree_in v w || exists (fun th -> vfree_in v (concl th)) others in
  let dead th = let c = concl th in rc_is_frame_fact c &&
     exists (fun v -> type_of v = `:num->num` && not(live v)) (frees c) in
  (REPEAT(FIRST_X_ASSUM(fun th -> if dead th then ALL_TAC else failwith "live"))) g;;

(* Reads of control words are evaluated (pl_set f p v n at numerals p, n);  *)
(* the updates themselves stay folded, as plans_abs.ml's executor leaves them. *)
let PL_SET_APP = prove
 (`!f p v n. pl_set f p v n = if n = p then v else (f:num->num) n`,
  REWRITE_TAC[pl_set]);;
let RC_EQ_TAC =
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN PL_ASM_TCL THEN RC_AFTER_TAC THEN
  REWRITE_TAC[PL_SET_APP] THEN CONV_TAC(DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[RC_OUTC] THEN
  RC_DROP_FRAMES_TAC;;

(* ------------------------------------------------------------------------- *)
(* Certificates at a call.                                                   *)
(* A certificate is  !vs. A1 /\ ... /\ rc_call P recipe args ns stk res /\ ... ==> C. *)
(* Its run is matched against the callee's run; variables the run does not  *)
(* fix are found by matching the other premises against the facts of the   *)
(* branch; premises not among the facts are left to RC_SIDE_TAC.           *)
(* ------------------------------------------------------------------------- *)
let RC_SIDE_LEMMAS = ref [LENGTH];;
let rc_cert_norm th =
  let th1 = REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] th in
  CONV_RULE NUM_REDUCE_CONV (CONV_RULE(TRY_CONV FORALL_UNWIND_CONV) th1);;
let rc_instance plain run cert =
  let cert = rc_cert_norm cert in
  let fixed = frees(concl cert) @ freesl(hyp cert) in
  let vs,_ = strip_forall(concl cert) in
  let vs' = map (genvar o type_of) vs in
  let th0 = SPECL vs' cert in
  let pat = find (is_const_app "rc_call") (conjuncts(lhand(concl th0))) in
  let th1 = INSTANTIATE (term_match fixed pat (concl run)) th0 in
  let rec fill th =
    let left = filter (fun v -> vfree_in v (concl th)) vs' in
    if left = [] then th else
    let ants = filter (fun a -> exists (fun v -> vfree_in v a) left) (conjuncts(lhand(concl th))) in
    let inst = tryfind (fun a ->
      let consts = subtract (frees a) left in
      tryfind (fun asm -> term_match (consts @ fixed) a (concl asm)) plain) ants in
    fill (INSTANTIATE inst th) in
  fill th1;;
let RC_SIDE_TAC =
  FIRST_ASSUM ACCEPT_TAC ORELSE
  (W(fun (asl,_) -> ASM_SIMP_TAC (!RC_SIDE_LEMMAS)) THEN NO_TAC) ORELSE
  (REWRITE_TAC (!RC_SIDE_LEMMAS) THEN ASM_ARITH_TAC) ORELSE ALL_TAC;;
(* Apply every certificate that matches the callee's run, in order (a frame *)
(* certificate first: it fixes the shape of the store the later ones match). *)
let RC_USE_ONE_TAC cert (asl,w as g) =
  let asms = map snd asl in
  let runs = filter (fun th -> is_const_app "rc_call" (concl th)) asms in
  let plain = filter (fun th -> not(is_const_app "rc_hide" (concl th))) asms in
  match mapfilter (fun run -> run, rc_instance plain run cert) runs with
    [] -> ALL_TAC g
  | (run,th)::_ ->
      (MP_TAC th THEN ANTS_TAC THENL
        [REPEAT CONJ_TAC THEN (ACCEPT_TAC run ORELSE RC_SIDE_TAC);
         DISCH_THEN PL_ASM_TCL THEN RC_AFTER_TAC]) g;;
let RC_USE_ALL_TAC certs =
  W(fun (asl,_) ->
    let hidden = mapfilter (fun (_,th) -> if is_const_app "rc_hide" (concl th) then RC_SHOW th
                                          else failwith "") asl in
    MAP_EVERY RC_USE_ONE_TAC (certs @ hidden));;

(* Conditional facts  !I1 I2. A1 /\ .. ==> C  whose premises match facts of *)
(* the branch are instantiated.                                              *)
let RC_INST_TAC (asl,w as g) =
  let asms = filter (fun th -> not(is_const_app "rc_hide" (concl th))) (map snd asl) in
  let one th =
    let c = concl th in
    if not(is_forall c) then failwith "" else
    let vs,body = strip_forall c in
    if not(is_imp body) || not(exists (fun v -> type_of v = `:num list`) vs) then failwith "" else
    let ants = conjuncts(lhand body) in
    let rec solve inst ants =
      match ants with [] -> inst | a::rest ->
        let a' = vsubst inst a in
        if intersect (frees a') vs = [] then solve inst rest else
        let i = tryfind (fun asm -> let (_,ins,_) = term_match (subtract (frees a') vs) a' (concl asm) in ins) asms in
        solve (i @ inst) rest in
    let inst = solve [] ants in
    let th' = SPECL (map (fun v -> try rev_assoc v inst with Failure _ -> failwith "") vs) th in
    MP th' (end_itlist CONJ (map (fun a -> find (fun asm -> aconv (concl asm) a) asms) (conjuncts(lhand(concl th'))))) in
  MAP_EVERY STRIP_ASSUME_TAC (mapfilter one asms) g;;

let rc_call_conv cR cA =
  RATOR_CONV(RATOR_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV cR)))) THENC
  RATOR_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV cA)));;
(* A call step: frame certificates, the outcome's case, fired certificates. *)
let RC_CALLSTEP_TAC frames fireds =
  GEN_REWRITE_TAC LAND_CONV [RC_EXEC_STEP] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV(GEN_REWRITE_CONV I [rc_args]))) THEN
  CONV_TAC(LAND_CONV PL_NORM_CONV) THEN REWRITE_TAC[] THEN
  W(fun (asl,_) ->
    let asms = map snd asl in
    let cA = REWRITE_CONV (pl_set :: asms) THENC DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV THENC
             REWRITE_CONV asms in
    CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV asms) THENC
                       ONCE_DEPTH_CONV(fun t -> if is_const_app "rc_call" t &&
                                                    length(snd(strip_comb t)) = 6
                                                 then rc_call_conv (REWRITE_CONV asms) cA t
                                                 else failwith "call")))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `rc_k:num` THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN MP_TAC(CONJUNCT2 th)) THEN
  RC_USE_ALL_TAC frames THEN
  ASM_CASES_TAC `rc_k = 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    RC_USE_ALL_TAC fireds THEN RC_INST_TAC THEN RC_MP_ASM_TAC THEN RC_FORWARD_TAC;
    ASM_REWRITE_TAC[]];;

(* The run: clauses, steps, calls, ends. It stops at a goal it does not know. *)
let rc_is_end a =
  (is_eq a && is_pair(rand a)) ||
  (is_conj a && forall (fun c -> is_eq c && (is_var(lhs c) || is_pair(lhs c))) (conjuncts a));;
let rec RC_RUN_TAC frames fireds g =
  let w = snd g in
  if not(is_imp w) then ALL_TAC g else
  let a = lhand w in
  if is_const_app "rc_call" a then
    let cls = el 1 (snd(strip_comb a)) in
    if is_const cls && fst(dest_const cls) = "NIL" then
      (GEN_REWRITE_TAC LAND_CONV [RC_CALL_NIL] THEN RC_EQ_TAC THEN RC_RUN_TAC frames fireds) g
    else if is_cons cls then (RC_CALL_CONS_TAC THEN RC_RUN_TAC frames fireds) g
    else ALL_TAC g
  else if is_const_app "rc_exec" a then
    let sts = el 1 (snd(strip_comb a)) in
    if is_const sts && fst(dest_const sts) = "NIL" then
      (GEN_REWRITE_TAC LAND_CONV [RC_EXEC_NIL] THEN RC_EQ_TAC THEN RC_RUN_TAC frames fireds) g
    else if is_cons sts then
      let opc = hd(dest_list(fst(dest_cons sts))) in
      if opc = `word 32:int64` then (RC_CALLSTEP_TAC frames fireds THEN RC_RUN_TAC frames fireds) g
      else (RC_LEAFSTEP_TAC THEN RC_RUN_TAC frames fireds) g
    else ALL_TAC g
  else if rc_is_end a then (RC_EQ_TAC THEN RC_RUN_TAC frames fireds) g
  else ALL_TAC g;;

(* Add the unfolded form of the facts the given definitions unfold. *)
let RC_UNFOLD_ASM_TAC ths (asl,w as g) =
  let news = mapfilter (fun (_,th) ->
     if is_const_app "rc_hide" (concl th) then failwith "" else
     CONV_RULE(CHANGED_CONV(REWRITE_CONV ths)) th) asl in
  MAP_EVERY STRIP_ASSUME_TAC news g;;

(* The start of a certificate's proof: premises to facts (folded and        *)
(* unfolded), induction hypotheses hidden, the recipe's clauses in the run.  *)
let RC_CERT_START_TAC recipe_def unfolds =
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(W(fun (_,w) -> if is_imp w && not(is_const_app "rc_call" (lhand w)) then STRIP_TAC else NO_TAC)) THEN
  RC_HIDE_IH_TAC THEN RC_UNFOLD_ASM_TAC unfolds THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [recipe_def];;
