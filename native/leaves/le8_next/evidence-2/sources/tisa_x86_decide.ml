(* ========================================================================= *)
(* Conditionals settled before splitting. The normal form of word arithmetic *)
(* (VAL_WORD_ADD_CASES and the like) is full of conditionals, and splitting  *)
(* on all of them costs 2^k arithmetic calls. Most are decided by the plain  *)
(* facts (no disjunction, no conditional): a pointer above its region's      *)
(* base, a sum that did not carry. Each round settles every condition the    *)
(* plain facts decide, by one arithmetic call each; only when none is        *)
(* decided does it split, on the smallest condition left, whose case then    *)
(* joins the plain facts.                                                    *)
(* ========================================================================= *)

let tisa_cond_condition t = rand(rator(rator t));;

(* The conditions of the conditionals in a term, smallest first. *)
let tisa_conditions tm =
  let cs = setify (map tisa_cond_condition (find_terms is_cond tm)) in
  let size t = length (find_terms (fun _ -> true) t) in
  map snd (sort (fun (a,_) (b,_) -> a < b) (map (fun c -> (size c, c)) cs));;

let tisa_plain_fact th =
  let c = concl th in
  not (can (find_term is_disj) c) && not (can (find_term is_cond) c) &&
  not (exists (fun v -> type_of v = `:x86state`) (frees c));;

(* c = T or c = F from the plain facts, by one arithmetic call each way. *)
let tisa_settle plain c =
  let attempt tm =
    let th = ARITH_RULE (itlist (curry mk_imp) (map concl plain) tm) in
    rev_itlist (fun f th -> MP th f) plain th in
  try Some(EQT_INTRO (attempt c)) with Failure _ ->
  try Some(EQF_INTRO (attempt (mk_neg c))) with Failure _ -> None;;

(* Rewrite with settled conditions the goal and the assumptions that have
   conditionals, but not the plain facts (one of which may be c itself). *)
let TISA_REWRITE_CONDS_TAC eqs =
  RULE_ASSUM_TAC(fun a -> if can (find_term is_cond) (concl a) then REWRITE_RULE eqs a else a) THEN
  REWRITE_TAC eqs;;

(* `handled` lists the conditions already settled or split, so that a
   conditional the rewriting cannot reach is never tried twice. *)
let rec TISA_COND_DECIDE_FROM handled (asl,w) =
  let conds = subtract (tisa_conditions (list_mk_conj (w :: map (concl o snd) asl))) handled in
  if conds = [] then ALL_TAC (asl,w) else
  let plain = filter tisa_plain_fact (map snd asl) in
  let settled = mapfilter (fun c -> match tisa_settle plain c with
                                    | Some th -> (c,th) | None -> failwith "open") conds in
  if settled <> [] then
    (TISA_REWRITE_CONDS_TAC (map snd settled) THEN
     TISA_COND_DECIDE_FROM (map fst settled @ handled)) (asl,w)
  else
    let c = hd conds in
    (ASM_CASES_TAC c THEN
     FIRST_X_ASSUM(fun th ->
       if concl th = c || concl th = mk_neg c then
         let eq = if concl th = c then EQT_INTRO th else EQF_INTRO th in
         TISA_REWRITE_CONDS_TAC [eq] THEN ASSUME_TAC th
       else failwith "not the case") THEN
     TISA_COND_DECIDE_FROM (c :: handled)) (asl,w);;

let TISA_COND_DECIDE_TAC = TISA_COND_DECIDE_FROM [];;
