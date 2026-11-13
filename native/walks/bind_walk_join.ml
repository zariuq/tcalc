(* ========================================================================= *)
(* Joins the x86 image theorem of bind_walk (from the t-ISA generator,       *)
(* proved in the same process from bind_walk.hol) with the functional        *)
(* theorem BW_RUN (tcalc/native/hol/bind_walk.ml): the native code's run     *)
(* ends in a state whose p1 run satisfies bw_result, and the x86 memory      *)
(* equals that state's memory outside the saved stack.                       *)
(*                                                                           *)
(* Run by tcalc/tisa/hol/run_x86_evidence.sh as its DRIVER, after the       *)
(* record. Also the audit of bind_walk.ml in the same process: every         *)
(* theorem it states is listed with its hypothesis count.                   *)
(* ========================================================================= *)

loadt "native/hol/bind_walk.ml";;

(* The proved program is the image's program, term for term. *)
let BIND_WALK_IMAGE_PROG = (fun (_,p,_,_) -> p) (assoc "bind_walk" !tisa_images);;
if rand(concl BIND_WALK_TERM) <> BIND_WALK_IMAGE_PROG
then failwith "JOIN bind_walk: the proved program is not the image's program";;

(* The image theorem for bind_walk, its postcondition strengthened by the    *)
(* result of every run (BW_RUN).                                             *)
let BIND_WALK_X86 =
  let eth = REWRITE_RULE[GSYM BIND_WALK_TERM] (assoc "bind_walk" !tisa_entry_thms) in
  let ant,ens = dest_imp(concl eth) in
  let (_,args) = strip_comb ens in
  let q = el 2 args in
  let sv = genvar `:x86state` in
  let extra = `!k u. tisa_run bind_walk t = TStop k u ==> bw_result t k u` in
  let q' = mk_abs(sv, mk_conj(mk_comb(q, sv), extra)) in
  let goal = mk_imp(ant, list_mk_comb(fst(strip_comb ens), [el 0 args; el 1 args; q'; el 3 args])) in
  prove(goal,
    DISCH_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC q THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC BW_RUN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC eth THEN FIRST_ASSUM ACCEPT_TAC]);;

if not (can (find_term ((=) `bind_walk`)) (concl BIND_WALK_X86))
then failwith "JOIN bind_walk: the image theorem does not speak of bind_walk";;

(* Every theorem bind_walk.ml states (bw_theorems, listed in that file), its *)
(* hypothesis count; then the main theorems and the join.                   *)
List.iter (fun (n,th) -> Printf.printf "AUDIT %s: %d hyps\n%!" n (length(hyp th)))
  (!bw_theorems @ ["BIND_WALK_X86", BIND_WALK_X86]);;

List.iter (fun th -> print_endline ("THEOREM " ^ string_of_thm th))
  [BW_RUN; BIND_WALK_SOUND; BIND_WALK_CANONICAL; BW_CTX_SATISFIABLE; BIND_WALK_X86];;
