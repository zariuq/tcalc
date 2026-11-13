(* ========================================================================= *)
(* Joins a plan leaf's x86 image theorem (proved in the same process by the  *)
(* t-ISA generator, from the leaf's image record LEAF.hol) with its          *)
(* functional theorem, and gives the driver's premise from it, as           *)
(* tcalc/native/reader/fnv_join.ml and tcalc/native/driver/drive_reader.ml  *)
(* do for fnv:                                                              *)
(*   leaf_x86   the image theorem, its postcondition strengthened by the    *)
(*              post of every run (the leaf's RUN theorem): the native      *)
(*              code's run ends in a state whose p1 run satisfies the post, *)
(*              and the x86 memory is that state's outside the saved stack; *)
(*   leaf_spec  !pc. tisa_leaf_spec prog prog_mc pc, the uniform image      *)
(*              theorem DRV_CORRECT takes of a leaf.                        *)
(* The leaf's tisa_leaf_wf is proved with the program (LEAF_WF_TAC).        *)
(* Run as the DRIVER of tcalc/tisa/hol/run_x86_evidence.sh, after the image *)
(* record.                                                                   *)
(* ========================================================================= *)

needs "native/leaves/common/leaf_lib.ml";;

let leaf_image_prog name = (fun (_,p,_,_) -> p) (assoc name !tisa_images);;

(* The proved program is the image's program, term for term. *)
let leaf_check_program name term_th =
  if rand(concl term_th) <> leaf_image_prog name
  then failwith ("JOIN " ^ name ^ ": the proved program is not the image's program")
  else Printf.printf "JOIN %s: the proved program is the image's program\n%!" name;;

(* run_th: !t k u. tisa_entry_ok prog t /\ tisa_run prog t = TStop k u      *)
(*                 ==> post t k u.                                           *)
let leaf_x86 name term_th run_th =
  leaf_check_program name term_th;
  let eth = REWRITE_RULE[GSYM term_th] (assoc name !tisa_entry_thms) in
  let ant,ens = dest_imp(concl eth) in
  let (_,args) = strip_comb ens in
  let q = el 2 args in
  let tv = find (fun v -> fst(dest_var v) = "t" && type_of v = `:tisa_state`) (frees ant) in
  let ku,body = strip_forall(concl(SPEC tv run_th)) in
  let hyps,post = dest_imp body in
  let extra = list_mk_forall(ku, mk_imp(rand hyps, post)) in
  let sv = genvar `:x86state` in
  let q' = mk_abs(sv, mk_conj(mk_comb(q, sv), extra)) in
  let goal = mk_imp(ant, list_mk_comb(fst(strip_comb ens), [el 0 args; el 1 args; q'; el 3 args])) in
  let th = prove(goal,
    DISCH_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC q THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC run_th THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC eth THEN FIRST_ASSUM ACCEPT_TAC]) in
  let prog = lhand(concl term_th) in
  if not (can (find_term ((=) prog)) (concl th))
  then failwith ("JOIN " ^ name ^ ": the image theorem does not speak of the program")
  else th;;

(* !pc. tisa_leaf_spec prog NAME_mc pc, for a program of nregions regions. *)
let leaf_spec name nregions term_th decls_th =
  let prog = lhand(concl term_th) in
  let mc = mk_const(name ^ "_mc", []) in
  let pc = mk_var("pc", `:num`) in
  let goal = mk_forall(pc, list_mk_comb(`tisa_leaf_spec`, [prog; mc; pc])) in
  let eth = REWRITE_RULE[GSYM term_th] (assoc name !tisa_entry_thms) in
  prove(goal, LEAF_SPEC_TAC nregions decls_th (leaf_mc_length (name ^ "_mc")) eth);;

(* Every theorem given, with its hypothesis count; then the statements of   *)
(* the main ones.                                                            *)
let leaf_audit named main =
  List.iter (fun (n,th) -> Printf.printf "AUDIT %s: %d hyps\n%!" n (length(hyp th))) named;
  Printf.printf "AUDIT theorems %d, with hypotheses %d\n%!" (length named)
    (length (filter (fun (_,th) -> hyp th <> []) named));
  List.iter (fun (n,th) -> print_endline ("THEOREM " ^ n ^ ": " ^ string_of_thm th)) main;;
