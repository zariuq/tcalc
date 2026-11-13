(* ========================================================================= *)
(* Joins the x86 image theorem of intern_name (from the t-ISA generator,     *)
(* proved in the same process from intern_name.hol) with the functional      *)
(* theorem NAME_RUN (tcalc/native/hol/intern_name.ml): the native code's run *)
(* ends in a state whose p1 run satisfies name_result, and the x86 memory    *)
(* equals that state's memory outside the saved stack.                       *)
(*                                                                           *)
(* Run by tcalc/tisa/hol/run_x86_evidence.sh as its DRIVER, after the       *)
(* record. Also the audit of intern_name.ml in the same process: every      *)
(* theorem it states is listed with its hypothesis count.                   *)
(* ========================================================================= *)

loadt "native/hol/intern_name.ml";;

(* The proved program is the image's program, term for term. *)
let INTERN_NAME_IMAGE_PROG = (fun (_,p,_,_) -> p) (assoc "intern_name" !tisa_images);;
if rand(concl INTERN_NAME_TERM) <> INTERN_NAME_IMAGE_PROG
then failwith "JOIN intern_name: the proved program is not the image's program";;

(* The image theorem for intern_name, its postcondition strengthened by the *)
(* result of every run (NAME_RUN).                                           *)
let NAME_X86 =
  let eth = REWRITE_RULE[GSYM INTERN_NAME_TERM] (assoc "intern_name" !tisa_entry_thms) in
  let ant,ens = dest_imp(concl eth) in
  let (_,args) = strip_comb ens in
  let q = el 2 args in
  let sv = genvar `:x86state` in
  let extra = `!k u. tisa_run intern_name t = TStop k u ==> name_result t k u` in
  let q' = mk_abs(sv, mk_conj(mk_comb(q, sv), extra)) in
  let goal = mk_imp(ant, list_mk_comb(fst(strip_comb ens), [el 0 args; el 1 args; q'; el 3 args])) in
  prove(goal,
    DISCH_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC q THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC NAME_RUN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC eth THEN FIRST_ASSUM ACCEPT_TAC]);;

if not (can (find_term ((=) `intern_name`)) (concl NAME_X86))
then failwith "JOIN intern_name: the image theorem does not speak of intern_name";;

let names_audit names =
  List.iter (fun (n,th) ->
    Printf.printf "AUDIT %s: %d hyps\n%!" n (length(hyp th))) names;;

names_audit
 ["INTERN_NAME_TERM", INTERN_NAME_TERM; "NAME_OK_APPEND", NAME_OK_APPEND; "NAME_ENTRY", NAME_ENTRY;
  "NAME_CMP_LOOP", NAME_CMP_LOOP; "NAME_COPY_LOOP", NAME_COPY_LOOP;
  "NAME_OCCUPIED_WP", NAME_OCCUPIED_WP; "NAME_APPEND_WP", NAME_APPEND_WP;
  "NAME_BODY_WP", NAME_BODY_WP; "NAME_PROLOGUE_WP", NAME_PROLOGUE_WP; "NAME_ROOT_WP", NAME_ROOT_WP;
  "NAME_RUN", NAME_RUN; "NAME_SOUND", NAME_SOUND; "NAME_RUN_COMPLETE", NAME_RUN_COMPLETE;
  "NAME_APPEND_ABSENT", NAME_APPEND_ABSENT; "NAME_PRESENT_FOUND", NAME_PRESENT_FOUND;
  "NAME_X86", NAME_X86];;

List.iter (fun th -> print_endline ("THEOREM " ^ string_of_thm th))
  [NAME_RUN; NAME_SOUND; NAME_RUN_COMPLETE; NAME_APPEND_ABSENT; NAME_PRESENT_FOUND; NAME_X86];;
