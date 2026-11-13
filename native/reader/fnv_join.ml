(* ========================================================================= *)
(* Joins the x86 image theorem of fnv (from the t-ISA generator, proved in  *)
(* the same process from fnv.hol) with the functional theorem FNV_RUN       *)
(* (tcalc/native/hol/reader_fnv.ml): the native code's run ends in a state  *)
(* whose p1 run satisfies fnv_post, and the x86 memory equals that state's  *)
(* memory outside the saved stack.                                           *)
(*                                                                           *)
(* Run by tcalc/tisa/hol/run_x86_evidence.sh as its DRIVER, after the       *)
(* record. Also the audit of reader_fnv.ml in a fresh process: every        *)
(* theorem it states is listed with its hypothesis count.                   *)
(* ========================================================================= *)

loadt "native/hol/reader_fnv.ml";;

(* The proved program is the image's program, term for term. *)
let FNV_IMAGE_PROG = (fun (_,p,_,_) -> p) (assoc "fnv" !tisa_images);;
if rand(concl FNV_TERM) <> FNV_IMAGE_PROG
then failwith "JOIN fnv: the proved program is not the image's program";;

(* The image theorem for fnv, its postcondition strengthened by the verdict *)
(* of every run (FNV_RUN).                                                   *)
let FNV_X86 =
  let eth = REWRITE_RULE[GSYM FNV_TERM] (assoc "fnv" !tisa_entry_thms) in
  let ant,ens = dest_imp(concl eth) in
  let (_,args) = strip_comb ens in
  let q = el 2 args in
  let sv = genvar `:x86state` in
  let extra = `!k u. tisa_run fnv t = TStop k u ==> fnv_post t k u` in
  let q' = mk_abs(sv, mk_conj(mk_comb(q, sv), extra)) in
  let goal = mk_imp(ant, list_mk_comb(fst(strip_comb ens), [el 0 args; el 1 args; q'; el 3 args])) in
  prove(goal,
    DISCH_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC q THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC FNV_RUN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC eth THEN FIRST_ASSUM ACCEPT_TAC]);;

if not (can (find_term ((=) `fnv`)) (concl FNV_X86))
then failwith "JOIN fnv: the image theorem does not speak of fnv";;

let reader_audit names =
  List.iter (fun (n,th) ->
    Printf.printf "AUDIT %s: %d hyps\n%!" n (length(hyp th))) names;;

reader_audit
 ["FNV1A_APPEND", FNV1A_APPEND; "FNV1A_SEQ_SUC", FNV1A_SEQ_SUC; "FNV_TERM", FNV_TERM;
  "FNV_ENTRY", FNV_ENTRY; "FNV_BODY_WP", FNV_BODY_WP; "FNV_PROLOGUE_WP", FNV_PROLOGUE_WP;
  "FNV_ROOT_WP", FNV_ROOT_WP; "FNV_RUN", FNV_RUN; "FNV_SOUND", FNV_SOUND;
  "FNV_COMPLETE", FNV_COMPLETE; "FNV_REFUSED", FNV_REFUSED; "FNV_X86", FNV_X86];;

List.iter (fun th -> print_endline ("THEOREM " ^ string_of_thm th))
  [FNV_RUN; FNV_SOUND; FNV_COMPLETE; FNV_REFUSED; FNV_X86];;
