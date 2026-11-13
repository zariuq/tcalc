(* ========================================================================= *)
(* Joins the x86 image theorem of leb128 (from the t-ISA generator, proved  *)
(* in the same process from leb128.hol) with the functional theorem          *)
(* LEB128_RUN (tcalc/native/hol/reader_leb128.ml): the native code's run     *)
(* ends in a state whose p1 run satisfies leb128_post, and the x86 memory    *)
(* equals that state's memory outside the saved stack.                       *)
(*                                                                           *)
(* Run by tcalc/tisa/hol/run_x86_evidence.sh as its DRIVER, after the       *)
(* record. Also the audit of reader_leb128.ml in a fresh process: every     *)
(* theorem it states is listed with its hypothesis count.                   *)
(* ========================================================================= *)

loadt "native/hol/reader_leb128.ml";;

(* The proved program is the image's program, term for term. *)
let LEB128_IMAGE_PROG = (fun (_,p,_,_) -> p) (assoc "leb128" !tisa_images);;
if rand(concl LEB128_TERM) <> LEB128_IMAGE_PROG
then failwith "JOIN leb128: the proved program is not the image's program";;

(* The image theorem for leb128, its postcondition strengthened by the       *)
(* verdict of every run (LEB128_RUN).                                        *)
let LEB128_X86 =
  let eth = REWRITE_RULE[GSYM LEB128_TERM] (assoc "leb128" !tisa_entry_thms) in
  let ant,ens = dest_imp(concl eth) in
  let (_,args) = strip_comb ens in
  let q = el 2 args in
  let sv = genvar `:x86state` in
  let extra = `!k u. tisa_run leb128 t = TStop k u ==> leb128_post t k u` in
  let q' = mk_abs(sv, mk_conj(mk_comb(q, sv), extra)) in
  let goal = mk_imp(ant, list_mk_comb(fst(strip_comb ens), [el 0 args; el 1 args; q'; el 3 args])) in
  prove(goal,
    DISCH_TAC THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC q THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC LEB128_RUN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC eth THEN FIRST_ASSUM ACCEPT_TAC]);;

if not (can (find_term ((=) `leb128`)) (concl LEB128_X86))
then failwith "JOIN leb128: the image theorem does not speak of leb128";;

let reader_audit names =
  List.iter (fun (n,th) ->
    Printf.printf "AUDIT %s: %d hyps\n%!" n (length(hyp th))) names;;

reader_audit
 ["LEB_DEC_ENC", LEB_DEC_ENC; "LEB_ENC_INJ", LEB_ENC_INJ; "LEB_ENC_LENGTH_62", LEB_ENC_LENGTH_62;
  "LEB_ENC_BYTES", LEB_ENC_BYTES; "LEB_ENC_SEQ", LEB_ENC_SEQ; "LEB_PREFIX_SCAN", LEB_PREFIX_SCAN;
  "LEB_SEQ_FIRES", LEB_SEQ_FIRES; "LEB_SEQ_SHORT", LEB_SEQ_SHORT;
  "LEB_SEQ_NONMINIMAL", LEB_SEQ_NONMINIMAL; "LEB_SEQ_TOO_BIG", LEB_SEQ_TOO_BIG;
  "LEB_SEQ_NINE", LEB_SEQ_NINE; "LEB_FIRES_UNIQUE", LEB_FIRES_UNIQUE;
  "LEB_FIRES_NOT_SHORT", LEB_FIRES_NOT_SHORT; "REGION_FROM_SPLIT", REGION_FROM_SPLIT;
  "LEB128_TERM", LEB128_TERM; "LEB128_ENTRY", LEB128_ENTRY;
  "LEB128_BODY_WP", LEB128_BODY_WP; "LEB128_PROLOGUE_WP", LEB128_PROLOGUE_WP;
  "LEB128_ROOT_WP", LEB128_ROOT_WP; "LEB128_RUN", LEB128_RUN;
  "LEB128_SOUND", LEB128_SOUND; "LEB128_COMPLETE", LEB128_COMPLETE;
  "LEB128_SHORT", LEB128_SHORT; "LEB128_MALFORMED", LEB128_MALFORMED;
  "LEB128_X86", LEB128_X86];;

List.iter (fun th -> print_endline ("THEOREM " ^ string_of_thm th))
  [LEB128_RUN; LEB128_SOUND; LEB128_COMPLETE; LEB128_SHORT; LEB128_MALFORMED; LEB128_X86];;
