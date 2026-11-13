(* ========================================================================= *)
(* Fidelity of the HOL semantics to the C reference evaluator.               *)
(*                                                                           *)
(* A corpus file (test_tisa_ref --export-hol) holds lines                    *)
(*   tisa_check "id" `prog` `state` `buffers` `result`;;                     *)
(* where result is what tisa_ref.c reported for that program and entry       *)
(* state. Each line evaluates the HOL run in the logic, giving a theorem     *)
(* |- tisa_observe buffers (tisa_run prog state) = r, and compares r with   *)
(* the C result.                                                             *)
(* ========================================================================= *)

needs "tisa/hol/tisa_p1_eval.ml";;

let tisa_checked = ref 0;;
let tisa_agreed = ref 0;;
let tisa_differ = ref ([]:string list);;
let tisa_slowest = ref (0.0, "");;

let tisa_check id prog st bufs expected =
  let t0 = Sys.time() in
  let tm = mk_comb(mk_comb(`tisa_observe`,bufs),mk_comb(mk_comb(`tisa_run`,prog),st)) in
  (try
     let th = TISA_EVAL_CONV tm in
     if hyp th <> [] || lhs(concl th) <> tm then failwith "evaluation theorem has the wrong shape";
     if rand(concl th) = expected then incr tisa_agreed
     else (tisa_differ := id :: !tisa_differ;
           Printf.printf "DIFFER %s\n  HOL %s\n  C   %s\n%!" id
             (string_of_term(rand(concl th))) (string_of_term expected))
   with Failure msg ->
     (tisa_differ := id :: !tisa_differ;
      Printf.printf "FAILED %s: %s\n%!" id msg));
  incr tisa_checked;
  let dt = Sys.time() -. t0 in
  if dt > fst !tisa_slowest then tisa_slowest := (dt, id);
  if !tisa_checked mod 50 = 0 then
    Printf.printf "fidelity: %d checked, %d agreed (%.0fs so far)\n%!"
      !tisa_checked !tisa_agreed (Sys.time());;

let tisa_fidelity_report name =
  Printf.printf "FIDELITY %s: %d checked, %d agree, %d differ; slowest %.1fs (%s)\n%!"
    name !tisa_checked !tisa_agreed (List.length !tisa_differ)
    (fst !tisa_slowest) (snd !tisa_slowest);;
