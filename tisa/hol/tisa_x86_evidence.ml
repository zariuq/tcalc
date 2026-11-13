(* ========================================================================= *)
(* Evidence run for the native-code theorems, in a fresh HOL Light process.  *)
(* Reads the p1 export (tisa_x86_p1_programs_v2.json) and proves, for each   *)
(* image: its body, the call theorem, and the                                 *)
(* image theorem over every entry state entry validation accepts. Then runs  *)
(* the controls, which must be refused, and lists the axioms.                *)
(* ========================================================================= *)

needs "tisa/hol/tisa_x86_wrapper.ml";;
needs "tisa/hol/tisa_x86_v2.ml";;
needs "tisa/hol/tisa_x86_loops.ml";;

let tisa_failed = ref ([] : string list);;

let tisa_image name prog hex spanlist =
  try ignore(tisa_prove_image name prog hex spanlist);
      ignore(tisa_prove_call name);
      ignore(tisa_prove_entry name)
  with Failure msg ->
    (tisa_failed := name :: !tisa_failed;
     Printf.printf "IMAGE %s FAILED: %s\n%!" name msg);;

(* The images of a v2 export (all when names = []). *)
let tisa_evidence_images file names =
  do_list (fun (n,p,h,s) -> tisa_image n p h s) (tisa_v2_images file names);;

(* A control: the same proof attempt on altered input must fail. *)
let tisa_control label f =
  let refused = (try ignore(f()); false with Failure _ -> true) in
  Printf.printf "CONTROL %s: %s\n%!" label (if refused then "refused" else "ACCEPTED (wrong)");
  refused;;

let tisa_evidence_summary () =
  let ax = axioms() in
  Printf.printf "AXIOMS %d:\n%!" (length ax);
  List.iter (fun th -> Printf.printf "  %s\n%!" (string_of_term (concl th))) ax;
  Printf.printf "EVIDENCE images %d, calls %d, entry theorems %d, failed %d\n%!"
    (length !tisa_images) (length !tisa_calls) (length !tisa_entry_thms) (length !tisa_failed);;
