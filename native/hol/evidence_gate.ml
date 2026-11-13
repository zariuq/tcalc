(* ========================================================================= *)
(* The evidence gate: every file this session loaded through HOL Light's    *)
(* loader (loads, loadt, needs; nested loads included), oldest first, with  *)
(* the MD5 digest it had when it was loaded. evidence_check.py compares the *)
(* list with the files on disk and names the stale evidence.                 *)
(* ========================================================================= *)

let evidence_gate () =
  Printf.printf "EVIDENCE-BEGIN %d files\n%!" (length !loaded_files);
  List.iter (fun (f,d) -> Printf.printf "EVIDENCE %s %s\n%!" (Digest.to_hex d) f)
            (rev !loaded_files);
  Printf.printf "EVIDENCE-END\n%!";;

evidence_gate ();;
