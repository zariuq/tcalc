(* ========================================================================= *)
(* Where the sources live. A session loads this file before any other file  *)
(* of this repository, by its path: from the repository root,               *)
(*   loadt "native/hol/roots.ml";;                                           *)
(* or, from elsewhere, through TCALC_DIR.                                    *)
(*                                                                           *)
(* The repository root is TCALC_DIR when it is set, else the working        *)
(* directory. It goes on HOL Light's load_path right after the working      *)
(* directory, as an absolute name, because model_on_s2n.ml changes the      *)
(* working directory while it loads the Model world. Sessions that load the *)
(* Model world (holfibre_all.ml) run with $METTAPEDIA_HOL_LIGHT/HolInHol as  *)
(* the working directory, since HolInHol's make.ml loads its files by bare  *)
(* names, and so set TCALC_DIR. The trees outside this repository are named *)
(* by environment variables and added to load_path when they are set:       *)
(*   S2N_BIGNUM_DIR        an s2n-bignum checkout (the x86 model and proofs) *)
(*   METTAPEDIA_HOL_LIGHT  Mettapedia's hol_light directory (HolInHol and    *)
(*                         Transform)                                        *)
(* Files then load each other by names relative to these roots, such as     *)
(* needs "native/hol/holr_spec.ml" or needs "HolInHol/syntax.ml". Each such *)
(* name exists in exactly one of the roots.                                  *)
(* ========================================================================= *)

let tcalc_root =
  let d = try Sys.getenv "TCALC_DIR" with Not_found -> Sys.getcwd() in
  if Filename.is_relative d then Filename.concat (Sys.getcwd()) d else d;;

let tcalc_path name = Filename.concat tcalc_root name;;

let tcalc_external var =
  try Sys.getenv var with Not_found ->
    failwith ("set " ^ var ^ " (see native/hol/roots.ml)");;

load_path := "." :: tcalc_root ::
             filter (fun d -> d <> "." && d <> tcalc_root) !load_path;;

do_list (fun var ->
           try let d = Sys.getenv var in
               if not (mem d !load_path) then load_path := !load_path @ [d]
           with Not_found -> ())
        ["S2N_BIGNUM_DIR"; "METTAPEDIA_HOL_LIGHT"];;
