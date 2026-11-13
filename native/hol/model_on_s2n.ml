(* ========================================================================= *)
(* The Model world -- HOL Light's Model, HolInHol, the transform calculus,   *)
(* the fibre and the HOLR checker (holfibre_all.ml, holr_native.ml,          *)
(* holr_instance.ml, holr_keys.ml) -- in a session built on s2n-bignum's     *)
(* x86 base, so that the checker's theorems and the x86 proofs of its        *)
(* routines are theorems of one session.                                     *)
(*                                                                           *)
(* Why it fails without this. HOL Light has one namespace of constants, and  *)
(* its parser reads every name that is a constant as that constant. The     *)
(* session gives such names to things the Model world means otherwise:       *)
(*   element  s2n-bignum common/components.ml (a memory component); Model's  *)
(*            modelset.ml defines its own element (the members of a set).    *)
(*            That definition fails to typecheck, modelset.ml stops there,   *)
(*            and semantics.ml, built on what is missing, fails with         *)
(*            Failure "ABS" (the reported symptom);                          *)
(*   ch       s2n-bignum x86/proofs/instruction.ml (the CH register);        *)
(*            Model's choice function (new_specification ["ch"]);            *)
(*   r10, sp  x86 registers, which HolInHol's embedding.ml and               *)
(*            holr_native.ml use as variable names;                          *)
(*   read     HOL Light's Library/components.ml (loaded by s2n-bignum's     *)
(*            base through Library/records.ml), which the transform          *)
(*            calculus (Transform/core.ml) uses as a variable name.          *)
(* Number priorities, overloads and rewrites are not the cause: Model loads  *)
(* after s2n-bignum's libraries with num prioritized, but Transform/core.ml  *)
(* then fails at "read".                                                     *)
(*                                                                           *)
(* The remedy, without touching Model or s2n-bignum. A plain session that    *)
(* loads the Model world (the reference) writes its constants with their     *)
(* types, its interface, infixes and type abbreviations, and the files it    *)
(* loaded with their digests, to model_world_consts.txt (model_world_write). *)
(* In a session on s2n-bignum's base, this file is loaded first (it records  *)
(* the core constants, for the report), and model_world_load.ml, loaded     *)
(* after the x86 files, loads the Model world with the parser seeing what    *)
(* the reference saw:                                                        *)
(*   - every constant of the session that the reference does not have, or   *)
(*     has with another type, is hidden, so its name reads as a variable;    *)
(*   - interface entries, infixes and type abbreviations the reference does  *)
(*     not have are set aside (those of files both load, such as            *)
(*     Library/words.ml's int64, stay), and an infix both have takes the     *)
(*     reference's precedence;                                               *)
(*   - a Model-world constant whose name the session gives another type      *)
(*     (element, ch) is defined as model_<name>, and the name reads as it    *)
(*     while the Model world loads;                                          *)
(*   - a constant the session has with the reference's name and type (the    *)
(*     byte-level HOLR definitions of holr_bytes.ml, Model's |->) stays      *)
(*     visible, and the Model world's definition of it is the benign         *)
(*     redefinition HOL Light takes it for.                                  *)
(* Afterwards the session's parser state is restored (hidden names visible   *)
(* again, its interface, infixes, abbreviations); the Model world's new      *)
(* infixes and abbreviations stay. The load fails if the reference is stale *)
(* (a file it loaded has changed) or a rename other than the expected ones   *)
(* happens.                                                                  *)
(* ========================================================================= *)

let model_world_reference = tcalc_path "native/hol/model_world_consts.txt";;
let model_world_dir = Filename.concat (tcalc_external "METTAPEDIA_HOL_LIGHT") "HolInHol";;
let model_world_files =
  map tcalc_path
   ["native/hol/holfibre_all.ml";
    "native/hol/holr_native.ml";
    "native/hol/holr_instance.ml";
    "native/hol/holr_keys.ml";
    "native/hol/plans_abs.ml"];;
let model_world_expected_renames = ["ch"; "element"];;

(* The constants of the session when this file is loaded (first): in a    *)
(* session on s2n-bignum's base, HOL Light's core.                          *)
let model_world_mark_consts = map fst (constants());;

let model_world_one_line s =
  String.concat " " (filter (fun w -> w <> "")
    (String.split_on_char ' ' (String.map (fun c -> if c = '\n' then ' ' else c) s)));;

(* A constant's generic type with its type variables renamed in order of  *)
(* first occurrence: generic types are compared up to their variables'    *)
(* names (some carry the parser's invented ?n variables, whose numbers     *)
(* depend on the session).                                                 *)
let model_world_type ty =
  let rec occ t acc =
    if is_vartype t then (if mem t acc then acc else t::acc)
    else rev_itlist occ (snd(dest_type t)) acc in
  let tvs = rev(occ ty []) in
  let ty' = type_subst (map2 (fun v i -> mk_vartype("V" ^ string_of_int i), v)
                             tvs (1--length tvs)) ty in
  model_world_one_line(string_of_type ty');;

(* The reference: written by a plain session after loading the Model world. *)
let model_world_write file =
  let oc = open_out file in
  output_string oc
    "GENERATED by model_on_s2n.ml (model_world_write) in a plain session; never edit by hand.\n";
  do_list (fun (f,d) -> Printf.fprintf oc "FILE\t%s\t%s\n" (Digest.to_hex d) f)
          (rev !loaded_files);
  do_list (fun (n,ty) -> Printf.fprintf oc "CONST\t%s\t%s\n" n (model_world_type ty))
          (rev (constants()));
  do_list (fun (s,(p,a)) -> Printf.fprintf oc "INFIX\t%s\t%d\t%s\n" s p a) (infixes());
  do_list (fun (s,_) -> Printf.fprintf oc "ABBREV\t%s\n" s) (type_abbrevs());
  do_list (fun (s,(c,_)) -> Printf.fprintf oc "IFACE\t%s\t%s\n" s c) (!the_interface);
  close_out oc;;

(* The reference: its constants (name to type), files (name, digest),     *)
(* infixes, type abbreviations' names and interface entries (symbol,      *)
(* constant).                                                              *)
let model_world_read file =
  let ic = open_in file in
  let consts = Hashtbl.create 8192 and files = ref [] and infs = ref []
  and abbrevs = ref [] and iface = ref [] in
  (try while true do
     match String.split_on_char '\t' (input_line ic) with
       ["CONST"; n; ty] -> Hashtbl.replace consts n ty
     | ["FILE"; d; f] -> files := (f,d) :: !files
     | ["INFIX"; s; p; a] -> infs := (s,(int_of_string p,a)) :: !infs
     | ["ABBREV"; s] -> abbrevs := s :: !abbrevs
     | ["IFACE"; s; c] -> iface := (s,c) :: !iface
     | _ -> ()
   done with End_of_file -> close_in ic);
  consts, rev !files, rev !infs, !abbrevs, !iface;;

(* While the Model world loads: the session's names it must not see, the  *)
(* names it defines under model_<name>, and what was renamed.              *)
let model_world_active = ref false;;
let model_world_hidden = ref ([]:string list);;
let model_world_candidates = ref ([]:string list);;
let model_world_renamed = ref ([]:(string*string)list);;
let model_world_shared = ref ([]:string list);;
let model_world_saved_interface = ref ([]:(string*(string*hol_type))list);;
let model_world_saved_infixes = ref ([]:(string*(int*string))list);;
let model_world_saved_abbrevs = ref ([]:(string*hol_type)list);;
let model_world_saved_cwd = ref "";;

(* After the Model world's constant name is defined as model_<name>: the   *)
(* name reads as it.                                                       *)
let model_world_alias name =
  let name' = "model_" ^ name in
  unhide_constant name;
  override_interface(name, mk_mconst(name', get_const_type name'));
  model_world_renamed := (name,name') :: !model_world_renamed;;

let model_world_fresh name =
  let name' = "model_" ^ name in
  if can get_const_type name' then failwith ("model_world: " ^ name' ^ " is taken")
  else name';;

(* The constants a definition defines: the heads of its clauses. *)
let model_world_heads tm =
  let head c =
    let c = snd(strip_forall c) in
    let c = if is_imp c then rand c else c in
    let c = if is_eq c then lhand c else c in
    fst(strip_comb c) in
  filter is_var (map head (conjuncts(snd(strip_forall tm))));;

let model_world_new_definition orig tm =
  if not !model_world_active then orig tm else
  let vs = filter (fun v -> mem (name_of v) !model_world_candidates) (model_world_heads tm) in
  if vs = [] then orig tm else
  let th = orig (vsubst (map (fun v -> mk_var(model_world_fresh(name_of v),type_of v),v) vs) tm) in
  do_list (fun v -> model_world_alias(name_of v)) vs; th;;

let model_world_new_specification orig names th =
  if not !model_world_active then orig names th else
  let ns = filter (fun n -> mem n !model_world_candidates) names in
  if ns = [] then orig names th else
  let th' = orig (map (fun n -> if mem n ns then model_world_fresh n else n) names) th in
  do_list model_world_alias ns; th';;

let model_world_enter () =
  let reference,_,ref_infixes,ref_abbrevs,ref_iface = model_world_read model_world_reference in
  let session = constants() in
  let other (n,_) =
    try Hashtbl.find reference n <> model_world_type(get_const_type n)
    with Not_found -> true in
  let hide = setify(map fst (filter (fun c -> not(is_hidden(fst c)) && other c) session)) in
  model_world_hidden := hide;
  model_world_candidates := filter (Hashtbl.mem reference) hide;
  model_world_shared :=
    filter (fun n -> not(mem n hide) && not(mem n model_world_mark_consts)) (map fst session);
  model_world_renamed := [];
  do_list hide_constant hide;
  model_world_saved_interface := !the_interface;
  model_world_saved_infixes := infixes();
  model_world_saved_abbrevs := type_abbrevs();
  model_world_saved_cwd := Sys.getcwd();
  the_interface := filter (fun (s,(c,_)) -> not(mem c hide) && mem (s,c) ref_iface) !the_interface;
  do_list (fun (s,_) -> if not(can (assoc s) ref_infixes) then unparse_as_infix s) (infixes());
  do_list (fun (s,pa) -> if can get_infix_status s && get_infix_status s <> pa
                         then parse_as_infix(s,pa)) ref_infixes;
  do_list (fun (s,_) -> if not(mem s ref_abbrevs) then remove_type_abbrev s) (type_abbrevs());
  Sys.chdir model_world_dir;
  model_world_active := true;;

let model_world_leave () =
  model_world_active := false;
  Sys.chdir !model_world_saved_cwd;
  let added = filter (fun e -> not(mem e !model_world_saved_interface) &&
                               not(mem (fst e) (map fst !model_world_renamed)))
                     !the_interface in
  the_interface := added @ !model_world_saved_interface;
  do_list parse_as_infix !model_world_saved_infixes;
  let new_abbrevs = filter (fun a -> not(mem a !model_world_saved_abbrevs)) (type_abbrevs()) in
  do_list (remove_type_abbrev o fst) (type_abbrevs());
  do_list new_type_abbrev (rev !model_world_saved_abbrevs);
  do_list (fun (s,ty) -> if not(can (assoc s) (type_abbrevs())) then new_type_abbrev(s,ty))
          new_abbrevs;
  do_list unhide_constant !model_world_hidden;;

(* The reference must describe the files this session loaded for the Model *)
(* world: each file it loaded, by name and digest, was loaded here.         *)
let model_world_check () =
  let _,files,_,_,_ = model_world_read model_world_reference in
  let stale = filter (fun (f,d) ->
    not(exists (fun (f',d') -> f' = f && Digest.to_hex d' = d) !loaded_files)) files in
  let renamed = sort (<) (map fst !model_world_renamed) in
  Printf.printf "MODEL-WORLD reference %s (%s): %d files, %d stale\n%!" model_world_reference
    (Digest.to_hex(Digest.file model_world_reference)) (length files) (length stale);
  do_list (fun (f,d) -> Printf.printf "MODEL-WORLD stale %s %s\n%!" d f) stale;
  Printf.printf "MODEL-WORLD hidden %d constants of the session while it loaded\n%!"
    (length !model_world_hidden);
  Printf.printf "MODEL-WORLD renamed: %s\n%!"
    (String.concat ", " (map (fun (n,n') -> n ^ " -> " ^ n') (rev !model_world_renamed)));
  Printf.printf "MODEL-WORLD shared with the session (same name and type): %s\n%!"
    (String.concat " " (sort (<) !model_world_shared));
  if stale <> [] then failwith "model_world: the reference is stale; regenerate it"
  else if renamed <> model_world_expected_renames then
    failwith "model_world: unexpected renames"
  else ();;
