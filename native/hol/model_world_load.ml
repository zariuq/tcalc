(* ========================================================================= *)
(* Loads the Model world (model_world_files) into a session on s2n-bignum's *)
(* base, as model_on_s2n.ml describes; that file must be the session's      *)
(* first load. While the Model world loads, new_definition and             *)
(* new_specification define a constant whose name the session gives another *)
(* type under model_<name>; afterwards they are HOL Light's again.           *)
(* ========================================================================= *)

let model_world_orig_new_definition = new_definition;;
let model_world_orig_new_specification = new_specification;;
let new_definition = model_world_new_definition model_world_orig_new_definition;;
let new_specification = model_world_new_specification model_world_orig_new_specification;;

model_world_enter ();;
do_list loadt model_world_files;;
model_world_leave ();;

let new_definition = model_world_orig_new_definition;;
let new_specification = model_world_orig_new_specification;;

model_world_check ();;
