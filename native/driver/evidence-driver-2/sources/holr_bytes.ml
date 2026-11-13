(* ========================================================================= *)
(* The byte-level definitions of HOLR v1, as holr_spec.ml states them:      *)
(* minimal unsigned LEB128 and the FNV-1a 64 state. The definitions are     *)
(* holr_spec.ml's, character for character, so that the reader's routines   *)
(* can be proved without the logic it loads; loading this file and          *)
(* holr_spec.ml in either order gives one constant per name (HOL Light      *)
(* accepts an identical definition again as a benign redefinition).         *)
(* ========================================================================= *)

needs "Library/words.ml";;

let leb_enc_def = define
 `leb_enc v = if v < 128 then [v] else CONS (v MOD 128 + 128) (leb_enc (v DIV 128))`;;

let LEB_ENC_NONEMPTY = prove
 (`!v. ~(leb_enc v = [])`,
  GEN_TAC THEN ONCE_REWRITE_TAC[leb_enc_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL]);;

(* The 64-bit FNV-1a state over a list of bytes. *)
let fnv1a_def = define
 `(fnv1a (h:int64) [] = h) /\
  (fnv1a h (CONS b bs) = fnv1a (word_mul (word_xor h (word b)) (word 1099511628211)) bs)`;;

let fnv_offset = new_definition
 `fnv_offset:int64 = word 14695981039346656037`;;
