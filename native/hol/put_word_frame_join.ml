(* Exact-image contract for the full table-word frame of put_word. *)

needs "tisa/hol/tisa_x86_evidence.ml";;
needs "native/leaves/put_word/put_word.hol";;
needs "native/hol/put_word_frame.ml";;
needs "native/leaves/common/leaf_join_lib.ml";;

let PUT_WORD_FRAME_X86 = leaf_x86 "put_word" PUT_WORD_TERM PUT_WORD_FRAME_RUN;;
let PUT_WORD_FRAME_LEAF_SPEC = leaf_spec "put_word" 2 PUT_WORD_TERM PUT_WORD_DECLS;;

let put_word_frame_join_theorems =
 put_word_frame_theorems @
 ["PUT_WORD_FRAME_X86",PUT_WORD_FRAME_X86;
  "PUT_WORD_FRAME_LEAF_SPEC",PUT_WORD_FRAME_LEAF_SPEC];;
