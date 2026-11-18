(* Exact x86 image and driver contract for the whole-word initializer. *)

needs "tisa/hol/tisa_x86_evidence.ml";;
needs "native/leaves/zero_words/zero_words.hol";;
needs "native/leaves/zero_words/zero_words.ml";;
needs "native/leaves/common/leaf_join_lib.ml";;

let ZERO_WORDS_X86 = leaf_x86 "zero_words" ZERO_WORDS_TERM ZERO_WORDS_CONTRACT_RUN;;
let ZERO_WORDS_LEAF_SPEC = leaf_spec "zero_words" 1 ZERO_WORDS_TERM ZERO_WORDS_DECLS;;

let zero_words_join_theorems = zero_words_theorems @
 ["ZERO_WORDS_X86",ZERO_WORDS_X86;"ZERO_WORDS_LEAF_SPEC",ZERO_WORDS_LEAF_SPEC];;

leaf_audit zero_words_join_theorems
 ["ZERO_WORDS_RUN",ZERO_WORDS_RUN;"ZERO_WORDS_EXACT",ZERO_WORDS_EXACT;
  "ZERO_WORDS_FRAME",ZERO_WORDS_FRAME;"ZERO_WORDS_TERMINATES",ZERO_WORDS_TERMINATES;
  "ZERO_WORDS_X86",ZERO_WORDS_X86;"ZERO_WORDS_LEAF_SPEC",ZERO_WORDS_LEAF_SPEC];;

tisa_evidence_summary ();;
needs "native/hol/evidence_gate.ml";;
