(* The existing put_word image preserves unpublished mark words. *)
needs "native/hol/put_word_frame_join.ml";;
needs "native/hol/put_word_mark_tail.ml";;

let PUT_WORD_MARK_X86 = leaf_x86 "put_word" PUT_WORD_TERM PUT_WORD_MARK_RUN;;

let put_word_mark_tail_join_theorems =
 put_word_frame_join_theorems @ put_word_mark_tail_theorems @
 ["PUT_WORD_MARK_X86",PUT_WORD_MARK_X86];;
leaf_audit put_word_mark_tail_join_theorems
 ["PUT_WORD_TABLE_KEPT",PUT_WORD_TABLE_KEPT;
  "PUT_WORD_MARK_ZERO_TAIL",PUT_WORD_MARK_ZERO_TAIL;
  "PUT_WORD_MARK_EXACT",PUT_WORD_MARK_EXACT;
  "PUT_WORD_MARK_PAST_COUNT",PUT_WORD_MARK_PAST_COUNT;
  "PUT_WORD_MARK_X86",PUT_WORD_MARK_X86];;
