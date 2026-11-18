(* The binding walk's checked p1 behavior on its linked x86 image. *)
needs "native/hol/bind_walk_table_contract.ml";;
needs "tisa/hol/tisa_x86_evidence.ml";;
needs "native/walks/bind_walk.hol";;
needs "native/leaves/common/leaf_join_lib.ml";;

let BIND_WALK_LEAF_SPEC = leaf_spec "bind_walk" 4 BIND_WALK_TERM BIND_WALK_DECLS;;

let bwt_leaf_post =
  let ts,body = strip_forall(concl BIND_WALK_TABLE_RUN) in
  let post = rand body in
  new_definition(mk_eq(list_mk_comb(mk_var("bwt_leaf_post",`:tisa_state->num->tisa_state->bool`),ts),post));;

let BIND_WALK_TABLE_X86 =
  leaf_x86 "bind_walk" BIND_WALK_TERM (REWRITE_RULE[GSYM bwt_leaf_post] BIND_WALK_TABLE_RUN);;

let bind_walk_table_native_theorems =
 ["BIND_WALK_LEAF_SPEC",BIND_WALK_LEAF_SPEC;"BIND_WALK_TABLE_X86",BIND_WALK_TABLE_X86];;
