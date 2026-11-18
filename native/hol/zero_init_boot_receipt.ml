(* Derive the bootstrap zero predicate from the native clearing receipt. *)
needs "native/hol/zero_init_boot_ready.ml";;

let BOOT_ZERO_FROM_INIT = prove
 (`!bw d plan used status m.
     hol_boot_lengths bw /\
     zinit_abi_post (zinit_word_view bw) zinit_boot_slots d plan used status m /\
     status = word 1
     ==> hol_boot_zero bw m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ZINIT_BOOT_ZERO_VIEW THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`zinit_word_view (bw:num->int64)`;`zinit_boot_slots`;`d:int64`;
                `plan:int64`;`used:int64`;`status:int64`;`m:int64->byte`] ZINIT_ABI_EXACT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let boot_from_receipt_on slots view zero_rule source =
  let basis = SPEC_ALL source in
  let ant,post = dest_imp(concl basis) in
  let premises = conjuncts ant in
  let zero = find (zinit_app "hol_boot_zero") premises in
  let bw,bytes = match snd(strip_comb zero) with
    [bw;bytes] -> bw,bytes | _ -> failwith "bootstrap zero predicate arity" in
  let receipt = subst [slots,`init_slots:num list`;
                      mk_comb(view,bw),`init_bindings:num->int64`;bytes,`init_mem:int64->byte`]
   `zinit_abi_post init_bindings init_slots init_descriptor init_plan
     init_used init_status init_mem /\ init_status = word 1` in
  let goal = mk_imp(list_mk_conj(map (fun premise -> if premise = zero then receipt else premise) premises),post) in
  GEN_ALL(prove(goal,
    STRIP_TAC THEN SUBGOAL_THEN zero ASSUME_TAC THENL
     [MATCH_MP_TAC zero_rule THEN
      MAP_EVERY EXISTS_TAC [`init_descriptor:int64`;`init_plan:int64`;`init_used:int64`;`init_status:int64`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC basis THEN ASM_REWRITE_TAC[]]));;

let boot_from_receipt = boot_from_receipt_on `zinit_boot_slots`;;
let boot_from_init = boot_from_receipt `zinit_word_view` BOOT_ZERO_FROM_INIT;;


let zero_init_boot_receipt_theorems = ["BOOT_ZERO_FROM_INIT",BOOT_ZERO_FROM_INIT];;
leaf_audit zero_init_boot_receipt_theorems zero_init_boot_receipt_theorems;;
