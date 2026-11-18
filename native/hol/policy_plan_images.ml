(* Exact images for the two leaves of the guarded policy plan. *)
needs "native/hol/tables_policy.ml";;
needs "tisa/hol/tisa_x86_evidence.ml";;
needs "native/leaves/pol_max/pol_max.hol";;
needs "native/leaves/eqw/eqw.hol";;
needs "native/leaves/common/leaf_join_lib.ml";;

let POLICY_MAX_X86 = leaf_x86 "pol_max" POL_MAX_TERM POL_MAX_RUN;;
let POLICY_MAX_LEAF_SPEC = leaf_spec "pol_max" 0 POL_MAX_TERM POL_MAX_DECLS;;
let POLICY_COPY_X86 = leaf_x86 "eqw" EQW_TERM EQW_RUN;;
let POLICY_COPY_LEAF_SPEC = leaf_spec "eqw" 0 EQW_TERM EQW_DECLS;;

let pl_policy_progs = new_definition
 `pl_policy_progs j = if j = 20 then pol_max else eqw`;;
let pl_policy_pcs = new_definition
 `pl_policy_pcs (maxpc:num) (copypc:num) j = if j = 20 then maxpc else copypc`;;
let pl_policy_mcs = new_definition
 `pl_policy_mcs j = if j = 20 then pol_max_mc else eqw_mc`;;

let POLICY_NATIVE_LEAVES = prove
 (`!maxpc copypc j. tisa_leaf_wf (pl_policy_progs j) /\
     tisa_leaf_spec (pl_policy_progs j) (pl_policy_mcs j) (pl_policy_pcs maxpc copypc j)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `j = 20` THEN
  ASM_REWRITE_TAC[pl_policy_progs;pl_policy_mcs;pl_policy_pcs;POL_MAX_LEAF_WF;EQW_LEAF_WF;
                  POLICY_MAX_LEAF_SPEC;POLICY_COPY_LEAF_SPEC]);;

(* The ABI theorem retains all concrete placement, entry and byte premises. *)
let POLICY_DRIVER_X86 = GEN_ALL(REWRITE_RULE[POLICY_NATIVE_LEAVES]
 (ISPECL [`pl_policy_progs`;`pl_policy_pcs maxpc copypc`;`pl_policy_mcs`;`21`;
           `pc:num`;`stackpointer:int64`;`d:int64`;`plan:int64`;`2`;`ctl:int64`;`nctl:num`;
           `bind:int64`;`nbw:num`;`leaves:int64`;`bw:num->int64`;`pl_plan_policy`;
           `budget:int64`;`used0:int64`;`m0:int64->byte`;`ret:int64`;
           `rbxv:int64`;`rbpv:int64`;`r12v:int64`;`r13v:int64`;`r14v:int64`;`r15v:int64`]
          DRV_CORRECT));;

let policy_image_theorems = policy_plan_theorems @ tables_policy_theorems @
 ["POLICY_MAX_X86",POLICY_MAX_X86;"POLICY_MAX_LEAF_SPEC",POLICY_MAX_LEAF_SPEC;
  "POLICY_COPY_X86",POLICY_COPY_X86;"POLICY_COPY_LEAF_SPEC",POLICY_COPY_LEAF_SPEC;
  "POLICY_NATIVE_LEAVES",POLICY_NATIVE_LEAVES;"POLICY_DRIVER_X86",POLICY_DRIVER_X86];;
leaf_audit policy_image_theorems policy_image_theorems;;
tisa_evidence_summary();;
