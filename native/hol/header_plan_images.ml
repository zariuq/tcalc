(* The header's actual leaf table and plan, specialized to the x86 driver. *)
needs "native/hol/header_image_basis_load.ml";;

let header_leaf_spec name term_th decls_th =
  leaf_spec name (length(dest_list(rhs(concl decls_th)))) term_th decls_th;;

let HEADER_COPY_LEAF_SPEC = header_leaf_spec "eqw" EQW_TERM EQW_DECLS;;
let HEADER_POLICY_LEAF_SPEC = header_leaf_spec "pol_max" POL_MAX_TERM POL_MAX_DECLS;;
let HEADER_CUR_LEAF_SPEC = header_leaf_spec "cur" CUR_TERM CUR_DECLS;;
let HEADER_LEB_LEAF_SPEC = header_leaf_spec "leb_next" LEB_NEXT_TERM LEB_NEXT_DECLS;;
let HEADER_CONST_LEAF_SPEC = header_leaf_spec "const_next" CONST_NEXT_TERM CONST_NEXT_DECLS;;
let HEADER_INC_LEAF_SPEC = header_leaf_spec "inc" INC_TERM INC_DECLS;;

let pl_hdr_select = new_definition
 `pl_hdr_select j (vpol:A) vcur vleb vconst vinc vcopy =
    if j = 20 then vpol else if j = 25 then vcur else if j = 26 then vleb else
    if j = 31 then vconst else if j = 32 then vinc else vcopy`;;
let pl_hdr_progs = new_definition
 `pl_hdr_progs j = pl_hdr_select j pol_max cur leb_next const_next inc eqw`;;
let pl_hdr_pcs = new_definition
 `pl_hdr_pcs (polpc:num) curpc lebpc conpc incpc copypc j =
    pl_hdr_select j polpc curpc lebpc conpc incpc copypc`;;
let pl_hdr_mcs = new_definition
 `pl_hdr_mcs j = pl_hdr_select j pol_max_mc cur_mc leb_next_mc const_next_mc inc_mc eqw_mc`;;

let HEADER_NATIVE_PROGS = prove
 (`pl_hdr_progs 3 = eqw /\ pl_hdr_progs 20 = pol_max /\ pl_hdr_progs 31 = const_next /\
   rd_progs_ok pl_hdr_progs`,
  REWRITE_TAC[rd_progs_ok;pl_hdr_progs;pl_hdr_select] THEN CONV_TAC NUM_REDUCE_CONV);;

let HEADER_NATIVE_LEAVES = prove
 (`!polpc curpc lebpc conpc incpc copypc j.
     tisa_leaf_wf (pl_hdr_progs j) /\
     tisa_leaf_spec (pl_hdr_progs j) (pl_hdr_mcs j)
                    (pl_hdr_pcs polpc curpc lebpc conpc incpc copypc j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_hdr_progs;pl_hdr_mcs;pl_hdr_pcs;pl_hdr_select] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[EQW_LEAF_WF;POL_MAX_LEAF_WF;CUR_LEAF_WF;LEB_NEXT_LEAF_WF;CONST_NEXT_LEAF_WF;INC_LEAF_WF;
              HEADER_COPY_LEAF_SPEC;HEADER_POLICY_LEAF_SPEC;HEADER_CUR_LEAF_SPEC;
              HEADER_LEB_LEAF_SPEC;HEADER_CONST_LEAF_SPEC;HEADER_INC_LEAF_SPEC]);;

(* Concrete layout, byte placement, entry and descriptor premises remain. *)
let HEADER_DRIVER_X86 = GEN_ALL(REWRITE_RULE[HEADER_NATIVE_LEAVES]
 (ISPECL [`pl_hdr_progs`;`pl_hdr_pcs polpc curpc lebpc conpc incpc copypc`;`pl_hdr_mcs`;`33`;
           `pc:num`;`stackpointer:int64`;`d:int64`;`plan:int64`;`LENGTH pl_plan_hdr`;`ctl:int64`;`nctl:num`;
           `bind:int64`;`nbw:num`;`leaves:int64`;`bw:num->int64`;`pl_plan_hdr`;
           `budget:int64`;`used0:int64`;`m0:int64->byte`;`ret:int64`;
           `rbxv:int64`;`rbpv:int64`;`r12v:int64`;`r13v:int64`;`r14v:int64`;`r15v:int64`]
          DRV_CORRECT));;

let header_plan_image_theorems =
 ["HEADER_COPY_LEAF_SPEC",HEADER_COPY_LEAF_SPEC;"HEADER_POLICY_LEAF_SPEC",HEADER_POLICY_LEAF_SPEC;
  "HEADER_CUR_LEAF_SPEC",HEADER_CUR_LEAF_SPEC;"HEADER_LEB_LEAF_SPEC",HEADER_LEB_LEAF_SPEC;
  "HEADER_CONST_LEAF_SPEC",HEADER_CONST_LEAF_SPEC;"HEADER_INC_LEAF_SPEC",HEADER_INC_LEAF_SPEC;
  "HEADER_NATIVE_PROGS",HEADER_NATIVE_PROGS;"HEADER_NATIVE_LEAVES",HEADER_NATIVE_LEAVES;
  "HEADER_DRIVER_X86",HEADER_DRIVER_X86];;
leaf_audit header_plan_image_theorems header_plan_image_theorems;;
tisa_evidence_summary();;
