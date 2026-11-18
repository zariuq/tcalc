(* The linked x86 driver and leaf images for ABS. *)
needs "native/hol/tables_abs_handler.ml";;
needs "native/hol/tables_abs_guard_native.ml";;
needs "native/hol/bind_walk_table_native.ml";;
needs "native/intern/intern16b.hol";;
needs "native/leaves/pack/pack.hol";;
needs "native/leaves/unpack/unpack.hol";;
needs "native/leaves/append_row/append_row.hol";;
needs "native/leaves/cur/cur.hol";;
needs "native/leaves/leb_next/leb_next.hol";;
needs "native/leaves/inc/inc.hol";;

let abs_leaf_spec name program declarations =
  leaf_check_program name program;
  leaf_spec name (length(dest_list(rhs(concl declarations)))) program declarations;;

let ABS_INTERN16_LEAF_SPEC = abs_leaf_spec "intern16" INTERN16_TERM INTERN16_DECLS;;
let ABS_PACK_LEAF_SPEC = abs_leaf_spec "pack" PACK_TERM PACK_DECLS;;
let ABS_UNPACK_LEAF_SPEC = abs_leaf_spec "unpack" UNPACK_TERM UNPACK_DECLS;;
let ABS_APPEND_ROW_LEAF_SPEC = abs_leaf_spec "append_row" APPEND_ROW_TERM APPEND_ROW_DECLS;;
let ABS_CUR_LEAF_SPEC = abs_leaf_spec "cur" CUR_TERM CUR_DECLS;;
let ABS_LEB_NEXT_LEAF_SPEC = abs_leaf_spec "leb_next" LEB_NEXT_TERM LEB_NEXT_DECLS;;
let ABS_INC_LEAF_SPEC = abs_leaf_spec "inc" INC_TERM INC_DECLS;;

let abs_leaf_select = new_definition
 `abs_leaf_select j (v_intern:A) v_pack v_unpack v_eq v_row v_live v_append v_walk v_cur v_leb v_inc =
    if j = 0 then v_intern else if j = 1 then v_pack else if j = 2 then v_unpack
    else if j = 4 then v_row else if j = 5 then v_live else if j = 6 then v_append
    else if j = 10 then v_walk else if j = 25 then v_cur else if j = 26 then v_leb
    else if j = 32 then v_inc else v_eq`;;
let abs_progs = new_definition
 `abs_progs j = abs_leaf_select j intern16 pack unpack eqw row_word live append_row bind_walk cur leb_next inc`;;
let abs_mcs = new_definition
 `abs_mcs j = abs_leaf_select j intern16_mc pack_mc unpack_mc eqw_mc row_word_mc live_mc
                                     append_row_mc bind_walk_mc cur_mc leb_next_mc inc_mc`;;
let abs_pcs = new_definition
 `abs_pcs (internpc:num) packpc unpackpc eqpc rowpc livepc appendpc walkpc curpc lebpc incpc j =
     abs_leaf_select j internpc packpc unpackpc eqpc rowpc livepc appendpc walkpc curpc lebpc incpc`;;
let ABS_X86_PROGS = prove
 (`pl_progs_ok abs_progs /\ abs_progs 10 = bind_walk /\ abs_progs 3 = eqw /\
    abs_hol_progs abs_progs /\ rd_progs_ok abs_progs`,
  REWRITE_TAC[abs_hol_progs;rd_progs_ok;pl_progs_ok;abs_progs;abs_leaf_select] THEN CONV_TAC NUM_REDUCE_CONV);;
let ABS_X86_LEAVES = prove
 (`!internpc packpc unpackpc eqpc rowpc livepc appendpc walkpc curpc lebpc incpc j.
     tisa_leaf_wf (abs_progs j) /\
     tisa_leaf_spec (abs_progs j) (abs_mcs j)
                  (abs_pcs internpc packpc unpackpc eqpc rowpc livepc appendpc walkpc curpc lebpc incpc j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_progs;abs_mcs;abs_pcs;abs_leaf_select] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC(PL_LEAVES_WF @ [BIND_WALK_LEAF_WF;ABS_INTERN16_LEAF_SPEC;ABS_PACK_LEAF_SPEC;
     ABS_UNPACK_LEAF_SPEC;ABS_GUARD_EQW_SPEC;ABS_GUARD_ROW_WORD_SPEC;ABS_GUARD_LIVE_SPEC;
     ABS_APPEND_ROW_LEAF_SPEC;BIND_WALK_LEAF_SPEC;CUR_LEAF_WF;LEB_NEXT_LEAF_WF;INC_LEAF_WF;
     ABS_CUR_LEAF_SPEC;ABS_LEB_NEXT_LEAF_SPEC;ABS_INC_LEAF_SPEC]));;

let ABS_HANDLER_WORDS = CONV_RULE(RAND_CONV
  (REWRITE_CONV[pl_prefix_op01;pl_prefix_op0;pl_plan_abs;pl_inc_cnt;APPEND])) pl_handler_abs;;

let abs_exact_driver program =
  let count = mk_comb(`LENGTH:(int64 list)list->num`,program) in
  REWRITE_RULE[ABS_X86_LEAVES]
    (ISPECL [`abs_progs`;
      `abs_pcs internpc packpc unpackpc eqpc rowpc livepc appendpc walkpc curpc lebpc incpc`;
      `abs_mcs`;`33`;`pc:num`;`stackpointer:int64`;`d:int64`;`plan:int64`;count;
      `ctl:int64`;`nctl:num`;`bind:int64`;`nbw:num`;`leaves:int64`;`bw:num->int64`;program;
      `budget:int64`;`used0:int64`;`m0:int64->byte`;`ret:int64`;`rbxv:int64`;
      `rbpv:int64`;`r12v:int64`;`r13v:int64`;`r14v:int64`;`r15v:int64`] DRV_CORRECT);;

let ABS_HANDLER_DRIVER_X86 = GEN_ALL(abs_exact_driver `pl_handler_abs`);;

let ABS_NATIVE_KIND_CONTRACT = prove
 (`!bw ctl nctl budget cfr.
     rd_tab_apart hol_layout bw /\ pl_cw_range nctl pl_plan_abs
     ==> tab_kind_contract hol_tables hol_layout hol_inv nat_step holr_rec_enc
           abs_progs bw ctl nctl budget cfr pl_handler_abs 7`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KC_ABS_TAB THEN ASM_REWRITE_TAC[ABS_X86_PROGS]);;
