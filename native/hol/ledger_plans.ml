(* ========================================================================= *)
(* LEDGER.txt, part 4: the premise ledgers of the per-record plans through  *)
(* the driver (plans_drv.ml), in the session that loaded the driver and the *)
(* Model world. Each leaf a plan calls is a premise pl_leaf_impl prel ... P *)
(* n, OPEN under its leaf's name until the leaf exists and its bridge (from *)
(* its specification in plans_leaves.ml and the representation plan_rel) is *)
(* proved. The bridged leaves (plans_rel.ml) discharge their premises at   *)
(* prel := plan_rel. Load after ledger.ml, plans_drv.ml and plans_rel.ml.  *)
(* ========================================================================= *)

let ledger_leaf_obl n name =
  (mk_abs(`prel:(int64->byte)->pstate->bool`,
    mk_abs(`progs:num->tisa_prog`, mk_abs(`bw:num->int64`, mk_abs(`ctl:int64`,
    mk_abs(`budget:int64`, mk_abs(`cfr:int64`, mk_abs(`P:(int64 list)list`,
      mk_comb(list_mk_comb(`pl_leaf_impl`,
        [`prel:(int64->byte)->pstate->bool`; `progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`;
         `budget:int64`; `cfr:int64`; `P:(int64 list)list`]), mk_small_numeral n)))))))),
   true, "LEAF_" ^ name ^ " (leaf " ^ string_of_int n ^
         " implements its abstract semantics in the plan's steps under the representation)");;

let ledger_obls_plans =
  [ledger_leaf_obl 7 "hyps_union (pl_union; spec pl_hyps_union_spec)";
   ledger_leaf_obl 8 "hyps_find (pl_findl; spec pl_hyps_find_spec)";
   `\progs. pl_progs_ok progs`, false,
     "PROGS (the host's leaf table: intern16, pack, unpack, eqw, row_word, live, append_row at 0..6; their images are LEAVES)";
   `\nctl P. pl_cw_range nctl P`, true,
     "PLAN_STEPS_OK (every step's control words lie below nctl, as drv_step_ok requires)";
   `\progs bw ctl budget cfr P m used res. drv_sem progs bw ctl budget cfr P 0 m used res`, true,
     "DRIVER_RUN (the x86 driver's run of the record's plan is drv_sem: DRV_CORRECT, not yet composed with the plans)";
   `\bw ctl nctl cfr m s. plan_rel bw ctl nctl cfr m s`, true,
     "PLAN_REL_BEFORE (the memory before the record is related: by the previous record's theorem; before the first, the host's initial tables)";
   `\(prel:(int64->byte)->pstate->bool) m s. prel m s`, true,
     "PLAN_REL (memory represents the abstract state; plans_rel.ml's plan_rel for the bridged leaves)";
   `\budget used. ~(val budget < val used)`, true,
     "BUDGET (the plan starts within its fuel budget: the record loop's receipt)";
   `\s. pl_inv s`, true,
     "PLAN_INV (the abstract state before the record satisfies pl_inv: every FIRED plan keeps it (PL_<KIND>); the bootstrap state's is not proved)";
   `\(cw:num->num) (t:num). cw 8 = t`, true,
     "READER_DECODES (the decode plan leaves the record's operands in OP0..OP3, NL, LS)";
   `\(cw:num->num) (t:num). cw 9 = t`, true,
     "READER_DECODES (the decode plan leaves the record's operands in OP0..OP3, NL, LS)";
   `\(cw:num->num) (t:num). cw 10 = t`, true,
     "READER_DECODES (the decode plan leaves the record's operands in OP0..OP3, NL, LS)";
   `\(cw:num->num) (stk:num list). cw 13 + cw 12 <= LENGTH stk`, true,
     "READER_DECODES (the decode plan leaves a list operand in the stack, at LS, NL words)";
   `\(cw:num->num) (stk:num list) (l:num list). list_of_seq (\j. EL (cw 13 + j) stk) (cw 12) = l`, true,
     "READER_DECODES (the decode plan leaves a list operand in the stack, at LS, NL words)"];;

let ledger_cands_plans = ["PL_LEAF_ASSUME_INTERN16", PL_LEAF_ASSUME_INTERN16; "PL_LEAF_ASSUME_PACK", PL_LEAF_ASSUME_PACK; "PL_LEAF_ASSUME_EQW", PL_LEAF_ASSUME_EQW; "PL_LEAF_ASSUME_ROW_WORD", PL_LEAF_ASSUME_ROW_WORD; "PL_LEAF_ASSUME_LIVE", PL_LEAF_ASSUME_LIVE; "PL_LEAF_ASSUME_APPEND_ROW", PL_LEAF_ASSUME_APPEND_ROW; "PL_LEAF_REFL_INTERN16", PL_LEAF_REFL_INTERN16; "PL_LEAF_REFL_PACK", PL_LEAF_REFL_PACK; "PL_LEAF_REFL_ROW_WORD", PL_LEAF_REFL_ROW_WORD; "PL_LEAF_REFL_LIVE", PL_LEAF_REFL_LIVE; "PL_LEAF_REFL_APPEND_ROW", PL_LEAF_REFL_APPEND_ROW; "PL_LEAF_EQMP_UNPACK", PL_LEAF_EQMP_UNPACK; "PL_LEAF_EQMP_EQW", PL_LEAF_EQMP_EQW; "PL_LEAF_EQMP_ROW_WORD", PL_LEAF_EQMP_ROW_WORD; "PL_LEAF_EQMP_LIVE", PL_LEAF_EQMP_LIVE; "PL_LEAF_EQMP_APPEND_ROW", PL_LEAF_EQMP_APPEND_ROW; "PL_LEAF_TRANS_INTERN16", PL_LEAF_TRANS_INTERN16; "PL_LEAF_TRANS_PACK", PL_LEAF_TRANS_PACK; "PL_LEAF_TRANS_UNPACK", PL_LEAF_TRANS_UNPACK; "PL_LEAF_TRANS_EQW", PL_LEAF_TRANS_EQW; "PL_LEAF_TRANS_ROW_WORD", PL_LEAF_TRANS_ROW_WORD; "PL_LEAF_TRANS_LIVE", PL_LEAF_TRANS_LIVE; "PL_LEAF_TRANS_APPEND_ROW", PL_LEAF_TRANS_APPEND_ROW; "PL_LEAF_MKCOMB_INTERN16", PL_LEAF_MKCOMB_INTERN16; "PL_LEAF_MKCOMB_PACK", PL_LEAF_MKCOMB_PACK; "PL_LEAF_MKCOMB_UNPACK", PL_LEAF_MKCOMB_UNPACK; "PL_LEAF_MKCOMB_EQW", PL_LEAF_MKCOMB_EQW; "PL_LEAF_MKCOMB_ROW_WORD", PL_LEAF_MKCOMB_ROW_WORD; "PL_LEAF_MKCOMB_LIVE", PL_LEAF_MKCOMB_LIVE; "PL_LEAF_MKCOMB_APPEND_ROW", PL_LEAF_MKCOMB_APPEND_ROW; "PL_LEAF_EXPECT_ALPHA_EQW", PL_LEAF_EXPECT_ALPHA_EQW; "PL_LEAF_EXPECT_ALPHA_ROW_WORD", PL_LEAF_EXPECT_ALPHA_ROW_WORD; "PL_LEAF_EXPECT_ALPHA_LIVE", PL_LEAF_EXPECT_ALPHA_LIVE];;

ledger_put_part (tcalc_path "native/hol/LEDGER.txt") 4
  "one session on s2n-bignum's base: the driver, the Model world with plans_abs.ml, plans_drv.ml, plans_rel.ml."
  (map (ledger_lines ledger_cands_plans ledger_obls_plans)
      ["PL_ASSUME_DRV", PL_ASSUME_DRV; "PL_EQMP_DRV", PL_EQMP_DRV; "PL_TRANS_DRV", PL_TRANS_DRV;
       "PL_REFL_DRV", PL_REFL_DRV; "PL_EXPECT_ALPHA_DRV", PL_EXPECT_ALPHA_DRV;
       "PL_MKCOMB_DRV", PL_MKCOMB_DRV;
       "PL_ASSUME_REL", PL_ASSUME_REL; "PL_EQMP_REL", PL_EQMP_REL; "PL_TRANS_REL", PL_TRANS_REL;
       "PL_REFL_REL", PL_REFL_REL; "PL_EXPECT_ALPHA_REL", PL_EXPECT_ALPHA_REL;
       "PL_MKCOMB_REL", PL_MKCOMB_REL]);;
