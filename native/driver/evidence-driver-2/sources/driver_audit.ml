(* ========================================================================= *)
(* Audit of the driver theorems, run last in a fresh process: hypotheses of  *)
(* each named theorem, the statements of the main ones, and the axioms.      *)
(* ========================================================================= *)

let drv_audit_thms =
  ["TISA_RUN_KEEPS", TISA_RUN_KEEPS; "TISA_RUN_STATUS", TISA_RUN_STATUS;
   "DRV_BUILD", DRV_BUILD; "DRV_CHILD_OK", DRV_CHILD_OK; "DRV_POST", DRV_POST;
   "DRV_LOOP", DRV_LOOP; "DRV_PROLOGUE", DRV_PROLOGUE; "DRV_EPILOGUE", DRV_EPILOGUE;
   "DRV_CORRECT_FRAME", DRV_CORRECT_FRAME; "DRV_STEP_KEEPS", DRV_STEP_KEEPS;
   "DRV_SEM_KEEPS", DRV_SEM_KEEPS; "DRV_CORRECT", DRV_CORRECT;
   "INTERN16_LEAF_WF", INTERN16_LEAF_WF; "INTERN16_LEAF_SPEC", INTERN16_LEAF_SPEC;
   "INTERN16_FIRED", INTERN16_FIRED; "INTERN16_RUN_FRAME", INTERN16_RUN_FRAME;
   "INTERN16_SAME_REGIONS", INTERN16_SAME_REGIONS; "DRV_SEM_TWO_FIRED", DRV_SEM_TWO_FIRED;
   "DRV_INTERN16_TWO", DRV_INTERN16_TWO; "DRV_INTERN16_X86", DRV_INTERN16_X86;
   "TISA_RUN_FUEL", TISA_RUN_FUEL;
   "FNV_LEAF_WF", FNV_LEAF_WF; "FNV_LEAF_SPEC", FNV_LEAF_SPEC;
   "LEB128_LEAF_WF", LEB128_LEAF_WF; "LEB128_LEAF_SPEC", LEB128_LEAF_SPEC;
   "NAME_LEAF_WF", NAME_LEAF_WF; "NAME_LEAF_SPEC", NAME_LEAF_SPEC;
   "DRV_NAME_TWO", DRV_NAME_TWO; "DRV_NAME_X86", DRV_NAME_X86;
   "DRV_SEM_FUEL", DRV_SEM_FUEL; "DRV_SEM_WITHIN", DRV_SEM_WITHIN;
   "REC_PLAN_FUEL", REC_PLAN_FUEL; "REC_PLAN_WITHIN", REC_PLAN_WITHIN; "REC_PLAN_LOCAL", REC_PLAN_LOCAL;
   "REC_HOLDS_TRANSFER", REC_HOLDS_TRANSFER; "REC_RUN", REC_RUN; "REC_LOOP", REC_LOOP;
   "REC_CORRECT", REC_CORRECT; "REC_RUN_FUEL", REC_RUN_FUEL];;

List.iter (fun (n,th) -> Printf.printf "HYPS %s: %d\n%!" n (length(hyp th))) drv_audit_thms;;

List.iter (fun n ->
    Printf.printf "STATEMENT %s:\n%s\n%!" n (string_of_term(concl(assoc n drv_audit_thms))))
  ["DRV_CORRECT"; "DRV_SEM_KEEPS"; "DRV_INTERN16_X86"; "DRV_INTERN16_TWO"; "INTERN16_LEAF_SPEC";
   "TISA_RUN_FUEL"; "FNV_LEAF_SPEC"; "DRV_NAME_TWO"; "DRV_NAME_X86";
   "REC_CORRECT"; "REC_RUN_FUEL"; "DRV_SEM_WITHIN"];;

List.iter (fun (n,th) ->
    Printf.printf "DEFINITION %s:\n%s\n%!" n (string_of_term(concl th)))
  ["rec_run_RULES", rec_run_RULES; "rec_plan", rec_plan; "rec_final", rec_final;
   "rec_missing", rec_missing; "rec_handler", rec_handler; "rec_stack", rec_stack];;

let drv_axioms = axioms();;
Printf.printf "DRIVER AXIOMS %d:\n%!" (length drv_axioms);;
List.iter (fun th -> Printf.printf "  %s\n%!" (string_of_term(concl th))) drv_axioms;;
Printf.printf "DRIVER AUDIT theorems %d, with hypotheses %d\n%!"
  (length drv_audit_thms) (length(filter (fun (_,th) -> hyp th <> []) drv_audit_thms));;
