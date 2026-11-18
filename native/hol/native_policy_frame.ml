(* Policy projections used when relating record plans to machine words. *)
needs "native/hol/kernel_source_load.ml";;

let nat_policy = new_definition
 `nat_policy ((ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate) = pol`;;

let NAT_STEP_POLICY_KEPT = prove
 (`!ns r ns'. nat_step ns r ns'
     ==> (!p. ~(r = RPolicy p)) ==> nat_policy ns' = nat_policy ns`,
  MATCH_MP_TAC nat_step_INDUCT THEN REWRITE_TAC[nat_policy] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let NAT_STEP_POLICY_GROWS = prove
 (`!ns r ns'. nat_step ns r ns' ==> nat_policy ns <= nat_policy ns'`,
  MATCH_MP_TAC nat_step_INDUCT THEN
  REWRITE_TAC[nat_policy;LE_REFL;ARITH_RULE `a <= MAX a b`]);;

let NAT_PATH_POLICY_GROWS = prove
 (`!recs ns ns'. tc_path nat_step recs ns ns' ==> nat_policy ns <= nat_policy ns'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[tc_path] THENL
   [MESON_TAC[LE_REFL];ASM_MESON_TAC[NAT_STEP_POLICY_GROWS;LE_TRANS]]);;

let native_policy_frame_theorems =
 ["NAT_STEP_POLICY_KEPT",NAT_STEP_POLICY_KEPT;
  "NAT_STEP_POLICY_GROWS",NAT_STEP_POLICY_GROWS;"NAT_PATH_POLICY_GROWS",NAT_PATH_POLICY_GROWS];;
leaf_audit native_policy_frame_theorems native_policy_frame_theorems;;
