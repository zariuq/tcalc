(* Bounds and separation transport from parent regions to clearing views. *)
needs "native/hol/zero_init_entry.ml";;

let zinit_subviews = new_definition
 `zinit_subviews (parent:num->int64) (view:num->int64) slots <=>
    !slot. MEM slot slots
       ==> view slot = parent slot /\ val(view(slot + 1)) <= val(parent(slot + 1))`;;

let ZINIT_SUBVIEWS_RANGE = prove
 (`!parent view slots ctl cfr slot.
     zinit_subviews parent view slots /\ MEM slot slots /\ zinit_range_ok parent ctl cfr slot
     ==> zinit_range_ok view ctl cfr slot`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `slot:num` o REWRITE_RULE[zinit_subviews] o
    check (fun th -> zinit_app "zinit_subviews" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[zinit_range_ok] o
    check (fun th -> zinit_app "zinit_range_ok" (concl th))) THEN
  ASM_REWRITE_TAC[zinit_range_ok;drv_apart] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[drv_apart]) THEN ASM_ARITH_TAC);;

let ZINIT_SUBVIEWS_APART = prove
 (`!parent view slots a b.
     zinit_subviews parent view slots /\ MEM a slots /\ MEM b slots /\
     drv_apart (parent a) (val(parent(a + 1))) (parent b) (val(parent(b + 1)))
     ==> drv_apart (view a) (val(view(a + 1))) (view b) (val(view(b + 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun slot -> FIRST_ASSUM(MP_TAC o SPEC slot o REWRITE_RULE[zinit_subviews] o
    check (fun th -> zinit_app "zinit_subviews" (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC) [`a:num`;`b:num`] THEN
  ASM_REWRITE_TAC[drv_apart] THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_apart]) THEN ASM_ARITH_TAC);;

let ZINIT_SUBVIEWS_PAIRWISE = prove
 (`!parent view slots.
     zinit_subviews parent view slots /\
     PAIRWISE (\a b. drv_apart (parent a) (val(parent(a + 1)))
                               (parent b) (val(parent(b + 1)))) slots
     ==> PAIRWISE (\a b. drv_apart (view a) (val(view(a + 1)))
                                     (view b) (val(view(b + 1)))) slots`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL
    [`\a b:num. drv_apart ((parent:num->int64) a) (val(parent(a + 1)))
                          (parent b) (val(parent(b + 1)))`;
     `\a b:num. drv_apart ((view:num->int64) a) (val(view(a + 1)))
                          (view b) (val(view(b + 1)))`;`slots:num list`] PAIRWISE_IMPLIES) THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`a:num`;`b:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC ZINIT_SUBVIEWS_APART THEN
  MAP_EVERY EXISTS_TAC [`parent:num->int64`;`slots:num list`] THEN ASM_REWRITE_TAC[]);;

let ZINIT_SUBVIEWS_READONLY = prove
 (`!parent view slots ctl cfr d b n.
     zinit_subviews parent view slots /\ zinit_readonly parent slots ctl cfr d b n
     ==> zinit_readonly view slots ctl cfr d b n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[zinit_readonly] o
    check (fun th -> zinit_app "zinit_readonly" (concl th))) THEN
  ASM_REWRITE_TAC[zinit_readonly] THEN X_GEN_TAC `slot:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `slot:num` o REWRITE_RULE[zinit_subviews] o
    check (fun th -> zinit_app "zinit_subviews" (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `slot:num` o check (fun th ->
    is_forall(concl th) && tisa_has_tm `drv_apart` th)) THEN
  ASM_REWRITE_TAC[drv_apart] THEN ASM_ARITH_TAC);;

let ZINIT_BOOT_SUBVIEWS = prove
 (`!parent. hol_boot_lengths parent
     ==> zinit_subviews parent (zinit_boot_view parent) zinit_boot_slots`,
  REWRITE_TAC[zinit_subviews] THEN MESON_TAC[ZINIT_BOOT_VIEW_SUBRANGE]);;

let ZINIT_ENTRY_SUBVIEWS = prove
 (`!parent. hol_boot_lengths parent
     ==> zinit_subviews parent (zinit_entry_view parent) zinit_entry_slots`,
  REWRITE_TAC[zinit_subviews] THEN MESON_TAC[ZINIT_ENTRY_VIEW_SUBRANGE]);;

let ZINIT_ENTRY_PARENT_GEOMETRY = prove
 (`!parent ctl cfr d b n.
     hol_boot_lengths parent /\
     (!slot. MEM slot zinit_entry_slots ==> zinit_range_ok parent ctl cfr slot) /\
     PAIRWISE (\a b. drv_apart (parent a) (val(parent(a + 1)))
                               (parent b) (val(parent(b + 1)))) zinit_entry_slots /\
     zinit_readonly parent zinit_entry_slots ctl cfr d b n
     ==> (!slot. MEM slot zinit_entry_slots
                  ==> zinit_range_ok (zinit_entry_view parent) ctl cfr slot) /\
         PAIRWISE (\a b. drv_apart (zinit_entry_view parent a) (val(zinit_entry_view parent (a + 1)))
                                   (zinit_entry_view parent b) (val(zinit_entry_view parent (b + 1)))) zinit_entry_slots /\
         zinit_readonly (zinit_entry_view parent) zinit_entry_slots ctl cfr d b n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `zinit_subviews parent (zinit_entry_view parent) zinit_entry_slots`
    ASSUME_TAC THENL [ASM_SIMP_TAC[ZINIT_ENTRY_SUBVIEWS]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `slot:num` THEN DISCH_TAC THEN MATCH_MP_TAC ZINIT_SUBVIEWS_RANGE THEN
    MAP_EVERY EXISTS_TAC [`parent:num->int64`;`zinit_entry_slots`] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC ZINIT_SUBVIEWS_PAIRWISE THEN EXISTS_TAC `parent:num->int64` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ZINIT_SUBVIEWS_READONLY THEN EXISTS_TAC `parent:num->int64` THEN ASM_REWRITE_TAC[]] THEN
  CONV_TAC(DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[]);;

let zinit_subview_parent_control = new_definition
 `zinit_subview_parent_control k = if k = 0 then word 0 else word 8:int64`;;
let zinit_subview_growing_control = new_definition
 `zinit_subview_growing_control k = if k = 1 then word 16 else zinit_subview_parent_control k`;;

let ZINIT_GROWING_VIEW_CONTROL = prove
 (`drv_apart (zinit_subview_parent_control 0) (val(zinit_subview_parent_control 1))
              (zinit_subview_parent_control 2) (val(zinit_subview_parent_control 3)) /\
   ~drv_apart (zinit_subview_growing_control 0) (val(zinit_subview_growing_control 1))
               (zinit_subview_growing_control 2) (val(zinit_subview_growing_control 3)) /\
   ~zinit_subviews zinit_subview_parent_control zinit_subview_growing_control [0;2]`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[drv_apart;zinit_subview_parent_control;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[drv_apart;zinit_subview_growing_control;zinit_subview_parent_control;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[zinit_subviews] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[MEM;zinit_subview_growing_control;zinit_subview_parent_control;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV] THEN
  REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let zero_init_subrange_theorems =
 ["ZINIT_SUBVIEWS_RANGE",ZINIT_SUBVIEWS_RANGE;
  "ZINIT_SUBVIEWS_APART",ZINIT_SUBVIEWS_APART;
  "ZINIT_SUBVIEWS_PAIRWISE",ZINIT_SUBVIEWS_PAIRWISE;
  "ZINIT_SUBVIEWS_READONLY",ZINIT_SUBVIEWS_READONLY;
  "ZINIT_BOOT_SUBVIEWS",ZINIT_BOOT_SUBVIEWS;
  "ZINIT_ENTRY_SUBVIEWS",ZINIT_ENTRY_SUBVIEWS;
  "ZINIT_ENTRY_PARENT_GEOMETRY",ZINIT_ENTRY_PARENT_GEOMETRY;
  "ZINIT_GROWING_VIEW_CONTROL",ZINIT_GROWING_VIEW_CONTROL];;
leaf_audit zero_init_subrange_theorems zero_init_subrange_theorems;;
