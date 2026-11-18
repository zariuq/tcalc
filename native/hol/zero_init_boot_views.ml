(* Minimal count/header views and complete-word mark views for bootstrap. *)
needs "native/hol/zero_init_boot.ml";;
needs "native/leaves/common/leaf_join_lib.ml";;

let zinit_boot_view = new_definition
 `zinit_boot_view (bw:num->int64) k =
    if MEM k [5;11;15;21;27;33] then word 8
    else if k = 51 then word 16
    else if MEM k [17;23;29;35] then zinit_round(bw k)
    else bw k`;;

let zinit_boot_marks = new_definition
 `zinit_boot_marks = [16;22;28;34]`;;

let ZINIT_BOOT_VIEW_BASE = prove
 (`!bw slot. MEM slot zinit_boot_slots ==> zinit_boot_view bw slot = bw slot`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zinit_boot_slots;MEM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[zinit_boot_view;MEM] THEN CONV_TAC NUM_REDUCE_CONV);;

let ZINIT_BOOT_VIEW_SUBRANGE = prove
 (`!bw slot. hol_boot_lengths bw /\ MEM slot zinit_boot_slots
     ==> zinit_boot_view bw slot = bw slot /\
         val(zinit_boot_view bw (slot + 1)) <= val(bw(slot + 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC ZINIT_BOOT_VIEW_BASE THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[hol_boot_lengths] o
      check (fun th -> zinit_app "hol_boot_lengths" (concl th))) THEN
    UNDISCH_TAC `MEM (slot:num) zinit_boot_slots` THEN
    REWRITE_TAC[zinit_boot_slots;MEM] THEN
    REPEAT(DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
    TRY(DISCH_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC[zinit_boot_view;MEM] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[ZINIT_ROUND_VALUE;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]);;

let ZINIT_BOOT_VIEW_WORD = prove
 (`!bw m slot i.
     zinit_zero (zinit_boot_view bw) zinit_boot_slots m /\
     MEM slot zinit_boot_slots /\ 8 * i + 8 <= val(zinit_boot_view bw (slot + 1))
     ==> pl_mw m (bw slot) i = 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`zinit_boot_view (bw:num->int64)`;`zinit_boot_slots`;`m:int64->byte`;
                `slot:num`;`i:num`] ZINIT_ZERO_NUMBER) THEN
  ASM_SIMP_TAC[ZINIT_BOOT_VIEW_BASE]);;

let ZINIT_BOOT_VIEW_ZERO = prove
 (`!bw m. zinit_zero (zinit_boot_view bw) zinit_boot_slots m ==> hol_boot_zero bw m`,
  MAP_EVERY X_GEN_TAC [`bw:num->int64`;`m:int64->byte`] THEN DISCH_TAC THEN
  REWRITE_TAC[hol_boot_zero] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  W(fun (_,goal) ->
    let _,args = strip_comb(lhs goal) in
    let slot = rand(el 1 args) and index = el 2 args in
    MATCH_MP_TAC(SPECL [`bw:num->int64`;`m:int64->byte`;slot;index] ZINIT_BOOT_VIEW_WORD)) THEN
  ASM_REWRITE_TAC[zinit_boot_slots;MEM;zinit_boot_view] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[ZINIT_ROUND_WORDS;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let ZINIT_BOOT_VIEW_SUPPORTED = prove
 (`!bw. ALL (zinit_supported (zinit_boot_view bw)) zinit_boot_slots <=>
        ALL (\slot. val(bw(slot + 1)) DIV 8 <= 4294967295) zinit_boot_marks`,
  GEN_TAC THEN
  REWRITE_TAC[zinit_boot_slots;zinit_boot_marks;ALL;zinit_supported;zinit_boot_view;MEM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[ZINIT_ROUND_DIV;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let ZINIT_BOOT_VIEW_COUNTS_SUPPORTED = prove
 (`!bw. ALL (zinit_supported (zinit_boot_view bw)) [4;10;14;20;26;32;50]`,
  GEN_TAC THEN REWRITE_TAC[ALL;zinit_supported;zinit_boot_view;MEM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let ZINIT_BOOT_VIEW_LARGE_COUNT = prove
 (`zinit_supported (zinit_boot_view (\k. word 34359738368)) 4 /\
   ~zinit_supported (zinit_word_view (\k. word 34359738368)) 4`,
  REWRITE_TAC[zinit_supported;zinit_boot_view;zinit_word_view;MEM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[ZINIT_ROUND_DIV;ZINIT_ROUND_VALUE;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let zero_init_boot_view_theorems =
 ["ZINIT_BOOT_VIEW_BASE",ZINIT_BOOT_VIEW_BASE;
  "ZINIT_BOOT_VIEW_SUBRANGE",ZINIT_BOOT_VIEW_SUBRANGE;
  "ZINIT_BOOT_VIEW_WORD",ZINIT_BOOT_VIEW_WORD;
  "ZINIT_BOOT_VIEW_ZERO",ZINIT_BOOT_VIEW_ZERO;
  "ZINIT_BOOT_VIEW_SUPPORTED",ZINIT_BOOT_VIEW_SUPPORTED;
  "ZINIT_BOOT_VIEW_COUNTS_SUPPORTED",ZINIT_BOOT_VIEW_COUNTS_SUPPORTED;
  "ZINIT_BOOT_VIEW_LARGE_COUNT",ZINIT_BOOT_VIEW_LARGE_COUNT];;
leaf_audit zero_init_boot_view_theorems zero_init_boot_view_theorems;;
