(* Cleared machine words establish the bootstrap's zero-memory predicate. *)
needs "native/hol/zero_init_views.ml";;
needs "native/hol/boot_memory.ml";;

let zinit_boot_slots = new_definition
 `zinit_boot_slots = [4;10;14;20;26;32;50;16;22;28;34]`;;

let ZINIT_BOOT_SLOTS_EVEN = prove
 (`ALL EVEN zinit_boot_slots`,
  REWRITE_TAC[zinit_boot_slots;ALL] THEN CONV_TAC NUM_REDUCE_CONV);;

let ZINIT_BOOT_SUPPORTED = prove
 (`!bw. ALL (zinit_supported (zinit_word_view bw)) zinit_boot_slots <=>
        ALL (\slot. val(bw(slot + 1)) DIV 8 <= 4294967295) zinit_boot_slots`,
  GEN_TAC THEN REWRITE_TAC[zinit_boot_slots;ALL] THEN
  SIMP_TAC[ZINIT_VIEW_SUPPORTED;
    EQT_ELIM(NUM_REDUCE_CONV
      `EVEN 4 /\ EVEN 10 /\ EVEN 14 /\ EVEN 20 /\ EVEN 26 /\
       EVEN 32 /\ EVEN 50 /\ EVEN 16 /\ EVEN 22 /\ EVEN 28 /\ EVEN 34`)]);;

let ZINIT_ZERO_NUMBER = prove
 (`!bw slots m slot i. zinit_zero bw slots m /\ MEM slot slots /\
                       8 * i + 8 <= val(bw(slot + 1))
       ==> pl_mw m (bw slot) i = 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zinit_zero;pl_mw] THEN STRIP_TAC THEN
  SUBGOAL_THEN `drv_word m (word_add ((bw:num->int64) slot) (word(8 * i))) = word 0`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[VAL_WORD_0]]);;

let ZINIT_BOOT_ZERO = prove
 (`!bw m. hol_boot_lengths bw /\ zinit_zero bw zinit_boot_slots m
       ==> hol_boot_zero bw m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[hol_boot_lengths] o
    check (fun th -> zinit_app "hol_boot_lengths" (concl th))) THEN
  REWRITE_TAC[hol_boot_zero] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  MATCH_MP_TAC ZINIT_ZERO_NUMBER THEN EXISTS_TAC `zinit_boot_slots` THEN
  ASM_REWRITE_TAC[zinit_boot_slots;MEM] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let ZINIT_BOOT_ZERO_VIEW = prove
 (`!bw m. hol_boot_lengths bw /\ zinit_zero (zinit_word_view bw) zinit_boot_slots m
       ==> hol_boot_zero bw m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ZINIT_BOOT_ZERO THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ZINIT_VIEW_ZERO_PARENT THEN
  ASM_REWRITE_TAC[ZINIT_BOOT_SLOTS_EVEN]);;
