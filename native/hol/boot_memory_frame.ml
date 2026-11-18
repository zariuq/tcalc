(* Bootstrap memory facts survive writes to separated control storage. *)
needs "native/hol/boot_memory.ml";;
needs "native/hol/driver_region_frame.ml";;

let hol_boot_frame_slots = new_definition
 `hol_boot_frame_slots = [4;10;14;20;26;32;50;16;22;28;34;62]`;;

let hol_boot_frame_regions = new_definition
 `hol_boot_frame_regions (bw:num->int64) cfr d ctl nctl <=>
    48 <= val cfr /\
    !slot. MEM slot hol_boot_frame_slots
           ==> val(bw slot) + val(bw(slot + 1)) < 2 EXP 64 /\
               drv_apart (word_sub cfr (word 48)) 304 (bw slot) (val(bw(slot + 1))) /\
               drv_apart d 64 (bw slot) (val(bw(slot + 1))) /\
               drv_apart ctl (8 * nctl) (bw slot) (val(bw(slot + 1)))`;;

let HOL_BOOT_REGION_FRAME = prove
 (`!bw cfr d ctl nctl before after slot.
     hol_boot_frame_regions bw cfr d ctl nctl /\ MEM slot hol_boot_frame_slots /\
     (!a. ~drv_stack cfr a /\ ~drv_in a d 64 /\ ~drv_in a ctl (8 * nctl)
          ==> (after:int64->byte) a = before a)
     ==> !a. drv_in a (bw slot) (val(bw(slot + 1))) ==> after a = before a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_boot_frame_regions] THEN STRIP_TAC THEN
  MATCH_MP_TAC DRV_MEMORY_FRAME_REGION THEN
  MAP_EVERY EXISTS_TAC [`cfr:int64`;`d:int64`;`ctl:int64`;`nctl:num`] THEN
  ASM_SIMP_TAC[]);;

let HOL_BOOT_WORD_FRAME = prove
 (`!bw cfr d ctl nctl before after.
     hol_boot_frame_regions bw cfr d ctl nctl /\
     (!a. ~drv_stack cfr a /\ ~drv_in a d 64 /\ ~drv_in a ctl (8 * nctl)
          ==> (after:int64->byte) a = before a)
     ==> !slot i. MEM slot hol_boot_frame_slots /\ 8 * i + 8 <= val(bw(slot + 1))
                  ==> pl_mw after (bw slot) i = pl_mw before (bw slot) i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`slot:num`;`i:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC DRV_REGION_WORD_AGREE THEN EXISTS_TAC `val((bw:num->int64)(slot + 1))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [hol_boot_frame_regions] o
     check (fun th -> fst(strip_comb(concl th)) = `hol_boot_frame_regions`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `slot:num`)) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MATCH_MP_TAC HOL_BOOT_REGION_FRAME THEN
    MAP_EVERY EXISTS_TAC [`cfr:int64`;`d:int64`;`ctl:int64`;`nctl:num`] THEN ASM_REWRITE_TAC[]]);;

let HOL_BOOT_ZERO_WORD_FRAME = prove
 (`!bw before after.
     hol_boot_lengths bw /\ hol_boot_zero bw before /\
     (!slot i. MEM slot hol_boot_frame_slots /\ 8 * i + 8 <= val(bw(slot + 1))
                ==> pl_mw after (bw slot) i = pl_mw before (bw slot) i)
     ==> hol_boot_zero bw after`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[hol_boot_lengths] o
    check (fun th -> fst(strip_comb(concl th)) = `hol_boot_lengths`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[hol_boot_zero] o
    check (fun th -> fst(strip_comb(concl th)) = `hol_boot_zero`)) THEN
  SUBGOAL_THEN `8 <= val((bw:num->int64) 51)` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[hol_boot_zero] THEN
  ASM_SIMP_TAC[hol_boot_frame_slots;MEM;ARITH]);;

let HOL_BOOT_BYTES_FRAME = prove
 (`!bw cfr d ctl nctl before after.
     hol_boot_frame_regions bw cfr d ctl nctl /\ hol_boot_bytes_at bw before /\
     (!a. ~drv_stack cfr a /\ ~drv_in a d 64 /\ ~drv_in a ctl (8 * nctl)
          ==> (after:int64->byte) a = before a)
     ==> hol_boot_bytes_at bw after`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[hol_boot_bytes_at] o
    check (fun th -> fst(strip_comb(concl th)) = `hol_boot_bytes_at`)) THEN
  MP_TAC(SPECL [`bw:num->int64`;`cfr:int64`;`d:int64`;`ctl:int64`;`nctl:num`;
                `before:int64->byte`;`after:int64->byte`;`62`] HOL_BOOT_REGION_FRAME) THEN
  ASM_REWRITE_TAC[hol_boot_frame_slots;MEM] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  REWRITE_TAC[hol_boot_bytes_at] THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word_add ((bw:num->int64) 62) (word i):int64) = val(bw 62) + i`
   ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [hol_boot_frame_regions] o
     check (fun th -> fst(strip_comb(concl th)) = `hol_boot_frame_regions`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `62`)) THEN
    ASM_REWRITE_TAC[hol_boot_frame_slots;MEM] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `drv_in (word_add ((bw:num->int64) 62) (word i)) (bw 62) (val(bw 63))`
     ASSUME_TAC THENL
     [ASM_REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC;ASM_SIMP_TAC[]]]);;

let HOL_BOOT_MEMORY_FRAME = prove
 (`!bw cfr d ctl nctl before after.
     hol_boot_frame_regions bw cfr d ctl nctl /\ hol_boot_lengths bw /\
     hol_boot_zero bw before /\ hol_boot_bytes_at bw before /\
     (!a. ~drv_stack cfr a /\ ~drv_in a d 64 /\ ~drv_in a ctl (8 * nctl)
          ==> (after:int64->byte) a = before a)
     ==> hol_boot_zero bw after /\ hol_boot_bytes_at bw after`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOL_BOOT_ZERO_WORD_FRAME THEN EXISTS_TAC `before:int64->byte` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOL_BOOT_WORD_FRAME THEN
    MAP_EVERY EXISTS_TAC [`cfr:int64`;`d:int64`;`ctl:int64`;`nctl:num`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOL_BOOT_BYTES_FRAME THEN
    MAP_EVERY EXISTS_TAC [`cfr:int64`;`d:int64`;`ctl:int64`;`nctl:num`;`before:int64->byte`] THEN
    ASM_REWRITE_TAC[]]);;

let boot_memory_frame_theorems =
 ["HOL_BOOT_REGION_FRAME",HOL_BOOT_REGION_FRAME;"HOL_BOOT_WORD_FRAME",HOL_BOOT_WORD_FRAME;
  "HOL_BOOT_ZERO_WORD_FRAME",HOL_BOOT_ZERO_WORD_FRAME;"HOL_BOOT_BYTES_FRAME",HOL_BOOT_BYTES_FRAME;
  "HOL_BOOT_MEMORY_FRAME",HOL_BOOT_MEMORY_FRAME];;
