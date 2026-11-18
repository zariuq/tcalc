(* Read-only ranges kept by initialization, including every refusal. *)
needs "native/hol/zero_init_preserve.ml";;

let zinit_readonly = new_definition
 `zinit_readonly (bw:num->int64) slots ctl cfr d b n <=>
    48 <= val cfr /\ val b + n <= 2 EXP 64 /\
    drv_apart (word_sub cfr (word 48)) 304 b n /\
    drv_apart b n d 64 /\ drv_apart b n ctl 8 /\
    (!slot. MEM slot slots ==> drv_apart b n (bw slot) (val(bw(slot + 1))))`;;

let ZINIT_APART_OUTSIDE = prove
 (`!a b n c k. drv_in a b n /\ drv_apart b n c k ==> ~drv_in a c k`,
  REWRITE_TAC[drv_in;drv_apart] THEN ARITH_TAC);;

let ZINIT_READONLY_BYTE = prove
 (`!bw slots ctl cfr d b n i.
     zinit_readonly bw slots ctl cfr d b n /\ i < n
     ==> ~drv_stack cfr (word_add b (word i)) /\
         ~drv_in (word_add b (word i)) d 64 /\
         ~drv_in (word_add b (word i)) ctl 8 /\
         (!slot. MEM slot slots
                 ==> ~drv_in (word_add b (word i)) (bw slot) (val(bw(slot + 1))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zinit_readonly] THEN STRIP_TAC THEN
  SUBGOAL_THEN `drv_in (word_add (b:int64) (word i)) b n` ASSUME_TAC THENL
   [MP_TAC(SPECL [`b:int64`;`i:num`] TISA_VAL_OFFSET) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ASM_REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [`b:int64`;`n:num`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ZINIT_APART_OUTSIDE THEN MAP_EVERY EXISTS_TAC [`b:int64`;`n:num`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ZINIT_APART_OUTSIDE THEN MAP_EVERY EXISTS_TAC [`b:int64`;`n:num`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `slot:num` THEN DISCH_TAC THEN MATCH_MP_TAC ZINIT_APART_OUTSIDE THEN
    MAP_EVERY EXISTS_TAC [`b:int64`;`n:num`] THEN ASM_SIMP_TAC[]]);;

let ZINIT_READONLY_FRAME = prove
 (`!bw slots ctl cfr d b n m0 m.
     zinit_readonly bw slots ctl cfr d b n /\
     (!a. ~drv_stack cfr a /\ ~drv_in a d 64 /\ ~drv_in a ctl 8 /\
          (!slot. MEM slot slots ==> ~drv_in a (bw slot) (val(bw(slot + 1))))
          ==> m a = m0 a)
     ==> !i. i < n ==> m(word_add b (word i)) = m0(word_add b (word i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC (SPECL [`bw:num->int64`;`slots:num list`;`ctl:int64`;`cfr:int64`;
                        `d:int64`;`b:int64`;`n:num`;`i:num`] ZINIT_READONLY_BYTE) THEN
  ASM_REWRITE_TAC[]);;

let zero_init_readonly_theorems =
 ["ZINIT_APART_OUTSIDE",ZINIT_APART_OUTSIDE;"ZINIT_READONLY_BYTE",ZINIT_READONLY_BYTE;
  "ZINIT_READONLY_FRAME",ZINIT_READONLY_FRAME];;
leaf_audit zero_init_readonly_theorems zero_init_readonly_theorems;;
