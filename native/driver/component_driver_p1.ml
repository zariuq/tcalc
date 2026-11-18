(* Recover the existing p1 driver contract through the component theorem. *)
needs "native/driver/component_driver.ml";;
needs "native/driver/native_component_p1.ml";;

let COMPONENT_P1_STEP = prove
 (`!progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw st.
     component_step_ok (\j. component_of_p1 (progs j))
       pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw st <=>
     drv_step_ok progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw st`,
  REWRITE_TAC[component_step_ok;drv_step_ok;COMPONENT_P1_FIELDS]);;

let COMPONENT_P1_STEP_FUNCTION = prove
 (`!progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw.
     component_step_ok (\j. component_of_p1 (progs j))
       pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw =
     drv_step_ok progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw`,
  REWRITE_TAC[FUN_EQ_THM;COMPONENT_P1_STEP]);;

let COMPONENT_P1_SEM = prove
 (`!progs bw ctl budget cfr sts i m used res.
     component_drv_sem (\j. component_of_p1 (progs j))
       bw ctl budget cfr sts i m used res <=>
     drv_sem progs bw ctl budget cfr sts i m used res`,
  MAP_EVERY X_GEN_TAC [`progs:num->tisa_prog`;`bw:num->int64`;`ctl:int64`;
                      `budget:int64`;`cfr:int64`] THEN
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[component_drv_sem;drv_sem;COMPONENT_P1_ENTRY;COMPONENT_P1_FIELDS]);;

let DRV_CORRECT_FROM_COMPONENTS = prove
 (`!progs lpc lmc nl pc stackpointer d plan ns ctl nctl bind nbw leaves bw stepl budget used0 m0
    ret rbxv rbpv r12v r13v r14v r15v.
     (!j. j < nl ==> tisa_leaf_wf (progs j) /\ tisa_leaf_spec (progs j) (lmc j) (lpc j)) /\
     drv_layout pc (word_sub stackpointer (word 248)) d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     ALL (drv_step_ok progs pc (word_sub stackpointer (word 248)) d plan ns nctl bind nbw leaves nl lpc lmc bw)
         stepl /\
     drv_holds m0 d plan ns ctl bind leaves budget used0 stepl bw nbw lpc nl /\
     drv_code m0 pc drv_mc /\
     (!j. j < nl ==> drv_code m0 (lpc j) (lmc j))
     ==> ensures x86
          (\s. read RIP s = word pc /\ read RSP s = stackpointer /\ read RDI s = d /\
               read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
               read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
               read memory s = m0 /\ read (memory :> bytes64 stackpointer) s = ret)
          (\s. read RIP s = ret /\ read RSP s = word_add stackpointer (word 8) /\
               read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
               read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
               ?res. drv_sem progs bw ctl budget (word_sub stackpointer (word 248)) stepl 0 m0 used0 res /\
                     read RAX s = FST res /\
                     (!a. ~drv_stack (word_sub stackpointer (word 248)) a
                          ==> read memory s a = drv_final d plan res a) /\
                     (!a. drv_static pc (word_sub stackpointer (word 248)) d plan ns bind nbw leaves nl lpc lmc a /\
                          ~drv_in a (word_add d (word 48)) 16
                          ==> read memory s a = m0 a) /\
                     (!a. ~drv_stack (word_sub stackpointer (word 248)) a /\
                          ~drv_in a (word_add d (word 48)) 16 /\
                          (!st r. MEM st stepl /\ tisa_rw (tisa_decls (progs (val(EL 0 st)))) r
                                  ==> ~drv_in a (drv_base bw st r) (val(drv_len bw st r))) /\
                          (!st. MEM st stepl
                                ==> ~drv_in a (word_add ctl (word(8 * val(EL 17 st)))) 8)
                          ==> read memory s a = m0 a))
          (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                      R12; R13; R14; R15; RBP] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`,

  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`\j:num. component_of_p1 ((progs:num->tisa_prog) j)`;
                `lpc:num->num`; `lmc:num->byte list`;
                `nl:num`; `pc:num`; `stackpointer:int64`; `d:int64`; `plan:int64`; `ns:num`;
                `ctl:int64`; `nctl:num`; `bind:int64`; `nbw:num`; `leaves:int64`;
                `bw:num->int64`; `stepl:(int64 list)list`; `budget:int64`; `used0:int64`;
                `m0:int64->byte`; `ret:int64`; `rbxv:int64`; `rbpv:int64`; `r12v:int64`;
                `r13v:int64`; `r14v:int64`; `r15v:int64`] COMPONENT_DRV_CORRECT) THEN
  REWRITE_TAC[COMPONENT_P1_IMAGE;COMPONENT_P1_STEP_FUNCTION;
              COMPONENT_P1_SEM;COMPONENT_P1_FIELDS] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `tisa_leaf_wf ((progs:num->tisa_prog) (j:num)) /\
                 tisa_leaf_spec (progs j) ((lmc:num->byte list) j) ((lpc:num->num) j)`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN
      ASM_SIMP_TAC[COMPONENT_P1_OK];
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[]]);;

if not (aconv (concl DRV_CORRECT_FROM_COMPONENTS) (concl DRV_CORRECT))
then failwith "Recovered driver contract differs from the p1 API";;

let component_driver_p1_theorems =
 ["COMPONENT_P1_STEP",COMPONENT_P1_STEP;
  "COMPONENT_P1_STEP_FUNCTION",COMPONENT_P1_STEP_FUNCTION;
  "COMPONENT_P1_SEM",COMPONENT_P1_SEM;
  "DRV_CORRECT_FROM_COMPONENTS",DRV_CORRECT_FROM_COMPONENTS];;
