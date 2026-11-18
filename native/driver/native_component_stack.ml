(* Native ABI profiles carry an explicit bound on private CPU stack use. *)
needs "native/driver/native_component.ml";;
needs "native/driver/driver.ml";;

let component_stack_saved = new_definition
 `component_stack_saved reserve (stackpointer:int64) (a:int64) <=>
    val stackpointer <= val a + reserve /\ val a < val stackpointer`;;

let component_stack_place = new_definition
 `component_stack_place reserve c (mc:byte list) pc t (stackpointer:int64) <=>
    nonoverlapping (tregs t 0,192) (word pc,LENGTH mc) /\
    (!r. tisa_rw (component_decls c) r
         ==> nonoverlapping (tisa_base t r,val(tisa_len t r)) (word pc,LENGTH mc)) /\
    reserve <= val stackpointer /\ val stackpointer + 8 <= 2 EXP 64 /\
    nonoverlapping (word_sub stackpointer (word reserve),reserve + 8) (word pc,LENGTH mc) /\
    (val(tregs t 0) + 192 <= val stackpointer - reserve \/ val stackpointer + 8 <= val(tregs t 0)) /\
    (!r. tisa_readable (component_decls c) r
         ==> val(tisa_len t r) = 0 \/
             val(tisa_base t r) + val(tisa_len t r) <= val stackpointer - reserve \/
             val stackpointer + 8 <= val(tisa_base t r))`;;

let component_stack_image = new_definition
 `component_stack_image reserve c mc pc <=>
    !t stackpointer returnaddress r14v r15v.
      component_entry c t /\ component_stack_place reserve c mc pc t stackpointer
      ==> ensures x86
          (\s. bytes_loaded s (word pc) mc /\ read RIP s = word pc /\
               read RSP s = stackpointer /\ read (memory :> bytes64 stackpointer) s = returnaddress /\
               tisa_x86_rel t s /\ read R14 s = r14v /\ read R15 s = r15v)
          (\s. read RIP s = returnaddress /\ read RSP s = word_add stackpointer (word 8) /\
               read RBX s = tregs t 9 /\ read R12 s = tregs t 10 /\
               read R13 s = tregs t 11 /\ read R14 s = r14v /\ read R15 s = r15v /\
               (?k u. component_run c t = TStop k u /\ read RAX s = tisa_fword u 19 /\
                      !a. ~component_stack_saved reserve stackpointer a ==> read memory s a = tmem u a))
          (MAYCHANGE [RIP;RSP;RAX;RBX;RCX;RDX;RSI;R8;R9;R10;R11;R12;R13;R14;R15] ,,
           MAYCHANGE [CF;PF;AF;ZF;SF;OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`;;

let COMPONENT_STACK_BASE_PLACE = prove
 (`!c mc pc t stackpointer. component_stack_place 40 c mc pc t stackpointer <=> component_place c mc pc t stackpointer`,
  REWRITE_TAC[component_stack_place;component_place] THEN CONV_TAC NUM_REDUCE_CONV);;
let COMPONENT_STACK_BASE_SAVED = prove
 (`!stackpointer a. component_stack_saved 40 stackpointer a <=> tisa_saved stackpointer a`,
  REWRITE_TAC[component_stack_saved;tisa_saved]);;
let COMPONENT_STACK_BASE_IMAGE = prove
 (`!c mc pc. component_stack_image 40 c mc pc <=> component_image c mc pc`,
  REWRITE_TAC[component_stack_image;component_image;COMPONENT_STACK_BASE_PLACE;
              COMPONENT_STACK_BASE_SAVED]);;

let COMPONENT_STACK_SAVED_MONO = prove
 (`!n m stackpointer a. n <= m /\ component_stack_saved n stackpointer a ==> component_stack_saved m stackpointer a`,
  REWRITE_TAC[component_stack_saved] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let COMPONENT_STACK_CONTAINED = prove
 (`!stackpointer n m. n <= m /\ m <= val(stackpointer:int64)
     ==> contained (word_sub stackpointer (word n),n + 8) (word_sub stackpointer (word m),m + 8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `m < 2 EXP 64 /\ n < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `stackpointer:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[CONTAINED_QFREE;DIMINDEX_64;
    WORD_RULE `word_sub (word_sub stackpointer (word n)) (word_sub stackpointer (word m)):int64 = word_sub (word m) (word n)`] THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64;MOD_LT] THEN ASM_ARITH_TAC);;

let COMPONENT_STACK_CONTAINED_SELF = prove
 (`!(p:int64) n. contained (p,n) (p,n)`,
  REWRITE_TAC[CONTAINED] THEN MESON_TAC[]);;

let COMPONENT_STACK_PLACE_MONO = prove
 (`!n m c mc pc t stackpointer.
     n <= m /\ component_stack_place m c mc pc t stackpointer
     ==> component_stack_place n c mc pc t stackpointer`,
  REPEAT GEN_TAC THEN REWRITE_TAC[component_stack_place] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST
   [ASM_ARITH_TAC;
    MATCH_MP_TAC NONOVERLAPPING_SUBREGIONS THEN
    MAP_EVERY EXISTS_TAC [`word_sub stackpointer (word m):int64`;`m + 8`;
                          `word pc:int64`;`LENGTH(mc:byte list)`] THEN
    ASM_REWRITE_TAC[COMPONENT_STACK_CONTAINED_SELF] THEN
    MATCH_MP_TAC COMPONENT_STACK_CONTAINED THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_readable`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let COMPONENT_STACK_IMAGE_MONO = prove
 (`!n m c mc pc.
     n <= m /\ component_stack_image n c mc pc
     ==> component_stack_image m c mc pc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[component_stack_image] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:tisa_state`;`stackpointer:int64`;`returnaddress:int64`;
                                `r14v:int64`;`r15v:int64`] o
    REWRITE_RULE[component_stack_image] o
    check (fun th -> fst(strip_comb(concl th)) = `component_stack_image`)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPONENT_STACK_PLACE_MONO THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP DRV_ENSURES_WEAKEN)] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[];
    X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`k:num`;`u:tisa_state`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[COMPONENT_STACK_SAVED_MONO];
    REWRITE_TAC[SUBSUMED_REFL]]);;

let native_component_stack_theorems =
 ["COMPONENT_STACK_BASE_PLACE",COMPONENT_STACK_BASE_PLACE;
  "COMPONENT_STACK_BASE_SAVED",COMPONENT_STACK_BASE_SAVED;
  "COMPONENT_STACK_BASE_IMAGE",COMPONENT_STACK_BASE_IMAGE;
  "COMPONENT_STACK_SAVED_MONO",COMPONENT_STACK_SAVED_MONO;
  "COMPONENT_STACK_CONTAINED",COMPONENT_STACK_CONTAINED;
  "COMPONENT_STACK_CONTAINED_SELF",COMPONENT_STACK_CONTAINED_SELF;
  "COMPONENT_STACK_PLACE_MONO",COMPONENT_STACK_PLACE_MONO;
  "COMPONENT_STACK_IMAGE_MONO",COMPONENT_STACK_IMAGE_MONO];;
