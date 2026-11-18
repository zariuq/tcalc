(* Native components share the runtime frame, regions and calling convention. *)
needs "native/driver/driver_leaf.ml";;
needs "native/driver/driver_fuel.ml";;

let native_component_INDUCT,native_component_RECURSION = define_type
 "native_component = NativeComponent ((num#num#num)list) ((num#tisa_ty#num)list) (tisa_state->tisa_result)";;

let component_decls = define
 `component_decls (NativeComponent ds init run) = ds`;;
let component_inits = define
 `component_inits (NativeComponent ds init run) = init`;;
let component_run = define
 `component_run (NativeComponent ds init run) = run`;;

let COMPONENT_CASES = prove
 (`!c. c = NativeComponent (component_decls c) (component_inits c) (component_run c)`,
  MATCH_MP_TAC native_component_INDUCT THEN
  REWRITE_TAC[component_decls;component_inits;component_run]);;

let component_entry = new_definition
 `component_entry c t <=>
    val(tisa_frame t) + 192 <= 2 EXP 64 /\
    val(tisa_fword t 21) <= val(tisa_fword t 20) /\
    tisa_decls_ok t 0 (component_decls c) /\
    tisa_init_ok t (component_inits c)`;;

let component_place = new_definition
 `component_place c (mc:byte list) pc t (stackpointer:int64) <=>
    nonoverlapping (tregs t 0,192) (word pc,LENGTH mc) /\
    (!r. tisa_rw (component_decls c) r
         ==> nonoverlapping (tisa_base t r,val(tisa_len t r)) (word pc,LENGTH mc)) /\
    40 <= val stackpointer /\ val stackpointer + 8 <= 2 EXP 64 /\
    nonoverlapping (word_sub stackpointer (word 40),48) (word pc,LENGTH mc) /\
    (val(tregs t 0) + 192 <= val stackpointer - 40 \/
     val stackpointer + 8 <= val(tregs t 0)) /\
    (!r. tisa_readable (component_decls c) r
         ==> val(tisa_len t r) = 0 \/
             val(tisa_base t r) + val(tisa_len t r) <= val stackpointer - 40 \/
             val stackpointer + 8 <= val(tisa_base t r))`;;

(* A component supplies termination and the state laws used by a caller.
   Its mathematical operation is component_run; component_image connects
   that operation to the bytes rather than assuming the connection. *)
let component_ok = new_definition
 `component_ok c <=>
    LENGTH(component_decls c) <= 9 /\
    ALL (\v:num#tisa_ty#num. FST(SND v) = TyU64) (component_inits c) /\
    (!t. ?k u. component_run c t = TStop k u) /\
    (!t k u. component_entry c t /\ component_run c t = TStop k u
       ==> tisa_fuel_le (component_decls c) t u /\ tisa_fword u 18 = word k)`;;

let component_image = new_definition
 `component_image c mc pc <=>
    !t stackpointer returnaddress r14v r15v.
      component_entry c t /\ component_place c mc pc t stackpointer
      ==> ensures x86
          (\s. bytes_loaded s (word pc) mc /\ read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               tisa_x86_rel t s /\ read R14 s = r14v /\ read R15 s = r15v)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read RBX s = tregs t 9 /\ read R12 s = tregs t 10 /\
               read R13 s = tregs t 11 /\ read R14 s = r14v /\ read R15 s = r15v /\
               (?k u. component_run c t = TStop k u /\ read RAX s = tisa_fword u 19 /\
                      !a. ~tisa_saved stackpointer a ==> read memory s a = tmem u a))
          (MAYCHANGE [RIP;RSP;RAX;RBX;RCX;RDX;RSI;R8;R9;R10;R11;R12;R13;R14;R15] ,,
           MAYCHANGE [CF;PF;AF;ZF;SF;OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`;;

let COMPONENT_STOP = prove
 (`!c t. component_ok c ==> ?k u. component_run c t = TStop k u`,
  REWRITE_TAC[component_ok] THEN MESON_TAC[]);;

let COMPONENT_ENTRY_AS_P1 = prove
 (`!c t. component_entry c t <=>
     tisa_entry_ok (TProg (component_decls c) (component_inits c) TSkip) t`,
  REWRITE_TAC[component_entry;tisa_entry_ok]);;

let COMPONENT_FRAME_SEP = prove
 (`!c t. component_ok c /\ component_entry c t
         ==> tisa_frame_sep (component_decls c) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[component_ok] o
    check (fun th -> fst(strip_comb(concl th)) = `component_ok`)) THEN
  MP_TAC(ISPECL [`component_decls c`;`component_inits c`;`TSkip`;`t:tisa_state`]
               TISA_ENTRY_FRAME_SEP) THEN
  ASM_REWRITE_TAC[GSYM COMPONENT_ENTRY_AS_P1]);;

let COMPONENT_INIT_U64 = prove
 (`!c t. component_ok c ==> tisa_init_ok t (component_inits c)`,
  REWRITE_TAC[component_ok] THEN MESON_TAC[TISA_INIT_U64]);;

let COMPONENT_RUN_LAWS = prove
 (`!c t k u. component_ok c /\ component_entry c t /\ component_run c t = TStop k u
             ==> tisa_fuel_le (component_decls c) t u /\ tisa_fword u 18 = word k`,
  REWRITE_TAC[component_ok] THEN MESON_TAC[]);;

let COMPONENT_RUN_FRAME = prove
 (`!c t k u. component_ok c /\ component_entry c t /\ component_run c t = TStop k u
             ==> tisa_keeps (component_decls c) t u /\
                 tisa_fword u 20 = tisa_fword t 20 /\ tisa_fword u 18 = word k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:native_component`;`t:tisa_state`;`k:num`;`u:tisa_state`] COMPONENT_RUN_LAWS) THEN
  ASM_REWRITE_TAC[tisa_fuel_le] THEN MESON_TAC[]);;

let COMPONENT_RUN_KEEPS = prove
 (`!c t k u. component_ok c /\ component_entry c t /\ component_run c t = TStop k u
             ==> tisa_keeps (component_decls c) t u`,
  MESON_TAC[COMPONENT_RUN_FRAME]);;

let COMPONENT_RUN_FUEL = prove
 (`!c t k u. component_ok c /\ component_entry c t /\ component_run c t = TStop k u
             ==> val(tisa_fword t 21) <= val(tisa_fword u 21) /\
                 val(tisa_fword u 21) <= val(tisa_fword t 20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[component_entry] o
    check (fun th -> fst(strip_comb(concl th)) = `component_entry`)) THEN
  MP_TAC(SPECL [`c:native_component`;`t:tisa_state`;`k:num`;`u:tisa_state`] COMPONENT_RUN_LAWS) THEN
  ASM_REWRITE_TAC[tisa_fuel_le;tisa_fuel_ok] THEN MESON_TAC[]);;

let COMPONENT_RUN_STATUS = prove
 (`!c t k u. component_ok c /\ component_entry c t /\ component_run c t = TStop k u
             ==> tisa_fword u 18 = word k`,
  MESON_TAC[COMPONENT_RUN_LAWS]);;

let native_component_theorems =
 ["COMPONENT_CASES",COMPONENT_CASES;"COMPONENT_STOP",COMPONENT_STOP;
  "COMPONENT_ENTRY_AS_P1",COMPONENT_ENTRY_AS_P1;"COMPONENT_RUN_LAWS",COMPONENT_RUN_LAWS;
  "COMPONENT_FRAME_SEP",COMPONENT_FRAME_SEP;"COMPONENT_INIT_U64",COMPONENT_INIT_U64;
  "COMPONENT_RUN_FRAME",COMPONENT_RUN_FRAME;"COMPONENT_RUN_KEEPS",COMPONENT_RUN_KEEPS;
  "COMPONENT_RUN_FUEL",COMPONENT_RUN_FUEL;
  "COMPONENT_RUN_STATUS",COMPONENT_RUN_STATUS];;
