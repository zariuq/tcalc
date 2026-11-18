(* Typed hot inputs use the same component data and native image contract. *)
needs "native/driver/native_component.ml";;

let component_typed_ok = new_definition
 `component_typed_ok c <=>
    LENGTH(component_decls c) <= 9 /\
    (!t. ?k u. component_run c t = TStop k u) /\
    (!t k u. component_entry c t /\ component_run c t = TStop k u
       ==> tisa_fuel_le (component_decls c) t u /\ tisa_fword u 18 = word k)`;;

let COMPONENT_U64_PROFILE = prove
 (`!c. component_ok c <=> component_typed_ok c /\
    ALL (\v:num#tisa_ty#num. FST(SND v) = TyU64) (component_inits c)`,
  REWRITE_TAC[component_ok;component_typed_ok] THEN MESON_TAC[]);;

let COMPONENT_TYPED_STOP = prove
 (`!c t. component_typed_ok c ==> ?k u. component_run c t = TStop k u`,
  REWRITE_TAC[component_typed_ok] THEN MESON_TAC[]);;

let COMPONENT_TYPED_FRAME_SEP = prove
 (`!c t. component_typed_ok c /\ component_entry c t
     ==> tisa_frame_sep (component_decls c) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[component_typed_ok] o
    check (fun th -> fst(strip_comb(concl th)) = `component_typed_ok`)) THEN
  MP_TAC(ISPECL [`component_decls c`;`component_inits c`;`TSkip`;`t:tisa_state`]
    TISA_ENTRY_FRAME_SEP) THEN ASM_REWRITE_TAC[GSYM COMPONENT_ENTRY_AS_P1]);;

let COMPONENT_TYPED_RUN_LAWS = prove
 (`!c t k u. component_typed_ok c /\ component_entry c t /\ component_run c t = TStop k u
     ==> tisa_fuel_le (component_decls c) t u /\ tisa_fword u 18 = word k`,
  REWRITE_TAC[component_typed_ok] THEN MESON_TAC[]);;

let COMPONENT_TYPED_RUN_FRAME = prove
 (`!c t k u. component_typed_ok c /\ component_entry c t /\ component_run c t = TStop k u
     ==> tisa_keeps (component_decls c) t u /\ tisa_fword u 20 = tisa_fword t 20 /\
         tisa_fword u 18 = word k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:native_component`;`t:tisa_state`;`k:num`;`u:tisa_state`] COMPONENT_TYPED_RUN_LAWS) THEN
  ASM_REWRITE_TAC[tisa_fuel_le] THEN MESON_TAC[]);;

let COMPONENT_TYPED_ENTRY_INIT = prove
 (`!c t. component_entry c t ==> tisa_init_ok t (component_inits c)`,
  REWRITE_TAC[component_entry] THEN MESON_TAC[]);;

let native_component_typed_theorems =
 ["COMPONENT_U64_PROFILE",COMPONENT_U64_PROFILE;
  "COMPONENT_TYPED_STOP",COMPONENT_TYPED_STOP;
  "COMPONENT_TYPED_FRAME_SEP",COMPONENT_TYPED_FRAME_SEP;
  "COMPONENT_TYPED_RUN_LAWS",COMPONENT_TYPED_RUN_LAWS;
  "COMPONENT_TYPED_RUN_FRAME",COMPONENT_TYPED_RUN_FRAME;
  "COMPONENT_TYPED_ENTRY_INIT",COMPONENT_TYPED_ENTRY_INIT];;
