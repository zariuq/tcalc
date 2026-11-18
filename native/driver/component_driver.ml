(* The 40-byte callee profile of the generic native-component driver. *)
needs "native/driver/stack_driver_load.ml";;

let COMPONENT_DRV_SEM_PROFILE40 = new_definition
 `component_drv_sem = stack_component_drv_sem 40`;;

let component_drv_sem = prove
 (`(component_drv_sem (progs:num->native_component) bw ctl budget cfr [] i m used
           (res:int64#num#(int64->byte)#int64) <=>
     res = (word 1, i, m, used)) /\
  (component_drv_sem progs bw ctl budget cfr (CONS st sts) i m used res <=>
     if val budget < val used then res = (word 3, i, m, used)
     else ?t k u. drv_child bw ctl budget cfr st m used t /\
                  component_entry (progs (val(EL 0 st))) t /\
                  component_run (progs (val(EL 0 st))) t = TStop k u /\
                  (if tisa_fword u 18 = word 1
                   then component_drv_sem progs bw ctl budget cfr sts (i + 1) (drv_after ctl st u)
                                (tisa_fword u 21) res
                   else res = (tisa_fword u 18, i, drv_after ctl st u, tisa_fword u 21)))`,
  REWRITE_TAC[COMPONENT_DRV_SEM_PROFILE40;stack_component_drv_sem;STACK_DRV_CHILD_BASE]);;

let COMPONENT_STEP_PROFILE40 = new_definition
 `component_step_ok = stack_component_step_ok 40`;;

let STACK_DRV_APART_PROFILE40 = prove
 (`!cfr b n. stack_drv_apart 40 cfr b n <=>
    drv_apart b n (word_sub cfr (word 48)) 304`,
  ONCE_REWRITE_TAC[DRV_APART_SYM] THEN REWRITE_TAC[STACK_DRV_APART_BASE]);;

let component_step_ok = prove
 (`component_step_ok (progs:num->native_component) pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw
              (st:int64 list) <=>
    LENGTH st = 18 /\ val(EL 0 st) < nl /\
    (!r. r < 9 ==> val(EL (1 + r) st) + 1 < nbw) /\
    (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\
    (!t. tregs t 0 = cfr /\
         (!r. r < 9 ==> tisa_base t r = drv_base bw st r /\ tisa_len t r = drv_len bw st r)
         ==> tisa_decls_ok t 0 (component_decls (progs (val(EL 0 st))))) /\
    (!r. tisa_readable (component_decls (progs (val(EL 0 st)))) r
         ==> drv_apart (drv_base bw st r) (val(drv_len bw st r)) (word_sub cfr (word 48)) 304) /\
    (!r a. tisa_rw (component_decls (progs (val(EL 0 st)))) r /\
           drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a
           ==> ~drv_in a (drv_base bw st r) (val(drv_len bw st r)))`,
  REWRITE_TAC[COMPONENT_STEP_PROFILE40;stack_component_step_ok;STACK_DRV_APART_PROFILE40]);;

let component_driver_profile40 th = REWRITE_RULE
 [GSYM COMPONENT_DRV_SEM_PROFILE40;GSYM COMPONENT_STEP_PROFILE40;
  STACK_DRV_CHILD_BASE;STACK_DRV_STACK_BASE;STACK_DRV_LAYOUT_BASE;
  COMPONENT_STACK_BASE_PLACE;COMPONENT_STACK_BASE_IMAGE] (SPEC `40` th);;

let COMPONENT_DRV_CHILD_OK = component_driver_profile40 STACK_COMPONENT_DRV_CHILD_OK;;
let COMPONENT_DRV_LOOP = component_driver_profile40 STACK_COMPONENT_DRV_LOOP;;
let COMPONENT_DRV_CORRECT_FRAME = component_driver_profile40 STACK_COMPONENT_DRV_CORRECT_FRAME;;
let COMPONENT_DRV_STEP_KEEPS = component_driver_profile40 STACK_COMPONENT_DRV_STEP_KEEPS;;
let COMPONENT_DRV_SEM_KEEPS = component_driver_profile40 STACK_COMPONENT_DRV_SEM_KEEPS;;
let COMPONENT_DRV_SEM_TWO_FIRED = component_driver_profile40 STACK_COMPONENT_DRV_SEM_TWO_FIRED;;
let COMPONENT_DRV_CORRECT = component_driver_profile40 STACK_COMPONENT_DRV_CORRECT;;

let component_driver_theorems =
 ["COMPONENT_DRV_CHILD_OK",COMPONENT_DRV_CHILD_OK;
  "COMPONENT_DRV_LOOP",COMPONENT_DRV_LOOP;
  "COMPONENT_DRV_CORRECT_FRAME",COMPONENT_DRV_CORRECT_FRAME;
  "COMPONENT_DRV_STEP_KEEPS",COMPONENT_DRV_STEP_KEEPS;
  "COMPONENT_DRV_SEM_KEEPS",COMPONENT_DRV_SEM_KEEPS;
  "COMPONENT_DRV_SEM_TWO_FIRED",COMPONENT_DRV_SEM_TWO_FIRED;
  "COMPONENT_DRV_CORRECT",COMPONENT_DRV_CORRECT];;
