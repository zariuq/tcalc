(* ========================================================================= *)
(* How a native x86-64 state realizes a t-ISA p1 state, for images emitted   *)
(* by tcalc/tisa/tisa_x86.c: v0..v11 live in rdi rsi rdx rcx r8 r9 r10 r11   *)
(* rax rbx r12 r13 (r14 and r15 are the emitter's scratch), and the native   *)
(* memory is the t-ISA memory. A statement's code ends either at the next    *)
(* statement with the state it continues with, or at the epilogue with the   *)
(* stopped state's memory and its return value in rax.                       *)
(* ========================================================================= *)

needs "tisa/hol/tisa_p1.ml";;
needs "tisa/hol/tisa_x86_steps.ml";;

let tisa_x86_rel = new_definition
 `tisa_x86_rel (t:tisa_state) (s:x86state) <=>
    read RDI s = tregs t 0 /\ read RSI s = tregs t 1 /\ read RDX s = tregs t 2 /\
    read RCX s = tregs t 3 /\ read R8 s = tregs t 4 /\ read R9 s = tregs t 5 /\
    read R10 s = tregs t 6 /\ read R11 s = tregs t 7 /\ read RAX s = tregs t 8 /\
    read RBX s = tregs t 9 /\ read R12 s = tregs t 10 /\ read R13 s = tregs t 11 /\
    read memory s = tmem t`;;

let tisa_x86_post = define
 `(tisa_x86_post next epi (TCont t) s <=>
     read RIP s = word next /\ tisa_x86_rel t s) /\
  (tisa_x86_post next epi (TStop k t) s <=>
     read RIP s = word epi /\ read memory s = tmem t /\ read RAX s = tisa_fword t 19)`;;

(* Everything a statement's code may change: never rdi (v0, the frame) nor
   rsp (the wrapper owns the stack). *)
let TISA_FRAME =
 `MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RSI; R8; R9; R10; R11; R12; R13; R14; R15] ,,
  MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory]`;;

let TISA_REL_CONV =
  REWRITE_CONV[tisa_x86_post; tisa_x86_rel; tisa_setreg; tregs; tmem; tisa_store] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[];;
