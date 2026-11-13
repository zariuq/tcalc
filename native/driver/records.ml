(* ========================================================================= *)
(* The record loop, tcalc/native/driver/records.S, proved against            *)
(* s2n-bignum's x86 model over the plan driver's theorem DRV_CORRECT: for    *)
(* every set of plans and leaves, it runs the iterate of drv_sem over        *)
(* records that rec_run states.                                              *)
(*                                                                           *)
(* Each record charges one unit of fuel to the receipt (EXHAUSTED when the  *)
(* receipt has reached the allowance), runs the decode plan, reads the      *)
(* opcode, runs the handler plan the table names for it (UNSUPPORTED when   *)
(* it names none), and ends the loop FIRED when the END word is set. The    *)
(* first outcome other than FIRED ends the loop with that outcome. Since    *)
(* every run's receipt stays at or above the receipt it starts from         *)
(* (TISA_RUN_FUEL), the receipt rises by at least one per record: the loop  *)
(* stops, and the theorem is total.                                          *)
(*                                                                           *)
(*   REC_RUN       run, the subroutine that runs one plan by DRV_CORRECT.    *)
(*   REC_LOOP      the records, from the loop head to done, by induction on  *)
(*                 the fuel left.                                            *)
(*   REC_CORRECT   the call, entry to return: rec_run from the entry memory, *)
(*                 the receipt and the count written back (rec_final), the   *)
(*                 caller's registers restored, the fixed bytes unchanged.   *)
(*   REC_RUN_FUEL  the receipt never falls, and a run that starts within the *)
(*                 allowance ends within it.                                 *)
(*                                                                           *)
(* records.S calls the driver as the driver calls its leaves, by `call      *)
(* enter` and `enter: push r15; ret`; no indirect CALL or JMP (FF /2, FF /4) *)
(* appears, since the x86 model takes their target as relative to the next   *)
(* instruction, which on x86 it is not. Supported profile: user-mode shadow  *)
(* stacks (CET SHSTK) disabled. Under SHSTK the ret in enter faults; the     *)
(* x86 model has no shadow stack, so the theorems say nothing about it.      *)
(* ========================================================================= *)

needs "native/driver/driver_fuel.ml";;

let rec_mc = define_assert_from_elf "rec_mc"
  (tcalc_path "native/driver/build/records.o")
[
  0x53;                           (* push rbx *)
  0x55;                           (* push rbp *)
  0x41; 0x54;                     (* push r12 *)
  0x41; 0x55;                     (* push r13 *)
  0x41; 0x56;                     (* push r14 *)
  0x41; 0x57;                     (* push r15 *)
  0x48; 0x89; 0xfb;               (* mov rbx,rdi *)
  0x48; 0x8b; 0x6b; 0x38;         (* mov rbp,QWORD PTR [rbx+0x38] *)
  0x45; 0x31; 0xe4;               (* xor r12d,r12d *)
  0x4c; 0x8b; 0x3b;               (* mov r15,QWORD PTR [rbx] *)
  0x48; 0x3b; 0x6b; 0x30;         (* cmp rbp,QWORD PTR [rbx+0x30] *)
  0x73; 0x4d;                     (* jae 6a *)
  0x48; 0x83; 0xc5; 0x01;         (* add rbp,0x1 *)
  0x4c; 0x8b; 0x6b; 0x08;         (* mov r13,QWORD PTR [rbx+0x8] *)
  0xe8; 0x5f; 0x00; 0x00; 0x00;   (* call 89 *)
  0x48; 0x83; 0xf8; 0x01;         (* cmp rax,0x1 *)
  0x75; 0x46;                     (* jne 76 *)
  0x48; 0x8b; 0x43; 0x20;         (* mov rax,QWORD PTR [rbx+0x20] *)
  0x48; 0x8b; 0x00;               (* mov rax,QWORD PTR [rax] *)
  0x48; 0x3b; 0x43; 0x18;         (* cmp rax,QWORD PTR [rbx+0x18] *)
  0x73; 0x34;                     (* jae 71 *)
  0x48; 0x8b; 0x4b; 0x10;         (* mov rcx,QWORD PTR [rbx+0x10] *)
  0x4c; 0x8b; 0x2c; 0xc1;         (* mov r13,QWORD PTR [rcx+rax*8] *)
  0x4d; 0x85; 0xed;               (* test r13,r13 *)
  0x74; 0x27;                     (* je 71 *)
  0xe8; 0x3a; 0x00; 0x00; 0x00;   (* call 89 *)
  0x48; 0x83; 0xf8; 0x01;         (* cmp rax,0x1 *)
  0x75; 0x21;                     (* jne 76 *)
  0x49; 0x83; 0xc4; 0x01;         (* add r12,0x1 *)
  0x48; 0x8b; 0x43; 0x28;         (* mov rax,QWORD PTR [rbx+0x28] *)
  0x48; 0x83; 0x38; 0x00;         (* cmp QWORD PTR [rax],0x0 *)
  0x74; 0xb4;                     (* je 17 *)
  0xb8; 0x01; 0x00; 0x00; 0x00;   (* mov eax,0x1 *)
  0xeb; 0x0c;                     (* jmp 76 *)
  0xb8; 0x04; 0x00; 0x00; 0x00;   (* mov eax,0x4 *)
  0xeb; 0x05;                     (* jmp 76 *)
  0xb8; 0x02; 0x00; 0x00; 0x00;   (* mov eax,0x2 *)
  0x48; 0x89; 0x6b; 0x38;         (* mov QWORD PTR [rbx+0x38],rbp *)
  0x4c; 0x89; 0x63; 0x40;         (* mov QWORD PTR [rbx+0x40],r12 *)
  0x41; 0x5f;                     (* pop r15 *)
  0x41; 0x5e;                     (* pop r14 *)
  0x41; 0x5d;                     (* pop r13 *)
  0x41; 0x5c;                     (* pop r12 *)
  0x5d;                           (* pop rbp *)
  0x5b;                           (* pop rbx *)
  0xc3;                           (* ret *)
  0x48; 0x8b; 0x43; 0x30;         (* mov rax,QWORD PTR [rbx+0x30] *)
  0x49; 0x89; 0x45; 0x28;         (* mov QWORD PTR [r13+0x28],rax *)
  0x49; 0x89; 0x6d; 0x30;         (* mov QWORD PTR [r13+0x30],rbp *)
  0x4c; 0x89; 0xef;               (* mov rdi,r13 *)
  0xe8; 0x05; 0x00; 0x00; 0x00;   (* call a2 *)
  0x49; 0x8b; 0x6d; 0x30;         (* mov rbp,QWORD PTR [r13+0x30] *)
  0xc3;                           (* ret *)
  0x41; 0x57;                     (* push r15 *)
  0xc3                            (* ret *)
];;

let REC_EXEC = X86_MK_EXEC_RULE rec_mc;;

(* Offsets in rec_mc: the record head, the returns from the two plan runs,
   the exits, run and enter. *)
let rec_next = 23 and rec_after_decode = 42 and rec_after_handler = 79
and rec_exhausted = 106 and rec_unsupported = 113 and rec_done = 118
and rec_run_sub = 137 and rec_back = 157 and rec_enter = 162;;

(* ------------------------------------------------------------------------- *)
(* The record loop's stack, the plans it runs, the record semantics.         *)
(* ------------------------------------------------------------------------- *)

(* Below the stack pointer E at entry: the six saved registers, run's and   *)
(* the driver's return addresses, and the driver's stack (its child frame   *)
(* at E - 312).                                                              *)
let rec_stack = new_definition
 `rec_stack (E:int64) (a:int64) <=> val E <= val a + 360 /\ val a < val E`;;

(* A plan run by the record loop from memory m and receipt used: the        *)
(* allowance and the receipt written to its descriptor d, the driver's      *)
(* result from a memory that agrees with that outside the record loop's     *)
(* stack, the descriptor's receipt and at words written back; r is the      *)
(* outcome, the memory and the receipt.                                     *)
let rec_plan = new_definition
 `rec_plan progs bw ctl budget E (pl:int64->(int64 list)list) (d:int64) m used
           (r:int64#(int64->byte)#int64) <=>
    ?m' res.
      (!a. ~rec_stack E a
           ==> m' a = write (bytes64 (word_add d (word 48))) used
                        (write (bytes64 (word_add d (word 40))) budget m) a) /\
      drv_sem progs bw ctl budget (word_sub E (word 312)) (pl d) 0 m' used res /\
      r = (FST res, drv_final d (drv_word m d) res, SND(SND(SND res)))`;;

(* The opcode in memory m names no handler: past the table, or entry 0. *)
let rec_missing = new_definition
 `rec_missing (ht:int64) (nh:int64) (opa:int64) m <=>
    val nh <= val(drv_word m opa) \/
    drv_word m (word_add ht (word(8 * val(drv_word m opa)))) = word 0`;;

let rec_handler = new_definition
 `rec_handler (ht:int64) (opa:int64) m = drv_word m (word_add ht (word(8 * val(drv_word m opa))))`;;

(* The records from memory m, receipt used and count c end with res =      *)
(* (outcome, records whose handler fired, memory, receipt).                *)
let rec_run_RULES, rec_run_INDUCT, rec_run_CASES = new_inductive_definition
 `(!m used c.
     val budget <= val used
     ==> rec_run progs bw ctl budget E pl dd ht nh opa enda m used c
                 ((word 4:int64), c, m, used)) /\
  (!m used c r1.
     ~(val budget <= val used) /\
     rec_plan progs bw ctl budget E pl dd m (word_add used (word 1)) r1 /\ ~(FST r1 = word 1)
     ==> rec_run progs bw ctl budget E pl dd ht nh opa enda m used c
                 (FST r1, c, FST(SND r1), SND(SND r1))) /\
  (!m used c r1.
     ~(val budget <= val used) /\
     rec_plan progs bw ctl budget E pl dd m (word_add used (word 1)) r1 /\ FST r1 = word 1 /\
     rec_missing ht nh opa (FST(SND r1))
     ==> rec_run progs bw ctl budget E pl dd ht nh opa enda m used c
                 (word 2, c, FST(SND r1), SND(SND r1))) /\
  (!m used c r1 r2.
     ~(val budget <= val used) /\
     rec_plan progs bw ctl budget E pl dd m (word_add used (word 1)) r1 /\ FST r1 = word 1 /\
     ~rec_missing ht nh opa (FST(SND r1)) /\
     rec_plan progs bw ctl budget E pl (rec_handler ht opa (FST(SND r1))) (FST(SND r1))
              (SND(SND r1)) r2 /\
     ~(FST r2 = word 1)
     ==> rec_run progs bw ctl budget E pl dd ht nh opa enda m used c
                 (FST r2, c, FST(SND r2), SND(SND r2))) /\
  (!m used c r1 r2.
     ~(val budget <= val used) /\
     rec_plan progs bw ctl budget E pl dd m (word_add used (word 1)) r1 /\ FST r1 = word 1 /\
     ~rec_missing ht nh opa (FST(SND r1)) /\
     rec_plan progs bw ctl budget E pl (rec_handler ht opa (FST(SND r1))) (FST(SND r1))
              (SND(SND r1)) r2 /\
     FST r2 = word 1 /\ ~(drv_word (FST(SND r2)) enda = word 0)
     ==> rec_run progs bw ctl budget E pl dd ht nh opa enda m used c
                 (word 1, c + 1, FST(SND r2), SND(SND r2))) /\
  (!m used c r1 r2 res.
     ~(val budget <= val used) /\
     rec_plan progs bw ctl budget E pl dd m (word_add used (word 1)) r1 /\ FST r1 = word 1 /\
     ~rec_missing ht nh opa (FST(SND r1)) /\
     rec_plan progs bw ctl budget E pl (rec_handler ht opa (FST(SND r1))) (FST(SND r1))
              (SND(SND r1)) r2 /\
     FST r2 = word 1 /\ drv_word (FST(SND r2)) enda = word 0 /\
     rec_run progs bw ctl budget E pl dd ht nh opa enda (FST(SND r2)) (SND(SND r2)) (c + 1) res
     ==> rec_run progs bw ctl budget E pl dd ht nh opa enda m used c res)`;;

(* The memory the caller sees: the records' memory with the receipt and the *)
(* count written back to the record descriptor r.                           *)
let rec_final = new_definition
 `rec_final (r:int64) (res:int64#num#(int64->byte)#int64) =
    write (bytes64 (word_add r (word 64))) (word(FST(SND res)))
      (write (bytes64 (word_add r (word 56))) (SND(SND(SND res))) (FST(SND(SND res))))`;;

(* ------------------------------------------------------------------------- *)
(* What a record program is: its plans, the record descriptor, the layout.   *)
(* ------------------------------------------------------------------------- *)

(* A plan's descriptor d in memory m: as drv_holds, without the allowance   *)
(* and receipt words, which the record loop writes before each run.         *)
let rec_holds = new_definition
 `rec_holds (m:int64->byte) d ctl bind leaves (stepl:(int64 list)list) (bw:num->int64) nbw
            (lpc:num->num) nl <=>
    drv_word m (word_add d (word 8)) = word_add (drv_word m d) (word(144 * LENGTH stepl)) /\
    drv_word m (word_add d (word 16)) = ctl /\ drv_word m (word_add d (word 24)) = bind /\
    drv_word m (word_add d (word 32)) = leaves /\
    (!i f. i < LENGTH stepl /\ f < 18
           ==> drv_word m (word_add (drv_word m d) (word(144 * i + 8 * f))) = EL f (EL i stepl)) /\
    (!k. k < nbw ==> drv_word m (word_add bind (word(8 * k))) = bw k) /\
    (!j. j < nl ==> drv_word m (word_add leaves (word(8 * j))) = word(lpc j))`;;

(* A plan the record loop may run: the driver's conditions for the child    *)
(* frame at E - 312, and its descriptor in m0.                               *)
let rec_plan_ok = new_definition
 `rec_plan_ok progs pcd E ctl nctl bind nbw leaves nl lpc lmc bw
              (pl:int64->(int64 list)list) (m0:int64->byte) d <=>
    drv_layout pcd (word_sub E (word 312)) d (drv_word m0 d) (LENGTH(pl d)) ctl nctl bind nbw
               leaves nl lpc lmc /\
    ALL (drv_step_ok progs pcd (word_sub E (word 312)) d (drv_word m0 d) (LENGTH(pl d)) nctl
                     bind nbw leaves nl lpc lmc bw) (pl d) /\
    rec_holds m0 d ctl bind leaves (pl d) bw nbw lpc nl`;;

(* The bytes no one writes while the records run: the two loops' code, the   *)
(* leaves' code, words 0..6 of the record descriptor r, the handler table,  *)
(* words 0..4 of every plan's descriptor and the plan's steps, the binding   *)
(* words and the leaf table.                                                 *)
let rec_fixed = new_definition
 `rec_fixed pcr pcd (r:int64) (ht:int64) (nh:int64) (ds:int64 list)
            (pl:int64->(int64 list)list) (m0:int64->byte) (bind:int64) nbw (leaves:int64) nl
            (lpc:num->num) (lmc:num->byte list) a <=>
    drv_in a (word pcr) 165 \/ drv_in a (word pcd) 522 \/
    (?j. j < nl /\ drv_in a (word(lpc j)) (LENGTH(lmc j))) \/
    drv_in a r 56 \/ drv_in a ht (8 * val nh) \/
    (?d. MEM d ds /\ (drv_in a d 40 \/ drv_in a (drv_word m0 d) (144 * LENGTH(pl d)))) \/
    drv_in a bind (8 * nbw) \/ drv_in a leaves (8 * nl)`;;

(* The record loop's stack and the caller's return address above it. *)
let rec_window = new_definition
 `rec_window (E:int64) (a:int64) <=> val E <= val a + 360 /\ val a < val E + 8`;;

(* The words the loops write outside the stack: allowance, receipt and at   *)
(* of each plan's descriptor, receipt and count of r.                       *)
let rec_written = new_definition
 `rec_written (r:int64) (ds:int64 list) (a:int64) <=>
    (?d. MEM d ds /\ drv_in a (word_add d (word 40)) 24) \/ drv_in a (word_add r (word 56)) 16`;;

(* The layout: no area wraps; the fixed bytes lie apart from the stack      *)
(* window and from the written words, which lie apart from the stack        *)
(* window too; the opcode and END words lie apart from the stack window;   *)
(* and no step of any plan writes a fixed byte, a descriptor, r, or the    *)
(* stack window.                                                             *)
let rec_layout = new_definition
 `rec_layout progs pcr pcd E r ht nh ds pl m0 opa enda ctl bind nbw leaves nl lpc lmc bw <=>
    360 <= val E /\ val E + 8 <= 2 EXP 64 /\ pcr + 165 <= 2 EXP 64 /\
    val r + 72 <= 2 EXP 64 /\ val ht + 8 * val nh <= 2 EXP 64 /\
    (!d. MEM d ds ==> val d + 64 <= 2 EXP 64) /\
    (!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a
         ==> ~rec_window E a /\ ~rec_written r ds a) /\
    (!a. rec_written r ds a ==> ~rec_window E a) /\
    (!k. k < 8 ==> ~rec_window E (word_add opa (word k)) /\ ~rec_window E (word_add enda (word k))) /\
    (!d st a. MEM d ds /\ MEM st (pl d) /\
              ((?q. tisa_rw (tisa_decls (progs (val(EL 0 st)))) q /\
                    drv_in a (drv_base bw st q) (val(drv_len bw st q))) \/
               drv_in a (word_add ctl (word(8 * val(EL 17 st)))) 8)
              ==> ~rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a /\
                  ~(?d'. MEM d' ds /\ drv_in a d' 64) /\ ~drv_in a r 72 /\ ~rec_window E a)`;;

(* The record descriptor r in m0. *)
let rec_desc = new_definition
 `rec_desc (m0:int64->byte) r pcd dd ht nh opa enda budget used0 <=>
    drv_word m0 r = word pcd /\ drv_word m0 (word_add r (word 8)) = dd /\
    drv_word m0 (word_add r (word 16)) = ht /\ drv_word m0 (word_add r (word 24)) = nh /\
    drv_word m0 (word_add r (word 32)) = opa /\ drv_word m0 (word_add r (word 40)) = enda /\
    drv_word m0 (word_add r (word 48)) = budget /\ drv_word m0 (word_add r (word 56)) = used0`;;

(* ------------------------------------------------------------------------- *)
(* The receipt through a plan: a plan's receipt is at least the one it       *)
(* starts from (DRV_SEM_FUEL), so a record raises the receipt.               *)
(* ------------------------------------------------------------------------- *)

let DRV_SEM_FUEL = prove
 (`!progs bw ctl budget cfr sts i m used res.
     drv_sem progs bw ctl budget cfr sts i m used res /\
     (!st. MEM st sts ==> tisa_leaf_wf (progs (val(EL 0 st))))
     ==> val used <= val(SND(SND(SND res)))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[drv_sem] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_sem; MEM] THEN
  COND_CASES_TAC THENL [STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `tc:tisa_state` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u:tisa_state` STRIP_ASSUME_TAC)))
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `val(used:int64) <= val(tisa_fword u 21)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
      check (fun th -> can (find_term ((=) `drv_child`)) (concl th))) THEN
    DISCH_THEN(MP_TAC o SPEC `21`) THEN REWRITE_TAC[ARITH; drv_fw] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`progs (val(EL 0 (h:int64 list))):tisa_prog`; `tc:tisa_state`; `k:num`; `u:tisa_state`]
                  TISA_RUN_FUEL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`; `drv_after ctl h u`; `tisa_fword u 21`;
                                  `res:int64#num#(int64->byte)#int64`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `drv_sem`)) (concl th))) THEN
    ASM_SIMP_TAC[] THEN UNDISCH_TAC `val(used:int64) <= val(tisa_fword u 21)` THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let REC_PLAN_FUEL = prove
 (`!progs bw ctl budget E pl d m used r.
     rec_plan progs bw ctl budget E pl d m used r /\
     (!st. MEM st (pl d) ==> tisa_leaf_wf (progs (val(EL 0 st))))
     ==> val used <= val(SND(SND r))`,
  REWRITE_TAC[rec_plan] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DRV_SEM_FUEL THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A plan's run depends on memory outside the record loop's stack only.      *)
(* ------------------------------------------------------------------------- *)

let REC_PLAN_LOCAL = prove
 (`!progs bw ctl budget E pl d m1 m2 used r.
     (!a. ~rec_stack E a ==> m1 a = m2 a) /\
     (!i. i < 8 ==> ~rec_stack E (word_add d (word i)))
     ==> (rec_plan progs bw ctl budget E pl d m1 used r <=>
          rec_plan progs bw ctl budget E pl d m2 used r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rec_plan] THEN
  SUBGOAL_THEN `drv_word m1 d = drv_word m2 (d:int64)` SUBST1_TAC THENL
   [MATCH_MP_TAC DRV_WORD_AGREE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. ~rec_stack E a
        ==> write (bytes64 (word_add d (word 48))) used
              (write (bytes64 (word_add d (word 40))) budget m1) a =
            write (bytes64 (word_add d (word 48))) used
              (write (bytes64 (word_add d (word 40))) budget m2) a`
  (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL [`\a:int64. ~rec_stack E a`;
     `write (bytes64 (word_add d (word 40))) budget (m1:int64->byte)`;
     `write (bytes64 (word_add d (word 40))) budget (m2:int64->byte)`;
     `word_add d (word 48):int64`; `used:int64`] DRV_WRITE_CONG)) THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL [`\a:int64. ~rec_stack E a`; `m1:int64->byte`; `m2:int64->byte`;
     `word_add d (word 40):int64`; `budget:int64`] DRV_WRITE_CONG)) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Facts read from fixed bytes hold in every memory that agrees with m0 on    *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

(* The 8 bytes at offset k of an area (b, n) that does not wrap. *)
let DRV_IN_OFFSET = prove
 (`!(b:int64) n k i. val b + n <= 2 EXP 64 /\ k + 8 <= n /\ i < 8
                     ==> drv_in (word_add (word_add b (word k)) (word i)) b n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[drv_in] THEN
  SUBGOAL_THEN `val(word_add (word_add b (word k)) (word i):int64) = val b + k + i` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let DRV_IN_BASE = prove
 (`!(b:int64) n i. val b + n <= 2 EXP 64 /\ 8 <= n /\ i < 8 ==> drv_in (word_add b (word i)) b n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:int64`; `n:num`; `0`; `i:num`] DRV_IN_OFFSET) THEN
  ASM_REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES]);;

(* A word read from an area on which two memories agree. *)
let DRV_WORD_AREA = prove
 (`!m1 m2 (b:int64) n k.
     val b + n <= 2 EXP 64 /\ k + 8 <= n /\ (!a. drv_in a b n ==> m1 a = m2 a)
     ==> drv_word m1 (word_add b (word k)) = drv_word m2 (word_add b (word k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_WORD_AGREE THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC DRV_IN_OFFSET THEN ASM_REWRITE_TAC[]);;

let DRV_WORD_AREA0 = prove
 (`!m1 m2 (b:int64) n.
     val b + n <= 2 EXP 64 /\ 8 <= n /\ (!a. drv_in a b n ==> m1 a = m2 a)
     ==> drv_word m1 b = drv_word m2 b`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`m1:int64->byte`; `m2:int64->byte`; `b:int64`; `n:num`; `0`]
    DRV_WORD_AREA) THEN ASM_REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES]);;

(* Code in an area two memories agree on. *)
let DRV_CODE_AREA = prove
 (`!m1 m2 p mc.
     p + LENGTH mc <= 2 EXP 64 /\ drv_code m2 p mc /\
     (!a. drv_in a (word p) (LENGTH mc) ==> m1 a = m2 a)
     ==> drv_code m1 p mc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_code] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REWRITE_TAC[DRV_READ_BYTELIST] THEN AP_TERM_TAC THEN
  REWRITE_TAC[READ_BYTES_EQ] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[drv_in] THEN
  SUBGOAL_THEN `val(word p:int64) = p` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `p + LENGTH(mc:byte list) <= 2 EXP 64` THEN
    UNDISCH_TAC `i < LENGTH(mc:byte list)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add (word p) (word i):int64) = p + i` SUBST1_TAC THENL
   [ASM_MESON_TAC[TISA_VAL_OFFSET; ARITH_RULE `i < l /\ p + l <= 2 EXP 64 ==> p + i < 2 EXP 64`];
    ASM_ARITH_TAC]);;

let REC_HOLDS_TRANSFER = prove
 (`!m m0 d ctl bind leaves stepl bw nbw lpc nl.
     val d + 40 <= 2 EXP 64 /\ val(drv_word m0 d) + 144 * LENGTH stepl < 2 EXP 64 /\
     val bind + 8 * nbw <= 2 EXP 64 /\ val leaves + 8 * nl <= 2 EXP 64 /\
     (!a. drv_in a d 40 \/ drv_in a (drv_word m0 d) (144 * LENGTH stepl) \/
          drv_in a bind (8 * nbw) \/ drv_in a leaves (8 * nl) ==> m a = m0 a) /\
     rec_holds m0 d ctl bind leaves stepl bw nbw lpc nl
     ==> rec_holds m d ctl bind leaves stepl bw nbw lpc nl /\ drv_word m d = drv_word m0 d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rec_holds] THEN
  ABBREV_TAC `plan = drv_word m0 (d:int64)` THEN ABBREV_TAC `ns = LENGTH(stepl:(int64 list)list)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `drv_word m d = (plan:int64)` ASSUME_TAC THENL
   [EXPAND_TAC "plan" THEN MATCH_MP_TAC DRV_WORD_AREA0 THEN EXISTS_TAC `40` THEN ASM_SIMP_TAC[ARITH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!k. k + 8 <= 40 ==> drv_word m (word_add d (word k)) = drv_word m0 (word_add d (word k))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_WORD_AREA THEN EXISTS_TAC `40` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `EL f (EL i stepl):int64`)) (concl th)
                            then (MP_TAC(SPECL [`i:num`; `f:num`] th)) else failwith "") THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC DRV_WORD_AREA THEN EXISTS_TAC `144 * ns` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `i < ns` THEN UNDISCH_TAC `f < 18` THEN UNDISCH_TAC `val(plan:int64) + 144 * ns < 2 EXP 64` THEN
    ARITH_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `bw:num->int64`)) (concl th)
                            then (MP_TAC(SPEC `k:num` th)) else failwith "") THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC DRV_WORD_AREA THEN EXISTS_TAC `8 * nbw` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `k < nbw` THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `lpc:num->num`)) (concl th)
                            then (MP_TAC(SPEC `j:num` th)) else failwith "") THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC DRV_WORD_AREA THEN EXISTS_TAC `8 * nl` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `j < nl` THEN ARITH_TAC]);;

(* Two areas that share no byte do not overlap. *)
let DRV_NONOVERLAP_APART = prove
 (`!(x:int64) n (y:int64) l.
     val x + n <= 2 EXP 64 /\ val y + l <= 2 EXP 64 /\ (!a. drv_in a x n ==> ~drv_in a y l)
     ==> nonoverlapping (x,n) (y,l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[nonoverlapping; DIMINDEX_64] THEN
  ASM_CASES_TAC `n = 0 \/ l = 0` THENL
   [MATCH_MP_TAC NONOVERLAPPING_MODULO_TRIVIAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  ASM_CASES_TAC `val(x:int64) <= val(y:int64)` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `y:int64`); FIRST_X_ASSUM(MP_TAC o SPEC `x:int64`)] THEN
  REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* REC_RUN: run, the subroutine that runs the plan whose descriptor is r13   *)
(* from the receipt in rbp, by DRV_CORRECT.                                  *)
(* ------------------------------------------------------------------------- *)

let rec_premises =
 `(!j. j < nl ==> tisa_leaf_wf (progs j) /\ tisa_leaf_spec (progs j) (lmc j) (lpc j)) /\
  rec_layout progs pcr pcd E r ht nh ds pl m0 opa enda ctl bind nbw leaves nl lpc lmc bw /\
  ALL (rec_plan_ok progs pcd E ctl nctl bind nbw leaves nl lpc lmc bw pl m0) ds /\
  drv_code m0 pcr rec_mc /\ drv_code m0 pcd drv_mc /\ (!j. j < nl ==> drv_code m0 (lpc j) (lmc j))`;;

let rec_runsub_goal = mk_imp(rec_premises,
 `!d used m budget r12v r14v.
     MEM d ds /\ drv_word m0 (word_add r (word 48)) = budget /\
     (!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a ==> m a = m0 a)
     ==> ensures x86
          (\s. read RIP s = word(pcr + 137) /\ read RSP s = word_sub E (word 56) /\
               read RBX s = r /\ read R13 s = d /\ read RBP s = used /\ read R15 s = word pcd /\
               read R12 s = r12v /\ read R14 s = r14v /\ read memory s = m)
          (\s. read RIP s = drv_word m (word_sub E (word 56)) /\ read RSP s = word_sub E (word 48) /\
               read RBX s = r /\ read R13 s = d /\ read R15 s = word pcd /\
               read R12 s = r12v /\ read R14 s = r14v /\
               ?r1. rec_plan progs bw ctl budget E pl d m used r1 /\
                    read RAX s = FST r1 /\ read RBP s = SND(SND r1) /\
                    (!a. ~rec_stack E a ==> read memory s a = FST(SND r1) a) /\
                    (!a. val E <= val a + 56 /\ val a < val E + 8 ==> read memory s a = m a) /\
                    (!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a
                         ==> read memory s a = m0 a))
          (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                      R12; R13; R14; R15; RBP] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`);;
let rec_runsub_goal = list_mk_forall(frees rec_runsub_goal, rec_runsub_goal);;

let REC_STACK_NORM = prove
 (`!E:int64. word_sub (word_sub E (word 56)) (word 8) = word_sub E (word 64) /\
             word_sub (word_sub (word_sub E (word 56)) (word 8)) (word 8) = word_sub E (word 72) /\
             word_add (word_sub E (word 72)) (word 8) = word_sub E (word 64) /\
             word_sub (word_sub E (word 64)) (word 248) = word_sub E (word 312) /\
             word_add (word_sub E (word 64)) (word 8) = word_sub E (word 56)`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let REC_HOLDS_DRV = prove
 (`!m d ctl bind leaves stepl bw nbw lpc nl budget used.
     rec_holds m d ctl bind leaves stepl bw nbw lpc nl /\
     drv_word m (word_add d (word 40)) = budget /\ drv_word m (word_add d (word 48)) = used
     ==> drv_holds m d (drv_word m d) (LENGTH stepl) ctl bind leaves budget used stepl bw nbw lpc nl`,
  REWRITE_TAC[rec_holds; drv_holds] THEN MESON_TAC[]);;

let VAL_FACTS_ARITH_TAC vs (asl,w) =
  let rel th = let c = concl th in
    not(can (find_term is_forall) c) && not(can (find_term is_exists) c) &&
    exists (fun v -> can (find_term ((=) v)) c) vs in
  (MAP_EVERY (fun (_,th) -> MP_TAC th) (filter (fun (_,th) -> rel th) asl) THEN ARITH_TAC) (asl,w);;

let DRV_WORD_WRITE_OTHER = prove
 (`!(y:int64) (v:int64) m (x:int64).
     val y + 8 <= 2 EXP 64 /\ val x + 8 <= 2 EXP 64 /\ (val y + 8 <= val x \/ val x + 8 <= val y)
     ==> drv_word (write (bytes64 y) v m) x = drv_word m x`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word_add x (word i):int64) = val x + i` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let DRV_APART_POINTS = prove
 (`!(x:int64) n (y:int64) l.
     val x + n <= 2 EXP 64 /\ val y + l <= 2 EXP 64 /\ (!a. drv_in a x n ==> ~drv_in a y l)
     ==> drv_apart x n y l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[drv_apart] THEN
  ASM_CASES_TAC `val(x:int64) <= val(y:int64)` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `y:int64`); FIRST_X_ASSUM(MP_TAC o SPEC `x:int64`)] THEN
  REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC);;

let REC_WINDOW_IN = prove
 (`!E a. 360 <= val E ==> (rec_window E a <=> drv_in a (word_sub E (word 360)) 368)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rec_window; drv_in] THEN
  MP_TAC(SPECL [`E:int64`; `360`] TISA_VAL_SP_SUB) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_ARITH_TAC);;

let REC_WINDOW_APART = prove
 (`!E (x:int64) n. 360 <= val E /\ val E + 8 <= 2 EXP 64 /\ val x + n <= 2 EXP 64 /\
     (!a. drv_in a x n ==> ~rec_window E a)
     ==> drv_apart x n (word_sub E (word 360)) 368`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_APART_POINTS THEN
  SUBGOAL_THEN `val(word_sub E (word 360):int64) = val E - 360` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_SP_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:int64`) THEN ASM_REWRITE_TAC[rec_window; drv_in] THEN
  MP_TAC(SPECL [`E:int64`; `360`] TISA_VAL_SP_SUB) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_ARITH_TAC);;

let REC_WRITTEN_D = prove
 (`!r ds d (a:int64). MEM d ds /\ drv_in a (word_add d (word 40)) 24 ==> rec_written r ds a`,
  REWRITE_TAC[rec_written] THEN MESON_TAC[]);;

let REC_WRITTEN_R = prove
 (`!r ds (a:int64). drv_in a (word_add r (word 56)) 16 ==> rec_written r ds a`,
  REWRITE_TAC[rec_written] THEN MESON_TAC[]);;

let REC_GUARD_STEP = prove
 (`!progs pcr pcd E r ht nh ds pl m0 opa enda ctl bind nbw leaves nl lpc lmc bw d (a:int64).
     rec_layout progs pcr pcd E r ht nh ds pl m0 opa enda ctl bind nbw leaves nl lpc lmc bw /\ MEM d ds /\
     (rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a \/ rec_window E a \/
      (?d'. MEM d' ds /\ drv_in a d' 64) \/ drv_in a r 72)
     ==> (!st q. MEM st (pl d) /\ tisa_rw (tisa_decls (progs (val(EL 0 st)))) q
                 ==> ~drv_in a (drv_base bw st q) (val(drv_len bw st q))) /\
         (!st. MEM st (pl d) ==> ~drv_in a (word_add ctl (word(8 * val(EL 17 st)))) 8)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rec_layout] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:int64` o check (fun th -> is_forall(concl th) &&
    length(fst(strip_forall(concl th))) = 3)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`st:int64 list`; `q:num`] THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`st:int64 list`; `a:int64`] o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a \/ rec_window E a \/
        (?d'. MEM d' ds /\ drv_in a d' 64) \/ drv_in a r 72` THEN CONV_TAC TAUT];
    X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`st:int64 list`; `a:int64`] o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2)) THEN ASM_REWRITE_TAC[NOT_IMP] THEN
    UNDISCH_TAC `rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a \/ rec_window E a \/
      (?d'. MEM d' ds /\ drv_in a d' 64) \/ drv_in a r 72` THEN CONV_TAC TAUT]);;

let REC_RUN = prove
 (rec_runsub_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `d:int64` o GEN_REWRITE_RULE I [GSYM ALL_MEM] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "rec_plan_ok")) (concl th))) THEN
  ASM_REWRITE_TAC[rec_plan_ok] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_layout] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "drv_layout")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rec_layout] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "rec_layout")) (concl th))) THEN
  SUBGOAL_THEN
   `(!a. drv_in a (word pcr) 165 ==> rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a) /\
    (!a. drv_in a (word pcd) 522 ==> rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a) /\
    (!j a. j < nl /\ drv_in a (word(lpc j)) (LENGTH(lmc j))
           ==> rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a) /\
    (!a. drv_in a r 56 ==> rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a) /\
    (!a. drv_in a d 40 \/ drv_in a (drv_word m0 d) (144 * LENGTH(pl d)) \/
         drv_in a bind (8 * nbw) \/ drv_in a leaves (8 * nl)
         ==> rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `MEM (d:int64) ds`) THEN REWRITE_TAC[rec_fixed] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:int64->byte`; `m0:int64->byte`; `d:int64`;
                `ctl:int64`; `bind:int64`; `leaves:int64`; `(pl:int64->(int64 list)list) d`; `bw:num->int64`;
                `nbw:num`; `lpc:num->num`; `nl:num`] REC_HOLDS_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `val(d:int64) + 64 <= 2 EXP 64` THEN ARITH_TAC;
      X_GEN_TAC `a:int64` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    STRIP_TAC] THEN
  SUBGOAL_THEN `drv_code m pcd drv_mc /\ (!j. j < nl ==> drv_code m (lpc j) (lmc j)) /\
                drv_code m pcr rec_mc /\
                drv_word m (word_add r (word 48)) = budget` STRIP_ASSUME_TAC THENL
 [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DRV_CODE_AREA THEN EXISTS_TAC `m0:int64->byte` THEN
      ASM_REWRITE_TAC[COMPUTE_LENGTH_RULE drv_mc] THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_CODE_AREA THEN EXISTS_TAC `m0:int64->byte` THEN ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `m:int64->byte`)) (concl th) && can (find_term ((=) `rec_fixed`)) (concl th))) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> length(fst(strip_forall(concl th))) = 2 &&
    can (find_term ((=) `lpc:num->num`)) (concl th) && can (find_term ((=) `rec_fixed`)) (concl th))) THEN
  EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DRV_CODE_AREA THEN EXISTS_TAC `m0:int64->byte` THEN
      ASM_REWRITE_TAC[COMPUTE_LENGTH_RULE rec_mc] THEN ASM_SIMP_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `drv_word m0 (word_add r (word 48)) = budget`)) THEN
      MATCH_MP_TAC DRV_WORD_AREA THEN EXISTS_TAC `56` THEN ASM_SIMP_TAC[ARITH] THEN
      UNDISCH_TAC `val(r:int64) + 72 <= 2 EXP 64` THEN ARITH_TAC];
  ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add d (word 40):int64) = val d + 40 /\ val(word_sub E (word 72):int64) = val E - 72`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC TISA_VAL_OFFSET THEN UNDISCH_TAC `val(d:int64) + 64 <= 2 EXP 64` THEN ARITH_TAC;
      MATCH_MP_TAC TISA_VAL_SP_SUB THEN UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `nonoverlapping (word pcr:int64,165) (word_add d (word 40),16)` ASSUME_TAC THENL
 [(MATCH_MP_TAC DRV_NONOVERLAP_APART THEN
  SUBGOAL_THEN `val(word pcr:int64) = pcr` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `pcr + 165 <= 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [UNDISCH_TAC `val(d:int64) + 64 <= 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:int64` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `rec_window`)) (concl th) && can (find_term ((=) `rec_written`)) (concl th) &&
      can (find_term ((=) `rec_fixed`)) (concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
  ANTS_TAC THENL [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `word pcr:int64`)) (concl th) &&
     is_forall(concl th))) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rec_written; DE_MORGAN_THM; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:int64`) THEN ASM_REWRITE_TAC[drv_in] THEN ARITH_TAC);
  ALL_TAC] THEN
  SUBGOAL_THEN `nonoverlapping (word pcr:int64,165) (word_sub E (word 72),16)` ASSUME_TAC THENL
 [(MATCH_MP_TAC DRV_NONOVERLAP_APART THEN
  SUBGOAL_THEN `val(word pcr:int64) = pcr` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `pcr + 165 <= 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [UNDISCH_TAC `val(E:int64) + 8 <= 2 EXP 64` THEN UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:int64` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `rec_window`)) (concl th) && can (find_term ((=) `rec_written`)) (concl th) &&
      can (find_term ((=) `rec_fixed`)) (concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
  ANTS_TAC THENL [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `word pcr:int64`)) (concl th) &&
     is_forall(concl th))) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rec_window; drv_in] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC);
  ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `bytes_loaded s0 (word pcr) rec_mc /\ read (memory :> bytes64 (word_add r (word 48))) s0 = budget`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DRV_READ64] THEN MATCH_MP_TAC DRV_LOADED_CODE THEN EXISTS_TAC `m:int64->byte` THEN
    ASM_REWRITE_TAC[COMPUTE_LENGTH_RULE rec_mc];
    ALL_TAC] THEN
  TISA_STEPS_TAC REC_EXEC (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REC_STACK_NORM]) THEN
  ABBREV_TAC `m7 = read memory s7` THEN
  SUBGOAL_THEN `!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a ==> m7 a = (m:int64->byte) a`
  ASSUME_TAC THENL
 [(X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `rec_window`)) (concl th) && can (find_term ((=) `rec_written`)) (concl th) &&
      can (find_term ((=) `rec_fixed`)) (concl th) && length(fst(strip_forall(concl th))) = 1
    then MP_TAC(MP (SPEC `a:int64` th) (ASSUME `rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a`))
    else failwith "") THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[rec_window])
     (STRIP_ASSUME_TAC o REWRITE_RULE[rec_written; DE_MORGAN_THM; NOT_EXISTS_THM])) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:int64` o check (fun th -> is_forall(concl th) &&
      fst(dest_var(fst(dest_forall(concl th)))) = "d" && can (find_term ((=) `word 40:int64`)) (concl th))) THEN
    ASM_REWRITE_TAC[drv_in] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m7:int64->byte`)) THEN
  SUBGOAL_THEN `val(word_sub E (word 64):int64) = val E - 64 /\ val(word_sub E (word 72):int64) = val E - 72 /\
                  val(word_add d (word 48):int64) = val d + 48` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC TISA_VAL_SP_SUB; MATCH_MP_TAC TISA_VAL_SP_SUB; MATCH_MP_TAC TISA_VAL_OFFSET] THEN
      UNDISCH_TAC `360 <= val(E:int64)` THEN UNDISCH_TAC `val(d:int64) + 64 <= 2 EXP 64` THEN ARITH_TAC;
      ALL_TAC] THEN
  REPEAT(W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
           ANTS_TAC THENL
            [ASM_REWRITE_TAC[] THEN VAL_FACTS_ARITH_TAC [`val(a:int64)`; `val(E:int64)`; `val(d:int64)`];
             DISCH_THEN SUBST1_TAC]) THEN
    REFL_TAC);
  ALL_TAC] THEN
  SUBGOAL_THEN `drv_apart (word_add d (word 40)) 24 (word_sub E (word 360)) 368` MP_TAC THENL
   [MATCH_MP_TAC REC_WINDOW_APART THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `val(word_add d (word 40):int64) = val d + 40` THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `val(d:int64) + 64 <= 2 EXP 64` THEN ARITH_TAC;
      X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) &&
          can (find_term ((=) `rec_written`)) (concl th) && can (find_term ((=) `rec_window`)) (concl th) &&
          not (can (find_term ((=) `rec_fixed`)) (concl th)) then MATCH_MP_TAC th else failwith "") THEN
      MATCH_MP_TAC REC_WRITTEN_D THEN EXISTS_TAC `d:int64` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub E (word 360):int64) = val E - 360` (fun th -> REWRITE_TAC[th; drv_apart]) THENL
   [MATCH_MP_TAC TISA_VAL_SP_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `drv_word m7 (word_add d (word 40)) = budget /\ drv_word m7 (word_add d (word 48)) = used`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m7:int64->byte`)) THEN
    SUBGOAL_THEN `val(word_sub E (word 64):int64) = val E - 64 /\ val(word_sub E (word 72):int64) = val E - 72 /\
                  val(word_add d (word 48):int64) = val d + 48` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC TISA_VAL_SP_SUB; MATCH_MP_TAC TISA_VAL_SP_SUB; MATCH_MP_TAC TISA_VAL_OFFSET] THEN
      UNDISCH_TAC `360 <= val(E:int64)` THEN UNDISCH_TAC `val(d:int64) + 64 <= 2 EXP 64` THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THEN
    REPEAT(GEN_REWRITE_TAC I [DRV_WORD_WRITE_SAME] ORELSE
           (MATCH_MP_TAC DRV_WORD_WRITE_OTHER THEN ASM_REWRITE_TAC[] THEN
            VAL_FACTS_ARITH_TAC [`val(E:int64)`; `val(d:int64)`] THEN NO_TAC) ORELSE
           (W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WORD_WRITE_OTHER (lhs w))) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN VAL_FACTS_ARITH_TAC [`val(E:int64)`; `val(d:int64)`];
                            DISCH_THEN SUBST1_TAC])) THEN
    REWRITE_TAC[DRV_WORD_WRITE_SAME];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a ==> m7 a = (m0:int64->byte) a`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub E (word 64):int64) = val E - 64 /\ val(word_sub E (word 72):int64) = val E - 72 /\
                val(word_add d (word 48):int64) = val d + 48` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC TISA_VAL_SP_SUB; MATCH_MP_TAC TISA_VAL_SP_SUB; MATCH_MP_TAC TISA_VAL_OFFSET] THEN
    UNDISCH_TAC `360 <= val(E:int64)` THEN UNDISCH_TAC `val(d:int64) + 64 <= 2 EXP 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(!a. ~rec_stack E a
                     ==> m7 a = write (bytes64 (word_add d (word 48))) used
                                  (write (bytes64 (word_add d (word 40))) budget (m:int64->byte)) a) /\
                (!a. val E <= val a + 56 /\ val a < val E + 8 ==> m7 a = m a)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m7:int64->byte`)) THEN
    CONJ_TAC THEN X_GEN_TAC `a:int64` THEN REWRITE_TAC[rec_stack] THEN DISCH_TAC THEN
    REPEAT(W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
           ANTS_TAC THENL
            [ASM_REWRITE_TAC[] THEN VAL_FACTS_ARITH_TAC [`val(a:int64)`; `val(E:int64)`; `val(d:int64)`];
             DISCH_THEN SUBST1_TAC]) THEN
    REFL_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m7:int64->byte`)) THEN
  MP_TAC(SPECL [`m7:int64->byte`; `m0:int64->byte`; `d:int64`;
                `ctl:int64`; `bind:int64`; `leaves:int64`; `(pl:int64->(int64 list)list) d`; `bw:num->int64`;
                `nbw:num`; `lpc:num->num`; `nl:num`] REC_HOLDS_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `val(d:int64) + 64 <= 2 EXP 64` THEN ARITH_TAC;
      X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `m7:int64->byte`)) (concl th) &&
         can (find_term ((=) `m0:int64->byte`)) (concl th) && can (find_term ((=) `rec_fixed`)) (concl th)
         then MATCH_MP_TAC th else failwith "") THEN
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `drv_in a bind (8 * nbw)`)) (concl th)
         then MATCH_MP_TAC th else failwith "") THEN ASM_REWRITE_TAC[]];
    STRIP_TAC] THEN
  SUBGOAL_THEN `drv_holds m7 d (drv_word m0 d) (LENGTH((pl:int64->(int64 list)list) d)) ctl bind leaves budget used (pl d) bw nbw lpc nl`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `drv_word m7 d = drv_word m0 d` then REWRITE_TAC[SYM th] else failwith "") THEN
    MATCH_MP_TAC REC_HOLDS_DRV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `drv_code m7 pcd drv_mc /\ (!j. j < nl ==> drv_code m7 (lpc j) (lmc j))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC DRV_CODE_AREA THEN EXISTS_TAC `m0:int64->byte` THEN
      ASM_REWRITE_TAC[COMPUTE_LENGTH_RULE drv_mc] THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_CODE_AREA THEN EXISTS_TAC `m0:int64->byte` THEN ASM_SIMP_TAC[] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `m7:int64->byte`)) (concl th) &&
         can (find_term ((=) `m0:int64->byte`)) (concl th) && can (find_term ((=) `rec_fixed`)) (concl th)
         then MATCH_MP_TAC th else failwith "") THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> length(fst(strip_forall(concl th))) = 2 &&
        can (find_term ((=) `lpc:num->num`)) (concl th) && can (find_term ((=) `rec_fixed`)) (concl th))) THEN
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `lpc:num->num`; `lmc:num->byte list`; `nl:num`; `pcd:num`;
              `word_sub E (word 64):int64`; `d:int64`; `drv_word m0 d`; `LENGTH((pl:int64->(int64 list)list) d)`;
              `ctl:int64`; `nctl:num`; `bind:int64`; `nbw:num`; `leaves:int64`; `bw:num->int64`;
              `(pl:int64->(int64 list)list) d`; `budget:int64`; `used:int64`; `m7:int64->byte`;
              `word(pcr + 157):int64`; `r:int64`; `used:int64`; `r12v:int64`; `d:int64`; `r14v:int64`;
              `word pcd:int64`] DRV_CORRECT) THEN
  REWRITE_TAC[REC_STACK_NORM] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN TISA_BIGSTEP_TAC "s8" THEN
  SUBGOAL_THEN `!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a ==> read memory s8 a = m0 a`
  ASSUME_TAC THENL
 [(X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `rec_window`)) (concl th) &&
         can (find_term ((=) `rec_written`)) (concl th) && can (find_term ((=) `rec_fixed`)) (concl th) &&
         length(fst(strip_forall(concl th))) = 1
         then MP_TAC(MP (SPEC `a:int64` th)
                (ASSUME `rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a`))
         else failwith "") THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[rec_window]) ASSUME_TAC) THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `pcr:num`; `pcd:num`; `E:int64`; `r:int64`; `ht:int64`; `nh:int64`;
                    `ds:int64 list`; `pl:int64->(int64 list)list`; `m0:int64->byte`; `opa:int64`; `enda:int64`;
                    `ctl:int64`; `bind:int64`; `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`;
                    `lmc:num->byte list`; `bw:num->int64`; `d:int64`; `a:int64`] REC_GUARD_STEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `(m7:int64->byte) a` THEN CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `tisa_rw`)) (concl th) && can (find_term ((=) `read memory s8`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [(REWRITE_TAC[drv_stack] THEN MP_TAC(SPECL [`E:int64`; `312`] TISA_VAL_SP_SUB) THEN
  ANTS_TAC THENL [UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `~(val(E:int64) <= val(a:int64) + 360 /\ val a < val E + 8)` THEN
  UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC);
    (DISCH_TAC THEN UNDISCH_TAC `~rec_written r ds (a:int64)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REC_WRITTEN_D THEN EXISTS_TAC `d:int64` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `drv_in a (word_add d (word 48)) 16` THEN REWRITE_TAC[drv_in] THEN
  REWRITE_TAC[ASSUME `val(word_add d (word 40):int64) = val d + 40`; ASSUME `val(word_add d (word 48):int64) = val d + 48`] THEN
  ARITH_TAC)]);
  ALL_TAC] THEN
  SUBGOAL_THEN `!a. val(E:int64) <= val(a:int64) + 56 /\ val a < val E + 8 ==> read memory s8 a = (m:int64->byte) a`
  ASSUME_TAC THENL
 [(X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `pcr:num`; `pcd:num`; `E:int64`; `r:int64`; `ht:int64`; `nh:int64`;
                    `ds:int64 list`; `pl:int64->(int64 list)list`; `m0:int64->byte`; `opa:int64`; `enda:int64`;
                    `ctl:int64`; `bind:int64`; `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`;
                    `lmc:num->byte list`; `bw:num->int64`; `d:int64`; `a:int64`] REC_GUARD_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[rec_window] THEN DISJ2_TAC THEN DISJ1_TAC THEN
    UNDISCH_TAC `val(E:int64) <= val(a:int64) + 56 /\ val a < val E + 8` THEN ARITH_TAC;
    STRIP_TAC] THEN
  TRANS_TAC EQ_TRANS `(m7:int64->byte) a` THEN CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `tisa_rw`)) (concl th) && can (find_term ((=) `read memory s8`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[drv_stack] THEN MP_TAC(SPECL [`E:int64`; `312`] TISA_VAL_SP_SUB) THEN
    ANTS_TAC THENL [UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `val(E:int64) <= val(a:int64) + 56 /\ val a < val E + 8` THEN
    UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC;
    REWRITE_TAC[drv_in; ASSUME `val(word_add d (word 48):int64) = val d + 48`] THEN
    UNDISCH_TAC `val(E:int64) <= val(a:int64) + 56 /\ val a < val E + 8` THEN
    UNDISCH_TAC `(val d + 40) + 24 <= val E - 360 \/ val(E:int64) - 360 + 368 <= val(d:int64) + 40` THEN
    UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC]);
  ALL_TAC] THEN
  SUBGOAL_THEN `bytes_loaded s8 (word pcr) rec_mc` ASSUME_TAC THENL
   [MATCH_MP_TAC DRV_LOADED_CODE THEN EXISTS_TAC `m0:int64->byte` THEN
    ASM_REWRITE_TAC[COMPUTE_LENGTH_RULE rec_mc] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes64 (word_add d (word 48))) s8 = SND(SND(SND(res:int64#num#(int64->byte)#int64))) /\
                read (memory :> bytes64 (word_sub E (word 56))) s8 = drv_word m (word_sub E (word 56))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `drv_word (drv_final d (drv_word m0 d) (res:int64#num#(int64->byte)#int64)) (word_add d (word 48))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC DRV_READ_OUT THEN EXISTS_TAC `word_sub E (word 312):int64` THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[drv_stack] THEN
        MP_TAC(SPECL [`E:int64`; `312`] TISA_VAL_SP_SUB) THEN
        ANTS_TAC THENL [UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        MP_TAC(SPECL [`word_add d (word 48):int64`; `i:num`] TISA_VAL_OFFSET) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [UNDISCH_TAC `val(d:int64) + 64 <= 2 EXP 64` THEN UNDISCH_TAC `i < 8` THEN ARITH_TAC;
          DISCH_THEN SUBST1_TAC] THEN
        UNDISCH_TAC `(val d + 40) + 24 <= val E - 360 \/ val(E:int64) - 360 + 368 <= val(d:int64) + 40` THEN
        UNDISCH_TAC `360 <= val(E:int64)` THEN UNDISCH_TAC `i < 8` THEN ARITH_TAC;
        REWRITE_TAC[drv_final] THEN
        W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WORD_WRITE_OTHER (lhs w))) THEN
        ANTS_TAC THENL
         [SUBGOAL_THEN `val(word_add d (word 56):int64) = val d + 56` SUBST1_TAC THENL
           [MATCH_MP_TAC TISA_VAL_OFFSET THEN UNDISCH_TAC `val(d:int64) + 64 <= 2 EXP 64` THEN ARITH_TAC;
            ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN UNDISCH_TAC `val(d:int64) + 64 <= 2 EXP 64` THEN ARITH_TAC;
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DRV_WORD_WRITE_SAME]]];
      REWRITE_TAC[DRV_READ64] THEN MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(SPECL [`word_sub E (word 56):int64`; `i:num`] TISA_VAL_OFFSET) THEN
      SUBGOAL_THEN `val(word_sub E (word 56):int64) = val E - 56` SUBST1_TAC THENL
       [MATCH_MP_TAC TISA_VAL_SP_SUB THEN UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `val(E:int64) + 8 <= 2 EXP 64` THEN UNDISCH_TAC `i < 8` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      UNDISCH_TAC `360 <= val(E:int64)` THEN UNDISCH_TAC `i < 8` THEN ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `m8 = read memory s8` THEN
  TISA_STEPS_TAC REC_EXEC (9--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_add (word_sub E (word 56)) (word 8):int64 = word_sub E (word 48)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(FST(res:int64#num#(int64->byte)#int64), drv_final d (drv_word m d) res, SND(SND(SND res)))` THEN
  REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[rec_plan] THEN
    MAP_EVERY EXISTS_TAC [`m7:int64->byte`; `res:int64#num#(int64->byte)#int64`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `a:int64` THEN REWRITE_TAC[rec_stack] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "drv_final")) (concl th) &&
      can (find_term ((=) `m8:int64->byte`)) (concl th))) THEN
    REWRITE_TAC[drv_stack] THEN MP_TAC(SPECL [`E:int64`; `312`] TISA_VAL_SP_SUB) THEN
    ANTS_TAC THENL [UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `~(val(E:int64) <= val(a:int64) + 360 /\ val a < val E)` THEN
    UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Facts the loop proof reads memory with.                                   *)
(* ------------------------------------------------------------------------- *)

(* A word all of whose bytes agree with m0. *)
let REC_READ_M0 = prove
 (`!s (m0:int64->byte) (P:int64->bool) (x:int64).
     (!a. P a ==> read memory s a = m0 a) /\ (!i. i < 8 ==> P (word_add x (word i)))
     ==> read (memory :> bytes64 x) s = drv_word m0 x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DRV_READ64] THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  ASM_SIMP_TAC[]);;

(* A word outside the record loop's stack. *)
let REC_READ_OUT = prove
 (`!s (M:int64->byte) E (x:int64).
     (!a. ~rec_stack E a ==> read memory s a = M a) /\ (!i. i < 8 ==> ~rec_stack E (word_add x (word i)))
     ==> read (memory :> bytes64 x) s = drv_word M x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DRV_READ64] THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  ASM_SIMP_TAC[]);;

(* Words 1..6 of the record descriptor r are fixed bytes. *)
let REC_R_FIXED = prove
 (`!pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc k.
     val r + 72 <= 2 EXP 64 /\ k + 8 <= 56
     ==> !i. i < 8 ==> rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc
                                 (word_add (word_add r (word k)) (word i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rec_fixed] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[drv_in] THEN
  SUBGOAL_THEN `val(word_add (word_add r (word k)) (word i):int64) = val(r:int64) + k + i` SUBST1_TAC THENL
   [SUBGOAL_THEN `val(word_add r (word k):int64) = val(r:int64) + k` ASSUME_TAC THENL
     [MATCH_MP_TAC TISA_VAL_OFFSET THEN UNDISCH_TAC `val(r:int64) + 72 <= 2 EXP 64` THEN
      UNDISCH_TAC `k + 8 <= 56` THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`word_add r (word k):int64`; `i:num`] TISA_VAL_OFFSET) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `val(r:int64) + 72 <= 2 EXP 64` THEN UNDISCH_TAC `k + 8 <= 56` THEN
      UNDISCH_TAC `i < 8` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ARITH_TAC];
    UNDISCH_TAC `k + 8 <= 56` THEN UNDISCH_TAC `i < 8` THEN ARITH_TAC]);;

(* The stack lies in the window. *)
let REC_STACK_WINDOW = prove
 (`!E a. rec_stack E a ==> rec_window E a`,
  REWRITE_TAC[rec_stack; rec_window] THEN ARITH_TAC);;

(* Above the run's return address: the saved registers and the caller's   *)
(* return address, read through a memory that agrees there with mh.       *)
let REC_WIN_READ = prove
 (`!s (mh:int64->byte) (E:int64) (x:int64).
     (!a. val E <= val a + 48 /\ val a < val E + 8 ==> read memory s a = mh a) /\
     val E <= val x + 48 /\ val x <= val E /\ val E + 8 <= 2 EXP 64
     ==> read (memory :> bytes64 x) s = drv_word mh x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DRV_READ64] THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPECL [`x:int64`; `i:num`] TISA_VAL_OFFSET) THEN ANTS_TAC THENL
   [UNDISCH_TAC `val(x:int64) <= val(E:int64)` THEN UNDISCH_TAC `val(E:int64) + 8 <= 2 EXP 64` THEN
    UNDISCH_TAC `i < 8` THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `val(x:int64) <= val(E:int64)` THEN UNDISCH_TAC `val(E:int64) <= val(x:int64) + 48` THEN
  UNDISCH_TAC `i < 8` THEN ARITH_TAC);;

(* The window above the run's return address survives a write of it. *)
let REC_WIN_WRITE = prove
 (`!(E:int64) (v:int64) (m:int64->byte) a.
     360 <= val E /\ val E <= val a + 48
     ==> write (bytes64 (word_sub E (word 56))) v m a = m a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN
  MP_TAC(SPECL [`E:int64`; `56`] TISA_VAL_SP_SUB) THEN
  ANTS_TAC THENL [UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPEC `E:int64` VAL_BOUND_64) THEN
  UNDISCH_TAC `360 <= val(E:int64)` THEN UNDISCH_TAC `val(E:int64) <= val(a:int64) + 48` THEN ARITH_TAC);;

(* So does everything outside the stack. *)
let REC_OUT_WRITE = prove
 (`!(E:int64) (v:int64) (m:int64->byte) a.
     360 <= val E /\ ~rec_stack E a
     ==> write (bytes64 (word_sub E (word 56))) v m a = m a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rec_stack] THEN STRIP_TAC THEN MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN
  MP_TAC(SPECL [`E:int64`; `56`] TISA_VAL_SP_SUB) THEN
  ANTS_TAC THENL [UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPEC `E:int64` VAL_BOUND_64) THEN
  UNDISCH_TAC `360 <= val(E:int64)` THEN
  UNDISCH_TAC `~(val(E:int64) <= val(a:int64) + 360 /\ val a < val E)` THEN ARITH_TAC);;

(* The loop's code lies apart from the stack words it pushes. *)
let REC_CODE_STACK_APART = prove
 (`!pcr (E:int64) k (P:int64->bool).
     pcr + 165 <= 2 EXP 64 /\ 360 <= val E /\ val E + 8 <= 2 EXP 64 /\ 8 <= k /\ k <= 360 /\
     (!a. drv_in a (word pcr) 165 ==> P a) /\ (!a. P a ==> ~rec_window E a)
     ==> nonoverlapping (word pcr:int64,165) (word_sub E (word k),8)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_NONOVERLAP_APART THEN
  SUBGOAL_THEN `val(word pcr:int64) = pcr` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `pcr + 165 <= 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`E:int64`; `k:num`] TISA_VAL_SP_SUB) THEN
  ANTS_TAC THENL [UNDISCH_TAC `360 <= val(E:int64)` THEN UNDISCH_TAC `k <= 360` THEN ARITH_TAC;
                  DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `360 <= val(E:int64)` THEN UNDISCH_TAC `val(E:int64) + 8 <= 2 EXP 64` THEN
    UNDISCH_TAC `k <= 360` THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~rec_window E (a:int64)` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[rec_window; drv_in] THEN
  UNDISCH_TAC `360 <= val(E:int64)` THEN UNDISCH_TAC `8 <= k` THEN UNDISCH_TAC `k <= 360` THEN ARITH_TAC);;
let REC_WIN_WORD = prove
 (`!(m:int64->byte) (mh:int64->byte) (E:int64) (x:int64).
     (!a. val E <= val a + 48 /\ val a < val E + 8 ==> m a = mh a) /\
     val E <= val x + 48 /\ val x <= val E /\ val E + 8 <= 2 EXP 64
     ==> drv_word m x = drv_word mh x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPECL [`x:int64`; `i:num`] TISA_VAL_OFFSET) THEN ANTS_TAC THENL
   [UNDISCH_TAC `val(x:int64) <= val(E:int64)` THEN UNDISCH_TAC `val(E:int64) + 8 <= 2 EXP 64` THEN
    UNDISCH_TAC `i < 8` THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `val(x:int64) <= val(E:int64)` THEN UNDISCH_TAC `val(E:int64) <= val(x:int64) + 48` THEN
  UNDISCH_TAC `i < 8` THEN ARITH_TAC);;
let REC_SAVED_SAME = prove
 (`!(m:int64->byte) (mh:int64->byte) (E:int64).
     360 <= val E /\ val E + 8 <= 2 EXP 64 /\
     (!a. val E <= val a + 48 /\ val a < val E + 8 ==> m a = mh a)
     ==> drv_word m (word_sub E (word 8)) = drv_word mh (word_sub E (word 8)) /\
         drv_word m (word_sub E (word 16)) = drv_word mh (word_sub E (word 16)) /\
         drv_word m (word_sub E (word 24)) = drv_word mh (word_sub E (word 24)) /\
         drv_word m (word_sub E (word 32)) = drv_word mh (word_sub E (word 32)) /\
         drv_word m (word_sub E (word 40)) = drv_word mh (word_sub E (word 40)) /\
         drv_word m (word_sub E (word 48)) = drv_word mh (word_sub E (word 48)) /\
         drv_word m E = drv_word mh E`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `val(word_sub E (word 8):int64) = val E - 8 /\ val(word_sub E (word 16):int64) = val E - 16 /\
                val(word_sub E (word 24):int64) = val E - 24 /\ val(word_sub E (word 32):int64) = val E - 32 /\
                val(word_sub E (word 40):int64) = val E - 40 /\ val(word_sub E (word 48):int64) = val E - 48`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_SP_SUB THEN
    UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC REC_WIN_WORD THEN EXISTS_TAC `E:int64` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC);;
let REC_TABLE_FIXED = prove
 (`!pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc k.
     val ht + 8 * val nh <= 2 EXP 64 /\ k < val nh
     ==> !i. i < 8 ==> rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc
                                 (word_add (word_add ht (word(8 * k))) (word i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rec_fixed] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[drv_in] THEN
  SUBGOAL_THEN `val(word_add ht (word(8 * k)):int64) = val(ht:int64) + 8 * k` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN UNDISCH_TAC `val(ht:int64) + 8 * val(nh:int64) <= 2 EXP 64` THEN
    UNDISCH_TAC `k < val(nh:int64)` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`word_add ht (word(8 * k)):int64`; `i:num`] TISA_VAL_OFFSET) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `val(ht:int64) + 8 * val(nh:int64) <= 2 EXP 64` THEN UNDISCH_TAC `k < val(nh:int64)` THEN
    UNDISCH_TAC `i < 8` THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `k < val(nh:int64)` THEN UNDISCH_TAC `i < 8` THEN ARITH_TAC);;
let REC_PLAN_WF = prove
 (`!progs pcd E ctl nctl bind nbw leaves nl lpc lmc bw pl m0 ds d.
     (!j. j < nl ==> tisa_leaf_wf (progs j) /\ tisa_leaf_spec (progs j) (lmc j) (lpc j)) /\
     ALL (rec_plan_ok progs pcd E ctl nctl bind nbw leaves nl lpc lmc bw pl m0) ds /\ MEM d ds
     ==> !st. MEM st (pl d) ==> tisa_leaf_wf (progs (val(EL 0 st)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:int64`) THEN ASM_REWRITE_TAC[rec_plan_ok; GSYM ALL_MEM] THEN
  STRIP_TAC THEN X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `st:int64 list` o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "drv_step_ok")) (concl th))) THEN
  ASM_REWRITE_TAC[drv_step_ok] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;
let REC_CODE_STACK_APART_N = prove
 (`!pcr (E:int64) k n (P:int64->bool).
     pcr + 165 <= 2 EXP 64 /\ 360 <= val E /\ val E + 8 <= 2 EXP 64 /\ n <= k + 8 /\ k <= 360 /\
     (!a. drv_in a (word pcr) 165 ==> P a) /\ (!a. P a ==> ~rec_window E a)
     ==> nonoverlapping (word pcr:int64,165) (word_sub E (word k),n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DRV_NONOVERLAP_APART THEN
  SUBGOAL_THEN `val(word pcr:int64) = pcr` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `pcr + 165 <= 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`E:int64`; `k:num`] TISA_VAL_SP_SUB) THEN
  ANTS_TAC THENL [UNDISCH_TAC `360 <= val(E:int64)` THEN UNDISCH_TAC `k <= 360` THEN ARITH_TAC;
                  DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `360 <= val(E:int64)` THEN UNDISCH_TAC `val(E:int64) + 8 <= 2 EXP 64` THEN
    UNDISCH_TAC `k <= 360` THEN UNDISCH_TAC `n <= k + 8` THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~rec_window E (a:int64)` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[rec_window; drv_in] THEN
  UNDISCH_TAC `360 <= val(E:int64)` THEN UNDISCH_TAC `n <= k + 8` THEN UNDISCH_TAC `k <= 360` THEN ARITH_TAC);;
(* The written words of r lie apart from the code and from the window. *)
let REC_R_WRITTEN_APART = prove
 (`!pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc (E:int64).
     pcr + 165 <= 2 EXP 64 /\ val r + 72 <= 2 EXP 64 /\ 360 <= val E /\ val E + 8 <= 2 EXP 64 /\
     (!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a
          ==> ~rec_window E a /\ ~rec_written r ds a) /\
     (!a. rec_written r ds a ==> ~rec_window E a)
     ==> nonoverlapping (word pcr:int64,165) (word_add r (word 56),16) /\
         nonoverlapping (word_add r (word 56),16) (word_sub E (word 48),56)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add r (word 56):int64) = val(r:int64) + 56` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN UNDISCH_TAC `val(r:int64) + 72 <= 2 EXP 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC DRV_NONOVERLAP_APART THENL
   [SUBGOAL_THEN `val(word pcr:int64) = pcr` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `pcr + 165 <= 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `val(r:int64) + 72 <= 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~rec_written r ds (a:int64)` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `a:int64` o check (fun th -> can (find_term ((=) `rec_fixed`)) (concl th))) THEN
      ANTS_TAC THENL [REWRITE_TAC[rec_fixed] THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
      REWRITE_TAC[rec_written; DE_MORGAN_THM] THEN MESON_TAC[]];
    MP_TAC(SPECL [`E:int64`; `48`] TISA_VAL_SP_SUB) THEN
    ANTS_TAC THENL [UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `val(r:int64) + 72 <= 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `360 <= val(E:int64)` THEN UNDISCH_TAC `val(E:int64) + 8 <= 2 EXP 64` THEN ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~rec_window E (a:int64)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `rec_written`)) (concl th) &&
         not (can (find_term ((=) `rec_fixed`)) (concl th)))) THEN
      REWRITE_TAC[rec_written] THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[rec_window; drv_in] THEN UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC]]);;
let REC_R_WRITTEN_SIDE = prove
 (`!r ds (E:int64).
     val r + 72 <= 2 EXP 64 /\ 360 <= val E /\ (!a. rec_written r ds a ==> ~rec_window E a)
     ==> val r + 432 <= val E \/ val E + 8 <= val r + 56`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `word_add r (word 56):int64` th) THEN MP_TAC(SPEC `word_add r (word 71):int64` th)) THEN
  SUBGOAL_THEN `val(word_add r (word 56):int64) = val(r:int64) + 56 /\ val(word_add r (word 71):int64) = val(r:int64) + 71`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN UNDISCH_TAC `val(r:int64) + 72 <= 2 EXP 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rec_written; rec_window; drv_in] THEN
  SUBGOAL_THEN `val(word_add r (word 56):int64) = val(r:int64) + 56` (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  UNDISCH_TAC `val(r:int64) + 72 <= 2 EXP 64` THEN ARITH_TAC);;
let REC_EPI_SAVED = prove
 (`!(r:int64) (E:int64) (v1:int64) (v2:int64) (m:int64->byte).
     val r + 72 <= 2 EXP 64 /\ 360 <= val E /\ val E + 8 <= 2 EXP 64 /\
     (val r + 432 <= val E \/ val E + 8 <= val r + 56)
     ==> let W = write (bytes64 (word_add r (word 64))) v1 (write (bytes64 (word_add r (word 56))) v2 m) in
         drv_word W (word_sub E (word 8)) = drv_word m (word_sub E (word 8)) /\
         drv_word W (word_sub E (word 16)) = drv_word m (word_sub E (word 16)) /\
         drv_word W (word_sub E (word 24)) = drv_word m (word_sub E (word 24)) /\
         drv_word W (word_sub E (word 32)) = drv_word m (word_sub E (word 32)) /\
         drv_word W (word_sub E (word 40)) = drv_word m (word_sub E (word 40)) /\
         drv_word W (word_sub E (word 48)) = drv_word m (word_sub E (word 48)) /\
         drv_word W E = drv_word m E`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `val(word_sub E (word 8):int64) = val E - 8 /\ val(word_sub E (word 16):int64) = val E - 16 /\
                val(word_sub E (word 24):int64) = val E - 24 /\ val(word_sub E (word 32):int64) = val E - 32 /\
                val(word_sub E (word 40):int64) = val E - 40 /\ val(word_sub E (word 48):int64) = val E - 48 /\
                val(word_add r (word 56):int64) = val r + 56 /\ val(word_add r (word 64):int64) = val r + 64`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    (MATCH_MP_TAC TISA_VAL_SP_SUB ORELSE MATCH_MP_TAC TISA_VAL_OFFSET) THEN
    UNDISCH_TAC `360 <= val(E:int64)` THEN UNDISCH_TAC `val(r:int64) + 72 <= 2 EXP 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  REPEAT(W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WORD_WRITE_OTHER (lhs w))) THEN
         ANTS_TAC THENL
          [ASM_REWRITE_TAC[] THEN VAL_FACTS_ARITH_TAC [`val(E:int64)`; `val(r:int64)`];
           DISCH_THEN SUBST1_TAC]) THEN
  REFL_TAC);;

(* Nested stack offsets. *)
let REC_SUB_SUB = prove
 (`!(E:int64) a b. word_sub (word_sub E (word a)) (word b) = word_sub E (word(a + b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* Reading word k of the record descriptor r in state sname, as v. *)
let REC_RWORD_TAC sname k v =
  let s = mk_var(sname, `:x86state`) in
  let x = subst [mk_small_numeral k, `k:num`] `word_add (r:int64) (word k)` in
  let goal = subst [s, `s:x86state`; x, `x:int64`; v, `v:int64`] `read (memory :> bytes64 x) s = (v:int64)` in
  SUBGOAL_THEN goal ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS (subst [x, `x:int64`] `drv_word (m0:int64->byte) x`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REC_READ_M0 THEN
      EXISTS_TAC `rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc` THEN
      CONJ_TAC THENL
       [FIRST_ASSUM(fun th -> if is_forall(concl th) &&
           can (find_term ((=) (mk_comb(`read (memory:(x86state,int64->byte)component)`, s)))) (concl th) &&
           can (find_term ((=) `rec_fixed`)) (concl th) then ACCEPT_TAC th else failwith "");
        MATCH_MP_TAC REC_R_FIXED THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC];;

(* The fixed bytes in state sname agree with m0, from agreement with M off the stack. *)
let REC_S_FIXED_TAC sname mvar =
  let s = mk_var(sname, `:x86state`) in
  SUBGOAL_THEN (subst [s, `s:x86state`]
     `!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a ==> read memory s a = (m0:int64->byte) a`)
  ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS (mk_comb(mvar, `a:int64`)) THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) (mk_comb(`read (memory:(x86state,int64->byte)component)`, s)))) (concl th) &&
        can (find_term ((=) `rec_stack`)) (concl th))) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `rec_stack`)) (concl th) && can (find_term ((=) `rec_fixed`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) mvar)) (concl th) && can (find_term ((=) `rec_fixed`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC];;

(* The loop's code is loaded in state sname. *)
let REC_LOADED_TAC sname =
  let s = mk_var(sname, `:x86state`) in
  SUBGOAL_THEN (subst [s, `s:x86state`] `bytes_loaded s (word pcr) rec_mc`) ASSUME_TAC THENL
   [MATCH_MP_TAC DRV_LOADED_CODE THEN EXISTS_TAC `m0:int64->byte` THEN
    ASM_REWRITE_TAC[COMPUTE_LENGTH_RULE rec_mc] THEN X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) (mk_comb(`read (memory:(x86state,int64->byte)component)`, s)))) (concl th) &&
        can (find_term ((=) `rec_fixed`)) (concl th))) THEN
    ASM_REWRITE_TAC[rec_fixed];
    ALL_TAC];;

(* The fixed bytes lie outside the window (from the layout). *)
let REC_FIXED_NOT_WINDOW_TAC =
  X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `rec_window`)) (concl th) && can (find_term ((=) `rec_written`)) (concl th) &&
      can (find_term ((=) `rec_fixed`)) (concl th) && length(fst(strip_forall(concl th))) = 1
      then ACCEPT_TAC(CONJUNCT1(MP (SPEC `a:int64` th)
             (ASSUME `rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a`)))
      else failwith "");;

(* The loop's code lies apart from the 8 stack bytes at E - k. *)
let REC_CODE_APART_TAC k =
  SUBGOAL_THEN (subst [mk_small_numeral k, `k:num`] `nonoverlapping (word pcr:int64,165) (word_sub E (word k),8)`)
  ASSUME_TAC THENL
   [MATCH_MP_TAC REC_CODE_STACK_APART THEN
    EXISTS_TAC `rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
     [SIMP_TAC[rec_fixed]; REC_FIXED_NOT_WINDOW_TAC];
    ALL_TAC];;

(* The 8 bytes at opa (or enda) lie off the stack. *)
let REC_WORD_OFF_STACK_TAC which =
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `opa:int64`)) (concl th) && can (find_term ((=) `enda:int64`)) (concl th) &&
      can (find_term ((=) `rec_window`)) (concl th) && length(fst(strip_forall(concl th))) = 1
      then MP_TAC(which(MP (SPEC `i:num` th) (ASSUME `i < 8`))) else failwith "") THEN
  REWRITE_TAC[rec_window; rec_stack] THEN ARITH_TAC;;

(* An assumption !a. ... ==> read memory s a = ... (or m a = ...) selected by its memory term and a marker. *)
let rec_mem_assum mtm marker th =
  is_forall(concl th) && can (find_term ((=) mtm)) (concl th) && can (find_term ((=) marker)) (concl th);;

(* The saved words and the caller's return address in memory mk. *)
let REC_SAVED_TAC mk =
  MP_TAC(SPECL [mk; `mh:int64->byte`; `E:int64`] REC_SAVED_SAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(REWRITE_RULE (map ASSUME
    [`drv_word mh (word_sub E (word 8)) = rbxv`; `drv_word mh (word_sub E (word 16)) = rbpv`;
     `drv_word mh (word_sub E (word 24)) = r12v`; `drv_word mh (word_sub E (word 32)) = r13v`;
     `drv_word mh (word_sub E (word 40)) = r14v`; `drv_word mh (word_sub E (word 48)) = r15v`;
     `drv_word mh E = ret`]) th));;

(* The final state at done: the post's facts, res, and the rec_run rule that gives it. *)
let REC_FINAL_TAC res_tm rule_th =
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[DRV_READ64] THEN ASM_REWRITE_TAC[] THEN
  TRY(CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC]) THEN
  EXISTS_TAC res_tm THEN
  CONJ_TAC THENL [MATCH_MP_TAC rule_th THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[];;

(* The same, for a rule whose conclusion leaves the decode plan's result r1 open. *)
let REC_FINAL2_TAC res_tm rule_th r1_tm =
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[DRV_READ64] THEN ASM_REWRITE_TAC[] THEN
  TRY(CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC]) THEN
  EXISTS_TAC res_tm THEN
  CONJ_TAC THENL [MATCH_MP_TAC rule_th THEN EXISTS_TAC r1_tm THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The loop, by induction on the fuel left (the allowance less the receipt). *)
(* ------------------------------------------------------------------------- *)

let REC_RUN_EXHAUSTED, REC_RUN_DECODE_STOP, REC_RUN_MISSING, REC_RUN_HANDLER_STOP,
    REC_RUN_END, REC_RUN_NEXT =
  match CONJUNCTS (SPEC_ALL rec_run_RULES) with
    [a;b;c;d;e;f] -> a,b,c,d,e,f | _ -> failwith "rec_run_RULES";;

let rec_loop_premises =
 `(!j. j < nl ==> tisa_leaf_wf (progs j) /\ tisa_leaf_spec (progs j) (lmc j) (lpc j)) /\
  rec_layout progs pcr pcd E r ht nh ds pl m0 opa enda ctl bind nbw leaves nl lpc lmc bw /\
  ALL (rec_plan_ok progs pcd E ctl nctl bind nbw leaves nl lpc lmc bw pl m0) ds /\
  MEM dd ds /\
  (!k. k < val nh
       ==> drv_word m0 (word_add ht (word(8 * k))) = word 0 \/
           MEM (drv_word m0 (word_add ht (word(8 * k)))) ds) /\
  rec_desc m0 r pcd dd ht nh opa enda budget used0 /\
  drv_code m0 pcr rec_mc /\ drv_code m0 pcd drv_mc /\ (!j. j < nl ==> drv_code m0 (lpc j) (lmc j))`;;

let rec_loop_goal = mk_imp(rec_loop_premises,
 `!n M used c.
     val budget - val used = n /\
     (!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a ==> M a = m0 a)
     ==> ensures x86
          (\s. read RIP s = word(pcr + 23) /\ read RSP s = word_sub E (word 48) /\
               read RBX s = r /\ read RBP s = used /\ read R12 s = word c /\ read R14 s = r14v /\
               read R15 s = word pcd /\
               read (memory :> bytes64 (word_sub E (word 8))) s = rbxv /\
               read (memory :> bytes64 (word_sub E (word 16))) s = rbpv /\
               read (memory :> bytes64 (word_sub E (word 24))) s = r12v /\
               read (memory :> bytes64 (word_sub E (word 32))) s = r13v /\
               read (memory :> bytes64 (word_sub E (word 40))) s = r14v /\
               read (memory :> bytes64 (word_sub E (word 48))) s = r15v /\
               read (memory :> bytes64 E) s = ret /\
               (!a. ~rec_stack E a ==> read memory s a = M a))
          (\s. read RIP s = word(pcr + 118) /\ read RSP s = word_sub E (word 48) /\
               read RBX s = r /\
               read (memory :> bytes64 (word_sub E (word 8))) s = rbxv /\
               read (memory :> bytes64 (word_sub E (word 16))) s = rbpv /\
               read (memory :> bytes64 (word_sub E (word 24))) s = r12v /\
               read (memory :> bytes64 (word_sub E (word 32))) s = r13v /\
               read (memory :> bytes64 (word_sub E (word 40))) s = r14v /\
               read (memory :> bytes64 (word_sub E (word 48))) s = r15v /\
               read (memory :> bytes64 E) s = ret /\
               ?res. rec_run progs bw ctl budget E pl dd ht nh opa enda M used c res /\
                     read RAX s = FST res /\ read RBP s = SND(SND(SND res)) /\
                     read R12 s = word(FST(SND res)) /\
                     (!a. ~rec_stack E a ==> read memory s a = FST(SND(SND res)) a) /\
                     (!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a
                          ==> FST(SND(SND res)) a = m0 a))
          (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                      R12; R13; R14; R15; RBP] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`);;
let rec_loop_goal = list_mk_forall(frees rec_loop_goal, rec_loop_goal);;

let REC_LOOP_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL REC_RUN) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rec_layout] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "rec_layout")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rec_desc] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "rec_desc")) (concl th))) THEN
  SUBGOAL_THEN `!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a ==> ~rec_stack E a`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `rec_window`)) (concl th) && can (find_term ((=) `rec_written`)) (concl th) &&
      can (find_term ((=) `rec_fixed`)) (concl th) && length(fst(strip_forall(concl th))) = 1
      then MP_TAC(CONJUNCT1(MP (SPEC `a:int64` th)
             (ASSUME `rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a`)))
      else failwith "") THEN
    REWRITE_TAC[rec_window; rec_stack] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!d i. MEM d ds /\ i < 8 ==> ~rec_stack E (word_add d (word i))` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `rec_stack`)) (concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
    REWRITE_TAC[rec_fixed] THEN
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `d:int64` THEN ASM_REWRITE_TAC[drv_in] THEN
    FIRST_ASSUM(MP_TAC o SPEC `d:int64` o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 1 &&
      fst(dest_var(fst(dest_forall(concl th)))) = "d" && can (find_term ((=) `64`)) (concl th))) THEN
    DISCH_THEN(ASSUME_TAC o C MP (ASSUME `MEM (d:int64) ds`)) THEN
    MP_TAC(SPECL [`d:int64`; `i:num`] TISA_VAL_OFFSET) THEN ANTS_TAC THENL
     [UNDISCH_TAC `val(d:int64) + 64 <= 2 EXP 64` THEN UNDISCH_TAC `i < 8` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC `i < 8` THEN ARITH_TAC];
    ALL_TAC];;

let REC_LOOP_HEAD_TAC =
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`M:int64->byte`; `used:int64`; `c:num`] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  REC_S_FIXED_TAC "s0" `M:int64->byte` THEN
  REC_LOADED_TAC "s0" THEN
  REC_RWORD_TAC "s0" 48 `budget:int64` THEN REC_RWORD_TAC "s0" 8 `dd:int64` THEN
  SUBGOAL_THEN
   `drv_word (read memory s0) (word_sub E (word 8)) = rbxv /\
    drv_word (read memory s0) (word_sub E (word 16)) = rbpv /\
    drv_word (read memory s0) (word_sub E (word 24)) = r12v /\
    drv_word (read memory s0) (word_sub E (word 32)) = r13v /\
    drv_word (read memory s0) (word_sub E (word 40)) = r14v /\
    drv_word (read memory s0) (word_sub E (word 48)) = r15v /\
    drv_word (read memory s0) E = ret` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DRV_READ64] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `mh = read memory s0`;;

let REC_LOOP_EXHAUSTED_TAC =
  SUBGOAL_THEN `~(val(used:int64) < val(budget:int64))` ASSUME_TAC THENL
   [UNDISCH_TAC `val(budget:int64) <= val(used:int64)` THEN ARITH_TAC; ALL_TAC] THEN
  TISA_STEPS_TAC REC_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC] THEN
  EXISTS_TAC `(word 4:int64, c:num, M:int64->byte, used:int64)` THEN
  REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REC_RUN_EXHAUSTED THEN ASM_REWRITE_TAC[];;

let REC_LOOP_DECODE_TAC =
  SUBGOAL_THEN `val(used:int64) < val(budget:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(val(budget:int64) <= val(used:int64))` THEN ARITH_TAC; ALL_TAC] THEN
  REC_CODE_APART_TAC 56 THEN
  TISA_STEPS_TAC REC_EXEC (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_sub (word_sub E (word 48)) (word 8):int64 = word_sub E (word 56)`]) THEN
  ABBREV_TAC `m5 = read memory s5` THEN
  SUBGOAL_THEN `!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a ==> m5 a = (m0:int64->byte) a`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m5:int64->byte`)) THEN
    TRANS_TAC EQ_TRANS `(mh:int64->byte) a` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REC_OUT_WRITE THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `rec_stack`)) (concl th) && can (find_term ((=) `rec_fixed`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `mh:int64->byte`)) (concl th) && can (find_term ((=) `rec_fixed`)) (concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`dd:int64`; `word_add used (word 1):int64`; `m5:int64->byte`; `budget:int64`;
                              `word c:int64`; `r14v:int64`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `word(pcr + 137):int64`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN TISA_BIGSTEP_TAC "s6";;

let REC_LOOP_AFTER1_TAC =
  SUBGOAL_THEN `drv_word m5 (word_sub E (word 56)) = word(pcr + 42)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m5:int64->byte`)) THEN
    REWRITE_TAC[DRV_WORD_WRITE_SAME];
    ALL_TAC] THEN
  REC_LOADED_TAC "s6" THEN
  REC_RWORD_TAC "s6" 32 `opa:int64` THEN REC_RWORD_TAC "s6" 24 `nh:int64` THEN
  REC_RWORD_TAC "s6" 16 `ht:int64` THEN REC_RWORD_TAC "s6" 40 `enda:int64` THEN
  SUBGOAL_THEN `read (memory :> bytes64 opa) s6 = drv_word (FST(SND(r1:int64#(int64->byte)#int64))) opa`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REC_READ_OUT THEN EXISTS_TAC `E:int64` THEN CONJ_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o check (rec_mem_assum `read memory s6` `rec_stack`));
      REC_WORD_OFF_STACK_TAC CONJUNCT1];
    ALL_TAC] THEN
  ABBREV_TAC `m6 = read memory s6` THEN
  SUBGOAL_THEN `!a. val(E:int64) <= val(a:int64) + 48 /\ val a < val E + 8 ==> m6 a = (mh:int64->byte) a`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS `(m5:int64->byte) a` THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (rec_mem_assum `m6:int64->byte` `56`)) THEN
      UNDISCH_TAC `val(E:int64) <= val(a:int64) + 48 /\ val a < val E + 8` THEN ARITH_TAC;
      FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m5:int64->byte`)) THEN
      MATCH_MP_TAC REC_WIN_WRITE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a
                    ==> FST(SND(r1:int64#(int64->byte)#int64)) a = (m0:int64->byte) a`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS `(m6:int64->byte) a` THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (rec_mem_assum `m6:int64->byte` `rec_stack`)) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `rec_stack`)) (concl th) && can (find_term ((=) `rec_fixed`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o check (rec_mem_assum `m6:int64->byte` `rec_fixed`)) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `rec_plan progs bw ctl budget E pl dd M (word_add used (word 1)) r1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `E:int64`;
                  `pl:int64->(int64 list)list`; `dd:int64`; `m5:int64->byte`; `M:int64->byte`;
                  `word_add used (word 1):int64`; `r1:int64#(int64->byte)#int64`] REC_PLAN_LOCAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS `(mh:int64->byte) a` THEN CONJ_TAC THENL
         [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m5:int64->byte`)) THEN
          MATCH_MP_TAC REC_OUT_WRITE THEN ASM_REWRITE_TAC[];
          FIRST_ASSUM(MATCH_MP_TAC o check (rec_mem_assum `mh:int64->byte` `M:int64->byte`)) THEN
          FIRST_ASSUM ACCEPT_TAC];
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 2 && can (find_term ((=) `rec_stack`)) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC];;

let REC_LOOP_DSTOP_TAC =
  SUBGOAL_THEN `~(val(word_sub (FST(r1:int64#(int64->byte)#int64)) (word 1)) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  TISA_STEPS_TAC REC_EXEC (7--8) THEN
  REC_SAVED_TAC `m6:int64->byte` THEN
  REC_FINAL_TAC `(FST(r1:int64#(int64->byte)#int64), c:num, FST(SND r1), SND(SND r1))` REC_RUN_DECODE_STOP;;

let REC_LOOP_PAST_TAC =
  SUBGOAL_THEN `rec_missing ht nh opa (FST(SND(r1:int64#(int64->byte)#int64)))` ASSUME_TAC THENL
   [REWRITE_TAC[rec_missing] THEN DISJ1_TAC THEN
    UNDISCH_TAC `~(val(drv_word (FST(SND(r1:int64#(int64->byte)#int64))) opa) < val(nh:int64))` THEN ARITH_TAC;
    ALL_TAC] THEN
  TISA_STEPS_TAC REC_EXEC (12--13) THEN
  REC_SAVED_TAC `m6:int64->byte` THEN
  REC_FINAL_TAC `(word 2:int64, c:num, FST(SND(r1:int64#(int64->byte)#int64)), SND(SND r1))` REC_RUN_MISSING;;

let REC_LOOP_ENTRY_TAC =
  TISA_STEPS_TAC REC_EXEC (12--13) THEN
  SUBGOAL_THEN `!i. i < 8 ==> rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc
       (word_add (word_add ht (word(8 * val(drv_word (FST(SND(r1:int64#(int64->byte)#int64))) opa)))) (word i))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REC_TABLE_FIXED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `drv_word (m0:int64->byte) (word_add ht (word(8 * val(drv_word (FST(SND(r1:int64#(int64->byte)#int64))) opa)))) =
                rec_handler ht opa (FST(SND r1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[rec_handler] THEN MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (rec_mem_assum `FST(SND(r1:int64#(int64->byte)#int64))` `rec_fixed`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes64 (word_add ht (word(8 * val(drv_word (FST(SND(r1:int64#(int64->byte)#int64))) opa))))) s13 =
                rec_handler ht opa (FST(SND r1))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `rec_handler`)) (rhs(concl th)) && is_comb(lhs(concl th)) &&
      rator(rator(lhs(concl th))) = `drv_word`)) THEN
    MATCH_MP_TAC REC_READ_M0 THEN
    EXISTS_TAC `rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `m6:int64->byte`)) (concl th) &&
       can (find_term ((=) `rec_fixed`)) (concl th) then ACCEPT_TAC(REWRITE_RULE[GSYM(ASSUME `read memory s13 = m6`)] th)
       else failwith "");
    ALL_TAC] THEN
  TISA_STEPS_TAC REC_EXEC (14--15);;

let REC_LOOP_EMPTY_TAC =
  SUBGOAL_THEN `val(rec_handler ht opa (FST(SND(r1:int64#(int64->byte)#int64)))) = 0 /\
                rec_missing ht nh opa (FST(SND r1))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_0; rec_missing] THEN DISJ2_TAC THEN
    UNDISCH_TAC `rec_handler ht opa (FST(SND(r1:int64#(int64->byte)#int64))) = word 0` THEN
    REWRITE_TAC[rec_handler];
    ALL_TAC] THEN
  TISA_STEPS_TAC REC_EXEC (16--17) THEN
  REC_SAVED_TAC `m6:int64->byte` THEN
  REC_FINAL_TAC `(word 2:int64, c:num, FST(SND(r1:int64#(int64->byte)#int64)), SND(SND r1))` REC_RUN_MISSING;;

let REC_LOOP_FIRED1_TAC =
  SUBGOAL_THEN `val(word_sub (FST(r1:int64#(int64->byte)#int64)) (word 1)) = 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0]; ALL_TAC] THEN
  TISA_STEPS_TAC REC_EXEC (7--11);;

let REC_LOOP_HFACTS_TAC =
  SUBGOAL_THEN `~(val(rec_handler ht opa (FST(SND(r1:int64#(int64->byte)#int64)))) = 0) /\
                ~rec_missing ht nh opa (FST(SND r1)) /\
                MEM (rec_handler ht opa (FST(SND r1))) ds` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[VAL_EQ_0];
      REWRITE_TAC[rec_missing; DE_MORGAN_THM; NOT_LE] THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `~(rec_handler ht opa (FST(SND(r1:int64#(int64->byte)#int64))) = word 0)` THEN
        REWRITE_TAC[rec_handler]];
      FIRST_ASSUM(MP_TAC o SPEC `val(drv_word (FST(SND(r1:int64#(int64->byte)#int64))) opa)` o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `ht:int64`)) (concl th) &&
                         length(fst(strip_forall(concl th))) = 1 &&
                         fst(dest_var(fst(dest_forall(concl th)))) = "k")) THEN
      REWRITE_TAC[ASSUME `val (drv_word (FST (SND (r1:int64#(int64->byte)#int64))) opa) < val (nh:int64)`] THEN
      REWRITE_TAC[ASSUME `drv_word (m0:int64->byte)
          (word_add ht (word (8 * val (drv_word (FST (SND (r1:int64#(int64->byte)#int64))) opa)))) =
          rec_handler ht opa (FST(SND r1))`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  TISA_STEPS_TAC REC_EXEC (16--17);;

let REC_LOOP_HRUN_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_sub (word_sub E (word 48)) (word 8):int64 = word_sub E (word 56)`]) THEN
  ABBREV_TAC `m17 = read memory s17` THEN
  SUBGOAL_THEN `!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a ==> m17 a = (m0:int64->byte) a`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m17:int64->byte`)) THEN
    TRANS_TAC EQ_TRANS `(m6:int64->byte) a` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REC_OUT_WRITE THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `rec_stack`)) (concl th) && can (find_term ((=) `rec_fixed`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o check (rec_mem_assum `m6:int64->byte` `rec_fixed`)) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`rec_handler ht opa (FST(SND(r1:int64#(int64->byte)#int64)))`;
                              `SND(SND(r1:int64#(int64->byte)#int64))`; `m17:int64->byte`; `budget:int64`;
                              `word c:int64`; `r14v:int64`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `word(pcr + 137):int64`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN TISA_BIGSTEP_TAC "s18";;

let REC_LOOP_AFTER2_TAC =
  SUBGOAL_THEN `drv_word m17 (word_sub E (word 56)) = word(pcr + 79)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m17:int64->byte`)) THEN
    REWRITE_TAC[DRV_WORD_WRITE_SAME];
    ALL_TAC] THEN
  REC_LOADED_TAC "s18" THEN
  REC_RWORD_TAC "s18" 40 `enda:int64` THEN
  SUBGOAL_THEN `read (memory :> bytes64 enda) s18 = drv_word (FST(SND(r1':int64#(int64->byte)#int64))) enda`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REC_READ_OUT THEN EXISTS_TAC `E:int64` THEN CONJ_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o check (rec_mem_assum `read memory s18` `rec_stack`));
      REC_WORD_OFF_STACK_TAC CONJUNCT2];
    ALL_TAC] THEN
  ABBREV_TAC `m18 = read memory s18` THEN
  SUBGOAL_THEN `!a. val(E:int64) <= val(a:int64) + 48 /\ val a < val E + 8 ==> m18 a = (mh:int64->byte) a`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS `(m17:int64->byte) a` THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (rec_mem_assum `m18:int64->byte` `56`)) THEN
      UNDISCH_TAC `val(E:int64) <= val(a:int64) + 48 /\ val a < val E + 8` THEN ARITH_TAC;
      TRANS_TAC EQ_TRANS `(m6:int64->byte) a` THEN CONJ_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m17:int64->byte`)) THEN
        MATCH_MP_TAC REC_WIN_WRITE THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM(MATCH_MP_TAC o check (rec_mem_assum `m6:int64->byte` `mh:int64->byte`)) THEN
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a
                    ==> FST(SND(r1':int64#(int64->byte)#int64)) a = (m0:int64->byte) a`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS `(m18:int64->byte) a` THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (rec_mem_assum `m18:int64->byte` `rec_stack`)) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `rec_stack`)) (concl th) && can (find_term ((=) `rec_fixed`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o check (rec_mem_assum `m18:int64->byte` `rec_fixed`)) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `rec_plan progs bw ctl budget E pl (rec_handler ht opa (FST(SND(r1:int64#(int64->byte)#int64))))
                         (FST(SND r1)) (SND(SND r1)) r1'` ASSUME_TAC THENL
   [MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `E:int64`;
                  `pl:int64->(int64 list)list`; `rec_handler ht opa (FST(SND(r1:int64#(int64->byte)#int64)))`;
                  `m17:int64->byte`; `FST(SND(r1:int64#(int64->byte)#int64))`;
                  `SND(SND(r1:int64#(int64->byte)#int64))`; `r1':int64#(int64->byte)#int64`] REC_PLAN_LOCAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS `(m6:int64->byte) a` THEN CONJ_TAC THENL
         [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m17:int64->byte`)) THEN
          MATCH_MP_TAC REC_OUT_WRITE THEN ASM_REWRITE_TAC[];
          FIRST_ASSUM(MATCH_MP_TAC o check (rec_mem_assum `m6:int64->byte` `rec_stack`)) THEN
          FIRST_ASSUM ACCEPT_TAC];
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 2 && can (find_term ((=) `rec_stack`)) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC];;

let REC_LOOP_HSTOP_TAC =
  SUBGOAL_THEN `~(val(word_sub (FST(r1':int64#(int64->byte)#int64)) (word 1)) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  TISA_STEPS_TAC REC_EXEC (19--20) THEN
  REC_SAVED_TAC `m18:int64->byte` THEN
  REC_FINAL2_TAC `(FST(r1':int64#(int64->byte)#int64), c:num, FST(SND r1'), SND(SND r1'))` REC_RUN_HANDLER_STOP
    `r1:int64#(int64->byte)#int64`;;

let REC_LOOP_HFIRED_TAC =
  SUBGOAL_THEN `val(word_sub (FST(r1':int64#(int64->byte)#int64)) (word 1)) = 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0]; ALL_TAC] THEN
  TISA_STEPS_TAC REC_EXEC (19--23);;

let REC_LOOP_END_TAC =
  SUBGOAL_THEN `~(val(word_sub (drv_word (FST(SND(r1':int64#(int64->byte)#int64))) enda) (word 0)) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB_0; VAL_EQ_0]; ALL_TAC] THEN
  TISA_STEPS_TAC REC_EXEC (24--26) THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) = `word_add (word c) (word 1):int64`
                          then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else failwith "") THEN
  REC_SAVED_TAC `m18:int64->byte` THEN
  REC_FINAL2_TAC `(word 1:int64, c + 1, FST(SND(r1':int64#(int64->byte)#int64)), SND(SND r1'))` REC_RUN_END
    `r1:int64#(int64->byte)#int64`;;

let REC_LOOP_NEXT_TAC =
  SUBGOAL_THEN `val(word_sub (drv_word (FST(SND(r1':int64#(int64->byte)#int64))) enda) (word 0)) = 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB_0; VAL_WORD_0]; ALL_TAC] THEN
  TISA_STEPS_TAC REC_EXEC (24--24) THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) = `word_add (word c) (word 1):int64`
                          then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else failwith "") THEN
  SUBGOAL_THEN `val(budget:int64) - val(SND(SND(r1':int64#(int64->byte)#int64))) < n` ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word_add used (word 1):int64) <= val(SND(SND(r1:int64#(int64->byte)#int64))) /\
                  val(SND(SND(r1:int64#(int64->byte)#int64))) <= val(SND(SND(r1':int64#(int64->byte)#int64)))`
     MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REC_PLAN_FUEL THEN
      MAP_EVERY EXISTS_TAC [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `E:int64`;
                            `pl:int64->(int64 list)list`] THENL
       [EXISTS_TAC `dd:int64` THEN EXISTS_TAC `M:int64->byte`;
        EXISTS_TAC `rec_handler ht opa (FST(SND(r1:int64#(int64->byte)#int64)))` THEN
        EXISTS_TAC `FST(SND(r1:int64#(int64->byte)#int64))`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REC_PLAN_WF THEN
      MAP_EVERY EXISTS_TAC [`pcd:num`; `E:int64`; `ctl:int64`; `nctl:num`; `bind:int64`; `nbw:num`;
                            `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`; `bw:num->int64`;
                            `m0:int64->byte`; `ds:int64 list`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`used:int64`; `1`] TISA_VAL_OFFSET) THEN ANTS_TAC THENL
     [MP_TAC(ISPEC `budget:int64` VAL_BOUND_64) THEN
      UNDISCH_TAC `val(used:int64) < val(budget:int64)` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `val(budget:int64) - val(used:int64) = n` THEN
    UNDISCH_TAC `val(used:int64) < val(budget:int64)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REC_SAVED_TAC `m18:int64->byte` THEN
  SUBGOAL_THEN
   `read (memory :> bytes64 (word_sub E (word 8))) s24 = rbxv /\
    read (memory :> bytes64 (word_sub E (word 16))) s24 = rbpv /\
    read (memory :> bytes64 (word_sub E (word 24))) s24 = r12v /\
    read (memory :> bytes64 (word_sub E (word 32))) s24 = r13v /\
    read (memory :> bytes64 (word_sub E (word 40))) s24 = r14v /\
    read (memory :> bytes64 (word_sub E (word 48))) s24 = r15v /\
    read (memory :> bytes64 E) s24 = ret /\
    (!a. ~rec_stack E a ==> read memory s24 a = FST(SND(r1':int64#(int64->byte)#int64)) a)`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[DRV_READ64] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `val(budget:int64) - val(SND(SND(r1':int64#(int64->byte)#int64)))` o
    check (fun th -> is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "m" &&
                     can (find_term ((=) `n:num`)) (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`FST(SND(r1':int64#(int64->byte)#int64))`; `SND(SND(r1':int64#(int64->byte)#int64))`;
                             `c + 1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN TISA_BIGSTEP_TAC "s25" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC]) THEN
  EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REC_RUN_NEXT THEN
  MAP_EVERY EXISTS_TAC [`r1:int64#(int64->byte)#int64`; `r1':int64#(int64->byte)#int64`] THEN
  ASM_REWRITE_TAC[];;

let REC_LOOP = prove
 (rec_loop_goal,
  REC_LOOP_SETUP_TAC THEN REC_LOOP_HEAD_TAC THEN
  ASM_CASES_TAC `val(budget:int64) <= val(used:int64)` THENL
   [REC_LOOP_EXHAUSTED_TAC;
    REC_LOOP_DECODE_TAC THEN REC_LOOP_AFTER1_TAC THEN
    ASM_CASES_TAC `FST(r1:int64#(int64->byte)#int64) = word 1` THENL
     [REC_LOOP_FIRED1_TAC THEN
      ASM_CASES_TAC `val(drv_word (FST(SND(r1:int64#(int64->byte)#int64))) opa) < val(nh:int64)` THENL
       [REC_LOOP_ENTRY_TAC THEN
        ASM_CASES_TAC `rec_handler ht opa (FST(SND(r1:int64#(int64->byte)#int64))) = word 0` THENL
         [REC_LOOP_EMPTY_TAC;
          REC_LOOP_HFACTS_TAC THEN REC_LOOP_HRUN_TAC THEN REC_LOOP_AFTER2_TAC THEN
          ASM_CASES_TAC `FST(r1':int64#(int64->byte)#int64) = word 1` THENL
           [REC_LOOP_HFIRED_TAC THEN
            ASM_CASES_TAC `drv_word (FST(SND(r1':int64#(int64->byte)#int64))) enda = word 0` THENL
             [REC_LOOP_NEXT_TAC; REC_LOOP_END_TAC];
            REC_LOOP_HSTOP_TAC]];
        REC_LOOP_PAST_TAC];
      REC_LOOP_DSTOP_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* REC_CORRECT: the call, from the entry to the return.                      *)
(* ------------------------------------------------------------------------- *)

let rec_correct_goal = mk_imp(rec_loop_premises,
 `ensures x86
    (\s. read RIP s = word pcr /\ read RSP s = E /\ read RDI s = r /\
         read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
         read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
         read memory s = m0 /\ read (memory :> bytes64 E) s = ret)
    (\s. read RIP s = ret /\ read RSP s = word_add E (word 8) /\
         read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
         read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
         ?res. rec_run progs bw ctl budget E pl dd ht nh opa enda m0 used0 0 res /\
               read RAX s = FST res /\
               (!a. ~rec_stack E a ==> read memory s a = rec_final r res a) /\
               (!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a
                    ==> read memory s a = m0 a))
    (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                R12; R13; R14; R15; RBP] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`);;
let rec_correct_goal = list_mk_forall(frees rec_correct_goal, rec_correct_goal);;

let REC_CORRECT = prove
 (rec_correct_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL REC_LOOP) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rec_layout] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "rec_layout")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rec_desc] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "rec_desc")) (concl th))) THEN
  SUBGOAL_THEN `nonoverlapping (word pcr:int64,165) (word_sub E (word 48),48)` ASSUME_TAC THENL
   [MATCH_MP_TAC REC_CODE_STACK_APART_N THEN
    EXISTS_TAC `rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
     [SIMP_TAC[rec_fixed]; REC_FIXED_NOT_WINDOW_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`pcr:num`; `pcd:num`; `r:int64`; `ht:int64`; `nh:int64`; `ds:int64 list`;
                `pl:int64->(int64 list)list`; `m0:int64->byte`; `bind:int64`; `nbw:num`; `leaves:int64`;
                `nl:num`; `lpc:num->num`; `lmc:num->byte list`; `E:int64`] REC_R_WRITTEN_APART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `bytes_loaded s0 (word pcr) rec_mc /\
                read (memory :> bytes64 (word_add r (word 56))) s0 = used0 /\
                read (memory :> bytes64 r) s0 = word pcd` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC DRV_LOADED_CODE THEN EXISTS_TAC `m0:int64->byte` THEN
      ASM_REWRITE_TAC[COMPUTE_LENGTH_RULE rec_mc];
      ASM_REWRITE_TAC[DRV_READ64];
      ASM_REWRITE_TAC[DRV_READ64]];
    ALL_TAC] THEN
  TISA_STEPS_TAC REC_EXEC (1--10) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV(REWR_CONV REC_SUB_SUB THENC RAND_CONV(RAND_CONV NUM_ADD_CONV)))) THEN
  ABBREV_TAC `m10 = read memory s10` THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `read R15 s10`
     then FIRST_ASSUM(fun eq -> if is_eq(concl eq) && lhs(concl eq) = `m10:int64->byte`
                                then ASSUME_TAC(REWRITE_RULE[DRV_MREAD64; SYM eq] th) else failwith "")
     else failwith "") THEN
  SUBGOAL_THEN `!a. ~rec_stack E a ==> m10 a = (m0:int64->byte) a` ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN REWRITE_TAC[rec_stack] THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m10:int64->byte`)) THEN
    SUBGOAL_THEN `val(word_sub E (word 8):int64) = val E - 8 /\ val(word_sub E (word 16):int64) = val E - 16 /\
                  val(word_sub E (word 24):int64) = val E - 24 /\ val(word_sub E (word 32):int64) = val E - 32 /\
                  val(word_sub E (word 40):int64) = val E - 40 /\ val(word_sub E (word 48):int64) = val E - 48`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_SP_SUB THEN
      UNDISCH_TAC `360 <= val(E:int64)` THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
           ANTS_TAC THENL
            [ASM_REWRITE_TAC[] THEN VAL_FACTS_ARITH_TAC [`val(a:int64)`; `val(E:int64)`];
             DISCH_THEN SUBST1_TAC]) THEN
    REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `drv_word m10 r = word pcd` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `drv_word m0 r = word pcd` then SUBST1_TAC(SYM th) else failwith "") THEN
    MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (rec_mem_assum `m10:int64->byte` `rec_stack`)) THEN
    MP_TAC(SPECL [`pcr:num`; `pcd:num`; `r:int64`; `ht:int64`; `nh:int64`; `ds:int64 list`;
                  `pl:int64->(int64 list)list`; `m0:int64->byte`; `bind:int64`; `nbw:num`; `leaves:int64`;
                  `nl:num`; `lpc:num->num`; `lmc:num->byte list`; `0`] REC_R_FIXED) THEN
    REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `rec_window`)) (concl th) && can (find_term ((=) `rec_written`)) (concl th) &&
      can (find_term ((=) `rec_fixed`)) (concl th) && length(fst(strip_forall(concl th))) = 1
      then MP_TAC(CONJUNCT1(MP (SPEC `word_add r (word i):int64` th)
             (ASSUME `rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc (word_add r (word i))`)))
      else failwith "") THEN
    REWRITE_TAC[rec_window; rec_stack] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `read R15 s10 = drv_word m10 r`
     then ASSUME_TAC(REWRITE_RULE[ASSUME `drv_word m10 r = word pcd`] th) else failwith "") THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `m10:int64->byte`)) THEN
  SUBGOAL_THEN `!a. ~rec_stack E a ==> read memory s10 a = (m0:int64->byte) a` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`val(budget:int64) - val(used0:int64)`; `m0:int64->byte`; `used0:int64`; `0`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `word(pcr + 23):int64`)) (concl th))) THEN
  ANTS_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN TISA_BIGSTEP_TAC "s11" THEN
  SUBGOAL_THEN `!a. rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a ==> ~rec_stack E a`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `rec_window`)) (concl th) && can (find_term ((=) `rec_written`)) (concl th) &&
      can (find_term ((=) `rec_fixed`)) (concl th) && length(fst(strip_forall(concl th))) = 1
      then MP_TAC(CONJUNCT1(MP (SPEC `a:int64` th)
             (ASSUME `rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a`)))
      else failwith "") THEN
    REWRITE_TAC[rec_window; rec_stack] THEN ARITH_TAC;
    ALL_TAC] THEN
  REC_S_FIXED_TAC "s11" `FST(SND(SND(res:int64#num#(int64->byte)#int64)))` THEN
  REC_LOADED_TAC "s11" THEN
  SUBGOAL_THEN
   `drv_word (read memory s11) (word_sub E (word 8)) = rbxv /\
    drv_word (read memory s11) (word_sub E (word 16)) = rbpv /\
    drv_word (read memory s11) (word_sub E (word 24)) = r12v /\
    drv_word (read memory s11) (word_sub E (word 32)) = r13v /\
    drv_word (read memory s11) (word_sub E (word 40)) = r14v /\
    drv_word (read memory s11) (word_sub E (word 48)) = r15v /\
    drv_word (read memory s11) E = ret` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DRV_READ64] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `m11 = read memory s11` THEN
  MP_TAC(SPECL [`r:int64`; `ds:int64 list`; `E:int64`] REC_R_WRITTEN_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  TISA_STEPS_TAC REC_EXEC (12--20) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DRV_MREAD64;
    WORD_RULE `word_add (word_sub E (word 48)) (word 8):int64 = word_sub E (word 40)`;
    WORD_RULE `word_add (word_sub E (word 48)) (word 16):int64 = word_sub E (word 32)`;
    WORD_RULE `word_add (word_sub E (word 48)) (word 24):int64 = word_sub E (word 24)`;
    WORD_RULE `word_add (word_sub E (word 48)) (word 32):int64 = word_sub E (word 16)`;
    WORD_RULE `word_add (word_sub E (word 48)) (word 40):int64 = word_sub E (word 8)`;
    WORD_RULE `word_add (word_sub E (word 48)) (word 48):int64 = E`;
    WORD_RULE `word_add (word_sub E (word 48)) (word 56):int64 = word_add E (word 8)`]) THEN
  MP_TAC(SPECL [`r:int64`; `E:int64`; `word(FST(SND(res:int64#num#(int64->byte)#int64))):int64`;
                `SND(SND(SND(res:int64#num#(int64->byte)#int64)))`; `m11:int64->byte`] REC_EPI_SAVED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  X_GEN_TAC `a:int64` THEN DISCH_TAC THENL
   [REWRITE_TAC[rec_final] THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\a:int64. ~rec_stack E a`;
       `write (bytes64 (word_add r (word 56))) (SND(SND(SND(res:int64#num#(int64->byte)#int64)))) (m11:int64->byte)`;
       `write (bytes64 (word_add r (word 56))) (SND(SND(SND(res:int64#num#(int64->byte)#int64))))
              (FST(SND(SND(res:int64#num#(int64->byte)#int64))))`;
       `word_add r (word 64):int64`; `word(FST(SND(res:int64#num#(int64->byte)#int64))):int64`] DRV_WRITE_CONG)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(BETA_RULE(ISPECL
        [`\a:int64. ~rec_stack E a`; `m11:int64->byte`;
         `FST(SND(SND(res:int64#num#(int64->byte)#int64)))`; `word_add r (word 56):int64`;
         `SND(SND(SND(res:int64#num#(int64->byte)#int64)))`] DRV_WRITE_CONG)) THEN
      FIRST_ASSUM(ACCEPT_TAC o check (rec_mem_assum `m11:int64->byte` `rec_stack`));
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    SUBGOAL_THEN `~(val(r:int64) + 56 <= val(a:int64) /\ val a < val r + 72)` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term ((=) `rec_window`)) (concl th) && can (find_term ((=) `rec_written`)) (concl th) &&
        can (find_term ((=) `rec_fixed`)) (concl th) && length(fst(strip_forall(concl th))) = 1
        then MP_TAC(CONJUNCT2(MP (SPEC `a:int64` th)
               (ASSUME `rec_fixed pcr pcd r ht nh ds pl m0 bind nbw leaves nl lpc lmc a`)))
        else failwith "") THEN
      REWRITE_TAC[rec_written; DE_MORGAN_THM; drv_in] THEN
      MP_TAC(SPECL [`r:int64`; `56`] TISA_VAL_OFFSET) THEN ANTS_TAC THENL
       [UNDISCH_TAC `val(r:int64) + 72 <= 2 EXP 64` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word_add r (word 56):int64) = val(r:int64) + 56 /\
                  val(word_add r (word 64):int64) = val(r:int64) + 64` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN
      UNDISCH_TAC `val(r:int64) + 72 <= 2 EXP 64` THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
           ANTS_TAC THENL
            [ASM_REWRITE_TAC[] THEN VAL_FACTS_ARITH_TAC [`val(a:int64)`; `val(r:int64)`];
             DISCH_THEN SUBST1_TAC]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (rec_mem_assum `m11:int64->byte` `rec_fixed`)) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The receipt through the records: it never falls, and a run that starts    *)
(* within the allowance stays within it.                                      *)
(* ------------------------------------------------------------------------- *)

(* A plan that starts within the allowance ends within it. *)
let DRV_SEM_WITHIN = prove
 (`!progs bw ctl budget cfr sts i m used res.
     drv_sem progs bw ctl budget cfr sts i m used res /\
     (!st. MEM st sts ==> tisa_leaf_wf (progs (val(EL 0 st)))) /\ val used <= val budget
     ==> val(SND(SND(SND res))) <= val budget`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[drv_sem] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_sem; MEM] THEN
  COND_CASES_TAC THENL [STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `tc:tisa_state` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u:tisa_state` STRIP_ASSUME_TAC)))
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `val(tisa_fword u 21) <= val(budget:int64)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
      check (fun th -> can (find_term ((=) `drv_child`)) (concl th))) THEN
    DISCH_THEN(MP_TAC o SPEC `20`) THEN REWRITE_TAC[ARITH; drv_fw] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`progs (val(EL 0 (h:int64 list))):tisa_prog`; `tc:tisa_state`; `k:num`; `u:tisa_state`]
                  TISA_RUN_FUEL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`; `drv_after ctl h u`; `tisa_fword u 21`;
                                  `res:int64#num#(int64->byte)#int64`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `drv_sem`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let REC_PLAN_WITHIN = prove
 (`!progs bw ctl budget E pl d m used r.
     rec_plan progs bw ctl budget E pl d m used r /\
     (!st. MEM st (pl d) ==> tisa_leaf_wf (progs (val(EL 0 st)))) /\ val used <= val budget
     ==> val(SND(SND r)) <= val budget`,
  REWRITE_TAC[rec_plan] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DRV_SEM_WITHIN THEN ASM_MESON_TAC[]);;

let FUEL_PLAN_TAC d m u rr =
  SUBGOAL_THEN (subst [d, `d:int64`] `!st. MEM st ((pl:int64->(int64 list)list) d) ==> tisa_leaf_wf (progs (val(EL 0 st)))`)
  ASSUME_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `E:int64`;
                `pl:int64->(int64 list)list`; d; m; u; rr] REC_PLAN_FUEL) THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `budget:int64`; `E:int64`;
                `pl:int64->(int64 list)list`; d; m; u; rr] REC_PLAN_WITHIN) THEN
  ASM_REWRITE_TAC[];;

let FUEL_R1_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add used (word 1):int64) = val(used:int64) + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN MP_TAC(ISPEC `budget:int64` VAL_BOUND_64) THEN
    UNDISCH_TAC `~(val(budget:int64) <= val(used:int64))` THEN ARITH_TAC;
    ALL_TAC] THEN
  FUEL_PLAN_TAC `dd:int64` `m:int64->byte` `word_add used (word 1):int64` `r1:int64#(int64->byte)#int64`;;

let FUEL_R2_TAC =
  FUEL_PLAN_TAC `rec_handler ht opa (FST(SND(r1:int64#(int64->byte)#int64)))`
    `FST(SND(r1:int64#(int64->byte)#int64))` `SND(SND(r1:int64#(int64->byte)#int64))`
    `r2:int64#(int64->byte)#int64`;;

(* REC_RUN_FUEL: the receipt never falls, and stays within the allowance when *)
(* it starts within it. The plans' leaves are well formed.                    *)
let REC_RUN_FUEL = prove
 (`!progs bw ctl budget E pl dd ht nh opa enda.
     (!d st. MEM st (pl d) ==> tisa_leaf_wf (progs (val(EL 0 st))))
     ==> !m used c res.
           rec_run progs bw ctl budget E pl dd ht nh opa enda m used c res
           ==> val used <= val(SND(SND(SND res))) /\
               (val used <= val budget ==> val(SND(SND(SND res))) <= val budget)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC rec_run_INDUCT THEN
  REWRITE_TAC[FST; SND; LE_REFL] THEN REPEAT CONJ_TAC THENL
   [FUEL_R1_TAC; FUEL_R1_TAC; FUEL_R1_TAC THEN FUEL_R2_TAC; FUEL_R1_TAC THEN FUEL_R2_TAC;
    FUEL_R1_TAC THEN FUEL_R2_TAC] THEN
  ASM_ARITH_TAC);;
