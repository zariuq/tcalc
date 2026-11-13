(* ========================================================================= *)
(* The plan driver, tcalc/native/driver/driver.S, proved against             *)
(* s2n-bignum's x86 model once, for every set of leaves: the leaves' image   *)
(* theorems are premises (tisa_leaf_spec, driver_leaf.ml), never axioms.     *)
(*                                                                           *)
(* A run of the driver calls the plan's leaves in order. Step i calls its    *)
(* leaf on a state whose registers and frame words are what the step         *)
(* describes (drv_child) and whose memory is the plan's memory outside the   *)
(* driver's stack; the leaf's effect is its tisa_run; the payload goes to    *)
(* the step's control word; the first outcome other than FIRED ends the     *)
(* plan with that outcome. The receipt passes from each step to the next.   *)
(* drv_sem states this as a relation over the steps.                         *)
(* ========================================================================= *)

needs "native/driver/driver_leaf.ml";;

let drv_mc = define_assert_from_elf "drv_mc"
  (tcalc_path "native/driver/build/driver.o")
[
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0xc8; 0x00; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 200)) *)
  0x49; 0x89; 0xfe;        (* MOV (% r14) (% rdi) *)
  0x49; 0x8b; 0x2e;        (* MOV (% rbp) (Memop Quadword (%% (r14,0))) *)
  0x49; 0x8b; 0x46; 0x30;  (* MOV (% rax) (Memop Quadword (%% (r14,48))) *)
  0x48; 0x89; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% rax) *)
  0x49; 0x3b; 0x6e; 0x08;  (* CMP (% rbp) (Memop Quadword (%% (r14,8))) *)
  0x0f; 0x84; 0xac; 0x01; 0x00; 0x00;
                           (* JE (Imm32 (word 428)) *)
  0x48; 0x8b; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x3b; 0x46; 0x28;  (* CMP (% rax) (Memop Quadword (%% (r14,40))) *)
  0x0f; 0x87; 0xa1; 0x01; 0x00; 0x00;
                           (* JA (Imm32 (word 417)) *)
  0x4d; 0x8b; 0x56; 0x18;  (* MOV (% r10) (Memop Quadword (%% (r14,24))) *)
  0x48; 0x8b; 0x45; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rbp,8))) *)
  0x4d; 0x8b; 0x1c; 0xc2;  (* MOV (% r11) (Memop Quadword (%%% (r10,3,rax))) *)
  0x4c; 0x89; 0x1c; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r11) *)
  0x4d; 0x8b; 0x5c; 0xc2; 0x08;
                           (* MOV (% r11) (Memop Quadword (%%%% (r10,3,rax,&8))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r11) *)
  0x48; 0x8b; 0x45; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rbp,16))) *)
  0x4d; 0x8b; 0x1c; 0xc2;  (* MOV (% r11) (Memop Quadword (%%% (r10,3,rax))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% r11) *)
  0x4d; 0x8b; 0x5c; 0xc2; 0x08;
                           (* MOV (% r11) (Memop Quadword (%%%% (r10,3,rax,&8))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r11) *)
  0x48; 0x8b; 0x45; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rbp,24))) *)
  0x4d; 0x8b; 0x1c; 0xc2;  (* MOV (% r11) (Memop Quadword (%%% (r10,3,rax))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r11) *)
  0x4d; 0x8b; 0x5c; 0xc2; 0x08;
                           (* MOV (% r11) (Memop Quadword (%%%% (r10,3,rax,&8))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r11) *)
  0x48; 0x8b; 0x45; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rbp,32))) *)
  0x4d; 0x8b; 0x1c; 0xc2;  (* MOV (% r11) (Memop Quadword (%%% (r10,3,rax))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r11) *)
  0x4d; 0x8b; 0x5c; 0xc2; 0x08;
                           (* MOV (% r11) (Memop Quadword (%%%% (r10,3,rax,&8))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r11) *)
  0x48; 0x8b; 0x45; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rbp,40))) *)
  0x4d; 0x8b; 0x1c; 0xc2;  (* MOV (% r11) (Memop Quadword (%%% (r10,3,rax))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r11) *)
  0x4d; 0x8b; 0x5c; 0xc2; 0x08;
                           (* MOV (% r11) (Memop Quadword (%%%% (r10,3,rax,&8))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r11) *)
  0x48; 0x8b; 0x45; 0x30;  (* MOV (% rax) (Memop Quadword (%% (rbp,48))) *)
  0x4d; 0x8b; 0x1c; 0xc2;  (* MOV (% r11) (Memop Quadword (%%% (r10,3,rax))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r11) *)
  0x4d; 0x8b; 0x5c; 0xc2; 0x08;
                           (* MOV (% r11) (Memop Quadword (%%%% (r10,3,rax,&8))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r11) *)
  0x48; 0x8b; 0x45; 0x38;  (* MOV (% rax) (Memop Quadword (%% (rbp,56))) *)
  0x4d; 0x8b; 0x1c; 0xc2;  (* MOV (% r11) (Memop Quadword (%%% (r10,3,rax))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r11) *)
  0x4d; 0x8b; 0x5c; 0xc2; 0x08;
                           (* MOV (% r11) (Memop Quadword (%%%% (r10,3,rax,&8))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r11) *)
  0x48; 0x8b; 0x45; 0x40;  (* MOV (% rax) (Memop Quadword (%% (rbp,64))) *)
  0x4d; 0x8b; 0x1c; 0xc2;  (* MOV (% r11) (Memop Quadword (%%% (r10,3,rax))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r11) *)
  0x4d; 0x8b; 0x5c; 0xc2; 0x08;
                           (* MOV (% r11) (Memop Quadword (%%%% (r10,3,rax,&8))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% r11) *)
  0x48; 0x8b; 0x45; 0x48;  (* MOV (% rax) (Memop Quadword (%% (rbp,72))) *)
  0x4d; 0x8b; 0x1c; 0xc2;  (* MOV (% r11) (Memop Quadword (%%% (r10,3,rax))) *)
  0x4c; 0x89; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r11) *)
  0x4d; 0x8b; 0x5c; 0xc2; 0x08;
                           (* MOV (% r11) (Memop Quadword (%%%% (r10,3,rax,&8))) *)
  0x4c; 0x89; 0x9c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r11) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x89; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% rax) *)
  0x49; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (r14,40))) *)
  0x48; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% rax) *)
  0x4d; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (r14,16))) *)
  0x48; 0x8b; 0x45; 0x50;  (* MOV (% rax) (Memop Quadword (%% (rbp,80))) *)
  0x4d; 0x8b; 0x1c; 0xc2;  (* MOV (% r11) (Memop Quadword (%%% (r10,3,rax))) *)
  0x4c; 0x89; 0x9c; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r11) *)
  0x48; 0x8b; 0x45; 0x58;  (* MOV (% rax) (Memop Quadword (%% (rbp,88))) *)
  0x4d; 0x8b; 0x1c; 0xc2;  (* MOV (% r11) (Memop Quadword (%%% (r10,3,rax))) *)
  0x4c; 0x89; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% r11) *)
  0x48; 0x8b; 0x45; 0x60;  (* MOV (% rax) (Memop Quadword (%% (rbp,96))) *)
  0x49; 0x8b; 0x34; 0xc2;  (* MOV (% rsi) (Memop Quadword (%%% (r10,3,rax))) *)
  0x48; 0x8b; 0x45; 0x68;  (* MOV (% rax) (Memop Quadword (%% (rbp,104))) *)
  0x49; 0x8b; 0x14; 0xc2;  (* MOV (% rdx) (Memop Quadword (%%% (r10,3,rax))) *)
  0x48; 0x8b; 0x45; 0x70;  (* MOV (% rax) (Memop Quadword (%% (rbp,112))) *)
  0x49; 0x8b; 0x0c; 0xc2;  (* MOV (% rcx) (Memop Quadword (%%% (r10,3,rax))) *)
  0x48; 0x8b; 0x45; 0x78;  (* MOV (% rax) (Memop Quadword (%% (rbp,120))) *)
  0x4d; 0x8b; 0x04; 0xc2;  (* MOV (% r8) (Memop Quadword (%%% (r10,3,rax))) *)
  0x48; 0x8b; 0x85; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rbp,128))) *)
  0x4d; 0x8b; 0x0c; 0xc2;  (* MOV (% r9) (Memop Quadword (%%% (r10,3,rax))) *)
  0x48; 0x8b; 0x45; 0x00;  (* MOV (% rax) (Memop Quadword (%% (rbp,0))) *)
  0x4d; 0x8b; 0x5e; 0x20;  (* MOV (% r11) (Memop Quadword (%% (r14,32))) *)
  0x4d; 0x8b; 0x3c; 0xc3;  (* MOV (% r15) (Memop Quadword (%%% (r11,3,rax))) *)
  0x48; 0x89; 0xe7;        (* MOV (% rdi) (% rsp) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x45; 0x31; 0xe4;        (* XOR (% r12d) (% r12d) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0xe8; 0x5f; 0x00; 0x00; 0x00;
                           (* CALL (Imm32 (word 95)) *)
  0x49; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (r14,16))) *)
  0x48; 0x8b; 0x95; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rbp,136))) *)
  0x48; 0x8b; 0x8c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x89; 0x0c; 0xd0;  (* MOV (Memop Quadword (%%% (rax,3,rdx))) (% rcx) *)
  0x48; 0x8b; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0x83; 0xf8; 0x01;  (* CMP (% rax) (Imm8 (word 1)) *)
  0x75; 0x18;              (* JNE (Imm8 (word 24)) *)
  0x48; 0x81; 0xc5; 0x90; 0x00; 0x00; 0x00;
                           (* ADD (% rbp) (Imm32 (word 144)) *)
  0xe9; 0x4a; 0xfe; 0xff; 0xff;
                           (* JMP (Imm32 (word 4294966858)) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0xeb; 0x05;              (* JMP (Imm8 (word 5)) *)
  0xb8; 0x03; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 3)) *)
  0x48; 0x8b; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,168))) *)
  0x49; 0x89; 0x56; 0x30;  (* MOV (Memop Quadword (%% (r14,48))) (% rdx) *)
  0x49; 0x89; 0x6e; 0x38;  (* MOV (Memop Quadword (%% (r14,56))) (% rbp) *)
  0x48; 0x81; 0xc4; 0xc8; 0x00; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 200)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3;                    (* RET *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0xc3                     (* RET *)
];;

let DRV_EXEC = X86_MK_EXEC_RULE drv_mc;;

(* Offsets in drv_mc: the loop head, the step's return point, the exits. *)
let drv_loop = 35 and drv_back = 424 and drv_fired = 473 and drv_invalid = 480
and drv_done = 485 and drv_enter = 519;;

(* ------------------------------------------------------------------------- *)
(* Memory words, areas, the driver's stack.                                  *)
(* ------------------------------------------------------------------------- *)

let drv_word = new_definition
 `drv_word (m:int64->byte) (a:int64) = word(read (bytes(a,8)) m):int64`;;

(* a lies in [b, b + n). *)
let drv_in = new_definition
 `drv_in (a:int64) (b:int64) n <=> val b <= val a /\ val a < val b + n`;;

(* [a, a + m) and [b, b + n) are disjoint. *)
let drv_apart = new_definition
 `drv_apart (a:int64) m (b:int64) n <=>
    m = 0 \/ n = 0 \/ val a + m <= val b \/ val b + n <= val a`;;

(* The stack the driver writes, around the child frame at cfr: the leaf's
   saved registers and return address below it, the driver's saved
   registers above it, up to the caller's return address at cfr + 248. *)
let drv_stack = new_definition
 `drv_stack (cfr:int64) (a:int64) <=> val cfr <= val a + 48 /\ val a < val cfr + 248`;;

(* ------------------------------------------------------------------------- *)
(* A step: words 0 leaf, 1..9 binding word indices, 10 and 11 the control    *)
(* words of arg0 and arg1, 12..16 those of v1..v5, 17 the payload's.         *)
(* ------------------------------------------------------------------------- *)

let drv_base = new_definition
 `drv_base (bw:num->int64) (st:int64 list) r = bw (val(EL (1 + r) st))`;;

let drv_len = new_definition
 `drv_len (bw:num->int64) (st:int64 list) r = bw (val(EL (1 + r) st) + 1)`;;

(* Control word k. *)
let drv_cw = new_definition
 `drv_cw (ctl:int64) m (k:int64) = drv_word m (word_add ctl (word(8 * val k)))`;;

(* The child frame's words. *)
let drv_fw = new_definition
 `drv_fw (bw:num->int64) (ctl:int64) (budget:int64) (used:int64) (st:int64 list) m j =
    if j < 18 then bw (val(EL (1 + j DIV 2) st) + j MOD 2)
    else if j < 20 then word 0
    else if j = 20 then budget
    else if j = 21 then used
    else drv_cw ctl m (EL (j - 12) st)`;;

(* The child's registers: v0 the frame, v1..v5 control words, the rest 0. *)
let drv_regs = new_definition
 `drv_regs (cfr:int64) (ctl:int64) (st:int64 list) m j =
    if j = 0 then cfr
    else if j <= 5 then drv_cw ctl m (EL (11 + j) st)
    else word 0`;;

(* The state a step calls its leaf on, for the plan's memory m. *)
let drv_child = new_definition
 `drv_child bw ctl budget cfr st m used t <=>
    tregs t = drv_regs cfr ctl st m /\
    (!j. j < 24 ==> tisa_fword t j = drv_fw bw ctl budget used st m j) /\
    (!a. ~drv_stack cfr a ==> tmem t a = m a)`;;

(* The plan's memory after a step: the leaf's, with the payload stored. *)
let drv_after = new_definition
 `drv_after (ctl:int64) (st:int64 list) u =
    write (bytes64 (word_add ctl (word(8 * val(EL 17 st))))) (tisa_fword u 19) (tmem u)`;;

(* The steps from index i, from memory m and receipt used, end with res =
   (outcome, index of the step that ended the plan, memory, receipt). Each
   step runs its leaf on a state its entry validation accepts. *)
let drv_sem = define
 `(drv_sem (progs:num->tisa_prog) bw ctl budget cfr [] i m used
           (res:int64#num#(int64->byte)#int64) <=>
     res = (word 1, i, m, used)) /\
  (drv_sem progs bw ctl budget cfr (CONS st sts) i m used res <=>
     if val budget < val used then res = (word 3, i, m, used)
     else ?t k u. drv_child bw ctl budget cfr st m used t /\
                  tisa_entry_ok (progs (val(EL 0 st))) t /\
                  tisa_run (progs (val(EL 0 st))) t = TStop k u /\
                  (if tisa_fword u 18 = word 1
                   then drv_sem progs bw ctl budget cfr sts (i + 1) (drv_after ctl st u)
                                (tisa_fword u 21) res
                   else res = (tisa_fword u 18, i, drv_after ctl st u, tisa_fword u 21)))`;;

(* The memory the caller sees: the plan's, with the receipt and the step
   that ended the plan written back to the descriptor. *)
let drv_final = new_definition
 `drv_final (d:int64) (plan:int64) (res:int64#num#(int64->byte)#int64) =
    write (bytes64 (word_add d (word 56))) (word_add plan (word(144 * FST(SND res))))
      (write (bytes64 (word_add d (word 48))) (SND(SND(SND res))) (FST(SND(SND res))))`;;

(* ------------------------------------------------------------------------- *)
(* Static conditions: layout, steps, the tables in memory.                   *)
(* ------------------------------------------------------------------------- *)

(* What neither the driver nor any leaf writes during the loop: the code,
   the descriptor, the plan, the binding words, the leaf table, and the
   caller's return address. *)
let drv_static = new_definition
 `drv_static pc cfr d plan ns bind nbw leaves nl (lpc:num->num) (lmc:num->byte list) a <=>
    drv_in a (word pc) 522 \/ (?j. j < nl /\ drv_in a (word(lpc j)) (LENGTH(lmc j))) \/
    drv_in a d 64 \/ drv_in a plan (144 * ns) \/ drv_in a bind (8 * nbw) \/
    drv_in a leaves (8 * nl) \/ drv_in a (word_add cfr (word 248)) 8`;;

let drv_layout = new_definition
 `drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl (lpc:num->num) (lmc:num->byte list) <=>
    48 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\
    pc + 522 <= 2 EXP 64 /\ val d + 64 <= 2 EXP 64 /\ val plan + 144 * ns < 2 EXP 64 /\
    val ctl + 8 * nctl <= 2 EXP 64 /\ val bind + 8 * nbw <= 2 EXP 64 /\
    val leaves + 8 * nl <= 2 EXP 64 /\
    (!j. j < nl ==> lpc j + LENGTH(lmc j) <= 2 EXP 64) /\
    drv_apart (word_sub cfr (word 48)) 304 (word pc) 522 /\
    (!j. j < nl ==> drv_apart (word_sub cfr (word 48)) 304 (word(lpc j)) (LENGTH(lmc j))) /\
    drv_apart (word_sub cfr (word 48)) 304 d 64 /\
    drv_apart (word_sub cfr (word 48)) 304 plan (144 * ns) /\
    drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl) /\
    drv_apart (word_sub cfr (word 48)) 304 bind (8 * nbw) /\
    drv_apart (word_sub cfr (word 48)) 304 leaves (8 * nl) /\
    drv_apart ctl (8 * nctl) (word pc) 522 /\
    (!j. j < nl ==> drv_apart ctl (8 * nctl) (word(lpc j)) (LENGTH(lmc j))) /\
    drv_apart ctl (8 * nctl) d 64 /\ drv_apart ctl (8 * nctl) plan (144 * ns) /\
    drv_apart ctl (8 * nctl) bind (8 * nbw) /\ drv_apart ctl (8 * nctl) leaves (8 * nl) /\
    drv_apart d 64 (word pc) 522 /\
    (!j. j < nl ==> drv_apart d 64 (word(lpc j)) (LENGTH(lmc j)))`;;

(* A step: its leaf exists, its indices are in range, its regions pass the
   leaf's entry validation for a frame at cfr, every accessible region lies
   apart from the driver's stack, and every writable one apart from what
   must not change. *)
let drv_step_ok = new_definition
 `drv_step_ok (progs:num->tisa_prog) pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw
              (st:int64 list) <=>
    LENGTH st = 18 /\ val(EL 0 st) < nl /\
    (!r. r < 9 ==> val(EL (1 + r) st) + 1 < nbw) /\
    (!f. 10 <= f /\ f < 18 ==> val(EL f st) < nctl) /\
    (!t. tregs t 0 = cfr /\
         (!r. r < 9 ==> tisa_base t r = drv_base bw st r /\ tisa_len t r = drv_len bw st r)
         ==> tisa_decls_ok t 0 (tisa_decls (progs (val(EL 0 st))))) /\
    (!r. tisa_readable (tisa_decls (progs (val(EL 0 st)))) r
         ==> drv_apart (drv_base bw st r) (val(drv_len bw st r)) (word_sub cfr (word 48)) 304) /\
    (!r a. tisa_rw (tisa_decls (progs (val(EL 0 st)))) r /\
           drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a
           ==> ~drv_in a (drv_base bw st r) (val(drv_len bw st r)))`;;

(* The descriptor, the plan, the binding words and the leaf table. *)
let drv_holds = new_definition
 `drv_holds (m:int64->byte) d plan ns ctl bind leaves budget used0
            (stepl:(int64 list)list) (bw:num->int64) nbw (lpc:num->num) nl <=>
    LENGTH stepl = ns /\
    drv_word m d = plan /\ drv_word m (word_add d (word 8)) = word_add plan (word(144 * ns)) /\
    drv_word m (word_add d (word 16)) = ctl /\ drv_word m (word_add d (word 24)) = bind /\
    drv_word m (word_add d (word 32)) = leaves /\ drv_word m (word_add d (word 40)) = budget /\
    drv_word m (word_add d (word 48)) = used0 /\
    (!i f. i < ns /\ f < 18
           ==> drv_word m (word_add plan (word(144 * i + 8 * f))) = EL f (EL i stepl)) /\
    (!k. k < nbw ==> drv_word m (word_add bind (word(8 * k))) = bw k) /\
    (!j. j < nl ==> drv_word m (word_add leaves (word(8 * j))) = word(lpc j))`;;

(* ------------------------------------------------------------------------- *)
(* Reading words, and where bytes lie.                                       *)
(* ------------------------------------------------------------------------- *)

let DRV_READ64 = prove
 (`!s a. read (memory :> bytes64 a) s = drv_word (read memory s) a`,
  REWRITE_TAC[drv_word; READ_COMPONENT_COMPOSE; bytes64; asword; through; read]);;

let DRV_MREAD64 = prove
 (`!m a. tisa_mread (bytes64 a) m = drv_word m a`,
  REWRITE_TAC[drv_word; TISA_MREAD_BYTES64]);;

let DRV_FWORD = prove
 (`!t j. tisa_fword t j = drv_word (tmem t) (word_add (tregs t 0) (word(8 * j)))`,
  REWRITE_TAC[tisa_fword; tisa_read; tisa_frame; drv_word]);;

let DRV_WORD_AGREE = prove
 (`!m1 m2 (a:int64). (!i. i < 8 ==> m1 (word_add a (word i)) = m2 (word_add a (word i)))
                     ==> drv_word m1 a = drv_word m2 a`,
  REWRITE_TAC[drv_word] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[READ_BYTES_EQ]);;

let DRV_WORD_WRITE_SAME = prove
 (`!(a:int64) (v:int64) m. drv_word (write (bytes64 a) v m) a = v`,
  REWRITE_TAC[drv_word; TISA_WRITE_BYTES64] THEN
  SIMP_TAC[READ_WRITE_BYTES; DIMINDEX_64; ARITH_RULE `8 <= 2 EXP 64`;
           ARITH_RULE `8 * 8 = 64`; MOD_LT; VAL_BOUND_64; WORD_VAL]);;

(* A write of 8 bytes at a leaves byte b when b lies outside them. *)
let DRV_WRITE64_OUTSIDE = prove
 (`!(a:int64) (v:int64) m b.
     val a + 8 <= 2 EXP 64 /\ ~(val a <= val b /\ val b < val a + 8)
     ==> write (bytes64 a) v m b = m b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TISA_WRITE_BYTES64] THEN
  MATCH_MP_TAC TISA_WRITE_BYTES_OUTSIDE THEN ASM_REWRITE_TAC[]);;

let DRV_BYTES_IN = prove
 (`!(x:int64) b n k. val b + n <= 2 EXP 64 /\ val x = val b + k /\ k + 8 <= n
                     ==> !i. i < 8 ==> drv_in (word_add x (word i)) b n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[drv_in] THEN
  SUBGOAL_THEN `val(word_add x (word i):int64) = val x + i` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let DRV_IN_NOT_STACK = prove
 (`!cfr a b n. 48 <= val cfr /\ drv_apart (word_sub cfr (word 48)) 304 b n /\ drv_in a b n
               ==> ~drv_stack cfr a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cfr:int64`; `48`] TISA_VAL_SP_SUB) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_apart; drv_in]) THEN
  REWRITE_TAC[drv_stack] THEN ASM_ARITH_TAC);;

let DRV_OUT_NONOVERLAP = prove
 (`!cfr (x:int64). 48 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\
                   (!i. i < 8 ==> ~drv_stack cfr (word_add x (word i)))
                   ==> nonoverlapping (x,8) (cfr,192)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NONOVERLAPPING; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[drv_stack] THEN
  SUBGOAL_THEN `val(word_add cfr (word j):int64) = val cfr + j` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

(* The same for the stack words up to the caller's return address. *)
let DRV_OUT_NONOVERLAP248 = prove
 (`!cfr (x:int64). 48 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\
                   (!i. i < 8 ==> ~drv_stack cfr (word_add x (word i)))
                   ==> nonoverlapping (x,8) (cfr,248)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NONOVERLAPPING; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[drv_stack] THEN
  SUBGOAL_THEN `val(word_add cfr (word j):int64) = val cfr + j` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let DRV_READ_BYTELIST = prove
 (`!(a:int64) n m. read (bytelist(a,n)) m = bytelist_of_num n (read (bytes(a,n)) m)`,
  REWRITE_TAC[bytelist; READ_COMPONENT_COMPOSE; through; read]);;

(* Code is loaded in a state whose memory agrees with m0 on it. *)
let DRV_LOADED = prove
 (`!s m0 (p:num) mc.
     p + LENGTH mc <= 2 EXP 64 /\ read (bytelist(word p,LENGTH mc)) m0 = mc /\
     (!a. drv_in a (word p) (LENGTH mc) ==> read memory s a = m0 a)
     ==> bytes_loaded s (word p) mc`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bytes_loaded; READ_COMPONENT_COMPOSE] THEN
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
   [ASM_MESON_TAC[TISA_VAL_OFFSET; ARITH_RULE
      `i < l /\ p + l <= 2 EXP 64 ==> p + i < 2 EXP 64`];
    ASM_ARITH_TAC]);;

(* The code mc at p in memory m. (A constant: s2n-bignum's state cleanup
   discards facts that mention read c X, taking X for a state.) *)
let drv_code = new_definition
 `drv_code (m:int64->byte) p (mc:byte list) <=> read (bytelist(word p,LENGTH mc)) m = mc`;;

let DRV_LOADED_CODE = prove
 (`!s m0 (p:num) mc.
     p + LENGTH mc <= 2 EXP 64 /\ drv_code m0 p mc /\
     (!a. drv_in a (word p) (LENGTH mc) ==> read memory s a = m0 a)
     ==> bytes_loaded s (word p) mc`,
  REWRITE_TAC[drv_code; DRV_LOADED]);;

(* The 8 bytes at offset k of an area apart from the stack. *)
let DRV_AREA_BYTES = prove
 (`!cfr (b:int64) n x k (P:int64->bool).
     48 <= val cfr /\ val b + n <= 2 EXP 64 /\ drv_apart (word_sub cfr (word 48)) 304 b n /\
     (!a. drv_in a b n ==> P a) /\ val x = val b + k /\ k + 8 <= n
     ==> !i. i < 8 ==> P (word_add x (word i)) /\ ~drv_stack cfr (word_add x (word i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:int64`; `b:int64`; `n:num`; `k:num`] DRV_BYTES_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[] THEN MATCH_MP_TAC DRV_IN_NOT_STACK THEN
  MAP_EVERY EXISTS_TAC [`b:int64`; `n:num`] THEN ASM_REWRITE_TAC[]);;

(* Reading a word of the plan's memory outside the stack. *)
let DRV_READ_OUT = prove
 (`!s M cfr (x:int64).
     (!a. ~drv_stack cfr a ==> read memory s a = M a) /\
     (!i. i < 8 ==> ~drv_stack cfr (word_add x (word i)))
     ==> read (memory :> bytes64 x) s = drv_word M x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DRV_READ64] THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  ASM_SIMP_TAC[]);;

(* Reading a word that neither the loop nor a leaf changes. *)
let DRV_READ_STATIC = prove
 (`!s M m0 cfr (P:int64->bool) (x:int64).
     (!a. ~drv_stack cfr a ==> read memory s a = M a) /\ (!a. P a ==> M a = m0 a) /\
     (!i. i < 8 ==> P (word_add x (word i)) /\ ~drv_stack cfr (word_add x (word i)))
     ==> read (memory :> bytes64 x) s = drv_word m0 x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DRV_READ64] THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  ASM_SIMP_TAC[]);;

(* The step pointer meets the plan's end only after the last step. *)
let DRV_NOT_END = prove
 (`!(plan:int64) ns i. val plan + 144 * ns < 2 EXP 64 /\ i < ns
       ==> ~(val(word_sub (word_add plan (word(144 * i))) (word_add plan (word(144 * ns)))) = 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `val(word_add plan (word(144 * i)):int64) = val plan + 144 * i /\
                val(word_add plan (word(144 * ns)):int64) = val plan + 144 * ns`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the loop: facts at a state from the plan's memory.            *)
(* ------------------------------------------------------------------------- *)

(* Linear arithmetic over the assumptions that are relations between
   numbers and share variables with the goal (two rounds), never over the
   whole context. *)
let DRV_ARITH_TAC (asl,w) =
  let is_num_rel t = match t with
    | Comb(Comb(Const(("<"|"<="|"="),_),l),_) -> type_of l = `:num`
    | _ -> false in
  let rels = filter (fun th -> is_num_rel(concl th)) (map snd asl) in
  let grow vs = filter (fun th -> exists (fun v -> mem v vs) (frees(concl th))) rels in
  let f1 = grow (frees w) in
  let f2 = grow (itlist (union o frees o concl) f1 (frees w)) in
  (MAP_EVERY MP_TAC f2 THEN ARITH_TAC) (asl,w);;

(* Side goals of the area lemmas, from the stripped layout facts. *)
let DRV_SIDE_TAC =
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  FIRST [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[drv_static] THEN ASM_REWRITE_TAC[];
         MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC;
         DRV_ARITH_TAC];;

(* read (memory :> bytes64 x) s = drv_word m0 x, for x at offset k of the
   static area (b, len). *)
let DRV_STATIC_READ_TAC sname x b len k =
  let s = mk_var(sname, `:x86state`) in
  let goal = subst [s, `s:x86state`; x, `x:int64`]
               `read (memory :> bytes64 x) s = drv_word m0 x` in
  SUBGOAL_THEN goal ASSUME_TAC THENL
   [MATCH_MP_TAC DRV_READ_STATIC THEN
    MAP_EVERY EXISTS_TAC [`M:int64->byte`; `cfr:int64`;
                          `drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DRV_AREA_BYTES THEN MAP_EVERY EXISTS_TAC [b; len; k] THEN
    ASM_REWRITE_TAC[] THEN DRV_SIDE_TAC;
    ALL_TAC];;

(* bytes_loaded s (word p) mc, for code at p lying in the static area. *)
let DRV_LOADED_TAC sname p mc len =
  let s = mk_var(sname, `:x86state`) in
  SUBGOAL_THEN (list_mk_comb(`bytes_loaded`, [s; mk_comb(`word:num->int64`, p); mc])) ASSUME_TAC THENL
   [MATCH_MP_TAC DRV_LOADED_CODE THEN EXISTS_TAC `m0:int64->byte` THEN
    REWRITE_TAC[COMPUTE_LENGTH_RULE drv_mc] THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    SUBGOAL_THEN (subst [s, `s:x86state`] `read memory s a = M a`) SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `drv_stack`)) (concl th) &&
                                                     is_forall(concl th))) THEN
      MATCH_MP_TAC DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [mk_comb(`word:num->int64`, p); len] THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `drv_static`)) (concl th) &&
                                                     is_forall(concl th))) THEN
      REWRITE_TAC[drv_static] THEN ASM_REWRITE_TAC[]];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* What a leaf call keeps.                                                   *)
(* ------------------------------------------------------------------------- *)

(* The 8 bytes at y lie in the stack area. *)
let drv_stk8 = new_definition
 `drv_stk8 (cfr:int64) (y:int64) <=> val cfr <= val y + 48 /\ val y + 8 <= val cfr + 248`;;

let DRV_WRITE_STACK = prove
 (`!cfr (y:int64) (v:int64) m a.
     val cfr + 256 <= 2 EXP 64 /\ drv_stk8 cfr y /\ ~drv_stack cfr a
     ==> write (bytes64 y) v m a = m a`,
  REWRITE_TAC[drv_stk8; drv_stack] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DRV_WRITE64_OUTSIDE THEN ASM_ARITH_TAC);;

let DRV_STK8_ADD = prove
 (`!cfr k. val cfr + 256 <= 2 EXP 64 /\ k + 8 <= 248
           ==> drv_stk8 cfr (word_add cfr (word k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[drv_stk8] THEN
  SUBGOAL_THEN `val(word_add cfr (word k):int64) = val cfr + k` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let DRV_STK8_SUB = prove
 (`!cfr k. 48 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\ 8 <= k /\ k <= 48
           ==> drv_stk8 cfr (word_sub cfr (word k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[drv_stk8] THEN
  SUBGOAL_THEN `val(word_sub cfr (word k):int64) = val cfr - k` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_SP_SUB THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

(* A word the leaf does not write reads the same after the call. *)
let DRV_KEPT_WORD = prove
 (`!decls t u (x:int64).
     tisa_keeps decls t u /\ (!i. i < 8 ==> ~tisa_writable decls t (word_add x (word i)))
     ==> drv_word (tmem u) x = drv_word (tmem t) x`,
  REWRITE_TAC[tisa_keeps] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DRV_WORD_AGREE THEN ASM_SIMP_TAC[]);;

(* After the call, a word outside the leaf's saved registers is the run's. *)
let DRV_RET_WORD = prove
 (`!s sp u (x:int64).
     (!a. ~tisa_saved sp a ==> read memory s a = tmem u a) /\
     (!i. i < 8 ==> ~tisa_saved sp (word_add x (word i)))
     ==> read (memory :> bytes64 x) s = drv_word (tmem u) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DRV_READ64] THEN MATCH_MP_TAC DRV_WORD_AGREE THEN
  ASM_SIMP_TAC[]);;

(* Bytes the leaf may not write: outside its read-write regions and its
   frame words 18..21. *)
let DRV_NOT_WRITABLE = prove
 (`!decls t cfr bw h (a:int64).
     tregs t 0 = cfr /\ LENGTH decls <= 9 /\
     (!r. r < 9 ==> tisa_base t r = drv_base bw h r /\ tisa_len t r = drv_len bw h r) /\
     (!r. tisa_rw decls r ==> ~drv_in a (drv_base bw h r) (val(drv_len bw h r))) /\
     ~(val cfr + 144 <= val a /\ val a < val cfr + 176)
     ==> ~tisa_writable decls t a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tisa_writable] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `r:num` THEN
  ASM_CASES_TAC `tisa_rw decls r` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `r < 9` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[tisa_rw]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> can (find_term ((=) `tisa_rw`)) (concl th) &&
                                                         is_forall(concl th))) THEN
  ASM_SIMP_TAC[drv_in]);;

(* A point of the stack area lies in no region apart from it. *)
let DRV_STACK_NOT_IN = prove
 (`!cfr b l (a:int64).
     48 <= val cfr /\ drv_apart b l (word_sub cfr (word 48)) 304 /\
     val cfr <= val a + 48 /\ val a < val cfr + 256
     ==> ~drv_in a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cfr:int64`; `48`] TISA_VAL_SP_SUB) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[drv_apart]) THEN
  REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC);;

(* The driver's receipt check, as the flags decide it. *)
let DRV_FUEL_COND = prove
 (`!(used:int64) (budget:int64).
     ~(val used < val budget \/ val(word_sub used budget) = 0) <=> val budget < val used`,
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ] THEN ARITH_TAC);;

let DRV_ADDR_ASSOC = prove
 (`!(p:int64) a b. word_add (word_add p (word a)) (word b) = word_add p (word(a + b))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

(* A part of an area apart from another does not overlap it. *)
let DRV_SUB_NONOVERLAP = prove
 (`!(a:int64) m (b:int64) n (x:int64) k l.
     val a + m <= 2 EXP 64 /\ val b + n <= 2 EXP 64 /\ drv_apart a m b n /\
     val x = val a + k /\ k + l <= m
     ==> nonoverlapping (x,l) (b,n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[nonoverlapping; DIMINDEX_64] THEN
  ASM_CASES_TAC `l = 0 \/ n = 0` THENL
   [MATCH_MP_TAC NONOVERLAPPING_MODULO_TRIVIAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  RULE_ASSUM_TAC(REWRITE_RULE[drv_apart; DE_MORGAN_THM]) THEN ASM_ARITH_TAC);;

(* Code apart from the stack area does not overlap a part of it. *)
let DRV_CODE_NONOVERLAP = prove
 (`!cfr p len (x:int64) k l.
     48 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\ p + len <= 2 EXP 64 /\
     drv_apart (word_sub cfr (word 48)) 304 (word p) len /\
     val x + 48 = val cfr + k /\ k + l <= 304
     ==> nonoverlapping (word p:int64,len) (x,l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `len = 0` THENL
   [ASM_REWRITE_TAC[nonoverlapping] THEN MATCH_MP_TAC NONOVERLAPPING_MODULO_TRIVIAL THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
  MATCH_MP_TAC DRV_SUB_NONOVERLAP THEN
  MAP_EVERY EXISTS_TAC [`word_sub cfr (word 48):int64`; `304`; `k:num`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cfr:int64`; `48`] TISA_VAL_SP_SUB) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `val(word p:int64) = p` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A word at offset k of an area apart from the stack, read in a state whose *)
(* memory is M outside the stack: as in M (DRV_AREA_READ), or as in m0 when  *)
(* the area is static (DRV_AREA_READ_STATIC); and it does not overlap the   *)
(* child frame, so stores to the frame keep the fact.                        *)
(* ------------------------------------------------------------------------- *)

let DRV_AREA_READ = prove
 (`!s (M:int64->byte) cfr (b:int64) len k.
     48 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\ val b + len <= 2 EXP 64 /\
     drv_apart (word_sub cfr (word 48)) 304 b len /\
     (!a. ~drv_stack cfr a ==> read memory s a = M a) /\ k + 8 <= len
     ==> read (memory :> bytes64 (word_add b (word k))) s = drv_word M (word_add b (word k)) /\
         nonoverlapping (word_add b (word k),8) (cfr,192)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cfr:int64`; `b:int64`; `len:num`; `word_add b (word k):int64`; `k:num`;
                 `\a:int64. T`] DRV_AREA_BYTES) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DRV_READ_OUT THEN EXISTS_TAC `cfr:int64` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC DRV_OUT_NONOVERLAP THEN ASM_SIMP_TAC[]]);;

let DRV_AREA_READ_STATIC = prove
 (`!s (M:int64->byte) m0 (P:int64->bool) cfr (b:int64) len k.
     48 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\ val b + len <= 2 EXP 64 /\
     drv_apart (word_sub cfr (word 48)) 304 b len /\
     (!a. drv_in a b len ==> P a) /\ (!a. P a ==> M a = m0 a) /\
     (!a. ~drv_stack cfr a ==> read memory s a = M a) /\ k + 8 <= len
     ==> read (memory :> bytes64 (word_add b (word k))) s = drv_word m0 (word_add b (word k)) /\
         nonoverlapping (word_add b (word k),8) (cfr,192)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cfr:int64`; `b:int64`; `len:num`; `word_add b (word k):int64`; `k:num`;
                 `P:int64->bool`] DRV_AREA_BYTES) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DRV_READ_STATIC THEN
    MAP_EVERY EXISTS_TAC [`M:int64->byte`; `cfr:int64`; `P:int64->bool`] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC DRV_OUT_NONOVERLAP THEN ASM_SIMP_TAC[]]);;

(* Static areas, one by one. *)
let DRV_STATIC_AREAS = prove
 (`!pc cfr d plan ns bind nbw leaves nl (lpc:num->num) (lmc:num->byte list).
     (!a. drv_in a (word pc) 522 ==> drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a) /\
     (!j a. j < nl /\ drv_in a (word(lpc j)) (LENGTH(lmc j))
            ==> drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a) /\
     (!a. drv_in a d 64 ==> drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a) /\
     (!a. drv_in a plan (144 * ns) ==> drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a) /\
     (!a. drv_in a bind (8 * nbw) ==> drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a) /\
     (!a. drv_in a leaves (8 * nl) ==> drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a) /\
     (!a. drv_in a (word_add cfr (word 248)) 8
          ==> drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a)`,
  REWRITE_TAC[drv_static] THEN MESON_TAC[]);;

(* A region that holds no static byte does not overlap a leaf's code. *)
let DRV_REGION_CODE = prove
 (`!pc cfr d plan ns bind nbw leaves nl (lpc:num->num) (lmc:num->byte list) (b:int64) l j.
     (!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a ==> ~drv_in a b l) /\
     val b + l <= 2 EXP 64 /\ lpc j + LENGTH(lmc j) <= 2 EXP 64 /\ j < nl
     ==> nonoverlapping (b,l) (word(lpc j),LENGTH(lmc j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[NONOVERLAPPING; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word_add (word((lpc:num->num) j)) (word q):int64`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [REWRITE_TAC[drv_static] THEN DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `j:num` THEN
    ASM_REWRITE_TAC[drv_in];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[drv_in]] THEN
  (SUBGOAL_THEN `val(word((lpc:num->num) j):int64) = lpc j` ASSUME_TAC THENL
    [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  TRY(SUBGOAL_THEN `val(word_add (word((lpc:num->num) j)) (word q):int64) = val(word(lpc j):int64) + q`
        SUBST1_TAC THENL
       [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  TRY(SUBGOAL_THEN `val(word_add (b:int64) (word p):int64) = val b + p` SUBST1_TAC THENL
       [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_ARITH_TAC);;


let find_assum tm (asl:(string*thm)list) =
  try snd(find (fun (_,a) -> aconv (concl a) tm) asl)
  with Failure _ -> failwith ("find_assum: " ^ string_of_term tm);;

(* ------------------------------------------------------------------------- *)
(* DRV_BUILD: from after the receipt check to the leaf's entry: the child   *)
(* frame built, the entry registers set, the leaf entered by `enter`.        *)
(* ------------------------------------------------------------------------- *)

let iv n s = mk_var(s ^ string_of_int n, `:int64`);;
let w64n n = mk_comb(`word:num->int64`, mk_small_numeral n);;
let wadd a b = mk_comb(mk_comb(`word_add:int64->int64->int64`, a), b);;
let rd x = subst [x, `x:int64`] `read (memory :> bytes64 x) s`;;
let rdeq x v = mk_eq(rd x, v);;
let nonov x = subst [x, `x:int64`] `nonoverlapping (x:int64,8) (cfr,192)`;;
let stpo k = if k = 0 then `stp:int64` else wadd `stp:int64` (w64n k);;
let cfro k = if k = 0 then `cfr:int64` else wadd `cfr:int64` (w64n k);;
let ix8 w = mk_binop `( * ):num->num->num` `8` (mk_comb(`val:int64->num`, w));;
let bind_lo r = wadd `bind:int64` (mk_comb(`word:num->int64`, ix8 (iv (r+1) "w")));;
let bind_hi r = wadd `bind:int64` (mk_comb(`word:num->int64`, mk_binop `(+):num->num->num` (ix8 (iv (r+1) "w")) `8`));;
let ctlw f = wadd `ctl:int64` (mk_comb(`word:num->int64`, ix8 (iv f "w")));;
let leafw = wadd `leaves:int64` (mk_comb(`word:num->int64`, ix8 (iv 0 "w")));;

(* The words the build reads, and their values. *)
let drv_build_reads =
  [wadd `d:int64` (w64n 24), `bind:int64`; wadd `d:int64` (w64n 40), `budget:int64`;
   wadd `d:int64` (w64n 16), `ctl:int64`; wadd `d:int64` (w64n 32), `leaves:int64`] @
  map (fun f -> stpo (8 * f), iv f "w") (0--16) @
  List.concat (map (fun r -> [bind_lo r, iv r "b"; bind_hi r, iv r "l"]) (0--8)) @
  map (fun f -> ctlw f, iv f "c") (10--16) @
  [leafw, `lp:int64`];;

let drv_pushed =
  [cfro 240, `rbxv:int64`; cfro 232, `rbpv:int64`; cfro 224, `r12v:int64`;
   cfro 216, `r13v:int64`; cfro 208, `r14v:int64`; cfro 200, `r15v:int64`];;

(* The child frame the build leaves. *)
let drv_frame_words =
  List.concat (map (fun r -> [cfro (16 * r), iv r "b"; cfro (16 * r + 8), iv r "l"]) (0--8)) @
  [cfro 144, `word 0:int64`; cfro 152, `word 0:int64`; cfro 160, `budget:int64`;
   cfro 168, `used:int64`; cfro 176, iv 10 "c"; cfro 184, iv 11 "c"];;

let drv_build_goal =
  let vars = [`pc:num`; `cfr:int64`; `d:int64`; `stp:int64`; `mh:int64->byte`; `ctl:int64`;
              `bind:int64`; `leaves:int64`; `budget:int64`; `used:int64`; `rbxv:int64`; `rbpv:int64`;
              `r12v:int64`; `r13v:int64`; `r14v:int64`; `r15v:int64`; `lp:int64`] @
             map (fun f -> iv f "w") (0--16) @
             List.concat (map (fun r -> [iv r "b"; iv r "l"]) (0--8)) @ map (fun f -> iv f "c") (10--16) in
  let hyps = [`nonoverlapping (word pc:int64,522) (cfr,192)`;
              `nonoverlapping (word pc:int64,522) (word_sub cfr (word 8),8)`;
              `nonoverlapping (word pc:int64,522) (word_sub cfr (word 16),8)`;
              `48 <= val(cfr:int64)`; `val(cfr:int64) + 256 <= 2 EXP 64`] @
             map (fun (x,_) -> nonov x) drv_build_reads in
  let pre = list_mk_conj
    ([`bytes_loaded s (word pc) drv_mc`; `read RIP s = word(pc + 63)`; `read RSP s = cfr`;
      `read R14 s = d`; `read RBP s = stp`; `read memory s = mh`] @
     map (fun (x,v) -> rdeq x v) (drv_build_reads @ [cfro 168, `used:int64`] @ drv_pushed)) in
  let post = list_mk_conj
    ([`read RIP s = lp`; `read RSP s = word_sub cfr (word 8)`;
      `read (memory :> bytes64 (word_sub cfr (word 8))) s = word(pc + 424)`;
      `read RDI s = cfr`; mk_eq(`read RSI s`, iv 12 "c"); mk_eq(`read RDX s`, iv 13 "c");
      mk_eq(`read RCX s`, iv 14 "c"); mk_eq(`read R8 s`, iv 15 "c"); mk_eq(`read R9 s`, iv 16 "c");
      `read RAX s = word 0`; `read RBX s = word 0`; `read R10 s = word 0`; `read R11 s = word 0`;
      `read R12 s = word 0`; `read R13 s = word 0`; `read R15 s = lp`] @
     map (fun (x,v) -> rdeq x v) (drv_frame_words @ drv_pushed) @
     [`!a. ~drv_stack cfr a ==> read memory s a = mh a`]) in
  let ens = list_mk_comb(`ensures x86`,
              [mk_abs(`s:x86state`, pre); mk_abs(`s:x86state`, post);
               `MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11; R12; R13; R15] ,,
                MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory]`]) in
  list_mk_forall(vars, mk_imp(list_mk_conj hyps, ens));;

let DRV_STK8_FACTS_TAC =
  W(fun (asl,w) ->
    let lo = find_assum `48 <= val(cfr:int64)` asl and hi = find_assum `val(cfr:int64) + 256 <= 2 EXP 64` asl in
    let num_th t = EQT_ELIM(NUM_REDUCE_CONV t) in
    let disch th = let a = lhand(concl th) in
      MP th (if concl lo = lhand a then CONJ lo (CONJ hi (num_th (rand(rand a))))
             else CONJ hi (num_th (rand a))) in
    let adds = map (fun k -> disch (SPECL [`cfr:int64`; mk_small_numeral k] DRV_STK8_ADD))
                   (map (fun i -> 8 * i) (1--23)) in
    let zero = REWRITE_RULE[WORD_ADD_0] (disch (SPECL [`cfr:int64`; `0`] DRV_STK8_ADD)) in
    let subs = map (fun k -> disch (SPECL [`cfr:int64`; mk_small_numeral k] DRV_STK8_SUB)) [8; 16] in
    MAP_EVERY ASSUME_TAC (zero :: adds @ subs));;

(* Peels writes inside the stack off a read outside it. *)
let DRV_PEEL_TAC =
  REPEAT(W(fun (asl,w) ->
    MP_TAC (PART_MATCH (lhand o rand) DRV_WRITE_STACK (lhs w)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]));;

let DRV_BUILD_FINISH_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_sub (word_sub cfr (word 8)) (word 8):int64 = word_sub cfr (word 16)`;
                              WORD_RULE `word_add (word_sub cfr (word 16)) (word 8):int64 = word_sub cfr (word 8)`]) THEN
  DRV_STK8_FACTS_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN DRV_PEEL_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC];;

let DRV_BUILD = prove(drv_build_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  TISA_STEPS_TAC DRV_EXEC (1--81) THEN DRV_BUILD_FINISH_TAC);;

(* ------------------------------------------------------------------------- *)
(* DRV_CHILD_OK: the state the build leaves is the step's child state, it  *)
(* passes the leaf's entry validation and placement, and the leaf is loaded. *)
(* ------------------------------------------------------------------------- *)

let drv_child_goal =
  let frame = map (fun j ->
      let x = if j = 0 then `cfr:int64` else wadd `cfr:int64` (w64n (8 * j)) in
      let v = mk_comb(list_mk_comb(`drv_fw (bw:num->int64) (ctl:int64) (budget:int64) (used:int64) (h:int64 list)`,
                                   [`M:int64->byte`]), mk_small_numeral j) in
      mk_eq(subst [x, `x:int64`] `read (memory :> bytes64 x) s`, v)) (0--23) in
  let regs = [`read RDI s = cfr`;
              `read RSI s = drv_cw ctl M (EL 12 h)`; `read RDX s = drv_cw ctl M (EL 13 h)`;
              `read RCX s = drv_cw ctl M (EL 14 h)`; `read R8 s = drv_cw ctl M (EL 15 h)`;
              `read R9 s = drv_cw ctl M (EL 16 h)`; `read RAX s = word 0`; `read RBX s = word 0`;
              `read R10 s = word 0`; `read R11 s = word 0`; `read R12 s = word 0`; `read R13 s = word 0`] in
  let hyps = [`tisa_leaf_wf (progs (val(EL 0 (h:int64 list))))`;
              `drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc`;
              `drv_step_ok progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw h`;
              `!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a ==> (M:int64->byte) a = m0 a`;
              `drv_code m0 (lpc(val(EL 0 (h:int64 list)))) (lmc(val(EL 0 h)))`;
              `~(val(budget:int64) < val(used:int64))`;
              `!a. ~drv_stack cfr a ==> read memory s a = (M:int64->byte) a`] @ regs @ frame in
  let t = `TState (drv_regs cfr ctl h M) (read memory s)` in
  let concl = list_mk_conj
    [mk_comb(mk_comb(`tisa_x86_rel`, t), `s:x86state`);
     list_mk_comb(`drv_child bw ctl budget cfr h M used`, [t]);
     mk_comb(`tisa_entry_ok (progs (val(EL 0 (h:int64 list))))`, t);
     list_mk_comb(`tisa_leaf_place (progs (val(EL 0 (h:int64 list)))) (lmc(val(EL 0 h))) (lpc(val(EL 0 h)))`,
                  [t; `word_sub cfr (word 8):int64`]);
     `bytes_loaded s (word(lpc(val(EL 0 (h:int64 list)))):int64) (lmc(val(EL 0 h)))`] in
  list_mk_forall(
    [`progs:num->tisa_prog`; `pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`;
     `nctl:num`; `bind:int64`; `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`;
     `lmc:num->byte list`; `bw:num->int64`; `budget:int64`; `used:int64`; `m0:int64->byte`;
     `M:int64->byte`; `h:int64 list`; `s:x86state`],
    mk_imp(list_mk_conj hyps, concl));;

if frees drv_child_goal <> [] then failwith "drv_child_goal: free variables";;

let DRV_CHILD_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_step_ok]) THEN
  ABBREV_TAC `t = TState (drv_regs cfr ctl h M) (read memory s)` THEN
  SUBGOAL_THEN `tregs t = drv_regs cfr ctl h M /\ tmem t = read memory s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[tregs; tmem]; ALL_TAC] THEN
  SUBGOAL_THEN `tregs t 0 = cfr` ASSUME_TAC THENL [ASM_REWRITE_TAC[drv_regs]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. j < 24 ==> tisa_fword t j = drv_fw bw ctl budget used h M j` ASSUME_TAC THENL
   [REWRITE_TAC[DRV_FWORD] THEN
    FIRST_ASSUM(fun th -> if concl th = `tregs t 0 = cfr` then REWRITE_TAC[th] else failwith "") THEN
    FIRST_ASSUM(fun th -> if concl th = `tmem t = read memory s` then REWRITE_TAC[th] else failwith "") THEN
    REWRITE_TAC[GSYM DRV_READ64] THEN CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[WORD_ADD_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r < 9 ==> tisa_base t r = drv_base bw h r /\ tisa_len t r = drv_len bw h r` ASSUME_TAC THENL
   [REWRITE_TAC[tisa_base; tisa_len] THEN CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[ARITH] THEN REWRITE_TAC[drv_fw; drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `tisa_fword t 20 = budget /\ tisa_fword t 21 = used` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `drv_fw`)) (concl th) &&
                             can (find_term ((=) `tisa_fword`)) (concl th)
                          then (fun g -> (W(fun (_,w) -> MP_TAC(SPEC (rand(lhs w)) th))) g) else failwith "") THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[drv_fw] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `tisa_decls_ok t 0 (tisa_decls (progs (val(EL 0 (h:int64 list)))))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
                    can (find_term ((=) `tisa_decls_ok`)) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub cfr (word 8):int64) = val cfr - 8 /\ val(word_sub cfr (word 48):int64) = val cfr - 48 /\
                word_sub (word_sub cfr (word 8)) (word 40):int64 = word_sub cfr (word 48)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC TISA_VAL_SP_SUB; MATCH_MP_TAC TISA_VAL_SP_SUB; CONV_TAC WORD_RULE] THEN
    MP_TAC(ASSUME `48 <= val(cfr:int64)`) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lpc(val(EL 0 (h:int64 list))) + LENGTH(lmc(val(EL 0 h)):byte list) <= 2 EXP 64 /\
                drv_apart (word_sub cfr (word 48)) 304 (word(lpc(val(EL 0 h)))) (LENGTH(lmc(val(EL 0 h)):byte list))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
       (can (find_term ((=) `drv_apart`)) (concl th) || can (find_term ((=) `(<=):num->num->bool`)) (concl th)) &&
       can (find_term ((=) `lmc:num->byte list`)) (concl th) && not (can (find_term ((=) `ctl:int64`)) (concl th)) &&
       not (can (find_term ((=) `d:int64`)) (concl th)))) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let DRV_CHILD_MAIN_TAC =
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[tisa_x86_rel] THEN ASM_REWRITE_TAC[drv_regs] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[drv_child] THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[TISA_PROG_CASES] THEN
    REWRITE_TAC[tisa_entry_ok; tisa_decls; tisa_inits; tisa_root; tisa_frame] THEN
    ASM_REWRITE_TAC[GSYM TISA_PROG_CASES] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY MP_TAC [ASSUME `val(cfr:int64) + 256 <= 2 EXP 64`] THEN ARITH_TAC;
      MAP_EVERY MP_TAC [ASSUME `~(val(budget:int64) < val(used:int64))`] THEN ARITH_TAC;
      MATCH_MP_TAC TISA_INIT_U64 THEN
      FIRST_ASSUM(fun th -> if can (find_term ((=) `tisa_leaf_wf`)) (concl th)
                            then MP_TAC(REWRITE_RULE[tisa_leaf_wf] th) else failwith "") THEN
      SIMP_TAC[]];
    ALL_TAC; ALL_TAC];;

let DRV_CHILD_PLACE_TAC =
  REWRITE_TAC[tisa_leaf_place] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN MATCH_MP_TAC DRV_CODE_NONOVERLAP THEN
    MAP_EVERY EXISTS_TAC [`cfr:int64`; `48`] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `r < 9` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if can (find_term ((=) `tisa_leaf_wf`)) (concl th)
                            then MP_TAC(CONJUNCT1(REWRITE_RULE[tisa_leaf_wf] th)) else failwith "") THEN
      UNDISCH_TAC `tisa_rw (tisa_decls (progs (val (EL 0 (h:int64 list))))) r` THEN
      REWRITE_TAC[tisa_rw] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC DRV_REGION_CODE THEN
    MAP_EVERY EXISTS_TAC [`pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `bind:int64`;
                          `nbw:num`; `leaves:int64`; `nl:num`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term ((=) `drv_in`)) (concl th) && can (find_term ((=) `tisa_rw`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`tisa_decls (progs (val(EL 0 (h:int64 list))))`; `0`; `t:tisa_state`] TISA_DECLS_OK_REGION) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `r:num`) THEN
      FIRST_ASSUM(fun th -> if concl th = `tisa_rw (tisa_decls (progs (val (EL 0 (h:int64 list))))) r`
                            then MP_TAC(REWRITE_RULE[tisa_rw] th) else failwith "") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; ARITH_EQ] THEN
      SUBGOAL_THEN `tisa_base t r = drv_base bw h r /\ tisa_len t r = drv_len bw h r`
         (fun th -> REWRITE_TAC[th]) THENL
       [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
           can (find_term ((=) `drv_base`)) (concl th) && can (find_term ((=) `tisa_base`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[tisa_region_ok] THEN ARITH_TAC]];
    MP_TAC(ASSUME `48 <= val(cfr:int64)`) THEN ARITH_TAC;
    MP_TAC(ASSUME `val(cfr:int64) + 256 <= 2 EXP 64`) THEN ARITH_TAC;
    ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN MATCH_MP_TAC DRV_CODE_NONOVERLAP THEN
    MAP_EVERY EXISTS_TAC [`cfr:int64`; `0`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `48 <= val(cfr:int64)`) THEN ARITH_TAC;
    MP_TAC(ASSUME `48 <= val(cfr:int64)`) THEN ARITH_TAC;
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `r < 9` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if can (find_term ((=) `tisa_leaf_wf`)) (concl th)
                            then MP_TAC(CONJUNCT1(REWRITE_RULE[tisa_leaf_wf] th)) else failwith "") THEN
      UNDISCH_TAC `tisa_readable (tisa_decls (progs (val (EL 0 (h:int64 list))))) r` THEN
      REWRITE_TAC[tisa_readable] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
       can (find_term ((=) `drv_apart`)) (concl th) && can (find_term ((=) `tisa_readable`)) (concl th))) THEN
    ASM_REWRITE_TAC[drv_apart] THEN
    MP_TAC(ASSUME `48 <= val(cfr:int64)`) THEN ARITH_TAC];;

let DRV_CHILD_LOADED_TAC =
  MATCH_MP_TAC DRV_LOADED_CODE THEN EXISTS_TAC `m0:int64->byte` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~drv_stack cfr a` ASSUME_TAC THENL
   [MATCH_MP_TAC DRV_IN_NOT_STACK THEN
    MAP_EVERY EXISTS_TAC [`word(lpc(val(EL 0 (h:int64 list)))):int64`;
                          `LENGTH(lmc(val(EL 0 (h:int64 list))):byte list)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
     can (find_term ((=) `drv_static`)) (concl th) && can (find_term ((=) `m0:int64->byte`)) (concl th))) THEN
  REWRITE_TAC[drv_static] THEN DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `val(EL 0 (h:int64 list))` THEN
  ASM_REWRITE_TAC[];;

let DRV_CHILD_OK = prove(drv_child_goal,
  DRV_CHILD_SETUP_TAC THEN DRV_CHILD_MAIN_TAC THENL [DRV_CHILD_PLACE_TAC; DRV_CHILD_LOADED_TAC]);;
(* ------------------------------------------------------------------------- *)
(* DRV_POST: from the leaf's return to the loop head (FIRED) or to `done`:   *)
(* the payload stored to its control word, the outcome tested.               *)
(* ------------------------------------------------------------------------- *)

let DRV_POST = prove
 (`!pc cfr d stp ctl dst pay stat m1 r21 rbxv rbpv r12v r13v r14v r15v.
     nonoverlapping (word pc:int64,522) (word_add ctl (word(8 * val(dst:int64))),8) /\
     nonoverlapping (word_add ctl (word(8 * val dst)),8) (cfr,248)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) drv_mc /\ read RIP s = word(pc + 424) /\
               read RSP s = cfr /\ read R14 s = d /\ read RBP s = stp /\ read memory s = m1 /\
               read (memory :> bytes64 (word_add d (word 16))) s = ctl /\
               read (memory :> bytes64 (word_add stp (word 136))) s = dst /\
               read (memory :> bytes64 (word_add cfr (word 152))) s = pay /\
               read (memory :> bytes64 (word_add cfr (word 144))) s = stat /\
               read (memory :> bytes64 (word_add cfr (word 168))) s = r21 /\
               read (memory :> bytes64 (word_add cfr (word 240))) s = rbxv /\
               read (memory :> bytes64 (word_add cfr (word 232))) s = rbpv /\
               read (memory :> bytes64 (word_add cfr (word 224))) s = r12v /\
               read (memory :> bytes64 (word_add cfr (word 216))) s = r13v /\
               read (memory :> bytes64 (word_add cfr (word 208))) s = r14v /\
               read (memory :> bytes64 (word_add cfr (word 200))) s = r15v)
          (\s. read RSP s = cfr /\ read R14 s = d /\
               read (memory :> bytes64 (word_add cfr (word 168))) s = r21 /\
               read (memory :> bytes64 (word_add cfr (word 240))) s = rbxv /\
               read (memory :> bytes64 (word_add cfr (word 232))) s = rbpv /\
               read (memory :> bytes64 (word_add cfr (word 224))) s = r12v /\
               read (memory :> bytes64 (word_add cfr (word 216))) s = r13v /\
               read (memory :> bytes64 (word_add cfr (word 208))) s = r14v /\
               read (memory :> bytes64 (word_add cfr (word 200))) s = r15v /\
               read memory s = write (bytes64 (word_add ctl (word(8 * val dst)))) pay m1 /\
               (if stat = word 1
                then read RIP s = word(pc + 35) /\ read RBP s = word_add stp (word 144)
                else read RIP s = word(pc + 485) /\ read RBP s = stp /\ read RAX s = stat))
          (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11; R12; R13; R15; RBP] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  TISA_STEPS_TAC DRV_EXEC (1--6) THEN
  ASM_CASES_TAC `stat:int64 = word 1` THENL
   [SUBGOAL_THEN `val(word_sub (stat:int64) (word 1)) = 0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0]; ALL_TAC] THEN
    TISA_STEPS_TAC DRV_EXEC (7--9);
    SUBGOAL_THEN `~(val(word_sub (stat:int64) (word 1)) = 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0]; ALL_TAC] THEN
    TISA_STEPS_TAC DRV_EXEC [7]] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* After the call: words the leaf could not write, and its frame words.      *)
(* ------------------------------------------------------------------------- *)

let DRV_NOT_SAVED = prove
 (`!cfr (a:int64). 48 <= val cfr /\ ~drv_stack cfr a ==> ~tisa_saved (word_sub cfr (word 8)) a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tisa_saved] THEN
  MP_TAC(SPECL [`cfr:int64`; `8`] TISA_VAL_SP_SUB) THEN ANTS_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[drv_stack]) THEN ASM_ARITH_TAC);;

let DRV_AFTER_STATIC = prove
 (`!s7 t u decls cfr bw h (M:int64->byte) m0 (P:int64->bool) x.
     (!a. ~tisa_saved (word_sub cfr (word 8)) a ==> read memory s7 a = tmem u a) /\
     tisa_keeps decls t u /\ tregs t 0 = cfr /\ LENGTH decls <= 9 /\
     (!r. r < 9 ==> tisa_base t r = drv_base bw h r /\ tisa_len t r = drv_len bw h r) /\
     (!r a. tisa_rw decls r /\ P a ==> ~drv_in a (drv_base bw h r) (val(drv_len bw h r))) /\
     (!a. ~drv_stack cfr a ==> tmem t a = M a) /\ (!a. P a ==> M a = m0 a) /\
     48 <= val cfr /\
     (!i. i < 8 ==> P (word_add x (word i)) /\ ~drv_stack cfr (word_add x (word i)))
     ==> read (memory :> bytes64 x) s7 = drv_word m0 x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i < 8 ==> ~tisa_writable decls t (word_add x (word i))` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC DRV_NOT_WRITABLE THEN
    MAP_EVERY EXISTS_TAC [`cfr:int64`; `bw:num->int64`; `h:int64 list`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[drv_stack] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s7:x86state`; `word_sub cfr (word 8):int64`; `u:tisa_state`; `x:int64`] DRV_RET_WORD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC DRV_NOT_SAVED THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`decls:(num#num#num)list`; `t:tisa_state`; `u:tisa_state`; `x:int64`] DRV_KEPT_WORD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC DRV_WORD_AGREE THEN ASM_MESON_TAC[]);;

let DRV_AFTER_FRAME = prove
 (`!s7 u cfr j.
     (!a. ~tisa_saved (word_sub cfr (word 8)) a ==> read memory s7 a = tmem u a) /\
     tregs u 0 = cfr /\ 48 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\ j < 24
     ==> read (memory :> bytes64 (word_add cfr (word(8 * j)))) s7 = tisa_fword u j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[DRV_FWORD] THEN
  MATCH_MP_TAC DRV_RET_WORD THEN EXISTS_TAC `word_sub cfr (word 8):int64` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[tisa_saved] THEN
  MP_TAC(SPECL [`cfr:int64`; `8`] TISA_VAL_SP_SUB) THEN ANTS_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `val(word_add (word_add cfr (word(8 * j))) (word i):int64) = val cfr + 8 * j + i`
  SUBST1_TAC THENL
   [REWRITE_TAC[DRV_ADDR_ASSOC] THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let DRV_AFTER_BYTE = prove
 (`!s7 tc u decls cfr bw h (M:int64->byte) m0 (P:int64->bool) a.
     (!a. ~tisa_saved (word_sub cfr (word 8)) a ==> read memory s7 a = tmem u a) /\
     tisa_keeps decls tc u /\ tregs tc 0 = cfr /\ LENGTH decls <= 9 /\
     (!r. r < 9 ==> tisa_base tc r = drv_base bw h r /\ tisa_len tc r = drv_len bw h r) /\
     (!r a. tisa_rw decls r /\ P a ==> ~drv_in a (drv_base bw h r) (val(drv_len bw h r))) /\
     (!a. ~drv_stack cfr a ==> tmem tc a = M a) /\ (!a. P a ==> M a = m0 a) /\
     48 <= val cfr /\ P a /\ ~drv_stack cfr a
     ==> read memory s7 a = m0 a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~tisa_writable decls tc a` ASSUME_TAC THENL
   [MATCH_MP_TAC DRV_NOT_WRITABLE THEN
    MAP_EVERY EXISTS_TAC [`cfr:int64`; `bw:num->int64`; `h:int64 list`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; RULE_ASSUM_TAC(REWRITE_RULE[drv_stack]) THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tisa_keeps]) THEN ASM_MESON_TAC[DRV_NOT_SAVED]);;

(* Static bytes lie outside the control words. *)
let DRV_CTL_APART = prove
 (`!ctl nctl (b:int64) n (a:int64) k.
     drv_apart ctl (8 * nctl) b n /\ drv_in a b n /\ k < nctl /\ val ctl + 8 * nctl <= 2 EXP 64
     ==> ~(val(word_add ctl (word(8 * k))) <= val a /\ val a < val(word_add ctl (word(8 * k))) + 8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add ctl (word(8 * k)):int64) = val ctl + 8 * k` SUBST1_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[drv_apart; drv_in]) THEN ASM_ARITH_TAC);;

let DRV_CTL_NOT_STATIC = prove
 (`!pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc a k.
     drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a /\ k < nctl
     ==> ~(val(word_add ctl (word(8 * k))) <= val a /\ val a < val(word_add ctl (word(8 * k))) + 8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_layout]) THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_static] o
    check (fun th -> can (find_term ((=) `drv_static`)) (concl th))) THEN
  TRY(FIRST [MATCH_MP_TAC DRV_CTL_APART THEN MAP_EVERY EXISTS_TAC [`nctl:num`; `word pc:int64`; `522`] THEN
             ASM_REWRITE_TAC[] THEN NO_TAC;
             MATCH_MP_TAC DRV_CTL_APART THEN MAP_EVERY EXISTS_TAC [`nctl:num`; `d:int64`; `64`] THEN
             ASM_REWRITE_TAC[] THEN NO_TAC;
             MATCH_MP_TAC DRV_CTL_APART THEN MAP_EVERY EXISTS_TAC [`nctl:num`; `plan:int64`; `144 * ns`] THEN
             ASM_REWRITE_TAC[] THEN NO_TAC;
             MATCH_MP_TAC DRV_CTL_APART THEN MAP_EVERY EXISTS_TAC [`nctl:num`; `bind:int64`; `8 * nbw`] THEN
             ASM_REWRITE_TAC[] THEN NO_TAC;
             MATCH_MP_TAC DRV_CTL_APART THEN MAP_EVERY EXISTS_TAC [`nctl:num`; `leaves:int64`; `8 * nl`] THEN
             ASM_REWRITE_TAC[] THEN NO_TAC;
             MATCH_MP_TAC DRV_CTL_APART THEN
             MAP_EVERY EXISTS_TAC [`nctl:num`; `word((lpc:num->num) j):int64`; `LENGTH((lmc:num->byte list) j)`] THEN
             ASM_SIMP_TAC[] THEN NO_TAC]) THEN
  (* the caller's return address, inside the stack area *)
  SUBGOAL_THEN `val(word_add ctl (word(8 * k)):int64) = val ctl + 8 * k /\
                val(word_add cfr (word 248):int64) = val cfr + 248 /\
                val(word_sub cfr (word 48):int64) = val cfr - 48`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC TISA_VAL_OFFSET; MATCH_MP_TAC TISA_VAL_OFFSET; MATCH_MP_TAC TISA_VAL_SP_SUB] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `drv_in`)) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `drv_apart (word_sub cfr (word 48)) 304 ctl (8 * nctl)`)) THEN
  REWRITE_TAC[drv_apart; drv_in] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY MP_TAC [ASSUME `48 <= val(cfr:int64)`; ASSUME `k < nctl`] THEN ARITH_TAC);;

(* Writes at one address preserve agreement elsewhere. *)
let DRV_WRITE_CONG = prove
 (`!(P:int64->bool) m1 m2 (x:int64) (v:int64).
     (!a. P a ==> m1 a = m2 a)
     ==> !a. P a ==> write (bytes64 x) v m1 a = write (bytes64 x) v m2 a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TISA_WRITE_BYTES64; WRITE_BYTES] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* After the call, a stack word above the frame words the leaf writes. *)
let DRV_AFTER_PUSHED = prove
 (`!s7 tc u decls cfr bw h (x:int64) v.
     (!a. ~tisa_saved (word_sub cfr (word 8)) a ==> read memory s7 a = tmem u a) /\
     tisa_keeps decls tc u /\ tregs tc 0 = cfr /\ LENGTH decls <= 9 /\
     (!r. r < 9 ==> tisa_base tc r = drv_base bw h r /\ tisa_len tc r = drv_len bw h r) /\
     (!r. tisa_readable decls r
          ==> drv_apart (drv_base bw h r) (val(drv_len bw h r)) (word_sub cfr (word 48)) 304) /\
     48 <= val cfr /\ val cfr + 256 <= 2 EXP 64 /\
     val cfr + 176 <= val x /\ val x + 8 <= val cfr + 248 /\
     drv_word (tmem tc) x = v
     ==> read (memory :> bytes64 x) s7 = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i < 8 ==> val(word_add x (word i):int64) = val x + i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`s7:x86state`; `word_sub cfr (word 8):int64`; `u:tisa_state`; `x:int64`] DRV_RET_WORD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[tisa_saved] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cfr:int64`; `8`] TISA_VAL_SP_SUB) THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && is_var(rhs(concl th)) &&
                                                     rhs(concl th) = `v:int64`)) THEN
  MATCH_MP_TAC DRV_KEPT_WORD THEN EXISTS_TAC `decls:(num#num#num)list` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC DRV_NOT_WRITABLE THEN
  MAP_EVERY EXISTS_TAC [`cfr:int64`; `bw:num->int64`; `h:int64 list`] THEN ASM_SIMP_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN MATCH_MP_TAC DRV_STACK_NOT_IN THEN
  EXISTS_TAC `cfr:int64` THEN ASM_SIMP_TAC[TISA_RW_READABLE] THEN ASM_ARITH_TAC);;

(* Static bytes lie outside the stack area. *)
let DRV_STATIC_NOT_STACK = prove
 (`!pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc a.
     drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a
     ==> ~drv_stack cfr a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_layout]) THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_static] o
    check (fun th -> can (find_term ((=) `drv_static`)) (concl th))) THEN
  TRY(FIRST (map (fun (b,n) ->
        MATCH_MP_TAC DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [b; n] THEN ASM_SIMP_TAC[] THEN NO_TAC)
       [`word pc:int64`, `522`; `d:int64`, `64`; `plan:int64`, `144 * ns`; `bind:int64`, `8 * nbw`;
        `leaves:int64`, `8 * nl`; `word((lpc:num->num) j):int64`, `LENGTH((lmc:num->byte list) j)`])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[drv_in]) THEN REWRITE_TAC[drv_stack] THEN
  SUBGOAL_THEN `val(word_add cfr (word 248):int64) = val cfr + 248` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop, by induction on the remaining steps.                            *)
(* ------------------------------------------------------------------------- *)

(* From the loop head with the steps sts left (steps i.. of the plan), the
   plan's memory M outside the stack and receipt used, the driver reaches its
   exit with the result drv_sem gives; static memory never changes. *)
let drv_loop_goal = `!progs lpc lmc nl pc cfr d plan ns ctl nctl bind nbw leaves bw stepl budget used0 m0
    rbxv rbpv r12v r13v r14v r15v.
     (!j. j < nl ==> tisa_leaf_wf (progs j) /\ tisa_leaf_spec (progs j) (lmc j) (lpc j)) /\
     drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     ALL (drv_step_ok progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw) stepl /\
     drv_holds m0 d plan ns ctl bind leaves budget used0 stepl bw nbw lpc nl /\
     drv_code m0 pc drv_mc /\
     (!j. j < nl ==> drv_code m0 (lpc j) (lmc j))
     ==> !sts i M used.
           LENGTH sts + i = ns /\ (!j. j < LENGTH sts ==> EL j sts = EL (i + j) stepl) /\
           (!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a ==> M a = m0 a)
           ==> ensures x86
                (\s. read RIP s = word(pc + 35) /\ read RSP s = cfr /\ read R14 s = d /\
                     read RBP s = word_add plan (word(144 * i)) /\
                     read (memory :> bytes64 (word_add cfr (word 168))) s = used /\
                     read (memory :> bytes64 (word_add cfr (word 240))) s = rbxv /\
                     read (memory :> bytes64 (word_add cfr (word 232))) s = rbpv /\
                     read (memory :> bytes64 (word_add cfr (word 224))) s = r12v /\
                     read (memory :> bytes64 (word_add cfr (word 216))) s = r13v /\
                     read (memory :> bytes64 (word_add cfr (word 208))) s = r14v /\
                     read (memory :> bytes64 (word_add cfr (word 200))) s = r15v /\
                     (!a. ~drv_stack cfr a ==> read memory s a = M a))
                (\s. read RIP s = word(pc + 485) /\ read RSP s = cfr /\ read R14 s = d /\
                     read (memory :> bytes64 (word_add cfr (word 240))) s = rbxv /\
                     read (memory :> bytes64 (word_add cfr (word 232))) s = rbpv /\
                     read (memory :> bytes64 (word_add cfr (word 224))) s = r12v /\
                     read (memory :> bytes64 (word_add cfr (word 216))) s = r13v /\
                     read (memory :> bytes64 (word_add cfr (word 208))) s = r14v /\
                     read (memory :> bytes64 (word_add cfr (word 200))) s = r15v /\
                     ?res. drv_sem progs bw ctl budget cfr sts i M used res /\
                           read RAX s = FST res /\
                           read RBP s = word_add plan (word(144 * FST(SND res))) /\
                           read (memory :> bytes64 (word_add cfr (word 168))) s =
                             SND(SND(SND res)) /\
                           (!a. ~drv_stack cfr a ==> read memory s a = FST(SND(SND res)) a) /\
                           (!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a
                                ==> FST(SND(SND res)) a = m0 a))
                (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                            R12; R13; R14; R15; RBP] ,,
                 MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`;;


(* Instantiate the assumption whose conclusion is tm at the numerals ks,
   reducing numeral arithmetic, as new assumptions. *)
let DRV_INST_TAC tm ks =
  FIRST_ASSUM(fun th ->
    if aconv (concl th) tm then
      MAP_EVERY (fun k ->
        let th1 = CONV_RULE NUM_REDUCE_CONV (SPEC (mk_small_numeral k) th) in
        ASSUME_TAC (CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[] th1))) ks
    else failwith "DRV_INST_TAC");;

let w64 n = mk_comb(`word:num->int64`, mk_small_numeral n);;
let nadd a b = mk_binop `(+):num->num->num` a b;;
let el_tm f l = mk_comb(mk_comb(`EL:num->int64 list->int64`, mk_small_numeral f), l);;
let el_h f = el_tm f `h:int64 list`;;
let val_tm x = mk_comb(`val:int64->num`, x);;
let mul8 t = mk_binop `( * ):num->num->num` `8` t;;

let static_P = `drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc`;;
let DRV_STATIC_AREA_THS = CONJUNCTS (SPEC_ALL DRV_STATIC_AREAS);;

let DRV_ANTS_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; FIRST (map MATCH_ACCEPT_TAC DRV_STATIC_AREA_THS); DRV_ARITH_TAC];;

(* Adds read (memory :> bytes64 (word_add b (word k))) s0 = drv_word m0/M ...
   and nonoverlapping (word_add b (word k),8) (cfr,192), rewritten by eqs. *)
let DRV_FACT_TAC static b len k eqs =
  let lem =
    if static then ISPECL [`s0:x86state`; `M:int64->byte`; `m0:int64->byte`; static_P; `cfr:int64`; b; len; k]
                     DRV_AREA_READ_STATIC
    else ISPECL [`s0:x86state`; `M:int64->byte`; `cfr:int64`; b; len; k] DRV_AREA_READ in
  MP_TAC lem THEN ANTS_TAC THENL
   [DRV_ANTS_TAC;
    DISCH_THEN(fun th -> W(fun (asl,w) ->
      let eqths = map (fun tm -> try snd(find (fun (_,a) -> aconv (concl a) tm) asl)
                                 with Failure _ -> failwith ("DRV_FACT_TAC: no " ^ string_of_term tm)) eqs in
      STRIP_ASSUME_TAC (CONV_RULE (NUM_REDUCE_CONV THENC REWRITE_CONV eqths) th)))];;


let holds_plan_tm = `!i f. i < ns /\ f < 18
                     ==> drv_word m0 (word_add plan (word (144 * i + 8 * f))) = EL f (EL i stepl)`;;
let holds_bind_tm = `!k. k < nbw ==> drv_word m0 (word_add bind (word (8 * k))) = bw k`;;
let holds_leaf_tm = `!j. j < nl ==> drv_word m0 (word_add leaves (word (8 * j))) = word (lpc j)`;;

(* The lemma instance for word k of area (b, len), its antecedent discharged. *)
let drv_fact_th static b len k (asl,w) =
  let lem =
    if static then ISPECL [`s0:x86state`; `M:int64->byte`; `m0:int64->byte`; static_P; `cfr:int64`; b; len; k]
                     DRV_AREA_READ_STATIC
    else ISPECL [`s0:x86state`; `M:int64->byte`; `cfr:int64`; b; len; k] DRV_AREA_READ in
  let ant = lhand(concl lem) in
  MP lem (TAC_PROOF((asl, ant), DRV_ANTS_TAC));;

(* Proves an arithmetic fact from the targeted assumptions. *)
let drv_arith tm (asl,w) = TAC_PROOF((asl, tm), DRV_ARITH_TAC);;

let DRV_DESC_FACTS_TAC =
  W(fun (asl,w) ->
    MAP_EVERY (fun k ->
      let th = drv_fact_th true `d:int64` `64` (mk_small_numeral k) (asl,w) in
      let eqs = mapfilter (fun (_,a) -> let c = concl a in
                  if is_eq c && (match lhs c with Comb(Comb(Const("drv_word",_),Var("m0",_)),_) -> true | _ -> false)
                  then a else failwith "") asl in
      STRIP_ASSUME_TAC (REWRITE_RULE eqs th)) [8; 16; 24; 32; 40]);;

let DRV_PLAN_FACTS_TAC =
  W(fun (asl,w) ->
    let hp = find_assum holds_plan_tm asl in
    let hi = find_assum `EL i stepl = h:int64 list` asl in
    let stp_eq = find_assum `word_add plan (word(144 * i)):int64 = stp` asl in
    let ilt = find_assum `i < ns` asl in
    MAP_EVERY (fun f ->
      let k = if f = 0 then `144 * i` else nadd `144 * i` (mul8 (mk_small_numeral f)) in
      let th = drv_fact_th true `plan:int64` `144 * ns` k (asl,w) in
      let v = MP (SPECL [`i:num`; mk_small_numeral f] hp)
                 (CONJ ilt (EQT_ELIM(NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral f) `18`)))) in
      let v = CONV_RULE (REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES] THENC NUM_REDUCE_CONV) v in
      let th = CONV_RULE (NUM_REDUCE_CONV THENC REWRITE_CONV[v; hi]) th in
      let th = CONV_RULE (REWRITE_CONV[GSYM DRV_ADDR_ASSOC] THENC REWRITE_CONV[stp_eq]) th in
      STRIP_ASSUME_TAC th) (0--17));;

let DRV_BIND_FACTS_TAC =
  W(fun (asl,w) ->
    let hb = find_assum holds_bind_tm asl in
    MAP_EVERY (fun r ->
      let wv = val_tm (el_h (r + 1)) in
      let k1 = mul8 wv and k2 = nadd (mul8 wv) `8` in
      let th1 = drv_fact_th true `bind:int64` `8 * nbw` k1 (asl,w) in
      let th2 = drv_fact_th true `bind:int64` `8 * nbw` k2 (asl,w) in
      let v1 = MP (SPEC wv hb) (drv_arith (mk_binop `(<):num->num->bool` wv `nbw:num`) (asl,w)) in
      let v2 = MP (SPEC (nadd wv `1`) hb) (drv_arith (mk_binop `(<):num->num->bool` (nadd wv `1`) `nbw:num`) (asl,w)) in
      let v2 = REWRITE_RULE[ARITH_RULE `8 * (x + 1) = 8 * x + 8`] v2 in
      STRIP_ASSUME_TAC (REWRITE_RULE[v1] th1) THEN STRIP_ASSUME_TAC (REWRITE_RULE[v2] th2)) (0--8));;

let DRV_LEAF_FACTS_TAC =
  W(fun (asl,w) ->
    let hl = find_assum holds_leaf_tm asl in
    let jv = val_tm (el_h 0) in
    let th = drv_fact_th true `leaves:int64` `8 * nl` (mul8 jv) (asl,w) in
    let v = MP (SPEC jv hl) (drv_arith (mk_binop `(<):num->num->bool` jv `nl:num`) (asl,w)) in
    STRIP_ASSUME_TAC (REWRITE_RULE[v] th));;

let DRV_CODE_FACTS_TAC =
  let one x k l =
    SUBGOAL_THEN (subst [x, `x:int64`; mk_small_numeral l, `l:num`] `nonoverlapping (word pc:int64,522) (x,l)`)
      ASSUME_TAC THENL
     [MATCH_MP_TAC DRV_CODE_NONOVERLAP THEN MAP_EVERY EXISTS_TAC [`cfr:int64`; mk_small_numeral k] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN
      TRY(W(fun (asl,w) -> let v = lhand(lhand w) in
             MP_TAC(SPECL [`cfr:int64`; rand(rand(rand v))] TISA_VAL_SP_SUB))) THEN
      MP_TAC(ASSUME `48 <= val(cfr:int64)`) THEN ARITH_TAC;
      ALL_TAC] in
  one `cfr:int64` 48 192 THEN
  one `word_sub cfr (word 8):int64` 40 8 THEN
  one `word_sub cfr (word 16):int64` 32 8;;

let DRV_FUEL_OK_TAC =
  SUBGOAL_THEN `val (used:int64) < val (budget:int64) \/ val(word_sub used budget) = 0` ASSUME_TAC THENL
   [MP_TAC(SPECL [`used:int64`; `budget:int64`] DRV_FUEL_COND) THEN
    FIRST_ASSUM(fun th -> if concl th = `~(val(budget:int64) < val(used:int64))` then REWRITE_TAC[th]
                          else failwith "") THEN
    CONV_TAC TAUT;
    ALL_TAC];;

let DRV_BASE_TAC =
  REWRITE_TAC[LENGTH; ADD_CLAUSES; CONJUNCT1 LT] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  DRV_LOADED_TAC "s0" `pc:num` `drv_mc` `522` THEN
  DRV_STATIC_READ_TAC "s0" `word_add (d:int64) (word 8)` `d:int64` `64` `8` THEN
  X86_STEPS_TAC DRV_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC] THEN
  EXISTS_TAC `(word 1:int64, ns:num, M:int64->byte, used:int64)` THEN
  ASM_REWRITE_TAC[drv_sem];;

let DRV_CONS_SETUP_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH] THEN STRIP_TAC THEN
  SUBGOAL_THEN `EL i stepl = h:int64 list /\ i < ns` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[EL; HD; ADD_CLAUSES; LT_0] THEN
      DISCH_THEN(ACCEPT_TAC o SYM);
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `drv_step_ok progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw h`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `i:num` o GEN_REWRITE_RULE I [GSYM ALL_EL] o
      check (fun th -> can (find_term ((=) `ALL:(int64 list->bool)->(int64 list)list->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_step_ok]) THEN
  SUBGOAL_THEN `tisa_leaf_wf (progs (val(EL 0 (h:int64 list)))) /\
                tisa_leaf_spec (progs (val(EL 0 h))) (lmc (val(EL 0 h))) (lpc (val(EL 0 h)))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `tisa_leaf_spec`)) (concl th) &&
                                                   is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val(word_sub (word_add (plan:int64) (word(144 * i))) (word_add plan (word(144 * ns)))) = 0)`
  ASSUME_TAC THENL [MATCH_MP_TAC DRV_NOT_END THEN ASM_REWRITE_TAC[]; ALL_TAC];;
let DRV_CTL_FACTS_TAC =
  W(fun (asl,w) ->
    MAP_EVERY (fun f ->
      STRIP_ASSUME_TAC (drv_fact_th false `ctl:int64` `8 * nctl` (mul8 (val_tm (el_h f))) (asl,w))) (10--17));;

let DRV_M1_TAC =
  ABBREV_TAC `stp = word_add plan (word(144 * i)):int64` THEN
  SUBGOAL_THEN `val(stp:int64) = val(plan:int64) + 144 * i` ASSUME_TAC THENL
   [EXPAND_TAC "stp" THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  DRV_LOADED_TAC "s0" `pc:num` `drv_mc` `522` THEN
  DRV_INST_TAC `!r. r < 9 ==> val(EL (1 + r) (h:int64 list)) + 1 < nbw` (0--8) THEN
  DRV_INST_TAC `!f. 10 <= f /\ f < 18 ==> val(EL f (h:int64 list)) < nctl` (10--17) THEN
  DRV_DESC_FACTS_TAC THEN DRV_PLAN_FACTS_TAC THEN DRV_BIND_FACTS_TAC THEN DRV_CTL_FACTS_TAC THEN
  DRV_LEAF_FACTS_TAC THEN DRV_CODE_FACTS_TAC THEN DRV_FUEL_OK_TAC THEN
  X86_STEPS_TAC DRV_EXEC (1--5);;

let drv_build_inst =
  [`pc:num`; `cfr:int64`; `d:int64`; `stp:int64`; `mh:int64->byte`; `ctl:int64`; `bind:int64`;
   `leaves:int64`; `budget:int64`; `used:int64`; `rbxv:int64`; `rbpv:int64`; `r12v:int64`;
   `r13v:int64`; `r14v:int64`; `r15v:int64`; `word(lpc(val(EL 0 (h:int64 list)))):int64`] @
  map (fun f -> el_h f) (0--16) @
  List.concat (map (fun r -> let w = val_tm (el_h (r + 1)) in
                             [mk_comb(`bw:num->int64`, w); mk_comb(`bw:num->int64`, nadd w `1`)]) (0--8)) @
  map (fun f -> mk_comb(mk_comb(`drv_word`, `M:int64->byte`),
                        wadd `ctl:int64` (mk_comb(`word:num->int64`, mul8 (val_tm (el_h f)))))) (10--16);;

let DRV_M2_TAC =
  ABBREV_TAC `mh = read memory s5` THEN
  MP_TAC(SPECL drv_build_inst (REWRITE_RULE[SOME_FLAGS] DRV_BUILD)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  TISA_BIGSTEP_TAC "s6";;

let drv_child_inst =
  [`progs:num->tisa_prog`; `pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`;
   `nctl:num`; `bind:int64`; `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`;
   `lmc:num->byte list`; `bw:num->int64`; `budget:int64`; `used:int64`; `m0:int64->byte`;
   `M:int64->byte`; `h:int64 list`; `s6:x86state`];;

let drv_pushed_words =
  [`word_add cfr (word 240):int64`, `rbxv:int64`; `word_add cfr (word 232):int64`, `rbpv:int64`;
   `word_add cfr (word 224):int64`, `r12v:int64`; `word_add cfr (word 216):int64`, `r13v:int64`;
   `word_add cfr (word 208):int64`, `r14v:int64`; `word_add cfr (word 200):int64`, `r15v:int64`];;

let DRV_M3_TAC =
  SUBGOAL_THEN `!a. ~drv_stack cfr a ==> read memory s6 a = (M:int64->byte) a` ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    W(fun (asl,w) ->
      let th1 = find (fun th -> let c = concl th in is_forall c && can (find_term ((=) `s6:x86state`)) c &&
                                  can (find_term ((=) `mh:int64->byte`)) c) (map snd asl)
      and th2 = find (fun th -> let c = concl th in is_forall c && can (find_term ((=) `mh:int64->byte`)) c &&
                                  can (find_term ((=) `M:int64->byte`)) c) (map snd asl) in
      ASM_SIMP_TAC[th1; th2]);
    ALL_TAC] THEN
  SUBGOAL_THEN `drv_code m0 (lpc(val(EL 0 (h:int64 list)))) (lmc(val(EL 0 h)))` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "drv_code")) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(CONV_RULE (REWRITE_CONV[drv_fw; drv_cw] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES])
                   (SPECL drv_child_inst DRV_CHILD_OK)) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN NO_TAC; STRIP_TAC] THEN
  (* the child state, by name, before s6's facts go *)
  MAP_EVERY (fun (x,v) ->
    SUBGOAL_THEN (mk_eq(mk_comb(mk_comb(`drv_word`, `read memory s6`), x), v)) ASSUME_TAC THENL
     [REWRITE_TAC[GSYM DRV_READ64] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) drv_pushed_words THEN
  ABBREV_TAC `tc = TState (drv_regs cfr ctl h M) (read memory s6)` THEN
  SUBGOAL_THEN `tregs tc = drv_regs cfr ctl h M /\ tmem tc = read memory s6` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tc" THEN REWRITE_TAC[tregs; tmem]; ALL_TAC] THEN
  SUBGOAL_THEN `tregs tc 0 = cfr /\ tregs tc 9 = word 0 /\ tregs tc 10 = word 0 /\ tregs tc 11 = word 0`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[drv_regs] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MAP_EVERY (fun (x,v) ->
    SUBGOAL_THEN (mk_eq(mk_comb(mk_comb(`drv_word`, `tmem tc`), x), v)) ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC]) drv_pushed_words THEN
  FIRST_X_ASSUM(MP_TAC o
    SPECL [`tc:tisa_state`; `word_sub cfr (word 8):int64`;
           `word(pc + 424):int64`; `d:int64`; `word(lpc(val(EL 0 (h:int64 list)))):int64`] o
    REWRITE_RULE[tisa_leaf_spec] o
    check (fun th -> can (find_term ((=) `tisa_leaf_spec`)) (concl th) && not (is_forall(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN TISA_BIGSTEP_TAC "s7";;
let DRV_AFTER_STATIC_TAC x b len k =
  W(fun (asl,w) ->
    let goal = subst [x, `x:int64`] `read (memory :> bytes64 x) s7 = drv_word m0 x` in
    SUBGOAL_THEN goal ASSUME_TAC THENL
     [MATCH_MP_TAC DRV_AFTER_STATIC THEN
      MAP_EVERY EXISTS_TAC [`tc:tisa_state`; `u:tisa_state`; `tisa_decls (progs (val(EL 0 (h:int64 list))))`;
                            `cfr:int64`; `bw:num->int64`; `h:int64 list`; `M:int64->byte`; static_P] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MP_TAC(ISPECL [`cfr:int64`; b; len; x; k; static_P] DRV_AREA_BYTES) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN
        FIRST [FIRST_ASSUM ACCEPT_TAC; FIRST (map MATCH_ACCEPT_TAC DRV_STATIC_AREA_THS);
               MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC; DRV_ARITH_TAC];
        SIMP_TAC[]];
      ALL_TAC]);;

let DRV_M4_TAC =
  SUBGOAL_THEN `tisa_keeps (tisa_decls (progs (val(EL 0 (h:int64 list))))) tc u` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_RUN_KEEPS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `tregs u 0 = cfr` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [tisa_keeps] o
      check (fun th -> can (find_term ((=) `tisa_keeps`)) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_child] o
    check (fun th -> can (find_term ((=) `drv_child`)) (concl th) && not(is_forall(concl th)))) THEN
  SUBGOAL_THEN `!r. r < 9 ==> tisa_base tc r = drv_base bw h r /\ tisa_len tc r = drv_len bw h r` ASSUME_TAC THENL
   [REWRITE_TAC[tisa_base; tisa_len] THEN CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[ARITH] THEN REWRITE_TAC[drv_fw; drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (tisa_decls (progs (val(EL 0 (h:int64 list))))) <= 9` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if can (find_term ((=) `tisa_leaf_wf`)) (concl th) && not(is_forall(concl th))
                          then ACCEPT_TAC(CONJUNCT1(REWRITE_RULE[tisa_leaf_wf] th)) else failwith "");
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_add (word_sub cfr (word 8)) (word 8):int64 = cfr`]) THEN
  DRV_AFTER_STATIC_TAC `word_add (d:int64) (word 16)` `d:int64` `64` `16` THEN
  DRV_AFTER_STATIC_TAC `word_add (plan:int64) (word(144 * i + 136))` `plan:int64` `144 * ns` `144 * i + 136` THEN
  W(fun (asl,w) ->
    let stp_eq = find_assum `word_add plan (word(144 * i)):int64 = stp` asl in
    FIRST_X_ASSUM(ASSUME_TAC o CONV_RULE (REWRITE_CONV[GSYM DRV_ADDR_ASSOC] THENC REWRITE_CONV[stp_eq]) o
      check (fun th -> can (find_term ((=) `word_add (plan:int64) (word(144 * i + 136))`)) (concl th) &&
                       can (find_term ((=) `s7:x86state`)) (concl th)))) THEN
  MAP_EVERY (fun j ->
    MP_TAC(SPECL [`s7:x86state`; `u:tisa_state`; `cfr:int64`; mk_small_numeral j] DRV_AFTER_FRAME) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN CONV_TAC NUM_REDUCE_CONV;
      DISCH_THEN(ASSUME_TAC o CONV_RULE(DEPTH_CONV NUM_MULT_CONV))]) [18; 19] THEN
  SUBGOAL_THEN `nonoverlapping (word pc:int64,522) (word_add ctl (word(8 * val(EL 17 (h:int64 list)))),8)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN MATCH_MP_TAC DRV_SUB_NONOVERLAP THEN
    MAP_EVERY EXISTS_TAC [`ctl:int64`; `8 * nctl`; `8 * val(EL 17 (h:int64 list))`] THEN
    SUBGOAL_THEN `val(word pc:int64) = pc` SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN DRV_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(MATCH_MP_TAC TISA_VAL_OFFSET) THEN DRV_ARITH_TAC;
    ALL_TAC];;

let drv_cx = `word_add ctl (word(8 * val(EL 17 (h:int64 list)))):int64`;;

let DRV_M5_TAC =
  W(fun (asl,w) ->
    let hp = find_assum holds_plan_tm asl and ilt = find_assum `i < ns` asl
    and hi = find_assum `EL i stepl = h:int64 list` asl
    and stp_eq = find_assum `word_add plan (word(144 * i)):int64 = stp` asl in
    let v = MP (SPECL [`i:num`; `17`] hp) (CONJ ilt (EQT_ELIM(NUM_REDUCE_CONV `17 < 18`))) in
    let v = CONV_RULE (NUM_REDUCE_CONV THENC REWRITE_CONV[hi; GSYM DRV_ADDR_ASSOC] THENC REWRITE_CONV[stp_eq]) v in
    ASSUME_TAC v) THEN
  SUBGOAL_THEN `bytes_loaded s7 (word pc) drv_mc` ASSUME_TAC THENL
   [MATCH_MP_TAC DRV_LOADED_CODE THEN EXISTS_TAC `m0:int64->byte` THEN
    REWRITE_TAC[COMPUTE_LENGTH_RULE drv_mc] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `a:int64` THEN DISCH_TAC THEN MATCH_MP_TAC DRV_AFTER_BYTE THEN
    MAP_EVERY EXISTS_TAC [`tc:tisa_state`; `u:tisa_state`; `tisa_decls (progs (val(EL 0 (h:int64 list))))`;
                          `cfr:int64`; `bw:num->int64`; `h:int64 list`; `M:int64->byte`; static_P] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[drv_static] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [`word pc:int64`; `522`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY (fun (x,v) ->
    let k = rand(rand x) in
    SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`, x), mk_binop `(+):num->num->num` `val(cfr:int64)` k))
      ASSUME_TAC THENL [MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (mk_eq(subst [x, `x:int64`] `read (memory :> bytes64 x) s7`, v)) ASSUME_TAC THENL
     [MATCH_MP_TAC DRV_AFTER_PUSHED THEN
      MAP_EVERY EXISTS_TAC [`tc:tisa_state`; `u:tisa_state`; `tisa_decls (progs (val(EL 0 (h:int64 list))))`;
                            `cfr:int64`; `bw:num->int64`; `h:int64 list`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN DRV_ARITH_TAC;
      ALL_TAC]) drv_pushed_words THEN
  MP_TAC(SPECL [`s7:x86state`; `u:tisa_state`; `cfr:int64`; `21`] DRV_AFTER_FRAME) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN(ASSUME_TAC o CONV_RULE(DEPTH_CONV NUM_MULT_CONV))] THEN
  SUBGOAL_THEN (subst [drv_cx, `x:int64`] `nonoverlapping (x:int64,8) (cfr,248)`) ASSUME_TAC THENL
   [MATCH_MP_TAC DRV_OUT_NONOVERLAP248 THEN
    MP_TAC(ISPECL [`cfr:int64`; `ctl:int64`; `8 * nctl`; drv_cx; `8 * val(EL 17 (h:int64 list))`;
                   `\a:int64. T`] DRV_AREA_BYTES) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      FIRST [MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC; DRV_ARITH_TAC];
      SIMP_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `m1 = read memory s7` THEN
  SUBGOAL_THEN `!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a ==> m1 a = (m0:int64->byte) a`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if concl th = `read memory s7 = (m1:int64->byte)` then REWRITE_TAC[SYM th]
                          else failwith "") THEN
    MATCH_MP_TAC DRV_AFTER_BYTE THEN
    MAP_EVERY EXISTS_TAC [`tc:tisa_state`; `u:tisa_state`; `tisa_decls (progs (val(EL 0 (h:int64 list))))`;
                          `cfr:int64`; `bw:num->int64`; `h:int64 list`; `M:int64->byte`; static_P] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> if concl th = `read memory s7 = (m1:int64->byte)` then REWRITE_TAC[th]
                          else failwith "") THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC DRV_STATIC_NOT_STACK THEN
    MAP_EVERY EXISTS_TAC [`pc:num`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`; `nctl:num`; `bind:int64`;
                          `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`pc:num`; `cfr:int64`; `d:int64`; `stp:int64`; `ctl:int64`; `EL 17 (h:int64 list)`;
                `tisa_fword u 19`; `tisa_fword u 18`; `m1:int64->byte`; `tisa_fword u 21`;
                `rbxv:int64`; `rbpv:int64`; `r12v:int64`; `r13v:int64`; `r14v:int64`; `r15v:int64`]
               (REWRITE_RULE[SOME_FLAGS] DRV_POST)) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  TISA_BIGSTEP_TAC "s8";;
let DRV_M6_COMMON_TAC =
  SUBGOAL_THEN `!a. ~drv_stack cfr a ==> read memory s8 a = drv_after ctl (h:int64 list) u a` ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `read memory s8` then REWRITE_TAC[th]
                          else failwith "") THEN
    REWRITE_TAC[drv_after] THEN
    MP_TAC(ISPECL [`\a:int64. ~drv_stack cfr a`; `m1:int64->byte`; `tmem u`; drv_cx; `tisa_fword u 19`]
                  DRV_WRITE_CONG) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [X_GEN_TAC `b:int64` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term ((=) `tisa_saved`)) (concl th) && can (find_term ((=) `m1:int64->byte`)) (concl th))) THEN
      MATCH_MP_TAC DRV_NOT_SAVED THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `read memory s8`)) THEN
  SUBGOAL_THEN `!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a
                    ==> drv_after ctl (h:int64 list) u a = (m0:int64->byte) a` ASSUME_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN REWRITE_TAC[drv_after] THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `val(word_add ctl (word(8 * val(EL 17 (h:int64 list)))):int64) =
                      val ctl + 8 * val(EL 17 h)` SUBST1_TAC THENL
         [MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC; DRV_ARITH_TAC];
        MATCH_MP_TAC DRV_CTL_NOT_STATIC THEN
        MAP_EVERY EXISTS_TAC [`pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `nctl:num`; `bind:int64`;
                              `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`] THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `~drv_stack cfr a` ASSUME_TAC THENL
     [MATCH_MP_TAC DRV_STATIC_NOT_STACK THEN
      MAP_EVERY EXISTS_TAC [`pc:num`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`; `nctl:num`; `bind:int64`;
                            `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(m1:int64->byte) a = tmem u a` (fun th -> REWRITE_TAC[SYM th]) THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term ((=) `tisa_saved`)) (concl th) && can (find_term ((=) `m1:int64->byte`)) (concl th))) THEN
      MATCH_MP_TAC DRV_NOT_SAVED THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term ((=) `drv_static`)) (concl th) && can (find_term ((=) `m1:int64->byte`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC];;
let DRV_COND_TAC case =
  FIRST_X_ASSUM(fun th -> if is_cond(concl th) then STRIP_ASSUME_TAC(REWRITE_RULE[ASSUME case] th)
                          else failwith "");;

let DRV_SEM_STEP_TAC =
  REWRITE_TAC[drv_sem] THEN
  FIRST_ASSUM(fun th -> if concl th = `~(val(budget:int64) < val(used:int64))` then REWRITE_TAC[th]
                        else failwith "") THEN
  MAP_EVERY EXISTS_TAC [`tc:tisa_state`; `k:num`; `u:tisa_state`] THEN ASM_REWRITE_TAC[];;

let DRV_NOTFIRED_TAC =
  DRV_COND_TAC `~(tisa_fword u 18 = word 1)` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC) THEN
  EXISTS_TAC `(tisa_fword u 18, i:num, drv_after ctl (h:int64 list) u, tisa_fword u 21)` THEN
  ASM_REWRITE_TAC[] THEN DRV_SEM_STEP_TAC;;

let DRV_FIRED_TAC =
  DRV_COND_TAC `tisa_fword u 18 = word 1` THEN
  SUBGOAL_THEN `word_add stp (word 144):int64 = word_add plan (word(144 * (i + 1)))` ASSUME_TAC THENL
   [EXPAND_TAC "stp" THEN REWRITE_TAC[DRV_ADDR_ASSOC] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `read RBP s8 = word_add stp (word 144)`
                          then ASSUME_TAC(REWRITE_RULE[ASSUME `word_add stp (word 144):int64 = word_add plan (word(144 * (i + 1)))`] th)
                          else failwith "") THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`; `drv_after ctl (h:int64 list) u`; `tisa_fword u 21`] o
    check (fun th -> is_forall(concl th) &&
             can (find_term (fun t -> is_const t && fst(dest_const t) = "ensures")) (concl th))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ASSUME `SUC (LENGTH (t:(int64 list)list)) + i = ns`) THEN ARITH_TAC;
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `SUC j` o check (fun th -> is_forall(concl th) &&
         can (find_term ((=) `CONS (h:int64 list) t`)) (concl th))) THEN
      REWRITE_TAC[LT_SUC; EL; TL; ARITH_RULE `i + SUC j = (i + 1) + j`] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN TISA_BIGSTEP_TAC "s9" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC) THEN
  EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN ASM_REWRITE_TAC[] THEN DRV_SEM_STEP_TAC;;

let DRV_REFUSE_TAC =
  ENSURES_INIT_TAC "s0" THEN
  DRV_LOADED_TAC "s0" `pc:num` `drv_mc` `522` THEN
  DRV_STATIC_READ_TAC "s0" `word_add (d:int64) (word 8)` `d:int64` `64` `8` THEN
  DRV_STATIC_READ_TAC "s0" `word_add (d:int64) (word 40)` `d:int64` `64` `40` THEN
  SUBGOAL_THEN `~(val (used:int64) < val (budget:int64) \/ val(word_sub used budget) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DRV_FUEL_COND]; ALL_TAC] THEN
  X86_STEPS_TAC DRV_EXEC (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC) THEN
  EXISTS_TAC `(word 3:int64, i:num, M:int64->byte, used:int64)` THEN
  ASM_REWRITE_TAC[drv_sem];;

let DRV_LOOP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_holds]) THEN
  LIST_INDUCT_TAC THENL
   [DRV_BASE_TAC;
    DRV_CONS_SETUP_TAC THEN
    ASM_CASES_TAC `val(budget:int64) < val(used:int64)` THENL
     [DRV_REFUSE_TAC;
      DRV_M1_TAC THEN DRV_M2_TAC THEN DRV_M3_TAC THEN DRV_M4_TAC THEN DRV_M5_TAC THEN
      DRV_M6_COMMON_TAC THEN
      ASM_CASES_TAC `tisa_fword u 18 = word 1` THENL [DRV_FIRED_TAC; DRV_NOTFIRED_TAC]]];;
let DRV_LOOP = prove(drv_loop_goal, DRV_LOOP_TAC);;

(* ------------------------------------------------------------------------- *)
(* DRV_PROLOGUE: from the entry, the caller's registers saved above the      *)
(* child frame, the descriptor in R14, the plan's first step in RBP and the  *)
(* receipt in the frame's spare word.                                        *)
(* ------------------------------------------------------------------------- *)

let DRV_PROLOGUE = prove
 (`!pc cfr d plan used rbxv rbpv r12v r13v r14v r15v m.
     val cfr + 256 <= 2 EXP 64 /\
     nonoverlapping (word pc:int64,522) (cfr,248) /\
     nonoverlapping (d:int64,64) (cfr,248)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) drv_mc /\ read RIP s = word pc /\
               read RSP s = word_add cfr (word 248) /\ read RDI s = d /\
               read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
               read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
               read memory s = m /\
               read (memory :> bytes64 d) s = plan /\
               read (memory :> bytes64 (word_add d (word 48))) s = used)
          (\s. read RIP s = word(pc + 35) /\ read RSP s = cfr /\ read R14 s = d /\
               read RBP s = plan /\
               read (memory :> bytes64 (word_add cfr (word 168))) s = used /\
               read (memory :> bytes64 (word_add cfr (word 240))) s = rbxv /\
               read (memory :> bytes64 (word_add cfr (word 232))) s = rbpv /\
               read (memory :> bytes64 (word_add cfr (word 224))) s = r12v /\
               read (memory :> bytes64 (word_add cfr (word 216))) s = r13v /\
               read (memory :> bytes64 (word_add cfr (word 208))) s = r14v /\
               read (memory :> bytes64 (word_add cfr (word 200))) s = r15v /\
               (!a. ~drv_stack cfr a ==> read memory s a = m a))
          (MAYCHANGE [RIP; RSP; RAX; RBP; R14] ,,
           MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  TISA_STEPS_TAC DRV_EXEC (1--11) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
  MAP_EVERY (fun k -> MP_TAC(SPECL [`cfr:int64`; mk_small_numeral k] DRV_STK8_ADD) THEN
                      ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
                      REWRITE_TAC[] THEN DISCH_TAC)
    [168; 200; 208; 216; 224; 232; 240] THEN
  REPEAT(W(fun (asl,w) ->
    MP_TAC(PART_MATCH (lhand o rand) (SPEC `cfr:int64` DRV_WRITE_STACK) (lhs w))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* DRV_EPILOGUE: from `done`, the receipt and the step pointer written back  *)
(* to the descriptor, the caller's registers restored, the return.           *)
(* ------------------------------------------------------------------------- *)

let DRV_EPILOGUE = prove
 (`!pc cfr d stp status used rbxv rbpv r12v r13v r14v r15v ret m.
     nonoverlapping (word pc:int64,522) (word_add d (word 48),8) /\
     nonoverlapping (word pc:int64,522) (word_add d (word 56),8) /\
     nonoverlapping (word_add d (word 48),8) (cfr,256) /\
     nonoverlapping (word_add d (word 56),8) (cfr,256)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) drv_mc /\ read RIP s = word(pc + 485) /\
               read RSP s = cfr /\ read R14 s = d /\ read RBP s = stp /\ read RAX s = status /\
               read memory s = m /\
               read (memory :> bytes64 (word_add cfr (word 168))) s = used /\
               read (memory :> bytes64 (word_add cfr (word 240))) s = rbxv /\
               read (memory :> bytes64 (word_add cfr (word 232))) s = rbpv /\
               read (memory :> bytes64 (word_add cfr (word 224))) s = r12v /\
               read (memory :> bytes64 (word_add cfr (word 216))) s = r13v /\
               read (memory :> bytes64 (word_add cfr (word 208))) s = r14v /\
               read (memory :> bytes64 (word_add cfr (word 200))) s = r15v /\
               read (memory :> bytes64 (word_add cfr (word 248))) s = ret)
          (\s. read RIP s = ret /\ read RSP s = word_add cfr (word 256) /\ read RAX s = status /\
               read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\ read R13 s = r13v /\
               read R14 s = r14v /\ read R15 s = r15v /\
               read memory s = write (bytes64 (word_add d (word 56))) stp
                                 (write (bytes64 (word_add d (word 48))) used m))
          (MAYCHANGE [RIP; RSP; RDX; RBX; RBP; R12; R13; R14; R15] ,,
           MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  TISA_STEPS_TAC DRV_EXEC (1--11) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (word_add cfr (word 200)) (word 8)) (word 8):int64 = word_add cfr (word 216)`]) THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE) THEN TRY MONOTONE_MAYCHANGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Composing ensures: weakening, ghosts, pure facts; areas apart.            *)
(* ------------------------------------------------------------------------- *)

let DRV_ENSURES_WEAKEN = prove
 (`!step (P:A->bool) Q C P' Q' C'.
     ensures step P Q C
     ==> (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s) /\ C subsumed C'
     ==> ensures step P' Q' C'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC `C:A->A->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `P:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC `Q:A->bool` THEN ASM_REWRITE_TAC[]);;

let DRV_ENSURES_GHOST = prove
 (`!step (P:A->bool) (G:B->A->bool) Q C.
     (!s. P s ==> ?x. G x s) /\ (!x. ensures step (G x) Q C)
     ==> ensures step P Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let DRV_ENSURES_PURE = prove
 (`!step (P:A->bool) Q C p. (p ==> ensures step P Q C) ==> ensures step (\s. p /\ P s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let DRV_APART_NONOVERLAP = prove
 (`!(a:int64) m (b:int64) n (x:int64) k l (y:int64) k' l'.
     val a + m <= 2 EXP 64 /\ val b + n <= 2 EXP 64 /\ drv_apart a m b n /\
     val x = val a + k /\ k + l <= m /\ val y = val b + k' /\ k' + l' <= n
     ==> nonoverlapping (x,l) (y,l')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[nonoverlapping; DIMINDEX_64] THEN
  ASM_CASES_TAC `l = 0 \/ l' = 0` THENL
   [MATCH_MP_TAC NONOVERLAPPING_MODULO_TRIVIAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  RULE_ASSUM_TAC(REWRITE_RULE[drv_apart; DE_MORGAN_THM]) THEN ASM_ARITH_TAC);;

(* The caller's return address: static, and above the driver's stack. *)
let DRV_RET_SLOT = prove
 (`!pc cfr d plan ns bind nbw leaves nl lpc lmc i.
     val cfr + 256 <= 2 EXP 64 /\ i < 8
     ==> drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc
           (word_add (word_add cfr (word 248)) (word i)) /\
         ~drv_stack cfr (word_add (word_add cfr (word 248)) (word i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add cfr (word 248):int64) = val cfr + 248` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`word_add cfr (word 248):int64`; `i:num`] TISA_VAL_OFFSET) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[drv_static] THEN REPEAT DISJ2_TAC THEN REWRITE_TAC[drv_in] THEN ASM_ARITH_TAC;
    REWRITE_TAC[drv_stack] THEN ASM_ARITH_TAC]);;

let is_ensures tm =
  try fst(dest_const(fst(strip_comb tm))) = "ensures" with Failure _ -> false;;

let ensures_arg n (asl,w) =
  let th = snd(find (fun (_,th) -> is_ensures(concl th)) asl) in
  el n (snd(strip_comb(concl th)));;

(* nonoverlapping (x,l) (y,l') from drv_apart a m b n, both orders. *)
let DRV_APART_TAC a m b n k k' =
  let fin = MAP_EVERY EXISTS_TAC [a; m; b; n; k; k'] THEN ASM_REWRITE_TAC[] THEN DRV_ARITH_TAC in
  FIRST [MATCH_MP_TAC DRV_APART_NONOVERLAP THEN fin;
         ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN MATCH_MP_TAC DRV_APART_NONOVERLAP THEN fin];;

(* ------------------------------------------------------------------------- *)
(* DRV_CORRECT_FRAME: the whole driver, from its entry to its return, with   *)
(* the child frame at cfr (the caller's stack pointer is cfr + 248).         *)
(* ------------------------------------------------------------------------- *)

let drv_correct_frame_goal = `!progs lpc lmc nl pc cfr d plan ns ctl nctl bind nbw leaves bw stepl budget used0 m0
    ret rbxv rbpv r12v r13v r14v r15v.
     (!j. j < nl ==> tisa_leaf_wf (progs j) /\ tisa_leaf_spec (progs j) (lmc j) (lpc j)) /\
     drv_layout pc cfr d plan ns ctl nctl bind nbw leaves nl lpc lmc /\
     ALL (drv_step_ok progs pc cfr d plan ns nctl bind nbw leaves nl lpc lmc bw) stepl /\
     drv_holds m0 d plan ns ctl bind leaves budget used0 stepl bw nbw lpc nl /\
     drv_code m0 pc drv_mc /\
     (!j. j < nl ==> drv_code m0 (lpc j) (lmc j))
     ==> ensures x86
          (\s. read RIP s = word pc /\ read RSP s = word_add cfr (word 248) /\ read RDI s = d /\
               read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
               read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
               read memory s = m0 /\
               read (memory :> bytes64 (word_add cfr (word 248))) s = ret)
          (\s. read RIP s = ret /\ read RSP s = word_add cfr (word 256) /\
               read RBX s = rbxv /\ read RBP s = rbpv /\ read R12 s = r12v /\
               read R13 s = r13v /\ read R14 s = r14v /\ read R15 s = r15v /\
               ?res. drv_sem progs bw ctl budget cfr stepl 0 m0 used0 res /\
                     read RAX s = FST res /\
                     (!a. ~drv_stack cfr a ==> read memory s a = drv_final d plan res a) /\
                     (!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a /\
                          ~drv_in a (word_add d (word 48)) 16
                          ==> read memory s a = m0 a))
          (MAYCHANGE [RIP; RSP; RAX; RBX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                      R12; R13; R14; R15; RBP] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory])`;;

let DRV_TOP_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_layout]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_holds]) THEN
  ASM_CASES_TAC `drv_word m0 (word_add cfr (word 248)) = (ret:int64)` THENL
   [ALL_TAC;
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `\s:x86state. F` THEN
    REWRITE_TAC[ENSURES_TRIVIAL] THEN X_GEN_TAC `s:x86state` THEN
    REWRITE_TAC[DRV_READ64] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `read memory s = (m0:int64->byte)`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
                                            can (find_term ((=) `ret:int64`)) (concl th))) THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `val(word_sub cfr (word 48):int64) = val cfr - 48` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_SP_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word pc:int64) = pc` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN DRV_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add d (word 48):int64) = val d + 48 /\
                val(word_add d (word 56):int64) = val d + 56` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`progs:num->tisa_prog`; `lpc:num->num`; `lmc:num->byte list`; `nl:num`; `pc:num`;
                `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`; `nctl:num`; `bind:int64`;
                `nbw:num`; `leaves:int64`; `bw:num->int64`; `stepl:(int64 list)list`; `budget:int64`;
                `used0:int64`; `m0:int64->byte`; `rbxv:int64`; `rbpv:int64`; `r12v:int64`; `r13v:int64`;
                `r14v:int64`; `r15v:int64`] DRV_LOOP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`stepl:(int64 list)list`; `0`; `m0:int64->byte`; `used0:int64`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ADD_CLAUSES]; DISCH_TAC];;

let DRV_TOP_PRO_TAC =
  MP_TAC(SPECL [`pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `used0:int64`; `rbxv:int64`; `rbpv:int64`;
                `r12v:int64`; `r13v:int64`; `r14v:int64`; `r15v:int64`; `m0:int64->byte`] DRV_PROLOGUE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DRV_ARITH_TAC;
      DRV_APART_TAC `word_sub cfr (word 48):int64` `304` `word pc:int64` `522` `48` `0`;
      DRV_APART_TAC `word_sub cfr (word 48):int64` `304` `d:int64` `64` `48` `0`];
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP DRV_ENSURES_WEAKEN)] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[DRV_READ64] THEN
    MATCH_MP_TAC DRV_LOADED_CODE THEN EXISTS_TAC `m0:int64->byte` THEN
    ASM_REWRITE_TAC[COMPUTE_LENGTH_RULE drv_mc];
    X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

let DRV_TOP_EPI_PRE_TAC =
  X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DRV_LOADED_CODE THEN EXISTS_TAC `m0:int64->byte` THEN
    ASM_REWRITE_TAC[COMPUTE_LENGTH_RULE drv_mc] THEN X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~drv_stack cfr a /\ drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC DRV_IN_NOT_STACK THEN MAP_EVERY EXISTS_TAC [`word pc:int64`; `522`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[drv_static] THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[]];
    REWRITE_TAC[DRV_READ64] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `ret:int64`)) THEN
    MATCH_MP_TAC DRV_WORD_AGREE THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`pc:num`; `cfr:int64`; `d:int64`; `plan:int64`; `ns:num`; `bind:int64`; `nbw:num`;
                  `leaves:int64`; `nl:num`; `lpc:num->num`; `lmc:num->byte list`; `i:num`] DRV_RET_SLOT) THEN
    ASM_SIMP_TAC[]];;

let DRV_TOP_EPI_POST_TAC =
  X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `a:int64` THEN DISCH_TAC THEN REWRITE_TAC[drv_final] THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\a:int64. ~drv_stack cfr a`;
       `write (bytes64 (word_add d (word 48))) (SND(SND(SND(res:int64#num#(int64->byte)#int64)))) (m:int64->byte)`;
       `write (bytes64 (word_add d (word 48))) (SND(SND(SND(res:int64#num#(int64->byte)#int64))))
              (FST(SND(SND(res:int64#num#(int64->byte)#int64))))`;
       `word_add d (word 56):int64`;
       `word_add plan (word(144 * FST(SND(res:int64#num#(int64->byte)#int64)))):int64`] DRV_WRITE_CONG)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(BETA_RULE(ISPECL
        [`\a:int64. ~drv_stack cfr a`; `m:int64->byte`;
         `FST(SND(SND(res:int64#num#(int64->byte)#int64)))`; `word_add d (word 48):int64`;
         `SND(SND(SND(res:int64#num#(int64->byte)#int64)))`] DRV_WRITE_CONG)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
    SUBGOAL_THEN `val(a:int64) < val(d:int64) + 48 \/ val d + 64 <= val a` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
                                              can (find_term ((=) `drv_in`)) (concl th))) THEN
      REWRITE_TAC[drv_in] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
           ANTS_TAC THENL
            [ASM_REWRITE_TAC[] THEN
             FIRST_ASSUM(MP_TAC o check (fun th -> is_disj(concl th) &&
                                                   can (find_term ((=) `val(a:int64)`)) (concl th))) THEN
             DRV_ARITH_TAC;
             DISCH_THEN SUBST1_TAC]) THEN
    SUBGOAL_THEN `~drv_stack cfr a` ASSUME_TAC THENL
     [MATCH_MP_TAC DRV_STATIC_NOT_STACK THEN
      MAP_EVERY EXISTS_TAC [`pc:num`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`; `nctl:num`;
                            `bind:int64`; `nbw:num`; `leaves:int64`; `nl:num`; `lpc:num->num`;
                            `lmc:num->byte list`] THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]]];;

let DRV_TOP_EPI_TAC =
  MATCH_MP_TAC(INST_TYPE [`:(int64#num#(int64->byte)#int64)#(int64->byte)`,`:B`] DRV_ENSURES_GHOST) THEN
  EXISTS_TAC
   `\(g:(int64#num#(int64->byte)#int64)#(int64->byte)) (s:x86state).
      (drv_sem progs bw ctl budget cfr stepl 0 m0 used0 (FST g) /\
       (!a. ~drv_stack cfr a ==> SND g a = FST(SND(SND(FST g))) a) /\
       (!a. drv_static pc cfr d plan ns bind nbw leaves nl lpc lmc a
            ==> FST(SND(SND(FST g))) a = m0 a)) /\
      read RIP s = word(pc + 485) /\ read RSP s = cfr /\ read R14 s = d /\
      read RBP s = word_add plan (word(144 * FST(SND(FST g)))) /\ read RAX s = FST(FST g) /\
      read memory s = SND g /\
      read (memory :> bytes64 (word_add cfr (word 168))) s = SND(SND(SND(FST g))) /\
      read (memory :> bytes64 (word_add cfr (word 240))) s = rbxv /\
      read (memory :> bytes64 (word_add cfr (word 232))) s = rbpv /\
      read (memory :> bytes64 (word_add cfr (word 224))) s = r12v /\
      read (memory :> bytes64 (word_add cfr (word 216))) s = r13v /\
      read (memory :> bytes64 (word_add cfr (word 208))) s = r14v /\
      read (memory :> bytes64 (word_add cfr (word 200))) s = r15v` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN
    EXISTS_TAC `(res:int64#num#(int64->byte)#int64, read memory s)` THEN
    REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`res:int64#num#(int64->byte)#int64`; `m:int64->byte`] THEN
  BETA_TAC THEN REWRITE_TAC[FST; SND] THEN
  MATCH_MP_TAC DRV_ENSURES_PURE THEN STRIP_TAC THEN
  MP_TAC(SPECL [`pc:num`; `cfr:int64`; `d:int64`;
                `word_add plan (word(144 * FST(SND(res:int64#num#(int64->byte)#int64)))):int64`;
                `FST(res:int64#num#(int64->byte)#int64)`;
                `SND(SND(SND(res:int64#num#(int64->byte)#int64)))`;
                `rbxv:int64`; `rbpv:int64`; `r12v:int64`; `r13v:int64`; `r14v:int64`; `r15v:int64`;
                `ret:int64`; `m:int64->byte`] DRV_EPILOGUE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DRV_APART_TAC `d:int64` `64` `word pc:int64` `522` `48` `0`;
      DRV_APART_TAC `d:int64` `64` `word pc:int64` `522` `56` `0`;
      DRV_APART_TAC `word_sub cfr (word 48):int64` `304` `d:int64` `64` `48` `48`;
      DRV_APART_TAC `word_sub cfr (word 48):int64` `304` `d:int64` `64` `48` `56`];
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP DRV_ENSURES_WEAKEN)] THEN
  REPEAT CONJ_TAC THENL
   [DRV_TOP_EPI_PRE_TAC;
    DRV_TOP_EPI_POST_TAC;
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

let DRV_CORRECT_FRAME = prove(drv_correct_frame_goal,
  DRV_TOP_SETUP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN W(fun g -> EXISTS_TAC (ensures_arg 2 g)) THEN
  CONJ_TAC THENL [REWRITE_TAC[SOME_FLAGS] THEN MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN W(fun g -> EXISTS_TAC (ensures_arg 1 g)) THEN
    CONJ_TAC THENL [REWRITE_TAC[SOME_FLAGS] THEN MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [DRV_TOP_PRO_TAC; FIRST_ASSUM ACCEPT_TAC];
    DRV_TOP_EPI_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The footprint. A step's leaf runs on a state whose region words are the  *)
(* step's bindings (DRV_CHILD_REGIONS); a plan changes the memory outside    *)
(* the driver's stack only in its steps' writable regions and payload words *)
(* (DRV_SEM_KEEPS).                                                          *)
(* ------------------------------------------------------------------------- *)

let DRV_CHILD_REGIONS = prove
 (`!bw ctl budget cfr st m used t.
     drv_child bw ctl budget cfr st m used t
     ==> tregs t 0 = cfr /\
         !r. r < 9 ==> tisa_base t r = drv_base bw st r /\ tisa_len t r = drv_len bw st r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_child] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[drv_regs];
    REWRITE_TAC[tisa_base; tisa_len] THEN CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[ARITH] THEN REWRITE_TAC[drv_fw; drv_base; drv_len] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ADD_CLAUSES]]);;

(* One step: outside the stack, its writable regions and its payload word,
   the plan's memory after the step is the memory before it. *)
let DRV_STEP_KEEPS = prove
 (`!prog bw ctl nctl budget cfr st m used t k u a.
     drv_child bw ctl budget cfr st m used t /\ tisa_leaf_wf prog /\ tisa_entry_ok prog t /\
     tisa_run prog t = TStop k u /\
     val ctl + 8 * nctl <= 2 EXP 64 /\ val(EL 17 st) < nctl /\
     ~drv_stack cfr a /\
     (!r. tisa_rw (tisa_decls prog) r ==> ~drv_in a (drv_base bw st r) (val(drv_len bw st r))) /\
     ~drv_in a (word_add ctl (word(8 * val(EL 17 st)))) 8
     ==> drv_after ctl st u a = m a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DRV_CHILD_REGIONS) THEN
  SUBGOAL_THEN `tisa_keeps (tisa_decls prog) t u` MP_TAC THENL
   [MATCH_MP_TAC TISA_RUN_KEEPS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[tisa_keeps] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add ctl (word(8 * val(EL 17 (st:int64 list)))):int64) =
                val ctl + 8 * val(EL 17 st)` ASSUME_TAC THENL
   [MATCH_MP_TAC TISA_VAL_OFFSET THEN
    UNDISCH_TAC `val(ctl:int64) + 8 * nctl <= 2 EXP 64` THEN UNDISCH_TAC `val(EL 17 (st:int64 list)) < nctl` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[drv_after] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `~drv_in a (word_add ctl (word(8 * val(EL 17 (st:int64 list))))) 8` THEN
    ASM_REWRITE_TAC[drv_in] THEN
    UNDISCH_TAC `val(ctl:int64) + 8 * nctl <= 2 EXP 64` THEN UNDISCH_TAC `val(EL 17 (st:int64 list)) < nctl` THEN
    ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `tmem u a = tmem t a` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tisa_writable`)) (concl th))) THEN
    MATCH_MP_TAC DRV_NOT_WRITABLE THEN
    MAP_EVERY EXISTS_TAC [`cfr:int64`; `bw:num->int64`; `st:int64 list`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ACCEPT_TAC(CONJUNCT1(REWRITE_RULE[tisa_leaf_wf] (ASSUME `tisa_leaf_wf prog`)));
      UNDISCH_TAC `~drv_stack cfr a` THEN REWRITE_TAC[drv_stack] THEN ARITH_TAC];
    FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [drv_child] o
      check (fun th -> can (find_term ((=) `drv_child`)) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let DRV_SEM_KEEPS = prove
 (`!progs bw ctl nctl budget cfr sts i m used res.
     drv_sem progs bw ctl budget cfr sts i m used res /\
     val ctl + 8 * nctl <= 2 EXP 64 /\
     (!st. MEM st sts ==> tisa_leaf_wf (progs (val(EL 0 st))) /\ val(EL 17 st) < nctl)
     ==> !a. ~drv_stack cfr a /\
             (!st r. MEM st sts /\ tisa_rw (tisa_decls (progs (val(EL 0 st)))) r
                     ==> ~drv_in a (drv_base bw st r) (val(drv_len bw st r))) /\
             (!st. MEM st sts ==> ~drv_in a (word_add ctl (word(8 * val(EL 17 st)))) 8)
             ==> FST(SND(SND res)) a = m a`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[drv_sem] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_sem; MEM] THEN
  COND_CASES_TAC THENL [STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `tc:tisa_state` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `u:tisa_state` STRIP_ASSUME_TAC)))
    STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
  SUBGOAL_THEN `drv_after ctl h u a = (m:int64->byte) a` ASSUME_TAC THENL
   [MATCH_MP_TAC DRV_STEP_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`progs (val(EL 0 (h:int64 list))):tisa_prog`; `bw:num->int64`; `nctl:num`;
                          `budget:int64`; `cfr:int64`; `used:int64`; `tc:tisa_state`; `k:num`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`; `drv_after ctl h u`; `tisa_fword u 21`;
                                  `res:int64#num#(int64->byte)#int64`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `drv_sem`)) (concl th))) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a:int64`) THEN ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Two steps that both FIRED, unfolded.                                      *)
(* ------------------------------------------------------------------------- *)

let DRV_SEM_TWO_FIRED = prove
 (`!progs bw ctl budget cfr st1 st2 m used res.
     drv_sem progs bw ctl budget cfr [st1; st2] 0 m used res /\ FST res = word 1
     ==> ?t1 k1 u1 t2 k2 u2.
           drv_child bw ctl budget cfr st1 m used t1 /\
           tisa_entry_ok (progs (val(EL 0 st1))) t1 /\
           tisa_run (progs (val(EL 0 st1))) t1 = TStop k1 u1 /\ tisa_fword u1 18 = word 1 /\
           drv_child bw ctl budget cfr st2 (drv_after ctl st1 u1) (tisa_fword u1 21) t2 /\
           tisa_entry_ok (progs (val(EL 0 st2))) t2 /\
           tisa_run (progs (val(EL 0 st2))) t2 = TStop k2 u2 /\ tisa_fword u2 18 = word 1 /\
           res = (word 1, 2, drv_after ctl st2 u2, tisa_fword u2 21)`,
  let NOT_FIRED_TAC =
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `res:int64#num#(int64->byte)#int64`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `FST:int64#num#(int64->byte)#int64->int64`))
                                                 (concl th))) THEN
    ASM_REWRITE_TAC[FST] THEN CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[] in
  REPEAT GEN_TAC THEN REWRITE_TAC[drv_sem] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `val(budget:int64) < val(used:int64)` THEN ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN NOT_FIRED_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t1:tisa_state` (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `u1:tisa_state`
       STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  ASM_CASES_TAC `tisa_fword u1 18 = word 1` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; DISCH_TAC THEN NOT_FIRED_TAC] THEN
  ASM_CASES_TAC `val(budget:int64) < val(tisa_fword u1 21)` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN NOT_FIRED_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:tisa_state` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `u2:tisa_state`
       STRIP_ASSUME_TAC))) THEN
  ASM_CASES_TAC `tisa_fword u2 18 = word 1` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(concl th))) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THENL [ALL_TAC; NOT_FIRED_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t1:tisa_state`; `k1:num`; `u1:tisa_state`;
                        `t2:tisa_state`; `k2:num`; `u2:tisa_state`] THEN
  ASM_REWRITE_TAC[]);;

let DRV_APART_SYM = prove
 (`!(a:int64) m (b:int64) n. drv_apart a m b n <=> drv_apart b n a m`,
  REWRITE_TAC[drv_apart] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* DRV_CORRECT: the driver called with its stack pointer at stackpointer.    *)
(* Its plan's result is drv_sem's, returned in RAX and written back to the   *)
(* descriptor; the caller's registers are restored; memory changes only in   *)
(* the driver's stack, the descriptor's two output words, and the steps'     *)
(* writable regions and payload words.                                       *)
(* ------------------------------------------------------------------------- *)

let DRV_CORRECT = prove
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
  MP_TAC(SPECL [`progs:num->tisa_prog`; `lpc:num->num`; `lmc:num->byte list`; `nl:num`; `pc:num`;
                `word_sub stackpointer (word 248):int64`; `d:int64`; `plan:int64`; `ns:num`; `ctl:int64`;
                `nctl:num`; `bind:int64`; `nbw:num`; `leaves:int64`; `bw:num->int64`;
                `stepl:(int64 list)list`; `budget:int64`; `used0:int64`; `m0:int64->byte`; `ret:int64`;
                `rbxv:int64`; `rbpv:int64`; `r12v:int64`; `r13v:int64`; `r14v:int64`; `r15v:int64`]
               DRV_CORRECT_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_sub stackpointer (word 248)) (word 248):int64 = stackpointer`;
              WORD_RULE `word_add (word_sub stackpointer (word 248)) (word 256):int64 = word_add stackpointer (word 8)`] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP DRV_ENSURES_WEAKEN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [drv_layout]) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:x86state` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `res:int64#num#(int64->byte)#int64` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `a:int64` THEN STRIP_TAC THEN
    SUBGOAL_THEN `val(word_add d (word 48):int64) = val d + 48 /\
                  val(word_add d (word 56):int64) = val d + 56` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC TISA_VAL_OFFSET THEN DRV_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(a:int64) < val(d:int64) + 48 \/ val d + 64 <= val a` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
                                              can (find_term ((=) `drv_in`)) (concl th) &&
                                              can (find_term ((=) `word_add d (word 48):int64`)) (concl th))) THEN
      REWRITE_TAC[drv_in] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `drv_final`)) (concl th)
                            then REWRITE_TAC[MATCH_MP th (ASSUME `~drv_stack (word_sub stackpointer (word 248)) a`)]
                            else failwith "") THEN
    REWRITE_TAC[drv_final] THEN
    REPEAT(W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) DRV_WRITE64_OUTSIDE (lhs w))) THEN
           ANTS_TAC THENL
            [ASM_REWRITE_TAC[] THEN
             FIRST_ASSUM(MP_TAC o check (fun th -> is_disj(concl th) &&
                                                   can (find_term ((=) `val(a:int64)`)) (concl th))) THEN
             DRV_ARITH_TAC;
             DISCH_THEN SUBST1_TAC]) THEN
    MP_TAC(SPECL [`progs:num->tisa_prog`; `bw:num->int64`; `ctl:int64`; `nctl:num`; `budget:int64`;
                  `word_sub stackpointer (word 248):int64`; `stepl:(int64 list)list`; `0`; `m0:int64->byte`;
                  `used0:int64`; `res:int64#num#(int64->byte)#int64`] DRV_SEM_KEEPS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `st:int64 list` THEN DISCH_TAC THEN
      SUBGOAL_THEN `drv_step_ok progs pc (word_sub stackpointer (word 248)) d plan ns nctl bind nbw leaves nl lpc lmc bw st`
      MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM ALL_MEM] o
          check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "ALL")) (concl th))) THEN
        DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[drv_step_ok] THEN STRIP_TAC THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `val(EL 0 (st:int64 list))` o
          check (fun th -> is_forall(concl th) && can (find_term ((=) `tisa_leaf_spec`)) (concl th))) THEN
        ASM_SIMP_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `17` o
          check (fun th -> is_forall(concl th) && can (find_term ((=) `nctl:num`)) (concl th) &&
                           can (find_term ((=) `10`)) (concl th))) THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]];
      DISCH_THEN(MATCH_MP_TAC) THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC]);;
