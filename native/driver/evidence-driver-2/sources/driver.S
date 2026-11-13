// driver.S -- runs a call plan over t-ISA p1 leaf images.
//
//   uint64_t tisa_drive(TcDrive *d);                     (SysV x86-64)
//
// A plan is an array of steps. Each step calls one leaf with a child frame
// (tisa.h's TcIsaRuntimeFrame) that the driver builds on its own stack, then
// stores the leaf's payload (frame word 19) into a control word. The leaf's
// outcome is its frame word 18; the first step whose outcome is not FIRED (1)
// ends the plan with that outcome. A step is called only while the receipt is
// within the allowance; otherwise the plan ends with INVALID_INPUT (3), which
// is what entry validation would say. The receipt (frame word 21) passes from
// each step to the next, whatever its outcome.
//
// Descriptor d, 8-byte words:
//    0 plan      first step               4 leaves   leaf entry addresses
//    1 plan_end  one past the last step   5 budget   fuel allowance
//    2 ctl       control words            6 used     receipt (in; out on return)
//    3 bind      binding words            7 at       out: the step that ended
//                                                    the plan (plan_end if all fired)
// Step, 18 words (144 bytes):
//    0      leaf: index into leaves
//    1..9   region r of the child frame is (bind[w], bind[w+1]), w = word 1+r
//   10, 11  arg0, arg1: control word indices for frame words 22, 23
//   12..16  v1..v5: control word indices for the entry registers rsi..r9
//   17      dst: the control word index the payload is stored to
// Returns the plan's outcome.
//
// Leaves are entered by `enter` (push the entry, ret) and return with ret.
// rbx r12 r13 (v9..v11), rax r10 r11 (v8, v6, v7) are zero at entry, so a
// leaf's entry state is determined by the plan; rbp r14 r15 hold the driver's
// state across calls (a p1 image preserves them, and rdi).
//
// There is no indirect CALL or JMP (FF /2, FF /4): the x86 model the proofs
// use (s2n-bignum) takes their target as relative to the next instruction,
// which on x86 it is not. `call enter` pushes the return address and
// `enter: push r15; ret` jumps to the leaf.
//
// Supported profile: user-mode shadow stacks (CET SHSTK) disabled. Under
// SHSTK the ret in `enter` faults (#CP): it returns to the leaf, while the
// shadow stack holds the address `call enter` pushed. (IBT does not check
// a ret.)

        .intel_syntax noprefix
        .text
        .globl  tisa_drive
        .type   tisa_drive, @function

#define STEP    144

tisa_drive:
        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15
        sub     rsp, 200                // the child frame at rsp; rsp stays 16-aligned
        mov     r14, rdi                // r14: the descriptor
        mov     rbp, [r14]              // rbp: the current step
        mov     rax, [r14 + 48]
        mov     [rsp + 168], rax        // the receipt lives in the child frame's fuel_used

loop:
        cmp     rbp, [r14 + 8]
        je      fired                   // every step fired
        mov     rax, [rsp + 168]
        cmp     rax, [r14 + 40]
        ja      invalid                 // receipt above the allowance

        // regions 0..8: (bind[w], bind[w+1])
        mov     r10, [r14 + 24]
        .irp    r, 0, 1, 2, 3, 4, 5, 6, 7, 8
        mov     rax, [rbp + 8 + 8*\r]
        mov     r11, [r10 + rax*8]
        mov     [rsp + 16*\r], r11
        mov     r11, [r10 + rax*8 + 8]
        mov     [rsp + 16*\r + 8], r11
        .endr

        xor     eax, eax
        mov     [rsp + 144], rax        // status
        mov     [rsp + 152], rax        // ret_val
        mov     rax, [r14 + 40]
        mov     [rsp + 160], rax        // fuel_budget

        mov     r10, [r14 + 16]         // control words
        mov     rax, [rbp + 80]
        mov     r11, [r10 + rax*8]
        mov     [rsp + 176], r11        // arg0
        mov     rax, [rbp + 88]
        mov     r11, [r10 + rax*8]
        mov     [rsp + 184], r11        // arg1
        mov     rax, [rbp + 96]
        mov     rsi, [r10 + rax*8]      // v1
        mov     rax, [rbp + 104]
        mov     rdx, [r10 + rax*8]      // v2
        mov     rax, [rbp + 112]
        mov     rcx, [r10 + rax*8]      // v3
        mov     rax, [rbp + 120]
        mov     r8, [r10 + rax*8]       // v4
        mov     rax, [rbp + 128]
        mov     r9, [r10 + rax*8]       // v5

        mov     rax, [rbp]
        mov     r11, [r14 + 32]
        mov     r15, [r11 + rax*8]      // the leaf's entry
        mov     rdi, rsp                // v0: the child frame
        xor     eax, eax
        xor     ebx, ebx
        xor     r10d, r10d
        xor     r11d, r11d
        xor     r12d, r12d
        xor     r13d, r13d
        call    enter

        mov     rax, [r14 + 16]
        mov     rdx, [rbp + 136]
        mov     rcx, [rsp + 152]
        mov     [rax + rdx*8], rcx      // ctl[dst] := the payload
        mov     rax, [rsp + 144]        // the outcome
        cmp     rax, 1
        jne     done
        add     rbp, STEP
        jmp     loop

fired:
        mov     eax, 1
        jmp     done
invalid:
        mov     eax, 3
done:
        mov     rdx, [rsp + 168]
        mov     [r14 + 48], rdx         // the receipt
        mov     [r14 + 56], rbp         // the step that ended the plan
        add     rsp, 200
        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx
        ret

enter:
        push    r15
        ret

        .size   tisa_drive, .-tisa_drive
        .section .note.GNU-stack,"",%progbits
