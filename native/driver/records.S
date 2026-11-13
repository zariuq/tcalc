// records.S -- the record loop over the plan driver tisa_drive (driver.S).
//
//   uint64_t tisa_records(TcRecords *r);                  (SysV x86-64)
//
// Each record: one unit of fuel is charged to the receipt (EXHAUSTED (4)
// when the receipt has reached the allowance, as t-ISA's FUND 1); the decode
// plan runs; its opcode is read from the opcode word; the handler table
// names the plan for it (UNSUPPORTED (2) when the opcode is past the table
// or its entry is 0); the handler runs. The first outcome other than FIRED
// ends the loop with that outcome. After a handler that fired, the loop
// ends FIRED when the END word is not 0, and goes on to the next record
// otherwise. The receipt passes from plan to plan and from record to record.
//
// Plans run by tisa_drive, entered as the driver enters its leaves: `call
// enter` pushes the return address and `enter: push r15; ret` jumps to the
// address in r15. There is no indirect CALL or JMP (FF /2, FF /4) here: the
// x86 model the proofs use (s2n-bignum) takes their target as relative to
// the next instruction, which on x86 it is not.
//
// Supported profile: user-mode shadow stacks (CET SHSTK) disabled, as for
// tisa_drive. Under SHSTK the ret in `enter` faults (#CP): it returns to
// tisa_drive, while the shadow stack holds the address `call enter` pushed.
//
// Descriptor r, 8-byte words:
//    0 drive    the address of tisa_drive
//    1 decode   the decode plan's TcDrive
//    2 table    the handlers' TcDrive addresses, indexed by opcode (0: none)
//    3 nh       the table's entries
//    4 op       the address of the opcode word
//    5 end      the address of the END word
//    6 budget   the fuel allowance, written to each plan's descriptor
//    7 used     the receipt (in; out on return)
//    8 count    out: the records whose handler fired
// Returns the outcome.

        .intel_syntax noprefix
        .text
        .globl  tisa_records
        .type   tisa_records, @function

tisa_records:
        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15                     // tisa_drive is entered with rsp = 8 (mod 16), as from a call
        mov     rbx, rdi                // rbx: the descriptor
        mov     rbp, [rbx + 56]         // rbp: the receipt
        xor     r12d, r12d              // r12: records whose handler fired
        mov     r15, [rbx]              // r15: tisa_drive

next:
        cmp     rbp, [rbx + 48]
        jae     exhausted               // no fuel left for a record
        add     rbp, 1                  // the record's unit
        mov     r13, [rbx + 8]
        call    run                     // the decode plan
        cmp     rax, 1
        jne     done
        mov     rax, [rbx + 32]
        mov     rax, [rax]              // the opcode
        cmp     rax, [rbx + 24]
        jae     unsupported
        mov     rcx, [rbx + 16]
        mov     r13, [rcx + rax*8]      // its handler
        test    r13, r13
        jz      unsupported
        call    run                     // the handler plan
        cmp     rax, 1
        jne     done
        add     r12, 1
        mov     rax, [rbx + 40]
        cmp     qword ptr [rax], 0
        je      next                    // not END: the next record
        mov     eax, 1
        jmp     done

exhausted:
        mov     eax, 4
        jmp     done
unsupported:
        mov     eax, 2
done:
        mov     [rbx + 56], rbp         // the receipt
        mov     [rbx + 64], r12         // the count
        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx
        ret

// run: the plan whose descriptor is r13, from the receipt in rbp; rbp takes
// the plan's receipt back. rax: the plan's outcome.
run:
        mov     rax, [rbx + 48]
        mov     [r13 + 40], rax         // the allowance
        mov     [r13 + 48], rbp         // the receipt
        mov     rdi, r13
        call    enter
        mov     rbp, [r13 + 48]
        ret
enter:
        push    r15
        ret

        .size   tisa_records, . - tisa_records
