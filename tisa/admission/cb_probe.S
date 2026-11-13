/* cb_probe.S (admission controls only): a TcFn computing add64 that records how it was called, for the
   control of the kernel's call into registered functions (admission_native.c). It is registered only
   in a test-only registry, in add64's place.
     tisa_test_cb_seen[0] in (RDI)           [1] out (RSI)
     tisa_test_cb_seen[2] the return word's address (RSP at entry)
     tisa_test_cb_seen[3] the return address  [4] the number of calls */
        .text
        .p2align 4
        .globl tisa_test_cb_probe
        .type tisa_test_cb_probe, @function
tisa_test_cb_probe:
        endbr64
        movq %rdi, tisa_test_cb_seen(%rip)
        movq %rsi, tisa_test_cb_seen+8(%rip)
        movq %rsp, tisa_test_cb_seen+16(%rip)
        movq (%rsp), %rax
        movq %rax, tisa_test_cb_seen+24(%rip)
        incq tisa_test_cb_seen+32(%rip)
        movq (%rdi), %rax
        addq 8(%rdi), %rax
        movq %rax, (%rsi)
        movl $1, %eax
        ret
        .size tisa_test_cb_probe, .-tisa_test_cb_probe
        .globl tisa_test_cb_probe_end
tisa_test_cb_probe_end:

        .bss
        .p2align 3
        .globl tisa_test_cb_seen
        .type tisa_test_cb_seen, @object
tisa_test_cb_seen:
        .zero 40
        .size tisa_test_cb_seen, 40

        .section .note.GNU-stack,"",@progbits
