# cb_probe: call a binary callback with every general register set to a
# known pattern, and record every register, RSP and RFLAGS after it returns.
#
#   uint64_t cb_probe(void *fn, const uint64_t *in, uint64_t *out,
#                     const uint64_t *pre, uint64_t *post);
#
# pre[0..12]  the values loaded before the call into
#             rbx rbp r8 r9 r10 r11 r12 r13 r14 r15 rax rdx rcx;
#             rdi = in and rsi = out, as the callback's arguments.
# post[0..14] rax rbx rcx rdx rsi rdi rbp r8 r9 r10 r11 r12 r13 r14 r15
#             after the call;
# post[15]    rsp just before the call, post[16] rsp just after it returns;
# post[17]    rflags before the call, post[18] rflags after it.
# The call is indirect, through memory, so no register holds the target.

        .text
        .globl  cb_probe
        .type   cb_probe, @function
cb_probe:
        push    %rbx
        push    %rbp
        push    %r12
        push    %r13
        push    %r14
        push    %r15
        push    %r8                 # post
        push    %rdi                # fn
        sub     $8, %rsp            # rsp = 0 mod 16 at the call
                                    # 8(%rsp) = fn, 16(%rsp) = post
        mov     16(%rsp), %r8
        mov     %rsp, %rax
        mov     %rax, 120(%r8)      # post[15] = rsp before the call
        pushfq
        pop     %rax
        mov     %rax, 136(%r8)      # post[17] = rflags before the call
        mov     %rsi, %rdi          # in
        mov     %rdx, %rsi          # out
        mov     0(%rcx), %rbx
        mov     8(%rcx), %rbp
        mov     16(%rcx), %r8
        mov     24(%rcx), %r9
        mov     32(%rcx), %r10
        mov     40(%rcx), %r11
        mov     48(%rcx), %r12
        mov     56(%rcx), %r13
        mov     64(%rcx), %r14
        mov     72(%rcx), %r15
        mov     80(%rcx), %rax
        mov     88(%rcx), %rdx
        mov     96(%rcx), %rcx
        call    *8(%rsp)
        push    %rax                # 0 rax; fn at 16, post at 24
        pushfq                      # 0 rflags, 8 rax; post at 32
        push    %r8                 # 0 r8, 8 rflags, 16 rax; post at 40
        mov     40(%rsp), %r8
        mov     %rbx, 8(%r8)
        mov     %rcx, 16(%r8)
        mov     %rdx, 24(%r8)
        mov     %rsi, 32(%r8)
        mov     %rdi, 40(%r8)
        mov     %rbp, 48(%r8)
        mov     %r9, 64(%r8)
        mov     %r10, 72(%r8)
        mov     %r11, 80(%r8)
        mov     %r12, 88(%r8)
        mov     %r13, 96(%r8)
        mov     %r14, 104(%r8)
        mov     %r15, 112(%r8)
        lea     24(%rsp), %rax
        mov     %rax, 128(%r8)      # post[16] = rsp after the call
        pop     %rax
        mov     %rax, 56(%r8)       # post[7] = r8
        pop     %rax
        mov     %rax, 144(%r8)      # post[18] = rflags after the call
        pop     %rax
        mov     %rax, 0(%r8)        # post[0] = rax
        add     $8, %rsp
        pop     %rdi
        pop     %r8
        pop     %r15
        pop     %r14
        pop     %r13
        pop     %r12
        pop     %rbp
        pop     %rbx
        xor     %eax, %eax
        ret
        .size   cb_probe, .-cb_probe

        .section .note.GNU-stack,"",@progbits
