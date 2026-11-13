"""Instruction families that matter for fast paths in a proof-checking
kernel, as Intel-syntax probes for GNU as. The probes give XED iforms and
encodings for rows that the targets may not contain."""

FAMILIES = {
    "copy": """
        rep movsb
        rep movsw
        rep movsd
        rep movsq
        movsb
        movsq
        movdqu xmm0, [rsi]
        movdqu [rdi], xmm0
        movdqa xmm0, [rsi]
        movups xmm0, [rsi]
        movups [rdi], xmm0
        movaps xmm0, [rsi]
        vmovdqu xmm0, [rsi]
        vmovdqu [rdi], xmm0
        vmovdqu ymm0, [rsi]
        vmovdqu [rdi], ymm0
        vmovdqu ymm0, ymm1
        vmovdqa ymm0, [rsi]
        vmovdqa [rdi], ymm0
        vmovups ymm0, [rsi]
        vmovups [rdi], ymm0
        vmovaps ymm0, [rsi]
        vmovntdq [rdi], ymm0
        vmovntdqa ymm0, [rsi]
        movnti [rdi], rax
        vlddqu ymm0, [rsi]
        vpmaskmovd ymm0, ymm1, [rsi]
        vpmaskmovq [rdi], ymm1, ymm0
        vmovdqu8 zmm0, [rsi]
        vmovdqu8 [rdi], zmm0
        vmovdqu8 ymm0{k1}{z}, [rsi]
        vmovdqu64 zmm0, [rsi]
        vmovdqu64 [rdi], zmm0
        vmovdqu32 zmm0, [rsi]
        vmovdqa64 zmm0, [rsi]
        vmovq xmm0, qword ptr [rsi]
        vmovq qword ptr [rdi], xmm0
        vmovd xmm0, dword ptr [rsi]
        vinserti128 ymm0, ymm1, [rsi], 1
        vextracti128 [rdi], ymm0, 1
        vperm2i128 ymm0, ymm1, ymm2, 0x21
        prefetcht0 [rsi]
        prefetchnta [rsi]
    """,
    "zero": """
        rep stosb
        rep stosw
        rep stosd
        rep stosq
        stosb
        stosq
        pxor xmm0, xmm0
        xorps xmm0, xmm0
        vpxor xmm0, xmm0, xmm0
        vpxor ymm0, ymm0, ymm0
        vxorps ymm0, ymm0, ymm0
        vpxord zmm0, zmm0, zmm0
        vpxorq zmm0, zmm0, zmm0
        vpbroadcastb ymm0, xmm1
        vpbroadcastw ymm0, xmm1
        vpbroadcastd ymm0, xmm1
        vpbroadcastq ymm0, qword ptr [rsi]
        vpbroadcastb zmm0, eax
        vpbroadcastq zmm0, rax
        vzeroupper
        vzeroall
    """,
    "equality": """
        pcmpeqb xmm0, xmm1
        pcmpeqq xmm0, xmm1
        vpcmpeqb xmm0, xmm1, xmm2
        vpcmpeqb ymm0, ymm1, ymm2
        vpcmpeqb ymm0, ymm1, [rsi]
        vpcmpeqw ymm0, ymm1, ymm2
        vpcmpeqd ymm0, ymm1, ymm2
        vpcmpeqq ymm0, ymm1, ymm2
        vpcmpgtb ymm0, ymm1, ymm2
        vpcmpgtd ymm0, ymm1, ymm2
        vpcmpgtq ymm0, ymm1, ymm2
        pmovmskb eax, xmm0
        vpmovmskb eax, xmm0
        vpmovmskb eax, ymm0
        vmovmskps eax, ymm0
        ptest xmm0, xmm1
        vptest xmm0, xmm1
        vptest ymm0, ymm1
        vptest ymm0, [rsi]
        vpminub ymm0, ymm1, ymm2
        vpminuw ymm0, ymm1, ymm2
        vpminud ymm0, ymm1, ymm2
        vpmaxub ymm0, ymm1, ymm2
        vpmaxud xmm0, xmm1, xmm2
        vpminsb ymm0, ymm1, ymm2
        vpsubusb ymm0, ymm1, ymm2
        vpsadbw ymm0, ymm1, ymm2
        vpand ymm0, ymm1, ymm2
        vpandn ymm0, ymm1, ymm2
        vpor ymm0, ymm1, ymm2
        vpor xmm0, xmm1, xmm2
        vandps ymm0, ymm1, ymm2
        vorps ymm0, ymm1, ymm2
        pcmpestri xmm0, [rsi], 0x18
        pcmpistri xmm0, xmm1, 0x18
        vpcmpistri xmm0, xmm1, 0x18
        vpcmpeqb k1, zmm0, zmm1
        vpcmpeqq k1, zmm0, zmm1
        vpcmpb k1, zmm0, zmm1, 0
        vpcmpub k1, zmm0, zmm1, 4
        vpcmpd k1, zmm0, zmm1, 1
        vpcmpuq k1, zmm0, zmm1, 2
        vptestmb k1, zmm0, zmm1
        vptestnmb k1, zmm0, zmm1
        kortestq k1, k1
        kortestd k1, k1
        kortestw k0, k1
        ktestq k1, k2
        kmovq rax, k1
        kmovd eax, k1
        kmovw k1, eax
        kandq k1, k2, k3
        cmpsb
        repe cmpsb
        repe cmpsq
        repne cmpsb
        scasb
        repne scasb
        repe scasq
    """,
    "bitscan": """
        bsf rax, rcx
        bsf eax, ecx
        bsf eax, [rsi]
        bsr rax, rcx
        bsr eax, ecx
        tzcnt rax, rcx
        tzcnt eax, ecx
        tzcnt eax, [rsi]
        lzcnt rax, rcx
        lzcnt eax, ecx
        popcnt rax, rcx
        popcnt eax, ecx
        bt rax, rcx
        bt qword ptr [rsi], rcx
        bt rax, 5
        bts rax, rcx
        btr rax, rcx
        btc rax, rcx
        vplzcntq zmm0, zmm1
        vpopcntq zmm0, zmm1
        vpopcntb zmm0, zmm1
    """,
    "bmi": """
        andn rax, rbx, rcx
        andn eax, ebx, [rsi]
        bextr rax, rcx, rdx
        blsi rax, rcx
        blsmsk rax, rcx
        blsr rax, rcx
        blsr eax, ecx
        bzhi rax, rcx, rdx
        pdep rax, rbx, rcx
        pext rax, rbx, rcx
        pext eax, ebx, ecx
        mulx rax, rbx, rcx
        mulx eax, ebx, ecx
        rorx rax, rcx, 13
        rorx eax, ecx, 13
        sarx rax, rcx, rdx
        shlx rax, rcx, rdx
        shlx eax, [rsi], edx
        shrx rax, rcx, rdx
        shrx eax, ecx, edx
        adcx rax, rcx
        adox rax, rcx
    """,
    "hashing": """
        crc32 eax, byte ptr [rsi]
        crc32 eax, ecx
        crc32 rax, qword ptr [rsi]
        crc32 rax, rcx
        aesenc xmm0, xmm1
        aesenclast xmm0, xmm1
        aesdec xmm0, xmm1
        aeskeygenassist xmm0, xmm1, 1
        vaesenc xmm0, xmm1, xmm2
        vaesenc ymm0, ymm1, ymm2
        pclmulqdq xmm0, xmm1, 0
        vpclmulqdq xmm0, xmm1, xmm2, 0
        vpclmulqdq ymm0, ymm1, ymm2, 0
        sha256rnds2 xmm0, xmm1
        sha256msg1 xmm0, xmm1
        sha1rnds4 xmm0, xmm1, 0
        pmuludq xmm0, xmm1
        vpmuludq ymm0, ymm1, ymm2
        vpmullq zmm0, zmm1, zmm2
        pshufb xmm0, xmm1
        vpshufb ymm0, ymm1, ymm2
        vpshufd ymm0, ymm1, 0x1b
        pshufd xmm0, xmm1, 0x1b
        vpsrlq ymm0, ymm1, 3
        vpsllq ymm0, ymm1, 3
        vpsrlvq ymm0, ymm1, ymm2
        vpaddq ymm0, ymm1, ymm2
        vpermq ymm0, ymm1, 0x1b
        vpermd ymm0, ymm1, ymm2
        vpermb zmm0, zmm1, zmm2
        vpternlogq zmm0, zmm1, zmm2, 0x96
        vpternlogd ymm0, ymm1, ymm2, 0x96
        vprolq zmm0, zmm1, 5
        imul rax, rcx
        imul rax, rcx, 0x1e3779b1
        mul rcx
        rol rax, 5
        ror rax, cl
    """,
    "control": """
        call rax
        call qword ptr [rax]
        call qword ptr [rip+0x100]
        jmp rax
        notrack jmp rax
        jmp qword ptr [rax+rcx*8]
        jmp qword ptr [rip+0x100]
        ret
        ret 8
        endbr64
        cmovz rax, rcx
        cmovz eax, [rsi]
        setz al
        pause
        lfence
        mfence
        sfence
        syscall
        ud2
        int3
        hlt
        cpuid
        rdtsc
        rdtscp
        xchg [rsi], rax
        lock xadd [rsi], rax
        lock cmpxchg [rsi], rcx
        lock inc qword ptr [rsi]
        cmpxchg [rsi], rcx
    """,
    "integer": """
        div rcx
        idiv rcx
        div ecx
        cqo
        cdq
        cdqe
        cwde
        movsxd rax, ecx
        movzx eax, word ptr [rsi]
        leave
        push qword ptr [rsp+8]
        pop qword ptr [rsp]
        push 0x12
        push 0x12345678
        bswap rax
        movbe rax, [rsi]
        neg rax
        not rax
        sar rax, 3
        shld rax, rcx, 5
        shrd rax, rcx, cl
        rcl rax, 1
        lea rax, [rcx+rdx*8+16]
        mov rax, qword ptr fs:[0x28]
        sub rax, qword ptr fs:[0x28]
        mov word ptr [rsi], ax
        cmp word ptr [rsi], 7
        cmovnz ax, word ptr [rsi]
        test ax, ax
        movzx eax, al
        movsx rax, byte ptr [rsi]
        xchg eax, ecx
        nop
        nop dword ptr [rax]
        nop word ptr [rax+rax*1+0]
        clc
        stc
        cld
        std
        cmc
        sahf
        lahf
        pushfq
        popfq
    """,
}
