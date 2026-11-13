/* native_alu.S: the five proved binary producers of the sealed function registry, byte for byte.

   Each image tisa/native_alu/NAME.bin is 34 bytes, bool fn(const uint64_t *in, uint64_t *out) under
   the System V ABI (in RDI, out RSI, the result in AL):
     ENDBR64; MOV RAX,[RDI+0]; MOV RDX,[RDI+8]; op RAX,RDX; MOV [RSI+0],RAX; MOV EAX,1; RET
   with op ADD, SUB, AND, OR or XOR. tisa/native_alu/SHA256SUMS holds the proved digests.

   Each image is emitted twice: into .text as the function tisa_native_NAME (global, 16-byte aligned,
   size 34), and into .rodata as tisa_native_NAME_expected, the copy the host compares the function's
   bytes with when it registers them (tisa_core.c); the build compares the slice at each function in
   every linked binary with SHA256SUMS (tisa/native_alu/check.sh). Paths are relative to the tcalc
   tree, where every build of this file runs.

   -DTISA_NATIVE_ALU_PATCHED (the admission controls only) changes one byte of add64's .text copy, so
   that registration and the build check can be seen to refuse it. */

        .macro NATIVE name
        .text
        .p2align 4
        .globl tisa_native_\name
        .type tisa_native_\name, @function
tisa_native_\name:
        .incbin "tisa/native_alu/\name\().bin"
        .size tisa_native_\name, 34
        .endm

        .macro EXPECTED name
        .section .rodata
        .p2align 4
        .globl tisa_native_\name\()_expected
        .type tisa_native_\name\()_expected, @object
tisa_native_\name\()_expected:
        .incbin "tisa/native_alu/\name\().bin"
        .size tisa_native_\name\()_expected, 34
        .endm

#ifdef TISA_NATIVE_ALU_PATCHED
        .text
        .p2align 4
        .globl tisa_native_add64
        .type tisa_native_add64, @function
tisa_native_add64:                              /* byte 20, the ADD's ModRM d0, becomes d1 */
        .incbin "tisa/native_alu/add64.bin", 0, 20
        .byte 0xd1
        .incbin "tisa/native_alu/add64.bin", 21, 13
        .size tisa_native_add64, 34
#else
        NATIVE add64
#endif
        NATIVE sub64
        NATIVE and64
        NATIVE or64
        NATIVE xor64

        EXPECTED add64
        EXPECTED sub64
        EXPECTED and64
        EXPECTED or64
        EXPECTED xor64

        .section .note.GNU-stack,"",@progbits
