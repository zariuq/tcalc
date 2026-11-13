/*
 * tisa_emit_x86.c — Direct Deterministic x86-64 Machine-Code Emitter for `t-ISA`
 *
 * Implements:
 *   1. Fixed physical register map (`v0..v11` -> `rdi,rsi,rdx,rcx,r8,r9,r10,r11,rax,rbx,r12,r13`;
 *      emitter scratch `s0/s1` -> `r14/r15`).
 *   2. Exact 9-byte public ABI prologue (`push rbx, r12, r13, r14, r15`) and
 *      10-byte epilogue (`pop r15, r14, r13, r12, rbx; ret`).
 *   3. Exact-step fuel accounting & overflow-safe capability bounds checking
 *      matching `tisa_eval_ref` and `tisa_eval_tcalc`.
 *   4. W^X executable page mapping (`mmap` RW -> `mprotect` `PROT_READ | PROT_EXEC`).
 *   5. Deterministic JSON manifest & disassembly export (`tisa_write_program_manifest_json`).
 */
#include "tisa.h"
#include <inttypes.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

/* =========================================================================
 * 1. Physical Register Mapping & SHA-256 Digest Helper
 * ========================================================================= */

static const uint8_t X86_HW_REG[TISA_TOTAL_REGS] = {
    7,  /* TISA_V0  -> rdi */
    6,  /* TISA_V1  -> rsi */
    2,  /* TISA_V2  -> rdx */
    1,  /* TISA_V3  -> rcx */
    8,  /* TISA_V4  -> r8  */
    9,  /* TISA_V5  -> r9  */
    10, /* TISA_V6  -> r10 */
    11, /* TISA_V7  -> r11 */
    0,  /* TISA_V8  -> rax */
    3,  /* TISA_V9  -> rbx */
    12, /* TISA_V10 -> r12 */
    13, /* TISA_V11 -> r13 */
    14, /* TISA_S0  -> r14 (emitter scratch 0) */
    15  /* TISA_S1  -> r15 (emitter scratch 1) */
};

static const char *const X86_REG_NAME[TISA_TOTAL_REGS] = {
    "rdi", "rsi", "rdx", "rcx", "r8",  "r9",  "r10",
    "r11", "rax", "rbx", "r12", "r13", "r14", "r15"
};

static const char *const AARCH64_REG_NAME[TISA_TOTAL_REGS] = {
    "x0", "x1", "x2", "x3", "x4",  "x5",  "x6",
    "x7", "x8", "x9", "x10", "x11", "x12", "x13"
};

static const char *const RV64_REG_NAME[TISA_TOTAL_REGS] = {
    "a0", "a1", "a2", "a3", "a4", "a5", "a6",
    "a7", "t0", "t1", "t2", "t3", "t4", "t5"
};

/* Self-contained FIPS 180-4 SHA-256 for emitted machine-byte digests */
typedef struct {
    uint32_t state[8];
    uint64_t bitcount;
    uint8_t  buffer[64];
} X86Sha256Ctx;

static inline uint32_t x86_rotr32(uint32_t x, uint32_t n) {
    return (x >> n) | (x << (32u - n));
}

static void x86_sha256_transform(X86Sha256Ctx *ctx, const uint8_t data[64]) {
    static const uint32_t K[64] = {
        0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u,
        0x3956c25bu, 0x59f111f1u, 0x923f82a4u, 0xab1c5ed5u,
        0xd807aa98u, 0x12835b01u, 0x243185beu, 0x550c7dc3u,
        0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u, 0xc19bf174u,
        0xe49b69c1u, 0xefbe4786u, 0x0fc19dc6u, 0x240ca1ccu,
        0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau,
        0x983e5152u, 0xa831c66du, 0xb00327c8u, 0xbf597fc7u,
        0xc6e00bf3u, 0xd5a79147u, 0x06ca6351u, 0x14292967u,
        0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu, 0x53380d13u,
        0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u,
        0xa2bfe8a1u, 0xa81a664bu, 0xc24b8b70u, 0xc76c51a3u,
        0xd192e819u, 0xd6990624u, 0xf40e3585u, 0x106aa070u,
        0x19a4c116u, 0x1e376c08u, 0x2748774cu, 0x34b0bcb5u,
        0x391c0cb3u, 0x4ed8aa4au, 0x5b9cca4fu, 0x682e6ff3u,
        0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u,
        0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u
    };
    uint32_t W[64];
    for (int i = 0; i < 16; i++) {
        W[i] = ((uint32_t)data[i * 4 + 0] << 24) |
               ((uint32_t)data[i * 4 + 1] << 16) |
               ((uint32_t)data[i * 4 + 2] << 8)  |
               ((uint32_t)data[i * 4 + 3]);
    }
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = x86_rotr32(W[i - 15], 7) ^ x86_rotr32(W[i - 15], 18) ^ (W[i - 15] >> 3);
        uint32_t s1 = x86_rotr32(W[i - 2], 17) ^ x86_rotr32(W[i - 2], 19) ^ (W[i - 2] >> 10);
        W[i] = W[i - 16] + s0 + W[i - 7] + s1;
    }
    uint32_t a = ctx->state[0], b = ctx->state[1], c = ctx->state[2], d = ctx->state[3];
    uint32_t e = ctx->state[4], f = ctx->state[5], g = ctx->state[6], h = ctx->state[7];
    for (int i = 0; i < 64; i++) {
        uint32_t S1 = x86_rotr32(e, 6) ^ x86_rotr32(e, 11) ^ x86_rotr32(e, 25);
        uint32_t ch = (e & f) ^ ((~e) & g);
        uint32_t temp1 = h + S1 + ch + K[i] + W[i];
        uint32_t S0 = x86_rotr32(a, 2) ^ x86_rotr32(a, 13) ^ x86_rotr32(a, 22);
        uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
        uint32_t temp2 = S0 + maj;
        h = g; g = f; f = e; e = d + temp1;
        d = c; c = b; b = a; a = temp1 + temp2;
    }
    ctx->state[0] += a; ctx->state[1] += b; ctx->state[2] += c; ctx->state[3] += d;
    ctx->state[4] += e; ctx->state[5] += f; ctx->state[6] += g; ctx->state[7] += h;
}

static void x86_sha256_hex(const uint8_t *bytes, size_t len, char out_hex[65]) {
    static const char hex[] = "0123456789abcdef";
    X86Sha256Ctx ctx;
    ctx.state[0] = 0x6a09e667u; ctx.state[1] = 0xbb67ae85u;
    ctx.state[2] = 0x3c6ef372u; ctx.state[3] = 0xa54ff53au;
    ctx.state[4] = 0x510e527fu; ctx.state[5] = 0x9b05688cu;
    ctx.state[6] = 0x1f83d9abu; ctx.state[7] = 0x5be0cd19u;
    ctx.bitcount = 0;
    size_t idx = 0;
    for (size_t i = 0; i < len; i++) {
        ctx.buffer[idx++] = bytes[i];
        ctx.bitcount += 8;
        if (idx == 64) {
            x86_sha256_transform(&ctx, ctx.buffer);
            idx = 0;
        }
    }
    ctx.buffer[idx++] = 0x80u;
    if (idx > 56) {
        while (idx < 64) ctx.buffer[idx++] = 0;
        x86_sha256_transform(&ctx, ctx.buffer);
        idx = 0;
    }
    while (idx < 56) ctx.buffer[idx++] = 0;
    for (int i = 0; i < 8; i++) {
        ctx.buffer[56 + i] = (uint8_t)((ctx.bitcount >> ((7 - i) * 8)) & 0xffu);
    }
    x86_sha256_transform(&ctx, ctx.buffer);
    for (int i = 0; i < 8; i++) {
        uint32_t w = ctx.state[i];
        out_hex[i * 8 + 0] = hex[(w >> 28) & 0xfu];
        out_hex[i * 8 + 1] = hex[(w >> 24) & 0xfu];
        out_hex[i * 8 + 2] = hex[(w >> 20) & 0xfu];
        out_hex[i * 8 + 3] = hex[(w >> 16) & 0xfu];
        out_hex[i * 8 + 4] = hex[(w >> 12) & 0xfu];
        out_hex[i * 8 + 5] = hex[(w >> 8)  & 0xfu];
        out_hex[i * 8 + 6] = hex[(w >> 4)  & 0xfu];
        out_hex[i * 8 + 7] = hex[w & 0xfu];
    }
    out_hex[64] = '\0';
}

/* =========================================================================
 * 2. Low-Level Byte Buffer & x86-64 Instruction Encoders
 * ========================================================================= */

#define X86_MAX_FIXUPS 1024
#define X86_MAX_SPANS  2048

typedef struct {
    const char  *kind;
    size_t       byte_offset;
    size_t       byte_len;
    uint8_t      dst;
    uint8_t      src1;
    uint8_t      src2;
    uint8_t      src3;
    uint8_t      subop;
    TcIsaValType ty;
    uint8_t      region_id;
    uint16_t     scratch_mask;
} X86TemplateSpan;

typedef struct {
    size_t      opcode_offset;
    size_t      disp_offset;
    size_t      next_ip;
    size_t      target_offset;
    int32_t     rel32;
    uint8_t     cc_op;
    bool        patched;
} X86PatchedBranch;

typedef struct {
    const TcIsaStmt *stmt;
    size_t           byte_offset;
    size_t           byte_len;
} X86StmtSpan;

typedef struct {
    uint8_t          bytes[16384];
    size_t           len;
    bool             overflow;
    uint32_t         branch_count;
    size_t           epilogue_fixups[X86_MAX_FIXUPS];
    size_t           num_epilogue_fixups;
    size_t           invalid_fixups[X86_MAX_FIXUPS];
    size_t           num_invalid_fixups;
    size_t           exhausted_fixups[X86_MAX_FIXUPS];
    size_t           num_exhausted_fixups;
    size_t           unsupported_fixups[X86_MAX_FIXUPS];
    size_t           num_unsupported_fixups;
    uint16_t         scratch_mask;
    X86TemplateSpan  spans[X86_MAX_SPANS];
    size_t           num_spans;
    X86PatchedBranch branches[X86_MAX_FIXUPS];
    size_t           num_branches;
    X86StmtSpan      stmt_spans[X86_MAX_SPANS];
    size_t           num_stmt_spans;
    TcIsaTargetProfile profile;
    const TcIsaProgram *prog;
    bool               is_static_leaf;
    const TcIsaInstr  *fused_cmp_ins;
    const TcIsaStmt   *fused_if_stmt;
    uint8_t            fused_cmp_inv_cc;
} X86EmitBuf;

static void push_span(X86EmitBuf *b, const char *kind, size_t start_off, size_t end_off,
                      uint8_t dst, uint8_t src1, uint8_t src2, uint8_t src3,
                      uint8_t subop, TcIsaValType ty, uint8_t region_id, uint16_t scratch_mask) {
    if (b->num_spans >= X86_MAX_SPANS) { b->overflow = true; return; }
    b->spans[b->num_spans++] = (X86TemplateSpan){
        .kind         = kind,
        .byte_offset  = start_off,
        .byte_len     = end_off - start_off,
        .dst          = dst,
        .src1         = src1,
        .src2         = src2,
        .src3         = src3,
        .subop        = subop,
        .ty           = ty,
        .region_id    = region_id,
        .scratch_mask = scratch_mask
    };
}

static void record_stmt_span(X86EmitBuf *b, const TcIsaStmt *stmt, size_t start_off, size_t end_off) {
    if (b->num_stmt_spans >= X86_MAX_SPANS) { b->overflow = true; return; }
    b->stmt_spans[b->num_stmt_spans++] = (X86StmtSpan){
        .stmt        = stmt,
        .byte_offset = start_off,
        .byte_len    = end_off - start_off
    };
}

static inline void emit_u8(X86EmitBuf *b, uint8_t v) {
    if (b->len >= sizeof(b->bytes)) { b->overflow = true; return; }
    b->bytes[b->len++] = v;
}

static inline void emit_u32(X86EmitBuf *b, uint32_t v) {
    emit_u8(b, (uint8_t)(v & 0xFFu));
    emit_u8(b, (uint8_t)((v >> 8) & 0xFFu));
    emit_u8(b, (uint8_t)((v >> 16) & 0xFFu));
    emit_u8(b, (uint8_t)((v >> 24) & 0xFFu));
}

static inline void emit_u64(X86EmitBuf *b, uint64_t v) {
    emit_u32(b, (uint32_t)(v & 0xFFFFFFFFull));
    emit_u32(b, (uint32_t)(v >> 32));
}

static inline void patch_rel32(X86EmitBuf *b, size_t disp_offset, size_t target_offset) {
    if (b->overflow || disp_offset + 4u > sizeof(b->bytes)) {
        b->overflow = true;
        return;
    }
    int64_t rel = (int64_t)target_offset - (int64_t)(disp_offset + 4u);
    if (rel < INT32_MIN || rel > INT32_MAX) {
        b->overflow = true;
        return;
    }
    uint32_t u = (uint32_t)(int32_t)rel;
    b->bytes[disp_offset + 0] = (uint8_t)(u & 0xFFu);
    b->bytes[disp_offset + 1] = (uint8_t)((u >> 8) & 0xFFu);
    b->bytes[disp_offset + 2] = (uint8_t)((u >> 16) & 0xFFu);
    b->bytes[disp_offset + 3] = (uint8_t)((u >> 24) & 0xFFu);
    for (size_t i = 0; i < b->num_branches; i++) {
        if (b->branches[i].disp_offset == disp_offset) {
            b->branches[i].target_offset = target_offset;
            b->branches[i].rel32         = (int32_t)rel;
            b->branches[i].patched       = true;
            break;
        }
    }
}

static inline uint8_t rex_byte(uint8_t w, uint8_t r_hw, uint8_t x_hw, uint8_t b_hw) {
    return (uint8_t)(0x40u | ((w & 1u) << 3) | (((r_hw >> 3) & 1u) << 2) |
                     (((x_hw >> 3) & 1u) << 1) | ((b_hw >> 3) & 1u));
}

static inline uint8_t modrm_byte(uint8_t mod, uint8_t reg_hw, uint8_t rm_hw) {
    return (uint8_t)(((mod & 3u) << 6) | ((reg_hw & 7u) << 3) | (rm_hw & 7u));
}

/* mov r64(dst), r64(src) */
static void emit_mov_r64_r64(X86EmitBuf *b, uint8_t dst_v, uint8_t src_v) {
    if (dst_v == src_v) return;
    uint8_t d = X86_HW_REG[dst_v];
    uint8_t s = X86_HW_REG[src_v];
    emit_u8(b, rex_byte(1, s, 0, d));
    emit_u8(b, 0x89u);
    emit_u8(b, modrm_byte(3, s, d));
}

/* mov r32(dst), r32(src) — zero-extends 32-bit value to 64 bits */
static void emit_zext32_reg(X86EmitBuf *b, uint8_t dst_v) {
    uint8_t d = X86_HW_REG[dst_v];
    uint8_t rx = rex_byte(0, d, 0, d);
    if (rx != 0x40u) emit_u8(b, rx);
    emit_u8(b, 0x89u);
    emit_u8(b, modrm_byte(3, d, d));
}

/* movsxd r64(dst), r32(dst) — sign-extends 32-bit value to 64 bits */
static void emit_sext32_reg(X86EmitBuf *b, uint8_t dst_v) {
    uint8_t d = X86_HW_REG[dst_v];
    emit_u8(b, rex_byte(1, d, 0, d));
    emit_u8(b, 0x63u);
    emit_u8(b, modrm_byte(3, d, d));
}

/* Canonicalize register `dst_v` according to `ty` */
static void emit_canon_reg(X86EmitBuf *b, uint8_t dst_v, TcIsaValType ty) {
    if (ty == TISA_TYPE_U32Z) {
        emit_zext32_reg(b, dst_v);
    } else if (ty == TISA_TYPE_I32S) {
        emit_sext32_reg(b, dst_v);
    } else if (ty == TISA_TYPE_BOOL) {
        uint8_t d = X86_HW_REG[dst_v];
        uint8_t rx = rex_byte(0, 0, 0, d);
        if (rx != 0x40u) emit_u8(b, rx);
        emit_u8(b, 0x83u);
        emit_u8(b, modrm_byte(3, 4, d)); /* and r32, 1 */
        emit_u8(b, 0x01u);
    }
}

/* Load 64-bit immediate into `dst_v` */
static void emit_mov_imm64(X86EmitBuf *b, uint8_t dst_v, uint64_t val) {
    uint8_t d = X86_HW_REG[dst_v];
    if (val == 0ull) {
        uint8_t rx = rex_byte(0, d, 0, d);
        if (rx != 0x40u) emit_u8(b, rx);
        emit_u8(b, 0x31u);
        emit_u8(b, modrm_byte(3, d, d)); /* xor r32, r32 */
    } else if (val <= 0xFFFFFFFFull) {
        uint8_t rx = rex_byte(0, 0, 0, d);
        if (rx != 0x40u) emit_u8(b, rx);
        emit_u8(b, (uint8_t)(0xB8u + (d & 7u)));
        emit_u32(b, (uint32_t)val);
    } else {
        emit_u8(b, rex_byte(1, 0, 0, d));
        emit_u8(b, (uint8_t)(0xB8u + (d & 7u)));
        emit_u64(b, val);
    }
}

/* Load qword from `[rdi + disp32]` into `dst_v` (`rdi` has hw=7, low=7) */
static void emit_load_frame_u64(X86EmitBuf *b, uint8_t dst_v, int32_t disp32) {
    uint8_t d = X86_HW_REG[dst_v];
    emit_u8(b, rex_byte(1, d, 0, 7));
    emit_u8(b, 0x8Bu);
    emit_u8(b, modrm_byte(2, d, 7)); /* [rdi + disp32] */
    emit_u32(b, (uint32_t)disp32);
}

/* Store qword `src_v` into `[rdi + disp32]` */
static void emit_store_frame_u64(X86EmitBuf *b, int32_t disp32, uint8_t src_v) {
    uint8_t s = X86_HW_REG[src_v];
    emit_u8(b, rex_byte(1, s, 0, 7));
    emit_u8(b, 0x89u);
    emit_u8(b, modrm_byte(2, s, 7));
    emit_u32(b, (uint32_t)disp32);
}

/* Store sign-extended imm32 into qword `[rdi + disp32]` */
static void emit_store_frame_imm32(X86EmitBuf *b, int32_t disp32, uint32_t imm32) {
    emit_u8(b, 0x48u);
    emit_u8(b, 0xC7u);
    emit_u8(b, modrm_byte(2, 0, 7));
    emit_u32(b, (uint32_t)disp32);
    emit_u32(b, imm32);
}

/* Emit a near conditional jump `0F <cc> rel32` and return offset of rel32 */
static size_t emit_jcc_rel32(X86EmitBuf *b, uint8_t cc_op) {
    size_t op_off = b->len;
    b->branch_count++;
    emit_u8(b, 0x0Fu);
    emit_u8(b, cc_op);
    size_t pos = b->len;
    emit_u32(b, 0u);
    if (b->num_branches < X86_MAX_FIXUPS) {
        b->branches[b->num_branches++] = (X86PatchedBranch){
            .opcode_offset = op_off,
            .disp_offset   = pos,
            .next_ip       = pos + 4u,
            .target_offset = 0u,
            .rel32         = 0,
            .cc_op         = cc_op,
            .patched       = false
        };
    } else {
        b->overflow = true;
    }
    return pos;
}

/* Emit an unconditional jump `E9 rel32` and return offset of rel32 */
static size_t emit_jmp_rel32(X86EmitBuf *b) {
    size_t op_off = b->len;
    b->branch_count++;
    emit_u8(b, 0xE9u);
    size_t pos = b->len;
    emit_u32(b, 0u);
    if (b->num_branches < X86_MAX_FIXUPS) {
        b->branches[b->num_branches++] = (X86PatchedBranch){
            .opcode_offset = op_off,
            .disp_offset   = pos,
            .next_ip       = pos + 4u,
            .target_offset = 0u,
            .rel32         = 0,
            .cc_op         = 0xE9u,
            .patched       = false
        };
    } else {
        b->overflow = true;
    }
    return pos;
}

static void record_fixup(size_t *arr, size_t *count, size_t pos, X86EmitBuf *b) {
    if (*count >= X86_MAX_FIXUPS) { b->overflow = true; return; }
    arr[(*count)++] = pos;
}

/*
 * Emit per-instruction fuel check & increment matching `tisa_consume_fuel(frame)`:
 *   mov r14, [rdi + 160]   ; fuel_budget
 *   test r14, r14
 *   jz .no_cap
 *   mov r15, [rdi + 168]   ; fuel_used
 *   cmp r15, r14
 *   jae exhausted_label
 * .no_cap:
 *   add qword ptr [rdi + 168], 1
 */
static void emit_fuel_step(X86EmitBuf *b) {
    size_t s0 = b->len;
    b->scratch_mask |= 0x3u;
    emit_load_frame_u64(b, TISA_S0, (int32_t)offsetof(TcIsaRuntimeFrame, fuel_budget));
    /* test r14, r14 (4D 85 F6) */
    emit_u8(b, 0x4Du); emit_u8(b, 0x85u); emit_u8(b, 0xF6u);
    size_t jz_no_cap = emit_jcc_rel32(b, 0x84u); /* jz */
    emit_load_frame_u64(b, TISA_S1, (int32_t)offsetof(TcIsaRuntimeFrame, fuel_used));
    /* cmp r15, r14 (4D 39 F7) */
    emit_u8(b, 0x4Du); emit_u8(b, 0x39u); emit_u8(b, 0xF7u);
    size_t jae_exh = emit_jcc_rel32(b, 0x83u); /* jae */
    record_fixup(b->exhausted_fixups, &b->num_exhausted_fixups, jae_exh, b);
    patch_rel32(b, jz_no_cap, b->len);
    /* add qword ptr [rdi + 168], 1 (48 83 87 A8 00 00 00 01) */
    emit_u8(b, 0x48u);
    emit_u8(b, 0x83u);
    emit_u8(b, modrm_byte(2, 0, 7));
    emit_u32(b, (uint32_t)offsetof(TcIsaRuntimeFrame, fuel_used));
    emit_u8(b, 0x01u);
    push_span(b, "FUEL_STEP", s0, b->len, 0xFFu, 0xFFu, 0xFFu, 0xFFu,
              0u, TISA_TYPE_U64, TISA_REGION_FRAME, 0x3u);
}

/*
 * Emit overflow-safe capability bounds check for a memory access of `width` bytes
 * at `regs[base_v] + disp32` in `region_id`, leaving the verified effective
 * address in `r14` (`TISA_S0`):
 *   1. r14 = regs[base_v]
 *   2. r14 -= frame->s<region_id>_ptr  (jb -> invalid_input)
 *   3. if disp32 >= 0: r14 += disp32   (jc -> invalid_input)
 *      else:           r14 -= -disp32  (jb -> invalid_input)
 *   4. r15 = frame->s<region_id>_len
 *   5. cmp r15, width                  (jb -> invalid_input)
 *   6. r15 -= width
 *   7. cmp r14, r15                    (ja -> invalid_input)
 *   8. r14 += frame->s<region_id>_ptr  (effective address in r14!)
 */
static void emit_checked_mem_addr_in_r14(X86EmitBuf *b,
                                         uint8_t region_id,
                                         uint8_t base_v,
                                         int32_t disp32,
                                         uint8_t width) {
    b->scratch_mask |= 0x3u;
    int32_t ptr_off = (int32_t)(region_id * 16u);
    int32_t len_off = (int32_t)(region_id * 16u + 8u);

    emit_mov_r64_r64(b, TISA_S0, base_v);
    emit_load_frame_u64(b, TISA_S1, ptr_off);
    /* sub r14, r15 (4D 29 FE) */
    emit_u8(b, 0x4Du); emit_u8(b, 0x29u); emit_u8(b, 0xFEu);
    size_t jb_base = emit_jcc_rel32(b, 0x82u); /* jb (ptr < base) */
    record_fixup(b->invalid_fixups, &b->num_invalid_fixups, jb_base, b);

    if (disp32 > 0) {
        emit_mov_imm64(b, TISA_S1, (uint64_t)(uint32_t)disp32);
        /* add r14, r15 (4D 01 FE) */
        emit_u8(b, 0x4Du); emit_u8(b, 0x01u); emit_u8(b, 0xFEu);
        size_t jc_disp = emit_jcc_rel32(b, 0x82u); /* jc */
        record_fixup(b->invalid_fixups, &b->num_invalid_fixups, jc_disp, b);
    } else if (disp32 < 0) {
        uint64_t mag = (uint64_t)(-(int64_t)disp32);
        emit_mov_imm64(b, TISA_S1, mag);
        /* sub r14, r15 (4D 29 FE) */
        emit_u8(b, 0x4Du); emit_u8(b, 0x29u); emit_u8(b, 0xFEu);
        size_t jb_disp = emit_jcc_rel32(b, 0x82u); /* jb */
        record_fixup(b->invalid_fixups, &b->num_invalid_fixups, jb_disp, b);
    }

    emit_load_frame_u64(b, TISA_S1, len_off);
    /* cmp r15, width (49 83 FF <width>) */
    emit_u8(b, 0x49u); emit_u8(b, 0x83u); emit_u8(b, 0xFFu); emit_u8(b, width);
    size_t jb_len = emit_jcc_rel32(b, 0x82u); /* jb (len < width) */
    record_fixup(b->invalid_fixups, &b->num_invalid_fixups, jb_len, b);

    /* sub r15, width (49 83 EF <width>) */
    emit_u8(b, 0x49u); emit_u8(b, 0x83u); emit_u8(b, 0xEFu); emit_u8(b, width);

    /* cmp r14, r15 (4D 39 FE) */
    emit_u8(b, 0x4Du); emit_u8(b, 0x39u); emit_u8(b, 0xFEu);
    size_t ja_oob = emit_jcc_rel32(b, 0x87u); /* ja (rel_off > len - width) */
    record_fixup(b->invalid_fixups, &b->num_invalid_fixups, ja_oob, b);

    /* Reconstruct verified effective address: r14 += frame->s<region_id>_ptr */
    emit_load_frame_u64(b, TISA_S1, ptr_off);
    /* add r14, r15 (4D 01 FE) */
    emit_u8(b, 0x4Du); emit_u8(b, 0x01u); emit_u8(b, 0xFEu);
}

static const char *tisa_opcode_name(TcIsaOpcode op);

static bool is_static_inbounds_mem(const X86EmitBuf *b,
                                   uint8_t region_id,
                                   uint8_t base_v,
                                   int32_t disp32,
                                   uint8_t width) {
    /* Entry validation permits any pointer `v` in `[base, base + len]` (including
     * `v == base + len`), not `v == base`, so `init_reg` pointers still require
     * dynamic bounds checking before dereference. */
    (void)b;
    (void)region_id;
    (void)base_v;
    (void)disp32;
    (void)width;
    return false;
}

static void emit_instr(X86EmitBuf *b, const TcIsaInstr *ins) {
    if (!b->is_static_leaf) {
        emit_fuel_step(b);
    }
    size_t s0 = b->len;
    uint16_t sm = 0u;
    switch (ins->op) {
        case TISA_OP_IMM: {
            uint64_t v = ins->imm64;
            if (ins->ty == TISA_TYPE_U32Z) v = (uint64_t)(uint32_t)v;
            else if (ins->ty == TISA_TYPE_I32S) v = (uint64_t)(int64_t)(int32_t)(uint32_t)v;
            else if (ins->ty == TISA_TYPE_BOOL) v &= 1ull;
            emit_mov_imm64(b, ins->dst, v);
            break;
        }

        case TISA_OP_MOV:
            emit_mov_r64_r64(b, ins->dst, ins->src1);
            emit_canon_reg(b, ins->dst, ins->ty);
            break;

        case TISA_OP_BIN: {
            sm = 0x1u;
            b->scratch_mask |= 0x1u;
            emit_mov_r64_r64(b, TISA_S0, ins->src1);
            uint8_t s2 = X86_HW_REG[ins->src2];
            uint8_t r14_hw = X86_HW_REG[TISA_S0]; /* 14 */
            switch (ins->subop) {
                case TISA_BIN_ADD:
                    emit_u8(b, rex_byte(1, s2, 0, r14_hw));
                    emit_u8(b, 0x01u);
                    emit_u8(b, modrm_byte(3, s2, r14_hw));
                    break;
                case TISA_BIN_SUB:
                    emit_u8(b, rex_byte(1, s2, 0, r14_hw));
                    emit_u8(b, 0x29u);
                    emit_u8(b, modrm_byte(3, s2, r14_hw));
                    break;
                case TISA_BIN_AND:
                    emit_u8(b, rex_byte(1, s2, 0, r14_hw));
                    emit_u8(b, 0x21u);
                    emit_u8(b, modrm_byte(3, s2, r14_hw));
                    break;
                case TISA_BIN_OR:
                    emit_u8(b, rex_byte(1, s2, 0, r14_hw));
                    emit_u8(b, 0x09u);
                    emit_u8(b, modrm_byte(3, s2, r14_hw));
                    break;
                case TISA_BIN_XOR:
                    emit_u8(b, rex_byte(1, s2, 0, r14_hw));
                    emit_u8(b, 0x31u);
                    emit_u8(b, modrm_byte(3, s2, r14_hw));
                    break;
                case TISA_BIN_MULLO:
                    emit_u8(b, rex_byte(1, r14_hw, 0, s2));
                    emit_u8(b, 0x0Fu);
                    emit_u8(b, 0xAFu);
                    emit_u8(b, modrm_byte(3, r14_hw, s2));
                    break;
            }
            emit_mov_r64_r64(b, ins->dst, TISA_S0);
            emit_canon_reg(b, ins->dst, ins->ty);
            break;
        }

        case TISA_OP_SHIFT: {
            emit_mov_r64_r64(b, ins->dst, ins->src1);
            uint8_t d = X86_HW_REG[ins->dst];
            uint8_t sh = ins->bit_width;
            if ((ins->ty == TISA_TYPE_U32Z || ins->ty == TISA_TYPE_I32S) && ins->subop == TISA_SHIFT_SHRU) {
                emit_zext32_reg(b, ins->dst);
            } else if ((ins->ty == TISA_TYPE_U32Z || ins->ty == TISA_TYPE_I32S) && ins->subop == TISA_SHIFT_SHRS) {
                emit_sext32_reg(b, ins->dst);
            }
            uint8_t ext = (ins->subop == TISA_SHIFT_SHL)  ? 4u :
                          (ins->subop == TISA_SHIFT_SHRU) ? 5u : 7u;
            emit_u8(b, rex_byte(1, 0, 0, d));
            emit_u8(b, 0xC1u);
            emit_u8(b, modrm_byte(3, ext, d));
            emit_u8(b, sh);
            emit_canon_reg(b, ins->dst, ins->ty);
            break;
        }

        case TISA_OP_EXTRACT: {
            sm = 0x1u;
            b->scratch_mask |= 0x1u;
            emit_mov_r64_r64(b, ins->dst, ins->src1);
            uint8_t d = X86_HW_REG[ins->dst];
            uint8_t lsb = ins->scale_lg2;
            uint8_t wid = ins->bit_width;
            if (lsb > 0u) {
                emit_u8(b, rex_byte(1, 0, 0, d));
                emit_u8(b, 0xC1u);
                emit_u8(b, modrm_byte(3, 5, d)); /* shr r64, lsb */
                emit_u8(b, lsb);
            }
            if (wid < 64u) {
                uint64_t mask = (1ull << wid) - 1ull;
                emit_mov_imm64(b, TISA_S0, mask);
                uint8_t r14_hw = X86_HW_REG[TISA_S0];
                emit_u8(b, rex_byte(1, r14_hw, 0, d));
                emit_u8(b, 0x21u);
                emit_u8(b, modrm_byte(3, r14_hw, d)); /* and r64(dst), r14 */
            }
            emit_canon_reg(b, ins->dst, ins->ty);
            break;
        }

        case TISA_OP_ADDR: {
            sm = 0x3u;
            b->scratch_mask |= 0x3u;
            int32_t ptr_off = (int32_t)(ins->region_id * 16u);
            int32_t len_off = (int32_t)(ins->region_id * 16u + 8u);

            /* r14 = cur_ptr - base_ptr (jb -> invalid_input) */
            emit_mov_r64_r64(b, TISA_S0, ins->src1);
            emit_load_frame_u64(b, TISA_S1, ptr_off);
            emit_u8(b, 0x4Du); emit_u8(b, 0x29u); emit_u8(b, 0xFEu); /* sub r14, r15 */
            size_t jb_base = emit_jcc_rel32(b, 0x82u);
            record_fixup(b->invalid_fixups, &b->num_invalid_fixups, jb_base, b);

            /* Verify base_off <= len_bytes */
            emit_load_frame_u64(b, TISA_S1, len_off);
            emit_u8(b, 0x4Du); emit_u8(b, 0x39u); emit_u8(b, 0xFEu); /* cmp r14, r15 */
            size_t ja_base = emit_jcc_rel32(b, 0x87u);
            record_fixup(b->invalid_fixups, &b->num_invalid_fixups, ja_base, b);

            if (ins->src2 != 0xFFu) {
                if (ins->scale_lg2 > 0u) {
                    emit_mov_r64_r64(b, TISA_S1, ins->src2);
                    /* shr r15, (64 - scale_lg2) */
                    emit_u8(b, 0x49u); emit_u8(b, 0xC1u); emit_u8(b, 0xEFu);
                    emit_u8(b, (uint8_t)(64u - ins->scale_lg2));
                    size_t jnz_sh = emit_jcc_rel32(b, 0x85u); /* jnz -> overflow */
                    record_fixup(b->invalid_fixups, &b->num_invalid_fixups, jnz_sh, b);
                }
                emit_mov_r64_r64(b, TISA_S1, ins->src2);
                if (ins->scale_lg2 > 0u) {
                    /* shl r15, scale_lg2 */
                    emit_u8(b, 0x49u); emit_u8(b, 0xC1u); emit_u8(b, 0xE7u);
                    emit_u8(b, ins->scale_lg2);
                }
                /* add r14, r15; jc -> invalid_input */
                emit_u8(b, 0x4Du); emit_u8(b, 0x01u); emit_u8(b, 0xFEu);
                size_t jc_idx = emit_jcc_rel32(b, 0x82u);
                record_fixup(b->invalid_fixups, &b->num_invalid_fixups, jc_idx, b);

                emit_load_frame_u64(b, TISA_S1, len_off);
                emit_u8(b, 0x4Du); emit_u8(b, 0x39u); emit_u8(b, 0xFEu); /* cmp r14, r15 */
                size_t ja_idx = emit_jcc_rel32(b, 0x87u);
                record_fixup(b->invalid_fixups, &b->num_invalid_fixups, ja_idx, b);
            }

            if (ins->disp32 > 0) {
                emit_mov_imm64(b, TISA_S1, (uint64_t)(uint32_t)ins->disp32);
                emit_u8(b, 0x4Du); emit_u8(b, 0x01u); emit_u8(b, 0xFEu); /* add r14, r15 */
                size_t jc_d = emit_jcc_rel32(b, 0x82u);
                record_fixup(b->invalid_fixups, &b->num_invalid_fixups, jc_d, b);

                emit_load_frame_u64(b, TISA_S1, len_off);
                emit_u8(b, 0x4Du); emit_u8(b, 0x39u); emit_u8(b, 0xFEu); /* cmp r14, r15 */
                size_t ja_d = emit_jcc_rel32(b, 0x87u);
                record_fixup(b->invalid_fixups, &b->num_invalid_fixups, ja_d, b);
            } else if (ins->disp32 < 0) {
                uint64_t mag = (uint64_t)(-(int64_t)ins->disp32);
                emit_mov_imm64(b, TISA_S1, mag);
                emit_u8(b, 0x4Du); emit_u8(b, 0x29u); emit_u8(b, 0xFEu); /* sub r14, r15 */
                size_t jb_d = emit_jcc_rel32(b, 0x82u);
                record_fixup(b->invalid_fixups, &b->num_invalid_fixups, jb_d, b);
            }

            /* Reconstruct pointer: r14 += base_ptr; mov dst, r14 */
            emit_load_frame_u64(b, TISA_S1, ptr_off);
            emit_u8(b, 0x4Du); emit_u8(b, 0x01u); emit_u8(b, 0xFEu); /* add r14, r15 */
            emit_mov_r64_r64(b, ins->dst, TISA_S0);
            break;
        }

        case TISA_OP_LOAD: {
            if (ins->region_id == TISA_REGION_FRAME) {
                emit_load_frame_u64(b, ins->dst, ins->disp32);
                emit_canon_reg(b, ins->dst, ins->ty);
                break;
            }
            if (is_static_inbounds_mem(b, ins->region_id, ins->src1, ins->disp32, ins->subop)) {
                uint8_t d = X86_HW_REG[ins->dst];
                uint8_t base_hw = X86_HW_REG[ins->src1];
                if (ins->subop == TISA_MEM_U8) {
                    emit_u8(b, rex_byte(0, d, 0, base_hw));
                    emit_u8(b, 0x0Fu);
                    emit_u8(b, 0xB6u);
                    emit_u8(b, modrm_byte(2, d, base_hw));
                    emit_u32(b, (uint32_t)ins->disp32);
                } else if (ins->subop == TISA_MEM_U32) {
                    emit_u8(b, rex_byte(0, d, 0, base_hw));
                    emit_u8(b, 0x8Bu);
                    emit_u8(b, modrm_byte(2, d, base_hw));
                    emit_u32(b, (uint32_t)ins->disp32);
                } else {
                    emit_u8(b, rex_byte(1, d, 0, base_hw));
                    emit_u8(b, 0x8Bu);
                    emit_u8(b, modrm_byte(2, d, base_hw));
                    emit_u32(b, (uint32_t)ins->disp32);
                }
                emit_canon_reg(b, ins->dst, ins->ty);
                break;
            }
            sm = 0x3u;
            emit_checked_mem_addr_in_r14(b, ins->region_id, ins->src1, ins->disp32, ins->subop);
            uint8_t d = X86_HW_REG[ins->dst];
            uint8_t r14_hw = X86_HW_REG[TISA_S0]; /* 14 -> low=6, REX.B=1 */
            if (ins->subop == TISA_MEM_U8) {
                emit_u8(b, rex_byte(0, d, 0, r14_hw));
                emit_u8(b, 0x0Fu);
                emit_u8(b, 0xB6u);
                emit_u8(b, modrm_byte(0, d, r14_hw)); /* movzx r32(dst), byte ptr [r14] */
            } else if (ins->subop == TISA_MEM_U32) {
                emit_u8(b, rex_byte(0, d, 0, r14_hw));
                emit_u8(b, 0x8Bu);
                emit_u8(b, modrm_byte(0, d, r14_hw)); /* mov r32(dst), dword ptr [r14] */
            } else {
                emit_u8(b, rex_byte(1, d, 0, r14_hw));
                emit_u8(b, 0x8Bu);
                emit_u8(b, modrm_byte(0, d, r14_hw)); /* mov r64(dst), qword ptr [r14] */
            }
            emit_canon_reg(b, ins->dst, ins->ty);
            break;
        }

        case TISA_OP_STORE: {
            if (is_static_inbounds_mem(b, ins->region_id, ins->src1, ins->disp32, ins->subop)) {
                uint8_t s = X86_HW_REG[ins->src2];
                uint8_t base_hw = X86_HW_REG[ins->src1];
                if (ins->subop == TISA_MEM_U8) {
                    emit_u8(b, rex_byte(0, s, 0, base_hw));
                    emit_u8(b, 0x88u);
                    emit_u8(b, modrm_byte(2, s, base_hw));
                    emit_u32(b, (uint32_t)ins->disp32);
                } else if (ins->subop == TISA_MEM_U32) {
                    emit_u8(b, rex_byte(0, s, 0, base_hw));
                    emit_u8(b, 0x89u);
                    emit_u8(b, modrm_byte(2, s, base_hw));
                    emit_u32(b, (uint32_t)ins->disp32);
                } else {
                    emit_u8(b, rex_byte(1, s, 0, base_hw));
                    emit_u8(b, 0x89u);
                    emit_u8(b, modrm_byte(2, s, base_hw));
                    emit_u32(b, (uint32_t)ins->disp32);
                }
                break;
            }
            sm = 0x3u;
            emit_checked_mem_addr_in_r14(b, ins->region_id, ins->src1, ins->disp32, ins->subop);
            uint8_t s = X86_HW_REG[ins->src2];
            uint8_t r14_hw = X86_HW_REG[TISA_S0]; /* 14 -> low=6, REX.B=1 */
            if (ins->subop == TISA_MEM_U8) {
                /* Always emit REX byte so rsi/rdi map to sil/dil! */
                emit_u8(b, rex_byte(0, s, 0, r14_hw));
                emit_u8(b, 0x88u);
                emit_u8(b, modrm_byte(0, s, r14_hw)); /* mov byte ptr [r14], r8(src2) */
            } else if (ins->subop == TISA_MEM_U32) {
                emit_u8(b, rex_byte(0, s, 0, r14_hw));
                emit_u8(b, 0x89u);
                emit_u8(b, modrm_byte(0, s, r14_hw)); /* mov dword ptr [r14], r32(src2) */
            } else {
                emit_u8(b, rex_byte(1, s, 0, r14_hw));
                emit_u8(b, 0x89u);
                emit_u8(b, modrm_byte(0, s, r14_hw)); /* mov qword ptr [r14], r64(src2) */
            }
            break;
        }

        case TISA_OP_CMP: {
            if (b->is_static_leaf && ins->ty == TISA_TYPE_U64 && ins->bit_width == 0u) {
                uint8_t s1_hw = X86_HW_REG[ins->src1];
                uint8_t s2_hw = X86_HW_REG[ins->src2];
                emit_u8(b, rex_byte(1, s2_hw, 0, s1_hw));
                emit_u8(b, 0x39u);
                emit_u8(b, modrm_byte(3, s2_hw, s1_hw));
            } else {
                sm = 0x3u;
                b->scratch_mask |= 0x3u;
                emit_mov_r64_r64(b, TISA_S0, ins->src1);
                if (ins->bit_width != 0u) {
                    emit_mov_imm64(b, TISA_S1, ins->imm64);
                } else {
                    emit_mov_r64_r64(b, TISA_S1, ins->src2);
                }
                if (ins->ty == TISA_TYPE_U32Z) {
                    emit_zext32_reg(b, TISA_S0);
                    emit_zext32_reg(b, TISA_S1);
                } else if (ins->ty == TISA_TYPE_I32S) {
                    emit_sext32_reg(b, TISA_S0);
                    emit_sext32_reg(b, TISA_S1);
                }
                /* cmp r14, r15 (4D 39 FE) */
                emit_u8(b, 0x4Du); emit_u8(b, 0x39u); emit_u8(b, 0xFEu);
            }

            if (b->is_static_leaf && ins == b->fused_cmp_ins) {
                uint8_t inv_cc = 0x85u;
                switch (ins->subop) {
                    case TISA_CMP_EQ:  inv_cc = 0x85u; break; /* jne */
                    case TISA_CMP_NE:  inv_cc = 0x84u; break; /* je  */
                    case TISA_CMP_ULT: inv_cc = 0x83u; break; /* jae */
                    case TISA_CMP_ULE: inv_cc = 0x87u; break; /* ja  */
                    case TISA_CMP_SLT: inv_cc = 0x8Du; break; /* jge */
                    case TISA_CMP_SLE: inv_cc = 0x8Fu; break; /* jg  */
                }
                b->fused_cmp_inv_cc = inv_cc;
                break;
            }

            uint8_t setcc_op = 0x94u;
            switch (ins->subop) {
                case TISA_CMP_EQ:  setcc_op = 0x94u; break; /* sete  */
                case TISA_CMP_NE:  setcc_op = 0x95u; break; /* setne */
                case TISA_CMP_ULT: setcc_op = 0x92u; break; /* setb  */
                case TISA_CMP_ULE: setcc_op = 0x96u; break; /* setbe */
                case TISA_CMP_SLT: setcc_op = 0x9Cu; break; /* setl  */
                case TISA_CMP_SLE: setcc_op = 0x9Eu; break; /* setle */
            }
            uint8_t d = X86_HW_REG[ins->dst];
            /* Emit REX byte unconditionally so rsi/rdi encode sil/dil */
            emit_u8(b, rex_byte(0, 0, 0, d));
            emit_u8(b, 0x0Fu);
            emit_u8(b, setcc_op);
            emit_u8(b, modrm_byte(3, 0, d));
            /* movzx r32(dst), r8(dst) */
            emit_u8(b, rex_byte(0, d, 0, d));
            emit_u8(b, 0x0Fu);
            emit_u8(b, 0xB6u);
            emit_u8(b, modrm_byte(3, d, d));
            break;
        }

        case TISA_OP_SELECT: {
            sm = 0x3u;
            b->scratch_mask |= 0x3u;
            emit_mov_r64_r64(b, TISA_S0, ins->src1); /* vtrue  -> r14 */
            emit_mov_r64_r64(b, TISA_S1, ins->src2); /* vfalse -> r15 */
            uint8_t c = X86_HW_REG[ins->src3];
            /* test r64(src3), r64(src3) */
            emit_u8(b, rex_byte(1, c, 0, c));
            emit_u8(b, 0x85u);
            emit_u8(b, modrm_byte(3, c, c));
            /* cmovz r14, r15 (4D 0F 44 F7) */
            emit_u8(b, 0x4Du);
            emit_u8(b, 0x0Fu);
            emit_u8(b, 0x44u);
            emit_u8(b, 0xF7u);
            emit_mov_r64_r64(b, ins->dst, TISA_S0);
            emit_canon_reg(b, ins->dst, ins->ty);
            break;
        }
    }
    push_span(b, tisa_opcode_name(ins->op), s0, b->len,
              ins->dst, ins->src1, ins->src2, ins->src3,
              ins->subop, ins->ty, ins->region_id, sm);
}

static const TcIsaInstr *rightmost_seq_instr(const TcIsaStmt *s) {
    while (s && s->kind == TISA_CTRL_SEQ) {
        s = s->u.seq.second;
    }
    if (s && s->kind == TISA_CTRL_INSTR) return &s->u.instr;
    return NULL;
}

/* Return -1 if `s` reads `reg` before writing it, +1 if `s` writes `reg` before reading it, 0 if neither */
static int stmt_reg_rw_order(const TcIsaStmt *s, uint8_t reg) {
    if (!s) return 0;
    switch (s->kind) {
        case TISA_CTRL_INSTR: {
            const TcIsaInstr *ins = &s->u.instr;
            if (ins->op != TISA_OP_IMM) {
                if (ins->src1 == reg) return -1;
                if ((ins->op == TISA_OP_BIN || ins->op == TISA_OP_STORE ||
                     ins->op == TISA_OP_SELECT ||
                     (ins->op == TISA_OP_ADDR && ins->src2 != 0xFFu) ||
                     (ins->op == TISA_OP_CMP && ins->bit_width == 0u)) && ins->src2 == reg) return -1;
                if (ins->op == TISA_OP_SELECT && ins->src3 == reg) return -1;
            }
            if (ins->op != TISA_OP_STORE && ins->dst == reg) return 1;
            return 0;
        }
        case TISA_CTRL_SEQ: {
            int r1 = stmt_reg_rw_order(s->u.seq.first, reg);
            if (r1 != 0) return r1;
            return stmt_reg_rw_order(s->u.seq.second, reg);
        }
        case TISA_CTRL_IF: {
            if (s->u.if_cond.cond_reg == reg) return -1;
            int rt = stmt_reg_rw_order(s->u.if_cond.then_branch, reg);
            int re = stmt_reg_rw_order(s->u.if_cond.else_branch, reg);
            if (rt < 0 || re < 0) return -1;
            if (rt > 0 && re > 0) return 1;
            return 0;
        }
        case TISA_CTRL_RETURN:
            return (s->u.ret.ret_reg == reg) ? -1 : 1;
        default:
            return -1;
    }
}

static size_t count_instr_ptr(const TcIsaStmt *s, const TcIsaInstr *target) {
    if (!s || !target) return 0;
    switch (s->kind) {
        case TISA_CTRL_INSTR:
            return (&s->u.instr == target) ? 1u : 0u;
        case TISA_CTRL_SEQ:
            return count_instr_ptr(s->u.seq.first, target) +
                   count_instr_ptr(s->u.seq.second, target);
        case TISA_CTRL_IF:
            return count_instr_ptr(s->u.if_cond.then_branch, target) +
                   count_instr_ptr(s->u.if_cond.else_branch, target);
        case TISA_CTRL_COUNT_LOOP:
            return count_instr_ptr(s->u.count_loop.body, target);
        case TISA_CTRL_EARLY_EXIT_LOOP:
            return count_instr_ptr(s->u.early_exit_loop.body, target);
        default:
            return 0u;
    }
}

static void emit_stmt(X86EmitBuf *b, const TcIsaStmt *stmt) {
    if (!stmt || b->overflow) return;
    size_t stmt_start = b->len;
    switch (stmt->kind) {
        case TISA_CTRL_INSTR:
            emit_instr(b, &stmt->u.instr);
            record_stmt_span(b, stmt, stmt_start, b->len);
            return;

        case TISA_CTRL_SEQ: {
            const TcIsaInstr * saved_cmp = b->fused_cmp_ins;
            const TcIsaStmt  * saved_if  = b->fused_if_stmt;
            if (b->is_static_leaf && stmt->u.seq.second &&
                stmt->u.seq.second->kind == TISA_CTRL_IF) {
                const TcIsaStmt *if_s = stmt->u.seq.second;
                const TcIsaInstr *last_ins = rightmost_seq_instr(stmt->u.seq.first);
                uint8_t cr = if_s->u.if_cond.cond_reg;
                if (last_ins && last_ins->op == TISA_OP_CMP && last_ins->dst == cr &&
                    count_instr_ptr(stmt->u.seq.first, last_ins) == 1u &&
                    stmt_reg_rw_order(if_s->u.if_cond.then_branch, cr) > 0 &&
                    stmt_reg_rw_order(if_s->u.if_cond.else_branch, cr) > 0) {
                    b->fused_cmp_ins = last_ins;
                    b->fused_if_stmt = if_s;
                }
            }
            emit_stmt(b, stmt->u.seq.first);
            emit_stmt(b, stmt->u.seq.second);
            b->fused_cmp_ins = saved_cmp;
            b->fused_if_stmt = saved_if;
            record_stmt_span(b, stmt, stmt_start, b->len);
            return;
        }

        case TISA_CTRL_IF: {
            size_t h0 = b->len;
            size_t jz_else;
            if (b->is_static_leaf && stmt == b->fused_if_stmt) {
                jz_else = emit_jcc_rel32(b, b->fused_cmp_inv_cc);
            } else {
                uint8_t c = X86_HW_REG[stmt->u.if_cond.cond_reg];
                /* test r64(cond), r64(cond) */
                emit_u8(b, rex_byte(1, c, 0, c));
                emit_u8(b, 0x85u);
                emit_u8(b, modrm_byte(3, c, c));
                jz_else = emit_jcc_rel32(b, 0x84u); /* jz */
            }
            push_span(b, "IF_TEST_JZ", h0, b->len,
                      0xFFu, stmt->u.if_cond.cond_reg, 0xFFu, 0xFFu,
                      0u, TISA_TYPE_BOOL, 0xFFu, 0u);
            emit_stmt(b, stmt->u.if_cond.then_branch);
            if (stmt->u.if_cond.else_branch) {
                size_t j0 = b->len;
                size_t jmp_end = emit_jmp_rel32(b);
                push_span(b, "IF_JMP_END", j0, b->len,
                          0xFFu, 0xFFu, 0xFFu, 0xFFu,
                          0u, TISA_TYPE_UNINIT, 0xFFu, 0u);
                patch_rel32(b, jz_else, b->len);
                emit_stmt(b, stmt->u.if_cond.else_branch);
                patch_rel32(b, jmp_end, b->len);
            } else {
                patch_rel32(b, jz_else, b->len);
            }
            record_stmt_span(b, stmt, stmt_start, b->len);
            return;
        }

        case TISA_CTRL_COUNT_LOOP: {
            size_t h0 = b->len;
            b->scratch_mask |= 0x1u;
            uint8_t ir = stmt->u.count_loop.idx_reg;
            uint8_t br = stmt->u.count_loop.bound_reg;
            /* Check bound <= max_iters */
            emit_mov_imm64(b, TISA_S0, (uint64_t)stmt->u.count_loop.max_iters);
            uint8_t br_hw  = X86_HW_REG[br];
            uint8_t r14_hw = X86_HW_REG[TISA_S0];
            /* cmp r64(br), r14 */
            emit_u8(b, rex_byte(1, r14_hw, 0, br_hw));
            emit_u8(b, 0x39u);
            emit_u8(b, modrm_byte(3, r14_hw, br_hw));
            size_t ja_unsup = emit_jcc_rel32(b, 0x87u); /* ja -> unsupported */
            record_fixup(b->unsupported_fixups, &b->num_unsupported_fixups, ja_unsup, b);

            /* idx_reg = 0 */
            emit_mov_imm64(b, ir, 0ull);

            size_t loop_head = b->len;
            uint8_t ir_hw = X86_HW_REG[ir];
            /* cmp r64(ir), r64(br) */
            emit_u8(b, rex_byte(1, br_hw, 0, ir_hw));
            emit_u8(b, 0x39u);
            emit_u8(b, modrm_byte(3, br_hw, ir_hw));
            size_t jae_exit = emit_jcc_rel32(b, 0x83u); /* jae */
            push_span(b, "COUNT_LOOP_HEAD", h0, b->len,
                      ir, br, 0xFFu, 0xFFu, 0u, TISA_TYPE_U64, 0xFFu, 0x1u);

            emit_stmt(b, stmt->u.count_loop.body);

            size_t t0 = b->len;
            /* add r64(ir), 1 */
            emit_u8(b, rex_byte(1, 0, 0, ir_hw));
            emit_u8(b, 0x83u);
            emit_u8(b, modrm_byte(3, 0, ir_hw));
            emit_u8(b, 0x01u);

            size_t jmp_back = emit_jmp_rel32(b);
            patch_rel32(b, jmp_back, loop_head);
            patch_rel32(b, jae_exit, b->len);
            push_span(b, "COUNT_LOOP_STEP", t0, b->len,
                      ir, br, 0xFFu, 0xFFu, 0u, TISA_TYPE_U64, 0xFFu, 0u);
            record_stmt_span(b, stmt, stmt_start, b->len);
            return;
        }

        case TISA_CTRL_EARLY_EXIT_LOOP: {
            size_t h0 = b->len;
            b->scratch_mask |= 0x1u;
            uint8_t ir = stmt->u.early_exit_loop.idx_reg;
            uint8_t br = stmt->u.early_exit_loop.bound_reg;
            uint8_t cr = stmt->u.early_exit_loop.cont_reg;
            /* Check bound <= max_iters */
            emit_mov_imm64(b, TISA_S0, (uint64_t)stmt->u.early_exit_loop.max_iters);
            uint8_t br_hw  = X86_HW_REG[br];
            uint8_t r14_hw = X86_HW_REG[TISA_S0];
            emit_u8(b, rex_byte(1, r14_hw, 0, br_hw));
            emit_u8(b, 0x39u);
            emit_u8(b, modrm_byte(3, r14_hw, br_hw));
            size_t ja_unsup = emit_jcc_rel32(b, 0x87u);
            record_fixup(b->unsupported_fixups, &b->num_unsupported_fixups, ja_unsup, b);

            /* idx_reg = 0 */
            emit_mov_imm64(b, ir, 0ull);

            size_t loop_head = b->len;
            uint8_t ir_hw = X86_HW_REG[ir];
            uint8_t cr_hw = X86_HW_REG[cr];
            /* cmp r64(ir), r64(br) */
            emit_u8(b, rex_byte(1, br_hw, 0, ir_hw));
            emit_u8(b, 0x39u);
            emit_u8(b, modrm_byte(3, br_hw, ir_hw));
            size_t jae_exit = emit_jcc_rel32(b, 0x83u);

            /* test r64(cr), r64(cr); jz exit */
            emit_u8(b, rex_byte(1, cr_hw, 0, cr_hw));
            emit_u8(b, 0x85u);
            emit_u8(b, modrm_byte(3, cr_hw, cr_hw));
            size_t jz_exit1 = emit_jcc_rel32(b, 0x84u);
            push_span(b, "EARLY_EXIT_LOOP_HEAD", h0, b->len,
                      ir, br, cr, 0xFFu, 0u, TISA_TYPE_U64, 0xFFu, 0x1u);

            emit_stmt(b, stmt->u.early_exit_loop.body);

            size_t t0 = b->len;
            /* Post-body check: test r64(cr), r64(cr); jz exit (matches tisa_eval_ref/tcalc) */
            emit_u8(b, rex_byte(1, cr_hw, 0, cr_hw));
            emit_u8(b, 0x85u);
            emit_u8(b, modrm_byte(3, cr_hw, cr_hw));
            size_t jz_exit2 = emit_jcc_rel32(b, 0x84u);

            /* add r64(ir), 1 */
            emit_u8(b, rex_byte(1, 0, 0, ir_hw));
            emit_u8(b, 0x83u);
            emit_u8(b, modrm_byte(3, 0, ir_hw));
            emit_u8(b, 0x01u);

            size_t jmp_back = emit_jmp_rel32(b);
            patch_rel32(b, jmp_back, loop_head);
            patch_rel32(b, jae_exit, b->len);
            patch_rel32(b, jz_exit1, b->len);
            patch_rel32(b, jz_exit2, b->len);
            push_span(b, "EARLY_EXIT_LOOP_POST", t0, b->len,
                      ir, br, cr, 0xFFu, 0u, TISA_TYPE_U64, 0xFFu, 0u);
            record_stmt_span(b, stmt, stmt_start, b->len);
            return;
        }

        case TISA_CTRL_RETURN: {
            size_t r0 = b->len;
            uint8_t rr = stmt->u.ret.ret_reg;
            emit_mov_r64_r64(b, TISA_V8, rr); /* rax = regs[ret_reg] */
            emit_store_frame_imm32(b, (int32_t)offsetof(TcIsaRuntimeFrame, status),
                                   (uint32_t)stmt->u.ret.outcome);
            emit_store_frame_u64(b, (int32_t)offsetof(TcIsaRuntimeFrame, ret_val), TISA_V8);
            size_t jmp_ep = emit_jmp_rel32(b);
            record_fixup(b->epilogue_fixups, &b->num_epilogue_fixups, jmp_ep, b);
            push_span(b, "RETURN", r0, b->len,
                      TISA_V8, rr, 0xFFu, 0xFFu,
                      (uint8_t)stmt->u.ret.outcome, TISA_TYPE_U64, TISA_REGION_FRAME, 0u);
            record_stmt_span(b, stmt, stmt_start, b->len);
            return;
        }
        case TISA_CTRL_FUND:   /* profile p1; this p0 emitter declines the program */
            b->overflow = true;
            return;
    }
}

/* =========================================================================
 * 3. Public Compiler, W^X Loader, Runner & Manifest Exporter
 * ========================================================================= */

/* Decode one x86-64 body instruction at `bytes[*pc]`, rejecting any rsp/rbp access,
 * SIB byte, or stack-touching opcode, and advancing `*pc` to the next instruction. */
static bool decode_and_verify_body_insn(const uint8_t *bytes,
                                        size_t byte_len,
                                        size_t *pc,
                                        size_t body_off,
                                        size_t epilogue_off,
                                        char *err_buf, size_t err_cap) {
    size_t p = *pc;
    if (p >= epilogue_off || epilogue_off > byte_len) return false;
    uint8_t b0 = bytes[p];

    /* 1. Unconditional near jump: E9 rel32 */
    if (b0 == 0xE9u) {
        if (p + 5u > epilogue_off) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "truncated jmp rel32 at %zu", p);
            return false;
        }
        uint32_t u = (uint32_t)bytes[p + 1] | ((uint32_t)bytes[p + 2] << 8) |
                     ((uint32_t)bytes[p + 3] << 16) | ((uint32_t)bytes[p + 4] << 24);
        int64_t tgt = (int64_t)(p + 5u) + (int64_t)(int32_t)u;
        if (tgt < (int64_t)body_off || tgt > (int64_t)epilogue_off) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "jmp rel32 at %zu targets %lld outside [%zu, %zu]", p, (long long)tgt, body_off, epilogue_off);
            return false;
        }
        *pc = p + 5u;
        return true;
    }

    /* 2. Conditional near jump: 0F 8x rel32 */
    if (b0 == 0x0Fu && p + 1u < epilogue_off && (bytes[p + 1] & 0xF0u) == 0x80u) {
        if (p + 6u > epilogue_off) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "truncated jcc rel32 at %zu", p);
            return false;
        }
        uint32_t u = (uint32_t)bytes[p + 2] | ((uint32_t)bytes[p + 3] << 8) |
                     ((uint32_t)bytes[p + 4] << 16) | ((uint32_t)bytes[p + 5] << 24);
        int64_t tgt = (int64_t)(p + 6u) + (int64_t)(int32_t)u;
        if (tgt < (int64_t)body_off || tgt > (int64_t)epilogue_off) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "jcc rel32 at %zu targets %lld outside [%zu, %zu]", p, (long long)tgt, body_off, epilogue_off);
            return false;
        }
        *pc = p + 6u;
        return true;
    }

    /* 3. Optional REX prefix (0x40..0x4F) */
    uint8_t rex_w = 0u, rex_r = 0u, rex_x = 0u, rex_b = 0u;
    if ((b0 & 0xF0u) == 0x40u) {
        rex_w = (b0 >> 3) & 1u;
        rex_r = (b0 >> 2) & 1u;
        rex_x = (b0 >> 1) & 1u;
        rex_b = b0 & 1u;
        if (rex_x != 0u) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "unexpected REX.X bit at %zu", p);
            return false;
        }
        p++;
        if (p >= epilogue_off) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "dangling REX prefix at %zu", p - 1u);
            return false;
        }
    }

    uint8_t op = bytes[p++];

    /* 3a. mov reg, imm32/imm64 (0xB8..0xBF) */
    if (op >= 0xB8u && op <= 0xBFu) {
        uint8_t hw = (uint8_t)((op - 0xB8u) | (rex_b << 3));
        if (hw == 4u || hw == 5u) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "mov imm touches rsp/rbp (hw=%u) at %zu", hw, *pc);
            return false;
        }
        size_t imm_len = rex_w ? 8u : 4u;
        if (p + imm_len > epilogue_off) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "truncated mov imm at %zu", *pc);
            return false;
        }
        *pc = p + imm_len;
        return true;
    }

    /* 3b. Two-byte opcode 0x0F after optional REX */
    if (op == 0x0Fu) {
        if (p + 2u > epilogue_off) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "truncated 0F insn at %zu", *pc);
            return false;
        }
        uint8_t op2   = bytes[p++];
        uint8_t modrm = bytes[p++];
        uint8_t mod   = (modrm >> 6) & 3u;
        uint8_t reg   = (uint8_t)(((modrm >> 3) & 7u) | (rex_r << 3));
        uint8_t rm    = (uint8_t)((modrm & 7u) | (rex_b << 3));
        if (reg == 4u || reg == 5u || rm == 4u || rm == 5u) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "0F %02x touches rsp/rbp at %zu", op2, *pc);
            return false;
        }
        if (op2 == 0xAFu || op2 == 0x44u) {
            if (mod != 3u) return false;
            *pc = p;
            return true;
        }
        if (op2 == 0xB6u) {
            if (mod == 2u && (rm & 7u) != 4u) {
                if (p + 4u > epilogue_off) return false;
                *pc = p + 4u;
                return true;
            }
            if (mod != 3u && !(mod == 0u && rm == 14u)) return false;
            *pc = p;
            return true;
        }
        if (op2 == 0x92u || op2 == 0x94u || op2 == 0x95u ||
            op2 == 0x96u || op2 == 0x9Cu || op2 == 0x9Eu) {
            if (mod != 3u || ((modrm >> 3) & 7u) != 0u) return false;
            *pc = p;
            return true;
        }
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "unsupported 0F %02x opcode at %zu", op2, *pc);
        return false;
    }

    /* 3c. Single-byte ModRM instructions */
    if (p >= epilogue_off) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "missing ModRM byte at %zu", *pc);
        return false;
    }
    uint8_t modrm = bytes[p++];
    uint8_t mod   = (modrm >> 6) & 3u;
    uint8_t reg   = (uint8_t)(((modrm >> 3) & 7u) | (rex_r << 3));
    uint8_t rm    = (uint8_t)((modrm & 7u) | (rex_b << 3));
    if (rm == 4u || rm == 5u) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "opcode %02x rm touches rsp/rbp at %zu", op, *pc);
        return false;
    }

    switch (op) {
        case 0x89u:
        case 0x8Bu:
        case 0x88u:
        case 0x63u:
        case 0x01u:
        case 0x29u:
        case 0x21u:
        case 0x09u:
        case 0x31u:
        case 0x39u:
        case 0x85u:
            if (reg == 4u || reg == 5u) {
                if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "opcode %02x reg touches rsp/rbp at %zu", op, *pc);
                return false;
            }
            if (mod == 3u) {
                *pc = p;
                return true;
            }
            if (mod == 2u && (rm & 7u) != 4u && (op == 0x89u || op == 0x8Bu || op == 0x88u)) {
                if (p + 4u > epilogue_off) return false;
                *pc = p + 4u;
                return true;
            }
            if (mod == 0u && rm == 14u && (op == 0x89u || op == 0x8Bu || op == 0x88u)) {
                *pc = p;
                return true;
            }
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "disallowed memory addressing in opcode %02x at %zu", op, *pc);
            return false;

        case 0x83u:
        case 0xC1u:
            if (mod == 3u) {
                if (p + 1u > epilogue_off) return false;
                *pc = p + 1u;
                return true;
            }
            if (op == 0x83u && mod == 2u && rm == 7u) {
                if (p + 5u > epilogue_off) return false;
                *pc = p + 5u;
                return true;
            }
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "disallowed ModRM in opcode %02x at %zu", op, *pc);
            return false;

        case 0xC7u:
            if (mod == 2u && rm == 7u && ((modrm >> 3) & 7u) == 0u) {
                if (p + 8u > epilogue_off) return false;
                *pc = p + 8u;
                return true;
            }
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "disallowed ModRM in C7 at %zu", *pc);
            return false;

        default:
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "disallowed or unknown body opcode %02x at %zu", op, *pc);
            return false;
    }
}

bool tisa_verify_x86_bytes(const uint8_t *bytes,
                           size_t byte_len,
                           size_t body_off,
                           size_t epilogue_off,
                           char *err_buf, size_t err_cap) {
    static const uint8_t EXP_PROLOGUE[9]  = { 0x53u, 0x41u, 0x54u, 0x41u, 0x55u, 0x41u, 0x56u, 0x41u, 0x57u };
    static const uint8_t EXP_EPILOGUE[10] = { 0x41u, 0x5Fu, 0x41u, 0x5Eu, 0x41u, 0x5Du, 0x41u, 0x5Cu, 0x5Bu, 0xC3u };
    if (!bytes || body_off != 9u || epilogue_off < body_off || epilogue_off + 10u != byte_len) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "invalid x86 wrapper offsets");
        return false;
    }
    if (memcmp(bytes, EXP_PROLOGUE, 9u) != 0) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "corrupted 9-byte ABI prologue");
        return false;
    }
    if (memcmp(bytes + epilogue_off, EXP_EPILOGUE, 10u) != 0) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "corrupted 10-byte ABI epilogue");
        return false;
    }
    size_t pc = body_off;
    while (pc < epilogue_off) {
        if (!decode_and_verify_body_insn(bytes, byte_len, &pc, body_off, epilogue_off, err_buf, err_cap)) {
            return false;
        }
    }
    if (pc != epilogue_off) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "body decode ended at %zu != epilogue %zu", pc, epilogue_off);
        return false;
    }
    return true;
}

/* Validate actual emitted body bytes, template spans, register operands, scratch mask,
 * and raw rel32 branch bytes before setting `no_spill_verified = true`. */
static bool verify_emitted_no_spill(const X86EmitBuf *b,
                                    size_t body_off,
                                    size_t epilogue_off,
                                    char *err_buf, size_t err_cap) {
    if (!b || b->num_spans < 3u || body_off != 9u || epilogue_off + 10u != b->len) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "invalid prologue/epilogue boundaries");
        return false;
    }
    if (!tisa_verify_x86_bytes(b->bytes, b->len, body_off, epilogue_off, err_buf, err_cap)) {
        return false;
    }
    size_t cur = 0u;
    for (size_t i = 0; i < b->num_spans; i++) {
        const X86TemplateSpan *sp = &b->spans[i];
        if (sp->byte_offset != cur || sp->byte_len == 0u) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "non-contiguous template span %zu", i);
            return false;
        }
        /* Verify that every body span decodes cleanly into whole instructions */
        if (sp->byte_offset >= body_off && sp->byte_offset + sp->byte_len <= epilogue_off) {
            size_t sp_pc = sp->byte_offset;
            size_t sp_end = sp->byte_offset + sp->byte_len;
            while (sp_pc < sp_end) {
                if (!decode_and_verify_body_insn(b->bytes, b->len, &sp_pc, body_off, epilogue_off, err_buf, err_cap)) {
                    return false;
                }
            }
            if (sp_pc != sp_end) {
                if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "span %zu does not end on instruction boundary", i);
                return false;
            }
        }
        cur += sp->byte_len;
        if ((sp->dst  != 0xFFu && sp->dst  >= TISA_NUM_VREGS) ||
            (sp->src1 != 0xFFu && sp->src1 >= TISA_NUM_VREGS) ||
            (sp->src2 != 0xFFu && sp->src2 >= TISA_NUM_VREGS) ||
            (sp->src3 != 0xFFu && sp->src3 >= TISA_NUM_VREGS)) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "span %zu uses out-of-range logical register", i);
            return false;
        }
        if ((sp->scratch_mask & ~0x3u) != 0u) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "span %zu uses scratch outside s0..s1", i);
            return false;
        }
    }
    if (cur != b->len) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "template spans do not cover full buffer");
        return false;
    }
    for (size_t i = 0; i < b->num_branches; i++) {
        const X86PatchedBranch *br = &b->branches[i];
        if (!br->patched || br->disp_offset < body_off || br->disp_offset + 4u > epilogue_off ||
            br->next_ip != br->disp_offset + 4u ||
            (int64_t)br->next_ip + (int64_t)br->rel32 != (int64_t)br->target_offset ||
            br->target_offset < body_off || br->target_offset > epilogue_off) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "unpatched or out-of-body branch %zu", i);
            return false;
        }
        /* Check raw opcode byte(s) and raw little-endian rel32 in b->bytes */
        if (br->cc_op == 0xE9u) {
            if (br->opcode_offset + 1u != br->disp_offset || b->bytes[br->opcode_offset] != 0xE9u) {
                if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "branch %zu jmp opcode byte mismatch", i);
                return false;
            }
        } else {
            if (br->opcode_offset + 2u != br->disp_offset ||
                b->bytes[br->opcode_offset] != 0x0Fu ||
                b->bytes[br->opcode_offset + 1u] != br->cc_op) {
                if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "branch %zu jcc opcode byte mismatch", i);
                return false;
            }
        }
        uint32_t raw_u = (uint32_t)b->bytes[br->disp_offset + 0] |
                         ((uint32_t)b->bytes[br->disp_offset + 1] << 8) |
                         ((uint32_t)b->bytes[br->disp_offset + 2] << 16) |
                         ((uint32_t)b->bytes[br->disp_offset + 3] << 24);
        int32_t raw_rel32 = (int32_t)raw_u;
        if (raw_rel32 != br->rel32 || (int64_t)br->next_ip + (int64_t)raw_rel32 != (int64_t)br->target_offset) {
            if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "branch %zu raw rel32 byte mismatch (%d vs %d)", i, raw_rel32, br->rel32);
            return false;
        }
    }
    return true;
}

static bool emit_program_to_buf(const TcIsaProgram *prog,
                                TcIsaTargetProfile profile,
                                X86EmitBuf *b,
                                TcIsaProgram *checked_out,
                                size_t *body_off_out,
                                size_t *epilogue_off_out,
                                char *err_buf, size_t err_cap) {
    memset(b, 0, sizeof(*b));
    *checked_out = *prog;
    if (!tisa_check_program(checked_out, err_buf, err_cap)) {
        return false;
    }
    b->profile        = profile;
    b->prog           = checked_out;
    b->is_static_leaf = (profile == TISA_PROFILE_P1 && checked_out->footprint.max_loop_bound == 0u);

    /* 1. Emit 9-byte System V AMD64 ABI callee-save prologue */
    size_t p0 = b->len;
    emit_u8(b, 0x53u);
    emit_u8(b, 0x41u); emit_u8(b, 0x54u);
    emit_u8(b, 0x41u); emit_u8(b, 0x55u);
    emit_u8(b, 0x41u); emit_u8(b, 0x56u);
    emit_u8(b, 0x41u); emit_u8(b, 0x57u);
    push_span(b, "PROLOGUE", p0, b->len, 0xFFu, 0xFFu, 0xFFu, 0xFFu,
              0u, TISA_TYPE_UNINIT, 0xFFu, 0u);

    *body_off_out = b->len; /* 9 */

    /* Reset frame->fuel_used = 0 at leaf entry in baseline profile */
    if (!b->is_static_leaf) {
        size_t f0 = b->len;
        emit_store_frame_imm32(b, (int32_t)offsetof(TcIsaRuntimeFrame, fuel_used), 0u);
        push_span(b, "INIT_FUEL_USED", f0, b->len, 0xFFu, 0xFFu, 0xFFu, 0xFFu,
                  0u, TISA_TYPE_U64, TISA_REGION_FRAME, 0u);
    }

    /* 2. Emit structured statement body */
    emit_stmt(b, checked_out->root);

    /* 3. Emit invalid_input handler if needed */
    if (b->num_invalid_fixups > 0) {
        size_t inv_pos = b->len;
        for (size_t i = 0; i < b->num_invalid_fixups; i++) {
            patch_rel32(b, b->invalid_fixups[i], inv_pos);
        }
        emit_mov_imm64(b, TISA_V8, (uint64_t)TISA_OUTCOME_INVALID_INPUT);
        emit_store_frame_imm32(b, (int32_t)offsetof(TcIsaRuntimeFrame, status),
                               (uint32_t)TISA_OUTCOME_INVALID_INPUT);
        emit_store_frame_u64(b, (int32_t)offsetof(TcIsaRuntimeFrame, ret_val), TISA_V8);
        size_t jmp_ep = emit_jmp_rel32(b);
        record_fixup(b->epilogue_fixups, &b->num_epilogue_fixups, jmp_ep, b);
        push_span(b, "INVALID_INPUT_HANDLER", inv_pos, b->len, TISA_V8, 0xFFu, 0xFFu, 0xFFu,
                  (uint8_t)TISA_OUTCOME_INVALID_INPUT, TISA_TYPE_U64, TISA_REGION_FRAME, 0u);
    }

    /* 4. Emit exhausted handler if needed */
    if (b->num_exhausted_fixups > 0) {
        size_t exh_pos = b->len;
        for (size_t i = 0; i < b->num_exhausted_fixups; i++) {
            patch_rel32(b, b->exhausted_fixups[i], exh_pos);
        }
        emit_mov_imm64(b, TISA_V8, (uint64_t)TISA_OUTCOME_EXHAUSTED);
        emit_store_frame_imm32(b, (int32_t)offsetof(TcIsaRuntimeFrame, status),
                               (uint32_t)TISA_OUTCOME_EXHAUSTED);
        emit_store_frame_u64(b, (int32_t)offsetof(TcIsaRuntimeFrame, ret_val), TISA_V8);
        size_t jmp_ep = emit_jmp_rel32(b);
        record_fixup(b->epilogue_fixups, &b->num_epilogue_fixups, jmp_ep, b);
        push_span(b, "EXHAUSTED_HANDLER", exh_pos, b->len, TISA_V8, 0xFFu, 0xFFu, 0xFFu,
                  (uint8_t)TISA_OUTCOME_EXHAUSTED, TISA_TYPE_U64, TISA_REGION_FRAME, 0u);
    }

    /* 5. Emit unsupported handler if needed */
    if (b->num_unsupported_fixups > 0) {
        size_t uns_pos = b->len;
        for (size_t i = 0; i < b->num_unsupported_fixups; i++) {
            patch_rel32(b, b->unsupported_fixups[i], uns_pos);
        }
        emit_mov_imm64(b, TISA_V8, (uint64_t)TISA_OUTCOME_UNSUPPORTED);
        emit_store_frame_imm32(b, (int32_t)offsetof(TcIsaRuntimeFrame, status),
                               (uint32_t)TISA_OUTCOME_UNSUPPORTED);
        emit_store_frame_u64(b, (int32_t)offsetof(TcIsaRuntimeFrame, ret_val), TISA_V8);
        size_t jmp_ep = emit_jmp_rel32(b);
        record_fixup(b->epilogue_fixups, &b->num_epilogue_fixups, jmp_ep, b);
        push_span(b, "UNSUPPORTED_HANDLER", uns_pos, b->len, TISA_V8, 0xFFu, 0xFFu, 0xFFu,
                  (uint8_t)TISA_OUTCOME_UNSUPPORTED, TISA_TYPE_U64, TISA_REGION_FRAME, 0u);
    }

    /* 6. Emit 10-byte System V AMD64 ABI callee-restore epilogue */
    *epilogue_off_out = b->len;
    for (size_t i = 0; i < b->num_epilogue_fixups; i++) {
        patch_rel32(b, b->epilogue_fixups[i], *epilogue_off_out);
    }
    size_t e0 = b->len;
    emit_u8(b, 0x41u); emit_u8(b, 0x5Fu);
    emit_u8(b, 0x41u); emit_u8(b, 0x5Eu);
    emit_u8(b, 0x41u); emit_u8(b, 0x5Du);
    emit_u8(b, 0x41u); emit_u8(b, 0x5Cu);
    emit_u8(b, 0x5Bu);
    emit_u8(b, 0xC3u);
    push_span(b, "EPILOGUE", e0, b->len, 0xFFu, 0xFFu, 0xFFu, 0xFFu,
              0u, TISA_TYPE_UNINIT, 0xFFu, 0u);

    if (b->overflow) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "x86-64 code/span buffer overflow");
        return false;
    }
    if (!verify_emitted_no_spill(b, *body_off_out, *epilogue_off_out, err_buf, err_cap)) {
        return false;
    }
    checked_out->footprint.scratch_reg_mask |= b->scratch_mask;
    checked_out->footprint.no_spill_verified = true;
    return true;
}

bool tisa_compile_x86(const TcIsaProgram *prog,
                      TcIsaTargetProfile profile,
                      TcIsaCompiledX86 *out,
                      char *err_buf, size_t err_cap) {
    if (!prog || !out) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "null program or output struct");
        return false;
    }
    memset(out, 0, sizeof(*out));
    X86EmitBuf b;
    TcIsaProgram checked;
    if (!emit_program_to_buf(prog, profile, &b, &checked, &out->body_offset, &out->epilogue_offset, err_buf, err_cap)) {
        return false;
    }

    /* Allocate page-aligned W^X buffer: write in PROT_READ|PROT_WRITE, then mprotect to PROT_READ|PROT_EXEC */
    size_t page_sz = (size_t)sysconf(_SC_PAGESIZE);
    if (page_sz == 0) page_sz = 4096u;
    size_t map_sz = (b.len + page_sz - 1u) & ~(page_sz - 1u);
    void *mem = mmap(NULL, map_sz, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mem == MAP_FAILED) {
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "mmap failed for x86-64 code page");
        return false;
    }
    memcpy(mem, b.bytes, b.len);
    if (mprotect(mem, map_sz, PROT_READ | PROT_EXEC) != 0) {
        munmap(mem, map_sz);
        if (err_buf && err_cap > 0) snprintf(err_buf, err_cap, "mprotect(PROT_READ|PROT_EXEC) failed");
        return false;
    }

    out->code_rx         = (uint8_t *)mem;
    out->code_cap        = map_sz;
    memcpy(out->bytes, b.bytes, b.len);
    out->byte_len        = b.len;
    out->branch_count    = b.branch_count;
    out->profile         = profile;
    out->footprint       = checked.footprint;
    x86_sha256_hex(out->bytes, out->byte_len, out->sha256_hex);
    out->entry           = (TcIsaNativeFn)(uintptr_t)mem;
    return true;
}

void tisa_free_x86(TcIsaCompiledX86 *comp) {
    if (!comp) return;
    if (comp->code_rx && comp->code_cap > 0) {
        munmap(comp->code_rx, comp->code_cap);
    }
    memset(comp, 0, sizeof(*comp));
}

TcIsaOutcome tisa_run_x86(const TcIsaProgram *prog,
                          const TcIsaCompiledX86 *comp,
                          TcIsaRuntimeFrame *frame,
                          uint64_t a1, uint64_t a2,
                          uint64_t a3, uint64_t a4,
                          uint64_t a5) {
    if (!prog || !comp || !comp->entry || !frame) {
        return TISA_OUTCOME_INVALID_INPUT;
    }
    uint64_t init_regs[TISA_NUM_VREGS] = {0};
    init_regs[TISA_V0] = (uint64_t)(uintptr_t)frame;
    init_regs[TISA_V1] = a1;
    init_regs[TISA_V2] = a2;
    init_regs[TISA_V3] = a3;
    init_regs[TISA_V4] = a4;
    init_regs[TISA_V5] = a5;

    char err[256] = {0};
    TcIsaOutcome vrc = tisa_validate_frame(prog, frame, init_regs, err, sizeof(err));
    if (vrc != TISA_OUTCOME_FIRED) {
        frame->status = vrc;
        frame->ret_val = vrc;
        return vrc;
    }

    (void)comp->entry(frame, a1, a2, a3, a4, a5);
    return (TcIsaOutcome)frame->status;
}

/* =========================================================================
 * 4. Deterministic JSON Manifest & Structured Disassembly Exporter
 * ========================================================================= */

static const char *tisa_type_name(TcIsaValType ty) {
    switch (ty) {
        case TISA_TYPE_UNINIT: return "uninit";
        case TISA_TYPE_U64:    return "U64";
        case TISA_TYPE_U32Z:   return "U32Z";
        case TISA_TYPE_I32S:   return "I32S";
        case TISA_TYPE_BOOL:   return "Bool";
        case TISA_TYPE_PTR:    return "Ptr";
        default:               return "unknown";
    }
}

static const char *tisa_opcode_name(TcIsaOpcode op) {
    switch (op) {
        case TISA_OP_IMM:     return "IMM";
        case TISA_OP_MOV:     return "MOV";
        case TISA_OP_BIN:     return "BIN";
        case TISA_OP_SHIFT:   return "SHIFT";
        case TISA_OP_EXTRACT: return "EXTRACT";
        case TISA_OP_ADDR:    return "ADDR";
        case TISA_OP_LOAD:    return "LOAD";
        case TISA_OP_STORE:   return "STORE";
        case TISA_OP_CMP:     return "CMP";
        case TISA_OP_SELECT:  return "SELECT";
        default:              return "UNKNOWN";
    }
}

static const char *x86_branch_mnemonic(uint8_t cc_op) {
    switch (cc_op) {
        case 0x82u: return "jb_jc";
        case 0x83u: return "jae_jnc";
        case 0x84u: return "jz_je";
        case 0x85u: return "jnz_jne";
        case 0x87u: return "ja";
        case 0xE9u: return "jmp";
        default:    return "jcc";
    }
}

static void lookup_stmt_span(const X86EmitBuf *b, const TcIsaStmt *stmt,
                             size_t *off_out, size_t *len_out) {
    *off_out = 0u;
    *len_out = 0u;
    if (!b || !stmt) return;
    for (size_t i = 0; i < b->num_stmt_spans; i++) {
        if (b->stmt_spans[i].stmt == stmt) {
            *off_out = b->stmt_spans[i].byte_offset;
            *len_out = b->stmt_spans[i].byte_len;
            return;
        }
    }
}

static void write_stmt_json(FILE *out, const X86EmitBuf *b, const TcIsaStmt *stmt, int indent) {
    if (!stmt) {
        fprintf(out, "null");
        return;
    }
    size_t boff = 0u, blen = 0u;
    lookup_stmt_span(b, stmt, &boff, &blen);

    switch (stmt->kind) {
        case TISA_CTRL_INSTR: {
            const TcIsaInstr *ins = &stmt->u.instr;
            fprintf(out,
                    "{\"ctrl\": \"INSTR\", \"byte_offset\": %zu, \"byte_len\": %zu, "
                    "\"op\": \"%s\", \"ty\": \"%s\", "
                    "\"dst\": %u, \"src1\": %u, \"src2\": %u, \"src3\": %u, "
                    "\"subop\": %u, \"region_id\": %u, \"scale_lg2\": %u, "
                    "\"bit_width\": %u, \"disp32\": %d, \"imm64\": \"0x%016" PRIx64 "\"}",
                    boff, blen,
                    tisa_opcode_name(ins->op), tisa_type_name(ins->ty),
                    (unsigned)ins->dst, (unsigned)ins->src1, (unsigned)ins->src2, (unsigned)ins->src3,
                    (unsigned)ins->subop, (unsigned)ins->region_id, (unsigned)ins->scale_lg2,
                    (unsigned)ins->bit_width, (int)ins->disp32, ins->imm64);
            return;
        }
        case TISA_CTRL_SEQ:
            fprintf(out, "{\"ctrl\": \"SEQ\", \"byte_offset\": %zu, \"byte_len\": %zu, \"first\": ", boff, blen);
            write_stmt_json(out, b, stmt->u.seq.first, indent + 2);
            fprintf(out, ", \"second\": ");
            write_stmt_json(out, b, stmt->u.seq.second, indent + 2);
            fprintf(out, "}");
            return;
        case TISA_CTRL_IF:
            fprintf(out, "{\"ctrl\": \"IF\", \"byte_offset\": %zu, \"byte_len\": %zu, \"cond_reg\": %u, \"then\": ",
                    boff, blen, (unsigned)stmt->u.if_cond.cond_reg);
            write_stmt_json(out, b, stmt->u.if_cond.then_branch, indent + 2);
            fprintf(out, ", \"else\": ");
            write_stmt_json(out, b, stmt->u.if_cond.else_branch, indent + 2);
            fprintf(out, "}");
            return;
        case TISA_CTRL_COUNT_LOOP:
            fprintf(out,
                    "{\"ctrl\": \"COUNT_LOOP\", \"byte_offset\": %zu, \"byte_len\": %zu, "
                    "\"idx_reg\": %u, \"bound_reg\": %u, \"max_iters\": %u, \"body\": ",
                    boff, blen,
                    (unsigned)stmt->u.count_loop.idx_reg,
                    (unsigned)stmt->u.count_loop.bound_reg,
                    stmt->u.count_loop.max_iters);
            write_stmt_json(out, b, stmt->u.count_loop.body, indent + 2);
            fprintf(out, "}");
            return;
        case TISA_CTRL_EARLY_EXIT_LOOP:
            fprintf(out,
                    "{\"ctrl\": \"EARLY_EXIT_LOOP\", \"byte_offset\": %zu, \"byte_len\": %zu, "
                    "\"idx_reg\": %u, \"bound_reg\": %u, "
                    "\"cont_reg\": %u, \"max_iters\": %u, \"body\": ",
                    boff, blen,
                    (unsigned)stmt->u.early_exit_loop.idx_reg,
                    (unsigned)stmt->u.early_exit_loop.bound_reg,
                    (unsigned)stmt->u.early_exit_loop.cont_reg,
                    stmt->u.early_exit_loop.max_iters);
            write_stmt_json(out, b, stmt->u.early_exit_loop.body, indent + 2);
            fprintf(out, "}");
            return;
        case TISA_CTRL_RETURN:
            fprintf(out,
                    "{\"ctrl\": \"RETURN\", \"byte_offset\": %zu, \"byte_len\": %zu, "
                    "\"outcome\": %u, \"ret_reg\": %u}",
                    boff, blen,
                    (unsigned)stmt->u.ret.outcome, (unsigned)stmt->u.ret.ret_reg);
            return;
        case TISA_CTRL_FUND:
            fprintf(out, "{\"ctrl\": \"FUND\", \"units\": %u}", (unsigned)stmt->u.fund.units);
            return;
    }
}

static const char *tisa_recipe_kind_name(TcIsaRecipeKind kind) {
    switch (kind) {
        case TISA_RECIPE_FUEL:            return "FUEL";
        case TISA_RECIPE_INSTR:           return "INSTR";
        case TISA_RECIPE_STORE_BYTE:      return "STORE_BYTE";
        case TISA_RECIPE_BRANCH:          return "BRANCH";
        case TISA_RECIPE_LOOP_ENTRY:      return "LOOP_ENTRY";
        case TISA_RECIPE_LOOP_HEADER:     return "LOOP_HEADER";
        case TISA_RECIPE_LOOP_LATCH:      return "LOOP_LATCH";
        case TISA_RECIPE_FINALIZE_STATUS: return "FINALIZE_STATUS";
        case TISA_RECIPE_FINALIZE_RETVAL: return "FINALIZE_RETVAL";
        default:                          return "UNKNOWN";
    }
}

bool tisa_write_program_manifest_json(FILE *out,
                                      const TcIsaProgram *prog,
                                      const TcIsaCompiledX86 *comp) {
    if (!out || !prog || !comp) return false;
    X86EmitBuf b;
    TcIsaProgram checked;
    size_t body_off = 0u, ep_off = 0u;
    char err[256] = {0};
    if (!emit_program_to_buf(prog, comp->profile, &b, &checked, &body_off, &ep_off, err, sizeof(err))) {
        return false;
    }
    TcIsaRecipeTable rtable;
    if (!tisa_lower_recipes(prog, &rtable, err, sizeof(err))) {
        return false;
    }

    fprintf(out, "{\n");
    fprintf(out, "  \"schema_version\": %u,\n", TISA_SCHEMA_VERSION);
    fprintf(out, "  \"profile_version\": \"%s\",\n", TISA_PROFILE_VERSION);
    fprintf(out, "  \"program_name\": \"%s\",\n", prog->name ? prog->name : "unnamed");
    fprintf(out, "  \"program_id\": %u,\n", prog->prog_id);
    fprintf(out, "  \"verification_status\": \"pending_formal_proof\",\n");
    fprintf(out, "  \"hosting_protocol\": {\n");
    fprintf(out, "    \"cell_constructor\": \"C_TISA_CELL(key_kind, key_lo32, key_hi32, val_lo32, val_hi32)\",\n");
    fprintf(out, "    \"key_injectivity\": \"full_64bit_key_lo32_hi32_plus_disjoint_key_kind_0_ctrl_1_reg_2_byte_3_frame\",\n");
    fprintf(out, "    \"carrier_rules\": [\"R_TISA_EDGE_0\", \"R_TISA_EDGE_1\", \"R_TISA_EDGE_2\", \"R_TISA_EDGE_3\", \"R_TISA_EDGE_4\", \"R_TISA_EDGE_5\", \"R_TISA_EDGE_6\", \"R_TISA_EDGE_7\", \"R_TISA_EDGE_8\", \"R_TISA_EDGE_9\"],\n");
    fprintf(out, "    \"control_rules\": [\"R_TISA_CTRL_0\", \"R_TISA_CTRL_1\", \"R_TISA_CTRL_2\"],\n");
    fprintf(out, "    \"carrier_role\": \"continuation_edge_take_ctrl_and_dst_keep_reads_make_ctrl_make_extra_dst\",\n");
    fprintf(out, "    \"valuation_guard\": \"tisa_edge_guard_allowed_and_tisa_eval_recipe_instr_guard_and_tisa_check_mem_offset_words\",\n");
    fprintf(out, "    \"execution_model\": \"board_driven_semantic_pc_recipe_table\",\n");
    fprintf(out, "    \"halt_point_encoding\": \"0x1000000000000000_or_outcome\",\n");
    fprintf(out, "    \"byte_cell_keys\": \"canonical_full_64bit_physical_address_deduplicated_across_ro_views\"\n");
    fprintf(out, "  },\n");

    fprintf(out, "  \"lowered_recipes\": {\n");
    fprintf(out, "    \"entry_point\": %" PRIu64 ",\n", rtable.entry_point);
    fprintf(out, "    \"point_count\": %u,\n", (unsigned)rtable.npoints);
    fprintf(out, "    \"halt_points\": {\n");
    fprintf(out, "      \"REFUSED\": \"0x%016" PRIx64 "\",\n", TISA_POINT_HALT(TISA_OUTCOME_REFUSED));
    fprintf(out, "      \"FIRED\": \"0x%016" PRIx64 "\",\n", TISA_POINT_HALT(TISA_OUTCOME_FIRED));
    fprintf(out, "      \"UNSUPPORTED\": \"0x%016" PRIx64 "\",\n", TISA_POINT_HALT(TISA_OUTCOME_UNSUPPORTED));
    fprintf(out, "      \"INVALID_INPUT\": \"0x%016" PRIx64 "\",\n", TISA_POINT_HALT(TISA_OUTCOME_INVALID_INPUT));
    fprintf(out, "      \"EXHAUSTED\": \"0x%016" PRIx64 "\"\n", TISA_POINT_HALT(TISA_OUTCOME_EXHAUSTED));
    fprintf(out, "    },\n");
    fprintf(out, "    \"fail_finalize_entry_points\": {\n");
    fprintf(out, "      \"REFUSED\": %" PRIu64 ",\n", rtable.fail_status_point[TISA_OUTCOME_REFUSED]);
    fprintf(out, "      \"FIRED\": %" PRIu64 ",\n", rtable.fail_status_point[TISA_OUTCOME_FIRED]);
    fprintf(out, "      \"UNSUPPORTED\": %" PRIu64 ",\n", rtable.fail_status_point[TISA_OUTCOME_UNSUPPORTED]);
    fprintf(out, "      \"INVALID_INPUT\": %" PRIu64 ",\n", rtable.fail_status_point[TISA_OUTCOME_INVALID_INPUT]);
    fprintf(out, "      \"EXHAUSTED\": %" PRIu64 "\n", rtable.fail_status_point[TISA_OUTCOME_EXHAUSTED]);
    fprintf(out, "    },\n");
    fprintf(out, "    \"immutable_frame_words\": [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 22, 23],\n");
    fprintf(out, "    \"mutable_frame_words\": [18, 19, 21],\n");
    fprintf(out, "    \"recipes\": [\n");
    for (uint32_t i = 0; i < rtable.npoints; i++) {
        const TcIsaPointRecipe *rc = &rtable.recipes[i];
        bool next_halt = (rc->next_point != UINT64_MAX) && TISA_POINT_IS_HALT(rc->next_point);
        int next_halt_oc = next_halt ? (int)TISA_POINT_HALT_OUTCOME(rc->next_point) : -1;
        int64_t next_pt = (rc->next_point == UINT64_MAX || next_halt) ? -1 : (int64_t)rc->next_point;
        int64_t alt_pt  = (rc->alt_point  == UINT64_MAX) ? -1 : (int64_t)rc->alt_point;
        int64_t fail_pt = (rc->fail_point == UINT64_MAX) ? -1 : (int64_t)rc->fail_point;
        fprintf(out,
                "      {\"point\": %u, \"kind\": \"%s\", \"charges_fuel\": %s, "
                "\"next_point\": %" PRId64 ", \"next_is_halt\": %s, \"next_halt_outcome\": %d, "
                "\"alt_point\": %" PRId64 ", \"fail_point\": %" PRId64 ", "
                "\"op\": \"%s\", \"ty\": \"%s\", \"dst\": %u, \"src1\": %u, \"src2\": %u, \"src3\": %u, "
                "\"subop\": %u, \"region_id\": %u, \"scale_lg2\": %u, \"bit_width\": %u, "
                "\"disp32\": %d, \"imm64\": \"0x%016" PRIx64 "\", "
                "\"byte_phase\": %u, \"byte_width\": %u, \"cond_reg\": %u, "
                "\"idx_reg\": %u, \"bound_reg\": %u, \"max_iters\": %u, "
                "\"outcome\": %u, \"ret_reg\": %u}%s\n",
                (unsigned)rc->point, tisa_recipe_kind_name(rc->kind),
                rc->charges_fuel ? "true" : "false",
                next_pt, next_halt ? "true" : "false", next_halt_oc,
                alt_pt, fail_pt,
                tisa_opcode_name(rc->instr.op), tisa_type_name(rc->instr.ty),
                (unsigned)rc->instr.dst, (unsigned)rc->instr.src1,
                (unsigned)rc->instr.src2, (unsigned)rc->instr.src3,
                (unsigned)rc->instr.subop, (unsigned)rc->instr.region_id,
                (unsigned)rc->instr.scale_lg2, (unsigned)rc->instr.bit_width,
                (int)rc->instr.disp32, rc->instr.imm64,
                (unsigned)rc->byte_phase, (unsigned)rc->byte_width, (unsigned)rc->cond_reg,
                (unsigned)rc->idx_reg, (unsigned)rc->bound_reg, rc->max_iters,
                (unsigned)rc->outcome, (unsigned)rc->ret_reg,
                (i + 1u < rtable.npoints) ? "," : "");
    }
    fprintf(out, "    ]\n");
    fprintf(out, "  },\n");

    fprintf(out, "  \"entry_state\": {\n");
    fprintf(out, "    \"init_reg_mask\": \"0x%04x\",\n", (unsigned)prog->init_reg_mask);
    fprintf(out, "    \"init_reg_types\": [");
    for (int r = 0; r < TISA_NUM_VREGS; r++) {
        fprintf(out, "\"%s\"%s", tisa_type_name(prog->init_reg_types[r]),
                (r + 1 < TISA_NUM_VREGS) ? ", " : "");
    }
    fprintf(out, "],\n");
    fprintf(out, "    \"init_reg_region\": [");
    for (int r = 0; r < TISA_NUM_VREGS; r++) {
        fprintf(out, "%u%s", (unsigned)prog->init_reg_region[r],
                (r + 1 < TISA_NUM_VREGS) ? ", " : "");
    }
    fprintf(out, "],\n");
    fprintf(out, "    \"regs\": [\n");
    for (int r = 0; r < TISA_NUM_VREGS; r++) {
        bool init = ((prog->init_reg_mask >> r) & 1u) != 0u;
        fprintf(out,
                "      {\"reg_id\": %d, \"initialized\": %s, \"ty\": \"%s\", \"region_id\": %u}%s\n",
                r, init ? "true" : "false",
                tisa_type_name(prog->init_reg_types[r]),
                (unsigned)prog->init_reg_region[r],
                (r + 1 < TISA_NUM_VREGS) ? "," : "");
    }
    fprintf(out, "    ]\n");
    fprintf(out, "  },\n");

    fprintf(out, "  \"register_map\": [\n");
    for (int r = 0; r < TISA_TOTAL_REGS; r++) {
        fprintf(out,
                "    {\"reg_id\": %d, \"role\": \"%s\", \"x86_64\": \"%s\", \"aarch64\": \"%s\", \"rv64\": \"%s\"}%s\n",
                r, (r < TISA_NUM_VREGS) ? "logical_vreg" : "emitter_scratch",
                X86_REG_NAME[r], AARCH64_REG_NAME[r], RV64_REG_NAME[r],
                (r + 1 < TISA_TOTAL_REGS) ? "," : "");
    }
    fprintf(out, "  ],\n");

    fprintf(out, "  \"regions\": [\n");
    for (uint8_t rid = 0; rid < prog->nregions; rid++) {
        const TcIsaRegionDecl *rd = &prog->regions[rid];
        const char *mstr = (rd->mode == TISA_CAP_RW) ? "RW" :
                           (rd->mode == TISA_CAP_RO) ? "RO" : "NONE";
        fprintf(out,
                "    {\"region_id\": %u, \"name\": \"%s\", \"mode\": \"%s\", "
                "\"min_byte_len\": %u, \"align_bytes\": %u}%s\n",
                (unsigned)rid, rd->name ? rd->name : "", mstr,
                rd->min_byte_len, rd->align_bytes,
                (rid + 1u < prog->nregions) ? "," : "");
    }
    fprintf(out, "  ],\n");

    fprintf(out, "  \"footprint\": {\n");
    fprintf(out, "    \"keep_reg_mask\": \"0x%04x\",\n", (unsigned)comp->footprint.keep_reg_mask);
    fprintf(out, "    \"write_reg_mask\": \"0x%04x\",\n", (unsigned)comp->footprint.write_reg_mask);
    fprintf(out, "    \"scratch_reg_mask\": \"0x%04x\",\n", (unsigned)comp->footprint.scratch_reg_mask);
    fprintf(out, "    \"keep_region_mask\": \"0x%04x\",\n", (unsigned)comp->footprint.keep_region_mask);
    fprintf(out, "    \"write_region_mask\": \"0x%04x\",\n", (unsigned)comp->footprint.write_region_mask);
    fprintf(out, "    \"max_loop_bound\": %u,\n", comp->footprint.max_loop_bound);
    fprintf(out, "    \"has_return\": %s,\n", comp->footprint.has_return ? "true" : "false");
    fprintf(out, "    \"no_spill_verified\": %s\n", comp->footprint.no_spill_verified ? "true" : "false");
    fprintf(out, "  },\n");

    fprintf(out, "  \"x86_64_artifact\": {\n");
    fprintf(out, "    \"target_profile\": \"%s\",\n",
            (comp->profile == TISA_PROFILE_P1) ? "P1_BMI1_BMI2" : "P0_BASELINE_X86_64");
    fprintf(out, "    \"byte_len\": %zu,\n", comp->byte_len);
    fprintf(out, "    \"prologue_offset\": 0,\n");
    fprintf(out, "    \"prologue_len\": %zu,\n", comp->body_offset);
    fprintf(out, "    \"body_offset\": %zu,\n", comp->body_offset);
    fprintf(out, "    \"epilogue_offset\": %zu,\n", comp->epilogue_offset);
    fprintf(out, "    \"epilogue_len\": %zu,\n", comp->byte_len - comp->epilogue_offset);
    fprintf(out, "    \"branch_count\": %u,\n", comp->branch_count);
    fprintf(out, "    \"sha256\": \"%s\",\n", comp->sha256_hex);
    fprintf(out, "    \"bytes_hex\": \"");
    for (size_t i = 0; i < comp->byte_len; i++) {
        fprintf(out, "%02x", comp->bytes[i]);
    }
    fprintf(out, "\",\n");

    fprintf(out, "    \"emitted_spans\": [\n");
    for (size_t i = 0; i < b.num_spans; i++) {
        const X86TemplateSpan *sp = &b.spans[i];
        fprintf(out,
                "      {\"span_idx\": %zu, \"kind\": \"%s\", \"byte_offset\": %zu, \"byte_len\": %zu, "
                "\"dst\": %u, \"src1\": %u, \"src2\": %u, \"src3\": %u, "
                "\"subop\": %u, \"ty\": \"%s\", \"region_id\": %u, \"scratch_mask\": \"0x%04x\"}%s\n",
                i, sp->kind, sp->byte_offset, sp->byte_len,
                (unsigned)sp->dst, (unsigned)sp->src1, (unsigned)sp->src2, (unsigned)sp->src3,
                (unsigned)sp->subop, tisa_type_name(sp->ty),
                (unsigned)sp->region_id, (unsigned)sp->scratch_mask,
                (i + 1 < b.num_spans) ? "," : "");
    }
    fprintf(out, "    ],\n");

    fprintf(out, "    \"patched_branches\": [\n");
    for (size_t i = 0; i < b.num_branches; i++) {
        const X86PatchedBranch *br = &b.branches[i];
        fprintf(out,
                "      {\"branch_idx\": %zu, \"mnemonic\": \"%s\", \"cc_op\": \"0x%02x\", "
                "\"opcode_offset\": %zu, \"disp_offset\": %zu, \"next_ip\": %zu, "
                "\"target_offset\": %zu, \"rel32\": %d, \"patched\": %s}%s\n",
                i, x86_branch_mnemonic(br->cc_op), (unsigned)br->cc_op,
                br->opcode_offset, br->disp_offset, br->next_ip,
                br->target_offset, (int)br->rel32,
                br->patched ? "true" : "false",
                (i + 1 < b.num_branches) ? "," : "");
    }
    fprintf(out, "    ]\n");
    fprintf(out, "  },\n");

    fprintf(out, "  \"structured_ast\": ");
    write_stmt_json(out, &b, prog->root, 2);
    fprintf(out, "\n}\n");
    return true;
}
