/* bench_hosted.c: cost of the tcalc-hosted t-ISA path on a fixed corpus, through the public API only
   (the same source builds against any tisa_core.c).

     bench_hosted --stats       one run per program: outcome, return value, firings (tcalc_fires),
                                live occurrences and the highest live occurrence id after the run,
                                each checked against the reference evaluator
     bench_hosted --time REPS   REPS hosted runs per program (for perf stat)

   Exit status 1 if a hosted run disagrees with the reference evaluator. */
#include "../tisa.h"
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NPROG 6

typedef struct {
    TcIsaProgram prog;
    TcIsaArena   arena;
    uint64_t     regs[TISA_NUM_VREGS];
    uint64_t     buf_init[8];
    uint64_t     fuel_budget;
    uint64_t     arg0;
} BenchCase;

static TcIsaStmt *seq(TcIsaArena *a, TcIsaStmt *s, TcIsaInstr ins) { return tisa_stmt_seq(a, s, tisa_stmt_instr(a, ins)); }

static void base_prog(BenchCase *c, const char *name, uint32_t id, bool region) {
    memset(c, 0, sizeof *c);
    tisa_arena_init(&c->arena, 256);
    c->prog.name = name;
    c->prog.prog_id = id;
    c->prog.init_reg_mask = 1u << TISA_V0;
    c->prog.init_reg_types[TISA_V0] = TISA_TYPE_U64;
    if (region) {
        c->prog.nregions = 1u;
        c->prog.regions[0] = (TcIsaRegionDecl){ 0, TISA_CAP_RW, 64, 8, "buf" };
        c->prog.init_reg_mask |= 1u << TISA_V1;
        c->prog.init_reg_types[TISA_V1] = TISA_TYPE_PTR;
        c->prog.init_reg_region[TISA_V1] = 0u;
    }
}

static void build(BenchCase *cs) {
    /* 0. scalar operations, with destination aliasing */
    BenchCase *c = &cs[0];
    base_prog(c, "bench_scalar", 201u, false);
    TcIsaArena *a = &c->arena;
    TcIsaStmt *s = NULL;
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U32Z, .dst = TISA_V2, .imm64 = 0x80000010ull });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_SHIFT, .subop = TISA_SHIFT_SHRS, .ty = TISA_TYPE_U32Z, .dst = TISA_V3, .src1 = TISA_V2, .bit_width = 4u });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U32Z, .dst = TISA_V4, .imm64 = 0xFFFFFFFFull });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_CMP, .subop = TISA_CMP_SLT, .ty = TISA_TYPE_U32Z, .dst = TISA_V5, .src1 = TISA_V4, .bit_width = 1u });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_CMP, .subop = TISA_CMP_ULT, .ty = TISA_TYPE_U64, .dst = TISA_V6, .src1 = TISA_V3, .src2 = TISA_V4 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V9, .imm64 = 0x1111222233334444ull });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V10, .imm64 = 0x5555666677778888ull });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_SELECT, .ty = TISA_TYPE_U64, .dst = TISA_V10, .src1 = TISA_V9, .src2 = TISA_V10, .src3 = TISA_V6 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_MOV, .ty = TISA_TYPE_BOOL, .dst = TISA_V11, .src1 = TISA_V5 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_SELECT, .ty = TISA_TYPE_BOOL, .dst = TISA_V11, .src1 = TISA_V5, .src2 = TISA_V6, .src3 = TISA_V11 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_EXTRACT, .ty = TISA_TYPE_U32Z, .dst = TISA_V7, .src1 = TISA_V9, .scale_lg2 = 16u, .bit_width = 16u });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U32Z, .dst = TISA_V8, .imm64 = 3ull });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_BIN, .subop = TISA_BIN_MULLO, .ty = TISA_TYPE_U32Z, .dst = TISA_V7, .src1 = TISA_V7, .src2 = TISA_V8 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_BIN, .subop = TISA_BIN_XOR, .ty = TISA_TYPE_U64, .dst = TISA_V9, .src1 = TISA_V9, .src2 = TISA_V10 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_BIN, .subop = TISA_BIN_SUB, .ty = TISA_TYPE_U64, .dst = TISA_V8, .src1 = TISA_V9, .src2 = TISA_V8 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_BIN, .subop = TISA_BIN_ADD, .ty = TISA_TYPE_U64, .dst = TISA_V8, .src1 = TISA_V8, .src2 = TISA_V8 });
    c->prog.root = tisa_stmt_seq(a, s, tisa_stmt_return(a, TISA_OUTCOME_FIRED, TISA_V8));

    /* 1. memory: stores and loads of 1, 4 and 8 bytes, an indexed address, a frame load */
    c = &cs[1];
    base_prog(c, "bench_memory", 202u, true);
    a = &c->arena; s = NULL;
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V2, .imm64 = 0x0102030405060708ull });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_STORE, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64, .src1 = TISA_V1, .src2 = TISA_V2, .region_id = 0u, .disp32 = 0 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_STORE, .subop = TISA_MEM_U32, .ty = TISA_TYPE_U64, .src1 = TISA_V1, .src2 = TISA_V2, .region_id = 0u, .disp32 = 8 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_STORE, .subop = TISA_MEM_U8, .ty = TISA_TYPE_U64, .src1 = TISA_V1, .src2 = TISA_V2, .region_id = 0u, .disp32 = 12 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_LOAD, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64, .dst = TISA_V3, .src1 = TISA_V1, .region_id = 0u, .disp32 = 0 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_LOAD, .subop = TISA_MEM_U32, .ty = TISA_TYPE_I32S, .dst = TISA_V4, .src1 = TISA_V1, .region_id = 0u, .disp32 = 4 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_LOAD, .subop = TISA_MEM_U8, .ty = TISA_TYPE_U64, .dst = TISA_V5, .src1 = TISA_V1, .region_id = 0u, .disp32 = 12 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V6, .imm64 = 2ull });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_ADDR, .dst = TISA_V7, .src1 = TISA_V1, .src2 = TISA_V6, .region_id = 0u, .scale_lg2 = 3u, .disp32 = 8 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_STORE, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64, .src1 = TISA_V7, .src2 = TISA_V3, .region_id = 0u, .disp32 = 0 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_LOAD, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64, .dst = TISA_V8, .src1 = TISA_V7, .region_id = 0u, .disp32 = -8 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_LOAD, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64, .dst = TISA_V9, .src1 = TISA_V0, .region_id = TISA_REGION_FRAME, .disp32 = 176 });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_BIN, .subop = TISA_BIN_ADD, .ty = TISA_TYPE_U64, .dst = TISA_V9, .src1 = TISA_V9, .src2 = TISA_V5 });
    c->prog.root = tisa_stmt_seq(a, s, tisa_stmt_return(a, TISA_OUTCOME_FIRED, TISA_V9));
    c->arg0 = 1000ull;

    /* 2. a counted loop of 40 iterations that adds and stores a byte */
    c = &cs[2];
    base_prog(c, "bench_count_loop", 203u, true);
    c->prog.init_reg_mask |= 1u << TISA_V2;
    c->prog.init_reg_types[TISA_V2] = TISA_TYPE_U64;
    a = &c->arena;
    TcIsaStmt *body = tisa_stmt_seq(a, tisa_stmt_instr(a, (TcIsaInstr){ .op = TISA_OP_BIN, .subop = TISA_BIN_ADD, .ty = TISA_TYPE_U64, .dst = TISA_V4, .src1 = TISA_V4, .src2 = TISA_V3 }),
                                       tisa_stmt_instr(a, (TcIsaInstr){ .op = TISA_OP_STORE, .subop = TISA_MEM_U8, .ty = TISA_TYPE_U64, .src1 = TISA_V1, .src2 = TISA_V4, .region_id = 0u, .disp32 = 16 }));
    s = NULL;
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V4, .imm64 = 7ull });
    s = tisa_stmt_seq(a, s, tisa_stmt_count_loop(a, TISA_V3, TISA_V2, 64u, body));
    c->prog.root = tisa_stmt_seq(a, s, tisa_stmt_return(a, TISA_OUTCOME_FIRED, TISA_V4));
    c->regs[TISA_V2] = 40ull;

    /* 3. an early-exit loop whose continuation turns false after 12 iterations, then a branch */
    c = &cs[3];
    base_prog(c, "bench_early_exit_if", 204u, false);
    c->prog.init_reg_mask |= 1u << TISA_V2;
    c->prog.init_reg_types[TISA_V2] = TISA_TYPE_U64;
    a = &c->arena;
    body = tisa_stmt_seq(a, tisa_stmt_instr(a, (TcIsaInstr){ .op = TISA_OP_BIN, .subop = TISA_BIN_ADD, .ty = TISA_TYPE_U64, .dst = TISA_V4, .src1 = TISA_V4, .src2 = TISA_V3 }),
                         tisa_stmt_instr(a, (TcIsaInstr){ .op = TISA_OP_CMP, .subop = TISA_CMP_ULT, .ty = TISA_TYPE_U64, .dst = TISA_V5, .src1 = TISA_V3, .bit_width = 1u, .imm64 = 11ull }));
    s = NULL;
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V4, .imm64 = 0ull });
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_BOOL, .dst = TISA_V5, .imm64 = 1ull });
    s = tisa_stmt_seq(a, s, tisa_stmt_early_exit_loop(a, TISA_V3, TISA_V2, TISA_V5, 64u, body));
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_CMP, .subop = TISA_CMP_EQ, .ty = TISA_TYPE_U64, .dst = TISA_V6, .src1 = TISA_V4, .bit_width = 1u, .imm64 = 66ull });
    TcIsaStmt *then_b = tisa_stmt_instr(a, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V7, .imm64 = 1ull });
    TcIsaStmt *else_b = tisa_stmt_instr(a, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V7, .imm64 = 2ull });
    s = tisa_stmt_seq(a, s, tisa_stmt_if(a, TISA_V6, then_b, else_b));
    c->prog.root = tisa_stmt_seq(a, s, tisa_stmt_return(a, TISA_OUTCOME_FIRED, TISA_V7));
    c->regs[TISA_V2] = 50ull;

    /* 4. fuel exhaustion inside a loop */
    c = &cs[4];
    base_prog(c, "bench_fuel", 205u, false);
    c->prog.init_reg_mask |= 1u << TISA_V2;
    c->prog.init_reg_types[TISA_V2] = TISA_TYPE_U64;
    a = &c->arena;
    body = tisa_stmt_instr(a, (TcIsaInstr){ .op = TISA_OP_BIN, .subop = TISA_BIN_ADD, .ty = TISA_TYPE_U64, .dst = TISA_V4, .src1 = TISA_V4, .src2 = TISA_V3 });
    s = NULL;
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = TISA_V4, .imm64 = 0ull });
    s = tisa_stmt_seq(a, s, tisa_stmt_count_loop(a, TISA_V3, TISA_V2, 64u, body));
    c->prog.root = tisa_stmt_seq(a, s, tisa_stmt_return(a, TISA_OUTCOME_FIRED, TISA_V4));
    c->regs[TISA_V2] = 60ull;
    c->fuel_budget = 25ull;

    /* 5. an out-of-bounds load: the failure edge */
    c = &cs[5];
    base_prog(c, "bench_oob_load", 206u, true);
    a = &c->arena; s = NULL;
    s = seq(a, s, (TcIsaInstr){ .op = TISA_OP_LOAD, .subop = TISA_MEM_U64, .ty = TISA_TYPE_U64, .dst = TISA_V2, .src1 = TISA_V1, .region_id = 0u, .disp32 = 60 });
    c->prog.root = tisa_stmt_seq(a, s, tisa_stmt_return(a, TISA_OUTCOME_FIRED, TISA_V2));
}

typedef struct {
    TcIsaOutcome rc;
    uint64_t regs[TISA_NUM_VREGS], status, ret_val, fuel_used, buf[8], fires;
    bool ok;
} RunOut;

static void run_case(BenchCase *c, int mode, RunOut *o) {
    TcIsaRuntimeFrame frame;
    memset(&frame, 0, sizeof frame);
    memset(o, 0, sizeof *o);
    memcpy(o->buf, c->buf_init, sizeof o->buf);
    if (c->prog.nregions) { frame.s0_ptr = (uint64_t)(uintptr_t)o->buf; frame.s0_len = sizeof o->buf; }
    frame.fuel_budget = c->fuel_budget;
    frame.arg0 = c->arg0;
    memcpy(o->regs, c->regs, sizeof o->regs);
    o->regs[TISA_V0] = (uint64_t)(uintptr_t)&frame;
    if (c->prog.nregions) o->regs[TISA_V1] = frame.s0_ptr;
    if (mode == 0) {
        o->rc = tisa_eval_ref(&c->prog, &frame, o->regs);
        o->ok = true;
    } else {
        TcIsaHostedRunResult hres;
        o->ok = tisa_try_eval_tcalc(&c->prog, &frame, o->regs, &hres) && hres.has_verdict;
        o->rc = hres.outcome;
        o->fires = hres.tcalc_fires;
    }
    o->regs[TISA_V0] = 0;   /* the frame's address differs between runs */
    uint64_t lo = (uint64_t)(uintptr_t)o->buf, hi = lo + sizeof o->buf;
    for (int r = 1; r < TISA_NUM_VREGS; r++)   /* so does the buffer's: pointers into it become offsets */
        if (c->prog.nregions && o->regs[r] >= lo && o->regs[r] <= hi) o->regs[r] = (o->regs[r] - lo) | (1ull << 63);
    o->status = frame.status; o->ret_val = frame.ret_val; o->fuel_used = frame.fuel_used;
}

static bool same(const RunOut *x, const RunOut *y) {
    return x->ok && y->ok && x->rc == y->rc && x->status == y->status && x->ret_val == y->ret_val &&
           x->fuel_used == y->fuel_used && !memcmp(x->regs, y->regs, sizeof x->regs) && !memcmp(x->buf, y->buf, sizeof x->buf);
}

int main(int argc, char **argv) {
    bool stats = argc >= 2 && !strcmp(argv[1], "--stats");
    long reps = (argc >= 3 && !strcmp(argv[1], "--time")) ? strtol(argv[2], NULL, 10) : 0;
    if (!stats && reps <= 0) { fprintf(stderr, "usage: %s --stats | --time REPS\n", argv[0]); return 2; }
    static BenchCase cs[NPROG];
    build(cs);
    char err[256];
    for (int i = 0; i < NPROG; i++)
        if (!tisa_check_program(&cs[i].prog, err, sizeof err)) { fprintf(stderr, "%s: %s\n", cs[i].prog.name, err); return 2; }
    int bad = 0;
    if (stats) {
        for (int i = 0; i < NPROG; i++) {
            RunOut ref, hosted;
            run_case(&cs[i], 0, &ref);
            run_case(&cs[i], 1, &hosted);
            uint32_t live = 0; Occ high = 0;
            for (Occ o = 1; o < (1u << 20); o++) if (tc_alive(o)) { live++; high = o; }
            bool agree = same(&ref, &hosted);
            bad += !agree;
            printf("%-20s outcome=%d ret=%" PRIu64 " fuel_used=%" PRIu64 " fires=%" PRIu64
                   " live_occurrences=%u highest_live_occurrence=%u reference=%s\n",
                   cs[i].prog.name, (int)hosted.rc, hosted.ret_val, hosted.fuel_used, hosted.fires,
                   live, (unsigned)high, agree ? "agrees" : "DIFFERS");
        }
    } else {
        for (long r = 0; r < reps; r++)
            for (int i = 0; i < NPROG; i++) {
                RunOut hosted;
                run_case(&cs[i], 1, &hosted);
                if (!hosted.ok) bad++;
            }
    }
    for (int i = 0; i < NPROG; i++) tisa_arena_free(&cs[i].arena);
    return bad ? 1 : 0;
}
