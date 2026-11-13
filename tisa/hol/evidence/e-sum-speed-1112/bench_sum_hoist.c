/* Sum of n u32 words: p1's default image, p1 with bounds hoisting, and GCC on the same loop. */
#include "tisa_ref.h"
#include "tisa_x86.h"
#include "tisa_print.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }

uint64_t sum_scalar(const uint32_t *v, uint64_t n);
static volatile uint64_t runtime_n = 4096;

__attribute__((noinline)) static uint64_t sum_c(const uint32_t *v, uint64_t n) {
    uint64_t s = 0;
    for (uint64_t i = 0; i < n; ++i) s += v[i];
    return s;
}

int main(int argc, char **argv) {
    const char *only = argc > 1 ? argv[1] : NULL;
    enum { N = 4096, REPS = 20000 };
    uint32_t *data = aligned_alloc(64, N * 4);
    for (unsigned i = 0; i < N; ++i) data[i] = i * 2654435761u;
    TcIsaStmt st[16]; memset(st, 0, sizeof st);
    TcIsaInstr acc = {.op = TISA_OP_IMM, .ty = TISA_TYPE_U64, .dst = 6, .imm64 = 0};
    TcIsaInstr at = {.op = TISA_OP_ADDR, .ty = TISA_TYPE_PTR, .dst = 8, .src1 = 1, .src2 = 7, .scale_lg2 = 2, .region_id = 0};
    TcIsaInstr ld = {.op = TISA_OP_LOAD, .ty = TISA_TYPE_U32Z, .dst = 9, .src1 = 8, .subop = 4, .region_id = 0};
    TcIsaInstr add = {.op = TISA_OP_BIN, .ty = TISA_TYPE_U64, .dst = 6, .src1 = 6, .src2 = 9, .subop = TISA_BIN_ADD};
    st[0] = (TcIsaStmt){.kind = TISA_CTRL_INSTR, .u.instr = acc};
    st[1] = (TcIsaStmt){.kind = TISA_CTRL_INSTR, .u.instr = at};
    st[2] = (TcIsaStmt){.kind = TISA_CTRL_INSTR, .u.instr = ld};
    st[3] = (TcIsaStmt){.kind = TISA_CTRL_INSTR, .u.instr = add};
    st[4] = (TcIsaStmt){.kind = TISA_CTRL_SEQ, .u.seq = {&st[2], &st[3]}};
    st[5] = (TcIsaStmt){.kind = TISA_CTRL_SEQ, .u.seq = {&st[1], &st[4]}};
    st[6] = (TcIsaStmt){.kind = TISA_CTRL_COUNT_LOOP, .u.count_loop = {.idx_reg = 7, .bound_reg = 2, .max_iters = 1u << 20, .body = &st[5]}};
    st[7] = (TcIsaStmt){.kind = TISA_CTRL_RETURN, .u.ret = {.outcome = TISA_OUTCOME_FIRED, .ret_reg = 6}};
    st[8] = (TcIsaStmt){.kind = TISA_CTRL_SEQ, .u.seq = {&st[6], &st[7]}};
    st[9] = (TcIsaStmt){.kind = TISA_CTRL_SEQ, .u.seq = {&st[0], &st[8]}};
    TcIsaProgram prog; memset(&prog, 0, sizeof prog);
    prog.name = "sum32"; prog.nregions = 1;
    prog.regions[0] = (TcIsaRegionDecl){.region_id = 0, .mode = TISA_CAP_RO, .min_byte_len = 0, .align_bytes = 4, .name = "v"};
    prog.init_reg_mask = 0x07; prog.init_reg_types[0] = TISA_TYPE_U64;
    prog.init_reg_types[1] = TISA_TYPE_PTR; prog.init_reg_region[1] = 0; prog.init_reg_types[2] = TISA_TYPE_U64;
    prog.root = &st[9];
    char err[256];

    TcIsaX86 p1, ph;
    const TcIsaX86Options hoist = {.hoist_bounds = true};
    if (!tisa_x86_emit(&prog, &p1, err, sizeof err) || !tisa_x86_load(&p1, err, sizeof err)) { printf("p1: %s\n", err); return 1; }
    if (!tisa_x86_emit_with(&prog, &hoist, &ph, err, sizeof err) || !tisa_x86_load(&ph, err, sizeof err)) { printf("hoisted: %s\n", err); return 1; }
    for (size_t l = 0; l < ph.nloops; ++l)
        printf("loop %zu: %s (%u checks at entry, %u kept)\n", l, ph.loops[l].hoisted ? "hoisted" : ph.loops[l].reason,
               ph.loops[l].hoisted_checks, ph.loops[l].kept_checks);

    TcIsaRuntimeFrame frame __attribute__((aligned(64)));
    uint64_t regs[TISA_NUM_VREGS];
    #define SETUP(budget) do { memset(&frame, 0, sizeof frame); frame.s0_ptr = (uint64_t)(uintptr_t)data; frame.s0_len = N * 4; \
        frame.fuel_budget = (budget); memset(regs, 0, sizeof regs); regs[0] = (uint64_t)(uintptr_t)&frame; regs[1] = frame.s0_ptr; regs[2] = N; } while (0)
    uint64_t want = sum_c(data, N), got1 = 0, goth = 0;
    double t, c_ns, p1_ns, ph_ns, ref_ns;
    volatile uint64_t sink = 0;
    if (only) {   /* one realization only, for counting cycles: c, d (default) or h (hoisted) */
        for (int r = 0; r < REPS; ++r) {
            if (*only == 'c') sink += sum_c(data, N);
            else if (*only == 's') sink += sum_scalar(data, runtime_n);
            else { SETUP(0); tisa_x86_run(&prog, *only == 'h' ? &ph : &p1, &frame, regs); sink += frame.ret_val; }
        }
        printf("%s: %d calls of %d elements\n", only, REPS, N);
        return 0;
    }
    t = now(); for (int r = 0; r < REPS; ++r) sink += sum_c(data, N); c_ns = (now() - t) / REPS / N * 1e9;
    t = now(); for (int r = 0; r < REPS; ++r) { SETUP(0); tisa_x86_run(&prog, &p1, &frame, regs); got1 = frame.ret_val; } p1_ns = (now() - t) / REPS / N * 1e9;
    t = now(); for (int r = 0; r < REPS; ++r) { SETUP(0); tisa_x86_run(&prog, &ph, &frame, regs); goth = frame.ret_val; } ph_ns = (now() - t) / REPS / N * 1e9;
    double scalar_ns; t = now(); for (int r = 0; r < REPS; ++r) sink += sum_scalar(data, runtime_n); scalar_ns = (now() - t) / REPS / N * 1e9;
    t = now(); for (int r = 0; r < 50; ++r) { SETUP(0); tisa_run(&prog, &frame, regs); } ref_ns = (now() - t) / 50 / N * 1e9;
    printf("sum of %d u32 words, per element: GCC -O2 scalar (noipa, n unknown) %.3f ns; GCC -O2 constprop %.3f ns; p1 default %.3f ns; p1 hoisted %.3f ns; p1 reference %.1f ns\n",
           N, scalar_ns, c_ns, p1_ns, ph_ns, ref_ns);
    printf("results agree: %s (want %" PRIu64 ", default %" PRIu64 ", hoisted %" PRIu64 ")\n", want == got1 && want == goth ? "yes" : "NO", want, got1, goth);
    printf("image bytes: default %zu, hoisted %zu\n", p1.len, ph.len);
    FILE *f = fopen("sum_hoisted.bin", "wb"); fwrite(ph.bytes, 1, ph.len, f); fclose(f);
    FILE *rec = fopen("sum_images.hol", "w");
    if (!tisa_print_image_record(rec, "sum_default", &prog, &p1) || !tisa_print_image_record(rec, "sum_hoisted", &prog, &ph)) printf("record failed\n");
    fclose(rec);
    for (size_t k = 0; k < ph.nspans; ++k) printf("  %4u %3u %s\n", ph.spans[k].offset, ph.spans[k].length, ph.spans[k].template_name);
    (void)sink;
    return 0;
}
