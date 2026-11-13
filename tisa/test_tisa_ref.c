/*
 * test_ref.c -- tests for the t-ISA p1 reference (tisa_ref.c).
 *
 *   1. Targeted cases: each instruction's results and refusals, admission
 *      refusals, and the loop-typing case p0 accepted unsoundly.
 *   2. Differential: random well-typed programs without FUND, run by the p0
 *      evaluator (where budget 0 meant unbounded) and by p1, compared
 *      on outcome, status, ret_val and every region byte.
 *   3. Cost laws: zero allowance, monotonicity and erasure, on random
 *      programs with FUND points.
 */
#include "tisa_ref.h"
#include "tisa_x86.h"
#include "tisa_print.h"

#include <inttypes.h>

/* tisa_ref.c built a second time with TISA_REF_P0_COMPAT. */
TcIsaOutcome tisa_run_p0compat(const TcIsaProgram *prog, TcIsaRuntimeFrame *frame, uint64_t regs[TISA_NUM_VREGS]);
/* tisa_ref.c built with TISA_REF_CHECK_TYPES: aborts if a typed register ever
   holds a value outside its admitted type. */
TcIsaOutcome tisa_run_checked(const TcIsaProgram *prog, TcIsaRuntimeFrame *frame, uint64_t regs[TISA_NUM_VREGS]);
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures;
#define EXPECT(cond, ...) do { if (!(cond)) { ++failures; fprintf(stderr, "FAIL %s:%d: ", __FILE__, __LINE__); \
                                fprintf(stderr, __VA_ARGS__); fputc('\n', stderr); } } while (0)

/* ---- Building programs ---------------------------------------------------- */

typedef struct { TcIsaStmt *items; size_t len, cap; } Pool;

static TcIsaStmt *node(Pool *p) {
    if (p->len == p->cap) { fprintf(stderr, "statement pool exhausted\n"); exit(2); }
    TcIsaStmt *s = &p->items[p->len++];
    memset(s, 0, sizeof *s);
    return s;
}
static TcIsaStmt *instr(Pool *p, TcIsaInstr i) { TcIsaStmt *s = node(p); s->kind = TISA_CTRL_INSTR; s->u.instr = i; return s; }
static TcIsaStmt *seq(Pool *p, TcIsaStmt *a, TcIsaStmt *b) {
    if (!a) return b;
    if (!b) return a;
    TcIsaStmt *s = node(p); s->kind = TISA_CTRL_SEQ; s->u.seq.first = a; s->u.seq.second = b; return s;
}
static TcIsaStmt *ret(Pool *p, TcIsaOutcome o, uint8_t r) { TcIsaStmt *s = node(p); s->kind = TISA_CTRL_RETURN; s->u.ret.outcome = o; s->u.ret.ret_reg = r; return s; }
static TcIsaStmt *fund(Pool *p, uint32_t u) { TcIsaStmt *s = node(p); s->kind = TISA_CTRL_FUND; s->u.fund.units = u; return s; }
static TcIsaStmt *if_(Pool *p, uint8_t c, TcIsaStmt *a, TcIsaStmt *b) {
    TcIsaStmt *s = node(p); s->kind = TISA_CTRL_IF; s->u.if_cond.cond_reg = c;
    s->u.if_cond.then_branch = a; s->u.if_cond.else_branch = b; return s;
}
static TcIsaStmt *count_loop(Pool *p, uint8_t x, uint8_t n, uint32_t cap, TcIsaStmt *body) {
    TcIsaStmt *s = node(p); s->kind = TISA_CTRL_COUNT_LOOP; s->u.count_loop.idx_reg = x; s->u.count_loop.bound_reg = n;
    s->u.count_loop.max_iters = cap; s->u.count_loop.body = body; return s;
}
static TcIsaStmt *early_loop(Pool *p, uint8_t x, uint8_t n, uint8_t k, uint32_t cap, TcIsaStmt *body) {
    TcIsaStmt *s = node(p); s->kind = TISA_CTRL_EARLY_EXIT_LOOP; s->u.early_exit_loop.idx_reg = x;
    s->u.early_exit_loop.bound_reg = n; s->u.early_exit_loop.cont_reg = k;
    s->u.early_exit_loop.max_iters = cap; s->u.early_exit_loop.body = body; return s;
}

static TcIsaInstr imm(TcIsaValType t, uint8_t d, uint64_t k) { return (TcIsaInstr){.op = TISA_OP_IMM, .ty = t, .dst = d, .imm64 = k}; }
static TcIsaInstr bin(TcIsaValType t, TcIsaBinOp op, uint8_t d, uint8_t a, uint8_t b) {
    return (TcIsaInstr){.op = TISA_OP_BIN, .ty = t, .dst = d, .src1 = a, .src2 = b, .subop = (uint8_t)op};
}
static TcIsaInstr cmp_reg(TcIsaValType t, TcIsaCmpCond c, uint8_t d, uint8_t a, uint8_t b) {
    return (TcIsaInstr){.op = TISA_OP_CMP, .ty = t, .dst = d, .src1 = a, .src2 = b, .subop = (uint8_t)c};
}
static TcIsaInstr cmp_imm(TcIsaValType t, TcIsaCmpCond c, uint8_t d, uint8_t a, uint64_t k) {
    return (TcIsaInstr){.op = TISA_OP_CMP, .ty = t, .dst = d, .src1 = a, .subop = (uint8_t)c, .bit_width = 1, .imm64 = k};
}
static TcIsaInstr load(TcIsaValType t, uint8_t w, uint8_t region, uint8_t d, uint8_t p, int32_t o) {
    return (TcIsaInstr){.op = TISA_OP_LOAD, .ty = t, .dst = d, .src1 = p, .subop = w, .region_id = region, .disp32 = o};
}
static TcIsaInstr store(uint8_t w, uint8_t region, uint8_t p, int32_t o, uint8_t v) {
    return (TcIsaInstr){.op = TISA_OP_STORE, .ty = TISA_TYPE_U64, .src1 = p, .src2 = v, .subop = w, .region_id = region, .disp32 = o};
}
static TcIsaInstr addr(uint8_t region, uint8_t d, uint8_t p, uint8_t i, uint8_t s, int32_t o) {
    return (TcIsaInstr){.op = TISA_OP_ADDR, .ty = TISA_TYPE_PTR, .dst = d, .src1 = p, .src2 = i, .scale_lg2 = s,
                        .region_id = region, .disp32 = o};
}

/* ---- Running ------------------------------------------------------------- */

#define REGIONS 3
#define SPAN 128

typedef struct {
    TcIsaRuntimeFrame frame;     /* aligned(64) by its type */
    uint8_t *bytes[REGIONS];     /* each region's buffer, SPAN bytes */
    uint64_t regs[TISA_NUM_VREGS];
} World;

static void world_init(World *w) {
    memset(w, 0, sizeof *w);
    for (unsigned r = 0; r < REGIONS; ++r) w->bytes[r] = aligned_alloc(64, SPAN);
}
static void world_free(World *w) { for (unsigned r = 0; r < REGIONS; ++r) free(w->bytes[r]); }

/* A simple program over one RW region: the targeted cases' scaffold. */
static void program_init(TcIsaProgram *p, TcIsaStmt *root) {
    memset(p, 0, sizeof *p);
    p->name = "case";
    p->nregions = 2;
    p->regions[0] = (TcIsaRegionDecl){.region_id = 0, .mode = TISA_CAP_RW, .min_byte_len = 16, .align_bytes = 8, .name = "out"};
    p->regions[1] = (TcIsaRegionDecl){.region_id = 1, .mode = TISA_CAP_RO, .min_byte_len = 16, .align_bytes = 8, .name = "in"};
    p->init_reg_mask = 0x0Fu;   /* v0 frame, v1 PTR(0), v2 PTR(1), v3 U64 */
    p->init_reg_types[0] = TISA_TYPE_U64;   /* the frame address, as the specializers declare it */
    p->init_reg_types[1] = TISA_TYPE_PTR; p->init_reg_region[1] = 0;
    p->init_reg_types[2] = TISA_TYPE_PTR; p->init_reg_region[2] = 1;
    p->init_reg_types[3] = TISA_TYPE_U64;
    p->root = root;
}

static void frame_setup(World *w, uint64_t len0, uint64_t len1, uint64_t a3) {
    memset(&w->frame, 0, sizeof w->frame);
    w->frame.s0_ptr = (uint64_t)(uintptr_t)w->bytes[0]; w->frame.s0_len = len0;
    w->frame.s1_ptr = (uint64_t)(uintptr_t)w->bytes[1]; w->frame.s1_len = len1;
    w->frame.fuel_budget = UINT64_MAX /* a number like any other */;
    memset(w->regs, 0, sizeof w->regs);
    w->regs[0] = (uint64_t)(uintptr_t)&w->frame;
    w->regs[1] = w->frame.s0_ptr;
    w->regs[2] = w->frame.s1_ptr;
    w->regs[3] = a3;
}

/* ---- 1. Targeted cases ---------------------------------------------------- */

static void targeted(void) {
    TcIsaStmt items[256]; Pool p = {items, 0, 256};
    World w; world_init(&w);
    TcIsaProgram prog; char err[256];

    /* Arithmetic and normalization: (2^32 - 1) + 1 as U32Z is 0; as U64 it is 2^32. */
    p.len = 0;
    program_init(&prog, seq(&p, instr(&p, imm(TISA_TYPE_U32Z, 4, UINT32_MAX)),
                  seq(&p, instr(&p, imm(TISA_TYPE_U32Z, 5, 1)),
                  seq(&p, instr(&p, bin(TISA_TYPE_U32Z, TISA_BIN_ADD, 6, 4, 5)),
                  seq(&p, instr(&p, bin(TISA_TYPE_U64, TISA_BIN_ADD, 7, 4, 5)),
                  seq(&p, instr(&p, store(8, 0, 1, 0, 6)),
                  seq(&p, instr(&p, store(8, 0, 1, 8, 7)), ret(&p, TISA_OUTCOME_FIRED, 6))))))));
    EXPECT(tisa_admit(&prog, NULL, err, sizeof err), "arithmetic program refused: %s", err);
    frame_setup(&w, 16, 16, 0);
    EXPECT(tisa_run(&prog, &w.frame, w.regs) == TISA_OUTCOME_FIRED, "arithmetic did not fire");
    uint64_t lo, hi; memcpy(&lo, w.bytes[0], 8); memcpy(&hi, w.bytes[0] + 8, 8);
    EXPECT(lo == 0 && hi == (UINT64_C(1) << 32) && w.frame.ret_val == 0 && w.frame.status == 1, "U32Z/U64 addition wrong");

    /* 32-bit signed comparison and I32S normalization: -1 < 0 as I32S. */
    p.len = 0;
    program_init(&prog, seq(&p, instr(&p, imm(TISA_TYPE_I32S, 4, UINT64_MAX)),
                  seq(&p, instr(&p, cmp_imm(TISA_TYPE_I32S, TISA_CMP_SLT, 5, 4, 0)),
                  seq(&p, instr(&p, cmp_imm(TISA_TYPE_I32S, TISA_CMP_ULT, 6, 4, 0)),
                  seq(&p, instr(&p, bin(TISA_TYPE_BOOL, TISA_BIN_XOR, 7, 5, 6)), ret(&p, TISA_OUTCOME_FIRED, 7))))));
    EXPECT(tisa_admit(&prog, NULL, err, sizeof err), "comparison refused: %s", err);
    frame_setup(&w, 16, 16, 0);
    EXPECT(tisa_run(&prog, &w.frame, w.regs) == TISA_OUTCOME_FIRED && w.frame.ret_val == 1, "signed/unsigned comparison wrong");

    /* Bounds: an 8-byte LOAD at offset 8 of a 16-byte region is in; at 9 it is out. */
    for (int32_t o = 8; o <= 9; ++o) {
        p.len = 0;
        program_init(&prog, seq(&p, instr(&p, load(TISA_TYPE_U64, 8, 1, 4, 2, o)), ret(&p, TISA_OUTCOME_FIRED, 4)));
        frame_setup(&w, 16, 16, 0);
        memset(w.bytes[1], 0xAB, SPAN);
        TcIsaOutcome got = tisa_run(&prog, &w.frame, w.regs);
        EXPECT(o == 8 ? got == TISA_OUTCOME_FIRED && w.frame.ret_val == UINT64_C(0xABABABABABABABAB)
                      : got == TISA_OUTCOME_INVALID_INPUT && w.frame.status == 3 && w.frame.ret_val == 3,
               "LOAD bound at offset %d wrong (outcome %d)", (int)o, (int)got);
    }

    /* ADDR may form one past the end, not beyond; the result is exact. */
    for (int32_t o = 16; o <= 17; ++o) {
        p.len = 0;
        program_init(&prog, seq(&p, instr(&p, addr(0, 4, 1, 0xFF, 0, o)), ret(&p, TISA_OUTCOME_FIRED, 4)));
        frame_setup(&w, 16, 16, 0);
        TcIsaOutcome got = tisa_run(&prog, &w.frame, w.regs);
        EXPECT(o == 16 ? got == TISA_OUTCOME_FIRED && w.frame.ret_val == w.frame.s0_ptr + 16 : got == TISA_OUTCOME_INVALID_INPUT,
               "ADDR one past the end wrong at %d", (int)o);
    }

    /* No pointer leaves its region in passing: index 3 * 8 = 24 past a
       16-byte region, then -16 back to offset 8, is refused. */
    p.len = 0;
    program_init(&prog, seq(&p, instr(&p, imm(TISA_TYPE_U64, 4, 3)),
                  seq(&p, instr(&p, addr(0, 5, 1, 4, 3, -16)), ret(&p, TISA_OUTCOME_FIRED, 5))));
    frame_setup(&w, 16, 16, 0);
    EXPECT(tisa_run(&prog, &w.frame, w.regs) == TISA_OUTCOME_INVALID_INPUT, "ADDR left its region in passing");

    /* A stored BOOL that is not 0 or 1 is refused when loaded as BOOL. */
    p.len = 0;
    program_init(&prog, seq(&p, instr(&p, load(TISA_TYPE_BOOL, 1, 1, 4, 2, 0)), ret(&p, TISA_OUTCOME_FIRED, 4)));
    frame_setup(&w, 16, 16, 0);
    w.bytes[1][0] = 2;
    EXPECT(tisa_run(&prog, &w.frame, w.regs) == TISA_OUTCOME_INVALID_INPUT, "non-Boolean byte loaded as BOOL");

    /* Admission: STORE to a read-only region, reading an untyped register, a
       path without RETURN, writing v0. */
    p.len = 0;
    program_init(&prog, seq(&p, instr(&p, store(8, 1, 2, 0, 3)), ret(&p, TISA_OUTCOME_FIRED, 3)));
    EXPECT(!tisa_admit(&prog, NULL, err, sizeof err) && strstr(err, "not writable"), "STORE to RO admitted: %s", err);
    p.len = 0;
    program_init(&prog, seq(&p, instr(&p, bin(TISA_TYPE_U64, TISA_BIN_ADD, 4, 3, 9)), ret(&p, TISA_OUTCOME_FIRED, 4)));
    EXPECT(!tisa_admit(&prog, NULL, err, sizeof err) && strstr(err, "untyped"), "untyped read admitted: %s", err);
    p.len = 0;
    program_init(&prog, if_(&p, 4, ret(&p, TISA_OUTCOME_FIRED, 3), NULL));
    prog.init_reg_mask |= 0x10u; prog.init_reg_types[4] = TISA_TYPE_BOOL;
    EXPECT(!tisa_admit(&prog, NULL, err, sizeof err) && strstr(err, "without RETURN"), "fall-through admitted: %s", err);
    p.len = 0;
    program_init(&prog, seq(&p, instr(&p, imm(TISA_TYPE_U64, 0, 7)), ret(&p, TISA_OUTCOME_FIRED, 3)));
    EXPECT(!tisa_admit(&prog, NULL, err, sizeof err) && strstr(err, "cannot be written"), "write to v0 admitted: %s", err);

    /* The loop-typing case. v4 is BOOL before the loop; the body tests it,
       then makes it the U64 value 5. On the second iteration the test reads
       5. p0 checked the body once and accepted this; p1 refuses it. */
    p.len = 0;
    TcIsaStmt *body = seq(&p, if_(&p, 4, NULL, NULL), instr(&p, imm(TISA_TYPE_U64, 4, 5)));
    program_init(&prog, seq(&p, instr(&p, imm(TISA_TYPE_BOOL, 4, 1)),
                  seq(&p, instr(&p, imm(TISA_TYPE_U64, 5, 2)),
                  seq(&p, count_loop(&p, 6, 5, 4, body), ret(&p, TISA_OUTCOME_FIRED, 3)))));
    EXPECT(!tisa_admit(&prog, NULL, err, sizeof err) && strstr(err, "not BOOL"), "unsound loop typing admitted: %s", err);
    char err0[256] = {0};
    EXPECT(tisa_check_program(&prog, err0, sizeof err0), "p0 now refuses the loop-typing case (%s); update this control", err0);

    /* The receipt bound is exact or says it does not fit. Two nested loops
       capped at 2^32 - 1 around FUND 2 can pay 2 * (2^32 - 1)^2 > 2^64 - 1:
       admitted, with no sufficient allowance. One loop paying 2^32 + 1 per
       iteration fits exactly at 2^64 - 1; one more unit does not fit. */
    {
        TcIsaAdmission bound;
        p.len = 0;
        TcIsaStmt *inner = count_loop(&p, 7, 5, UINT32_MAX, fund(&p, 2));
        program_init(&prog, seq(&p, instr(&p, imm(TISA_TYPE_U64, 5, 1)),
                      seq(&p, count_loop(&p, 6, 5, UINT32_MAX, inner), ret(&p, TISA_OUTCOME_FIRED, 3))));
        EXPECT(tisa_admit(&prog, &bound, err, sizeof err), "nested capped loops refused: %s", err);
        EXPECT(!bound.max_receipt_fits && bound.max_receipt == UINT64_MAX,
               "a bound above 2^64 - 1 reported as fitting (%" PRIu64 ")", bound.max_receipt);
        p.len = 0;
        TcIsaStmt *exact = count_loop(&p, 6, 5, UINT32_MAX, seq(&p, fund(&p, UINT32_MAX), fund(&p, 2)));
        program_init(&prog, seq(&p, instr(&p, imm(TISA_TYPE_U64, 5, 1)), seq(&p, exact, ret(&p, TISA_OUTCOME_FIRED, 3))));
        EXPECT(tisa_admit(&prog, &bound, err, sizeof err) && bound.max_receipt_fits && bound.max_receipt == UINT64_MAX,
               "the bound 2^64 - 1 not reported exactly: %s", err);
        p.len = 0;
        exact = count_loop(&p, 6, 5, UINT32_MAX, seq(&p, fund(&p, UINT32_MAX), fund(&p, 2)));
        program_init(&prog, seq(&p, instr(&p, imm(TISA_TYPE_U64, 5, 1)),
                      seq(&p, exact, seq(&p, fund(&p, 1), ret(&p, TISA_OUTCOME_FIRED, 3)))));
        EXPECT(tisa_admit(&prog, &bound, err, sizeof err) && !bound.max_receipt_fits,
               "the bound 2^64 reported as fitting: %s", err);
    }

    /* FUND: allowance 3 pays FUND 2 then refuses FUND 2; the store between
       them stays, and the receipt is 2. */
    p.len = 0;
    program_init(&prog, seq(&p, fund(&p, 2), seq(&p, instr(&p, store(8, 0, 1, 0, 3)),
                  seq(&p, fund(&p, 2), seq(&p, instr(&p, store(8, 0, 1, 8, 3)), ret(&p, TISA_OUTCOME_FIRED, 3))))));
    frame_setup(&w, 16, 16, 0x1234);
    memset(w.bytes[0], 0, SPAN);
    w.frame.fuel_budget = 3;
    EXPECT(tisa_run(&prog, &w.frame, w.regs) == TISA_OUTCOME_EXHAUSTED && w.frame.fuel_used == 2 &&
           w.frame.status == 4 && w.bytes[0][0] == 0x34 && w.bytes[0][8] == 0, "partial funding wrong");
    /* The receipt carries over: with 2 already used of 4, the first FUND
       leaves no room for the second. */
    frame_setup(&w, 16, 16, 0x1234);
    w.frame.fuel_budget = 4; w.frame.fuel_used = 2;
    EXPECT(tisa_run(&prog, &w.frame, w.regs) == TISA_OUTCOME_EXHAUSTED && w.frame.fuel_used == 4, "running receipt wrong");
    /* A receipt above the allowance is invalid input. */
    frame_setup(&w, 16, 16, 0);
    w.frame.fuel_budget = 1; w.frame.fuel_used = 2;
    EXPECT(tisa_run(&prog, &w.frame, w.regs) == TISA_OUTCOME_INVALID_INPUT, "receipt above allowance accepted");

    /* Entry: a short region and an RW region overlapping another are refused. */
    p.len = 0;
    program_init(&prog, ret(&p, TISA_OUTCOME_FIRED, 3));
    frame_setup(&w, 8, 16, 0);
    EXPECT(tisa_run(&prog, &w.frame, w.regs) == TISA_OUTCOME_INVALID_INPUT, "short region accepted");
    frame_setup(&w, 16, 16, 0);
    w.frame.s1_ptr = w.frame.s0_ptr + 8; w.regs[2] = w.frame.s1_ptr;
    EXPECT(tisa_run(&prog, &w.frame, w.regs) == TISA_OUTCOME_INVALID_INPUT, "overlapping writable region accepted");

    world_free(&w);
}

/* ---- Random programs ------------------------------------------------------ */

static uint64_t rng = 0x9E3779B97F4A7C15ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static unsigned pick(unsigned n) { return (unsigned)(next() % n); }

static const uint64_t interesting[] = {0, 1, 2, 3, 7, 8, 31, 32, 63, 64, 255, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF,
    UINT64_C(0x100000000), UINT64_C(0x7FFFFFFFFFFFFFFF), UINT64_C(0x8000000000000000), UINT64_MAX, UINT64_MAX - 1};
static uint64_t value(void) { return pick(3) ? interesting[pick(sizeof interesting / sizeof *interesting)] : next(); }

typedef struct {
    Pool *pool;
    TcIsaProgram *prog;
    TcIsaValType type[TISA_NUM_VREGS];
    uint8_t region[TISA_NUM_VREGS];
    uint16_t locked;
    bool funds;
    bool extended;      /* also frame loads and RETURN UNSUPPORTED (corpus export only) */
    unsigned budget;    /* statements left */
    int last;           /* destination of the latest instruction, or -1 */
} Gen;

static bool extended_generation;
static bool array_generation;   /* --hoist: count loops often index a region by the loop index */

static int reg_of(Gen *g, TcIsaValType t, int region) {
    uint8_t found[TISA_NUM_VREGS]; unsigned n = 0;
    for (uint8_t r = 1; r < TISA_NUM_VREGS; ++r)
        if (g->type[r] == t && (t != TISA_TYPE_PTR || region < 0 || g->region[r] == region)) found[n++] = r;
    return n ? found[pick(n)] : -1;
}
static int any_reg(Gen *g) {
    uint8_t found[TISA_NUM_VREGS]; unsigned n = 0;
    for (uint8_t r = 1; r < TISA_NUM_VREGS; ++r) if (g->type[r] != TISA_TYPE_UNINIT) found[n++] = r;
    return n ? found[pick(n)] : -1;
}
static int scalar_reg(Gen *g) {
    uint8_t found[TISA_NUM_VREGS]; unsigned n = 0;
    for (uint8_t r = 1; r < TISA_NUM_VREGS; ++r)
        if (g->type[r] == TISA_TYPE_U64 || g->type[r] == TISA_TYPE_U32Z || g->type[r] == TISA_TYPE_I32S) found[n++] = r;
    return n ? found[pick(n)] : -1;
}
/* The register a RETURN reports. Under extended generation it is often the
   latest destination, so that a value just loaded or computed is observed
   before any later use could check it. */
static uint8_t ret_reg(Gen *g) {
    if (g->extended && g->last > 0 && g->type[g->last] != TISA_TYPE_UNINIT && pick(2)) return (uint8_t)g->last;
    int r = any_reg(g);
    return (uint8_t)(r > 0 ? r : 3);
}
static uint8_t dst_reg(Gen *g) {
    uint8_t found[TISA_NUM_VREGS]; unsigned n = 0;
    for (uint8_t r = 1; r < TISA_NUM_VREGS; ++r) if (!(g->locked & (1u << r))) found[n++] = r;
    return found[pick(n)];
}
static TcIsaValType int_type(void) {
    static const TcIsaValType t[] = {TISA_TYPE_U64, TISA_TYPE_U32Z, TISA_TYPE_I32S};
    return t[pick(3)];
}

static TcIsaStmt *gen_instr(Gen *g) {
    TcIsaInstr i = {0};
    uint8_t d = dst_reg(g);
    int a = any_reg(g), s = scalar_reg(g);
    unsigned choice = pick(g->extended ? 13 : 12);
    TcIsaValType t = int_type();
    if (choice <= 1 || a < 0) {
        i = imm(pick(5) ? t : TISA_TYPE_BOOL, d, 0);
        i.imm64 = i.ty == TISA_TYPE_BOOL ? pick(2) : i.ty == TISA_TYPE_U32Z ? (uint32_t)value() : value();
    } else if (choice == 2) {
        i = (TcIsaInstr){.op = TISA_OP_MOV, .ty = g->type[a] == TISA_TYPE_BOOL || g->type[a] == TISA_TYPE_PTR ? g->type[a] : t,
                         .dst = d, .src1 = (uint8_t)a};
    } else if (choice == 3 && s >= 0) {
        int b = scalar_reg(g);
        i = bin(t, (TcIsaBinOp)pick(6), d, (uint8_t)s, (uint8_t)b);
    } else if (choice == 4) {
        int x = reg_of(g, TISA_TYPE_BOOL, -1), y = reg_of(g, TISA_TYPE_BOOL, -1);
        if (x < 0 || y < 0) return gen_instr(g);
        static const TcIsaBinOp logic[] = {TISA_BIN_AND, TISA_BIN_OR, TISA_BIN_XOR};
        i = bin(TISA_TYPE_BOOL, logic[pick(3)], d, (uint8_t)x, (uint8_t)y);
    } else if (choice == 5 && s >= 0) {
        i = (TcIsaInstr){.op = TISA_OP_SHIFT, .ty = t, .dst = d, .src1 = (uint8_t)s, .subop = (uint8_t)pick(3),
                         .bit_width = (uint8_t)pick(t == TISA_TYPE_U64 ? 64 : 32)};
    } else if (choice == 6 && s >= 0) {
        uint8_t lsb = (uint8_t)pick(64), width = (uint8_t)(1 + pick(64 - lsb));
        i = (TcIsaInstr){.op = TISA_OP_EXTRACT, .ty = t, .dst = d, .src1 = (uint8_t)s, .scale_lg2 = lsb, .bit_width = width};
    } else if (choice == 7 && s >= 0) {
        int b = scalar_reg(g);
        i = pick(2) ? cmp_reg(t, (TcIsaCmpCond)pick(6), d, (uint8_t)s, (uint8_t)b)
                    : cmp_imm(t, (TcIsaCmpCond)pick(6), d, (uint8_t)s, value());
    } else if (choice == 8) {
        int c = reg_of(g, TISA_TYPE_BOOL, -1), x = scalar_reg(g), y = scalar_reg(g);
        if (g->extended && pick(3) == 0) { x = reg_of(g, TISA_TYPE_BOOL, -1); y = reg_of(g, TISA_TYPE_BOOL, -1); t = TISA_TYPE_BOOL; }
        if (c < 0 || x < 0 || y < 0) return gen_instr(g);
        i = (TcIsaInstr){.op = TISA_OP_SELECT, .ty = t, .dst = d, .src1 = (uint8_t)x, .src2 = (uint8_t)y, .src3 = (uint8_t)c};
    } else if (choice == 9) {
        uint8_t r = (uint8_t)pick(g->prog->nregions);
        int ptr = reg_of(g, TISA_TYPE_PTR, r);
        if (ptr < 0) return gen_instr(g);
        int idx = pick(2) ? scalar_reg(g) : -1;
        i = addr(r, d, (uint8_t)ptr, idx < 0 ? 0xFF : (uint8_t)idx, (uint8_t)pick(4), (int32_t)pick(40) - 12);
    } else if (choice == 10) {
        uint8_t r = (uint8_t)pick(g->prog->nregions);
        int ptr = reg_of(g, TISA_TYPE_PTR, r);
        if (ptr < 0) return gen_instr(g);
        static const uint8_t widths[] = {1, 4, 8};
        uint8_t w = widths[pick(3)];
        i = load(pick(8) ? t : TISA_TYPE_BOOL, w, r, d, (uint8_t)ptr, (int32_t)pick(40) - 4);
    } else if (choice == 11) {
        uint8_t r = (uint8_t)pick(g->prog->nregions);
        int ptr = reg_of(g, TISA_TYPE_PTR, r), v = any_reg(g);
        if (ptr < 0 || v < 0 || g->prog->regions[r].mode != TISA_CAP_RW) return gen_instr(g);
        /* Extended generation often stores the value just produced: a store
           is observed even when the run fails later. */
        if (g->extended && g->last > 0 && g->type[g->last] != TISA_TYPE_UNINIT && pick(2)) v = g->last;
        static const uint8_t widths[] = {1, 4, 8};
        TcIsaStmt *st = instr(g->pool, store(widths[pick(3)], r, (uint8_t)ptr, (int32_t)pick(40) - 4, (uint8_t)v));
        return st;
    } else if (choice == 12) {
        unsigned word = pick(24);
        TcIsaValType ft = pick(4) ? t : TISA_TYPE_BOOL;
        if (pick(3) == 0 && word % 2 == 0 && word / 2 < g->prog->nregions) ft = TISA_TYPE_PTR;
        i = (TcIsaInstr){.op = TISA_OP_LOAD, .ty = ft, .dst = d, .src1 = TISA_V0, .subop = 8,
                         .region_id = TISA_REGION_FRAME, .disp32 = (int32_t)(8 * word)};
    } else return gen_instr(g);
    /* Track the destination's new type as admission will. */
    TcIsaValType result = i.op == TISA_OP_CMP ? TISA_TYPE_BOOL : i.op == TISA_OP_ADDR ? TISA_TYPE_PTR : i.ty;
    g->type[i.dst] = result;
    g->region[i.dst] = i.op == TISA_OP_ADDR ? i.region_id : i.op == TISA_OP_MOV ? g->region[i.src1] :
                       i.op == TISA_OP_LOAD && i.ty == TISA_TYPE_PTR ? (uint8_t)(i.disp32 / 16) : 0;
    g->last = i.dst;
    return instr(g->pool, i);
}

/* An element access through the loop index x: ADDR d = p + x * 2^s + o, then a
   LOAD or STORE through d (--hoist only). */
static TcIsaStmt *array_access(Gen *g, uint8_t x) {
    uint8_t r = (uint8_t)pick(g->prog->nregions);
    int ptr = reg_of(g, TISA_TYPE_PTR, r);
    if (ptr < 0) return NULL;
    uint8_t d = dst_reg(g), s = (uint8_t)pick(4);
    TcIsaStmt *at = instr(g->pool, addr(r, d, (uint8_t)ptr, x, s, (int32_t)pick(24) - 8));
    g->type[d] = TISA_TYPE_PTR; g->region[d] = r; g->last = d;
    static const uint8_t widths[] = {1, 4, 8};
    uint8_t w = widths[pick(3)];
    if (g->prog->regions[r].mode == TISA_CAP_RW && pick(2)) {
        int v = any_reg(g);
        return seq(g->pool, at, instr(g->pool, store(w, r, d, (int32_t)pick(16) - 4, (uint8_t)(v > 0 ? v : d))));
    }
    uint8_t e = dst_reg(g);
    TcIsaValType t = pick(8) ? int_type() : TISA_TYPE_BOOL;
    TcIsaStmt *ld = instr(g->pool, load(t, w, r, e, d, (int32_t)pick(16) - 4));
    g->type[e] = t; g->region[e] = 0; g->last = e;
    return seq(g->pool, at, ld);
}

static TcIsaStmt *gen_block(Gen *g, unsigned depth);

static TcIsaStmt *gen_stmt(Gen *g, unsigned depth) {
    if (g->budget) --g->budget;
    unsigned choice = pick(depth < 3 ? 14 : 10);
    if (g->funds && choice == 0) return fund(g->pool, 1 + pick(3));
    if (choice < 10 || !g->budget) return gen_instr(g);
    if (choice == 10) {
        int c = reg_of(g, TISA_TYPE_BOOL, -1);
        if (c < 0) return gen_instr(g);
        TcIsaValType saved[TISA_NUM_VREGS]; uint8_t saved_region[TISA_NUM_VREGS];
        memcpy(saved, g->type, sizeof saved); memcpy(saved_region, g->region, sizeof saved_region);
        TcIsaStmt *yes = gen_block(g, depth + 1);
        TcIsaValType after_yes[TISA_NUM_VREGS]; memcpy(after_yes, g->type, sizeof after_yes);
        memcpy(g->type, saved, sizeof saved); memcpy(g->region, saved_region, sizeof saved_region);
        TcIsaStmt *no = pick(2) ? gen_block(g, depth + 1) : NULL;
        for (unsigned r = 0; r < TISA_NUM_VREGS; ++r) if (after_yes[r] != g->type[r]) g->type[r] = TISA_TYPE_UNINIT;
        return if_(g->pool, (uint8_t)c, yes, no);
    }
    if (choice == 11 && pick(3) == 0) {
        TcIsaStmt *block = gen_block(g, depth + 1);
        TcIsaOutcome o = g->extended && pick(6) == 0 ? TISA_OUTCOME_UNSUPPORTED
                                                     : pick(4) ? TISA_OUTCOME_FIRED : TISA_OUTCOME_REFUSED;
        if (!g->extended) return seq(g->pool, block, ret(g->pool, o, (uint8_t)(any_reg(g) > 0 ? any_reg(g) : 3)));
        return seq(g->pool, block, ret(g->pool, o, ret_reg(g)));
    }
    /* A loop: bound from a fresh small immediate or an existing scalar. */
    int n = scalar_reg(g);
    TcIsaStmt *pre = NULL;
    if (n < 0 || pick(2)) {
        n = dst_reg(g);
        pre = instr(g->pool, imm(TISA_TYPE_U64, (uint8_t)n, pick(5)));
        g->type[n] = TISA_TYPE_U64;
    }
    uint8_t x = dst_reg(g);
    if (x == n) return seq(g->pool, pre, gen_instr(g));
    uint16_t saved_locked = g->locked;
    g->type[x] = TISA_TYPE_U64;
    g->locked |= (uint16_t)((1u << x) | (1u << n));
    uint32_t cap = 1 + pick(6);
    TcIsaStmt *loop;
    if (choice == 12) {
        uint8_t k = dst_reg(g);
        if (k == n || k == x) { g->locked = saved_locked; return seq(g->pool, pre, gen_instr(g)); }
        TcIsaStmt *init = instr(g->pool, imm(TISA_TYPE_BOOL, k, 1));
        g->type[k] = TISA_TYPE_BOOL;
        g->locked |= (uint16_t)(1u << k);   /* the generator keeps k BOOL by writing it only below */
        TcIsaStmt *body = array_generation && pick(3) ? array_access(g, x) : NULL;
        body = seq(g->pool, body, gen_block(g, depth + 1));
        int s = scalar_reg(g);
        TcIsaStmt *update = s >= 0 ? instr(g->pool, cmp_imm(TISA_TYPE_U64, TISA_CMP_ULT, k, (uint8_t)s, value())) : NULL;
        loop = seq(g->pool, init, early_loop(g->pool, x, (uint8_t)n, k, cap, seq(g->pool, body, update)));
    } else if (array_generation && pick(3)) {
        TcIsaStmt *body = array_access(g, x);
        if (pick(2)) body = seq(g->pool, body, array_access(g, x));
        if (g->funds && pick(2)) body = seq(g->pool, body, fund(g->pool, 1 + pick(3)));
        loop = count_loop(g->pool, x, (uint8_t)n, array_generation ? 1 + pick(40) : cap, seq(g->pool, body, gen_block(g, depth + 1)));
    } else loop = count_loop(g->pool, x, (uint8_t)n, cap, gen_block(g, depth + 1));
    g->locked = saved_locked;
    return seq(g->pool, pre, loop);
}

static TcIsaStmt *gen_block(Gen *g, unsigned depth) {
    TcIsaStmt *s = NULL;
    unsigned n = 1 + pick(depth ? 4 : 10);
    for (unsigned k = 0; k < n && g->budget; ++k) s = seq(g->pool, s, gen_stmt(g, depth));
    return s;
}

/* A random program with regions 0 (RW), 1 (RO) and maybe 2 (RW). */
static void gen_program(Pool *pool, TcIsaProgram *prog, bool funds) {
    memset(prog, 0, sizeof *prog);
    prog->name = "random";
    prog->nregions = (uint8_t)(2 + pick(2));
    for (uint8_t r = 0; r < prog->nregions; ++r)
        prog->regions[r] = (TcIsaRegionDecl){.region_id = r, .mode = r == 1 ? TISA_CAP_RO : TISA_CAP_RW,
                                             .min_byte_len = (uint32_t)pick(17), .align_bytes = pick(2) ? 8 : 1};
    Gen g = {.pool = pool, .prog = prog, .funds = funds, .extended = extended_generation, .budget = 40, .last = -1};
    prog->init_reg_mask = 0x3Fu;
    prog->init_reg_types[0] = TISA_TYPE_U64;
    for (uint8_t r = 1; r <= 5; ++r) {
        TcIsaValType t = r <= prog->nregions ? TISA_TYPE_PTR : pick(4) ? int_type() : TISA_TYPE_BOOL;
        prog->init_reg_types[r] = t;
        prog->init_reg_region[r] = t == TISA_TYPE_PTR ? (uint8_t)(r - 1) : 0;
        g.type[r] = t; g.region[r] = prog->init_reg_region[r];
    }
    g.locked = 1u;
    TcIsaStmt *body = gen_block(&g, 0);
    if (g.extended) {
        prog->root = seq(pool, body, ret(pool, pick(5) ? TISA_OUTCOME_FIRED : TISA_OUTCOME_REFUSED, ret_reg(&g)));
        return;
    }
    int r = any_reg(&g);
    prog->root = seq(pool, body, ret(pool, pick(5) ? TISA_OUTCOME_FIRED : TISA_OUTCOME_REFUSED, (uint8_t)(r > 0 ? r : 3)));
}

static void strip_funds(const TcIsaStmt *s, TcIsaStmt *copy, const TcIsaStmt *base, TcIsaStmt *copy_base) {
    /* The copy shares the pool layout; FUND nodes become the empty sequence. */
    (void)base; (void)copy_base;
    if (s->kind == TISA_CTRL_FUND) { copy->kind = TISA_CTRL_SEQ; copy->u.seq.first = NULL; copy->u.seq.second = NULL; }
}

/* Random inputs for prog: buffers, lengths and initial registers. */
static void gen_inputs(World *w, const TcIsaProgram *prog) {
    memset(&w->frame, 0, sizeof w->frame);
    uint64_t *words = (uint64_t *)(void *)&w->frame;
    for (uint8_t r = 0; r < prog->nregions; ++r) {
        for (unsigned b = 0; b < SPAN; ++b) w->bytes[r][b] = (uint8_t)next();
        if (pick(4) == 0) for (unsigned b = 0; b < SPAN; ++b) w->bytes[r][b] &= 1;   /* Boolean-looking bytes */
        uint64_t len = pick(20) == 0 ? pick(prog->regions[r].min_byte_len + 1) : prog->regions[r].min_byte_len + pick(SPAN - 16);
        if (len > SPAN) len = SPAN;
        words[2 * r] = (uint64_t)(uintptr_t)w->bytes[r];
        words[2 * r + 1] = len;
    }
    w->frame.fuel_budget = UINT64_MAX /* a number like any other */;
    w->regs[0] = (uint64_t)(uintptr_t)&w->frame;
    for (uint8_t r = 1; r <= 5; ++r) {
        TcIsaValType t = prog->init_reg_types[r];
        if (t == TISA_TYPE_PTR) {
            uint8_t q = prog->init_reg_region[r];
            w->regs[r] = words[2 * q] + pick((unsigned)words[2 * q + 1] + 1);
        } else if (t == TISA_TYPE_BOOL) w->regs[r] = pick(2);
        else if (t == TISA_TYPE_U32Z) w->regs[r] = (uint32_t)value();
        else if (t == TISA_TYPE_I32S) w->regs[r] = (uint64_t)(int64_t)(int32_t)(uint32_t)value();
        else w->regs[r] = value();
    }
    for (uint8_t r = 6; r < TISA_NUM_VREGS; ++r) w->regs[r] = 0;
}

typedef struct { TcIsaOutcome outcome; uint64_t status, ret_val, receipt; uint8_t bytes[REGIONS][SPAN]; } Result;

static void capture(const World *w, TcIsaOutcome o, Result *res) {
    res->outcome = o; res->status = w->frame.status; res->ret_val = w->frame.ret_val; res->receipt = w->frame.fuel_used;
    for (unsigned r = 0; r < REGIONS; ++r) memcpy(res->bytes[r], w->bytes[r], SPAN);
}

static bool same_result(const Result *a, const Result *b) {
    return a->outcome == b->outcome && a->status == b->status && a->ret_val == b->ret_val &&
           !memcmp(a->bytes, b->bytes, sizeof a->bytes);
}

/* ---- 2. Differential against p0 ------------------------------------------- */

/* True when some loop body, followed once from the loop's entry, can leave a
   register typed at entry with another type: the case p1 refuses and p0
   accepted. A conservative syntactic test: the body writes a register that
   holds a different type at the loop's entry. */
typedef struct { TcIsaValType t[TISA_NUM_VREGS]; uint8_t region[TISA_NUM_VREGS]; } Types;
static void follow(const TcIsaStmt *s, Types *ty, bool *found);
static void follow_loop(const TcIsaStmt *body, uint8_t x, Types *ty, bool *found) {
    Types inside = *ty; inside.t[x] = TISA_TYPE_U64;
    Types entry = inside;
    follow(body, &inside, found);
    for (unsigned r = 0; r < TISA_NUM_VREGS; ++r)
        if (entry.t[r] != TISA_TYPE_UNINIT && (inside.t[r] != entry.t[r] ||
            (entry.t[r] == TISA_TYPE_PTR && inside.region[r] != entry.region[r]))) *found = true;
    ty->t[x] = TISA_TYPE_U64;
}
static void follow(const TcIsaStmt *s, Types *ty, bool *found) {
    if (!s) return;
    switch (s->kind) {
    case TISA_CTRL_INSTR: {
        const TcIsaInstr *i = &s->u.instr;
        if (i->op == TISA_OP_STORE) return;
        ty->t[i->dst] = i->op == TISA_OP_CMP ? TISA_TYPE_BOOL : i->op == TISA_OP_ADDR ? TISA_TYPE_PTR :
                        i->op == TISA_OP_MOV && i->ty == TISA_TYPE_UNINIT ? ty->t[i->src1] : i->ty;
        ty->region[i->dst] = i->op == TISA_OP_ADDR ? i->region_id : i->op == TISA_OP_MOV ? ty->region[i->src1] :
                             i->op == TISA_OP_LOAD && i->region_id == TISA_REGION_FRAME ? (uint8_t)(i->disp32 / 16) : 0;
        return;
    }
    case TISA_CTRL_SEQ: follow(s->u.seq.first, ty, found); follow(s->u.seq.second, ty, found); return;
    case TISA_CTRL_IF: {
        Types a = *ty, b = *ty;
        follow(s->u.if_cond.then_branch, &a, found); follow(s->u.if_cond.else_branch, &b, found);
        for (unsigned r = 0; r < TISA_NUM_VREGS; ++r) {
            bool same = a.t[r] == b.t[r] && (a.t[r] != TISA_TYPE_PTR || a.region[r] == b.region[r]);
            ty->t[r] = same ? a.t[r] : TISA_TYPE_UNINIT;
            ty->region[r] = same ? a.region[r] : 0;
        }
        return;
    }
    case TISA_CTRL_COUNT_LOOP: follow_loop(s->u.count_loop.body, s->u.count_loop.idx_reg, ty, found); return;
    case TISA_CTRL_EARLY_EXIT_LOOP: follow_loop(s->u.early_exit_loop.body, s->u.early_exit_loop.idx_reg, ty, found); return;
    default: return;
    }
}
static bool unsound_loop(const TcIsaProgram *p) {
    Types ty; bool found = false;
    for (unsigned r = 0; r < TISA_NUM_VREGS; ++r) {
        ty.t[r] = (p->init_reg_mask >> r) & 1 ? p->init_reg_types[r] : TISA_TYPE_UNINIT;
        ty.region[r] = p->init_reg_region[r];
    }
    follow(p->root, &ty, &found);
    return found;
}

static const char *const op_names[] = {"IMM","MOV","BIN","SHIFT","EXTRACT","ADDR","LOAD","STORE","CMP","SELECT"};
static const char *const type_names[] = {"-","U64","U32Z","I32S","BOOL","PTR"};
static void dump(const TcIsaStmt *s, int depth) {
    if (!s) { fprintf(stderr, "%*s(empty)\n", depth, ""); return; }
    switch (s->kind) {
    case TISA_CTRL_INSTR: {
        const TcIsaInstr *i = &s->u.instr;
        fprintf(stderr, "%*s%s %s d=v%u a=v%u b=v%u c=v%u sub=%u reg=%u sc=%u bw=%u disp=%d imm=%" PRIx64 "\n", depth, "",
                op_names[i->op], type_names[i->ty], i->dst, i->src1, i->src2, i->src3, i->subop, i->region_id,
                i->scale_lg2, i->bit_width, (int)i->disp32, i->imm64);
        return;
    }
    case TISA_CTRL_SEQ: dump(s->u.seq.first, depth); dump(s->u.seq.second, depth); return;
    case TISA_CTRL_IF: fprintf(stderr, "%*sIF v%u\n", depth, "", s->u.if_cond.cond_reg); dump(s->u.if_cond.then_branch, depth + 2);
        fprintf(stderr, "%*sELSE\n", depth, ""); dump(s->u.if_cond.else_branch, depth + 2); return;
    case TISA_CTRL_COUNT_LOOP: fprintf(stderr, "%*sCOUNT x=v%u n=v%u cap=%u\n", depth, "", s->u.count_loop.idx_reg,
        s->u.count_loop.bound_reg, s->u.count_loop.max_iters); dump(s->u.count_loop.body, depth + 2); return;
    case TISA_CTRL_EARLY_EXIT_LOOP: fprintf(stderr, "%*sEARLY x=v%u n=v%u k=v%u cap=%u\n", depth, "", s->u.early_exit_loop.idx_reg,
        s->u.early_exit_loop.bound_reg, s->u.early_exit_loop.cont_reg, s->u.early_exit_loop.max_iters);
        dump(s->u.early_exit_loop.body, depth + 2); return;
    case TISA_CTRL_RETURN: fprintf(stderr, "%*sRETURN %d v%u\n", depth, "", (int)s->u.ret.outcome, s->u.ret.ret_reg); return;
    case TISA_CTRL_FUND: fprintf(stderr, "%*sFUND %u\n", depth, "", s->u.fund.units); return;
    default: return;
    }
}


static void differential(unsigned programs, unsigned inputs) {
    static TcIsaStmt items[4096];
    Pool pool = {items, 0, 4096};
    World w; world_init(&w);
    unsigned admitted = 0, runs = 0, agree = 0, intended = 0, p0_only = 0, p1_only = 0, checked_runs = 0, outcome_counts[5] = {0};
    for (unsigned k = 0; k < programs; ++k) {
        TcIsaProgram prog; char err[256];
        pool.len = 0;
        gen_program(&pool, &prog, false);
        if (!tisa_admit(&prog, NULL, err, sizeof err)) {
            /* A program p0 accepts and p1 refuses must be one of p1's
               intended refusals: a loop body that changes a type. */
            TcIsaProgram probe = prog; char err0[256];
            if (tisa_check_program(&probe, err0, sizeof err0)) {
                ++p0_only;
                if (!unsound_loop(&prog)) {
                    ++failures;
                    if (failures < 5) { fprintf(stderr, "p1 refuses a p0 program without a type-changing loop: %s\n", err); dump(prog.root, 2); }
                }
            }
            continue;
        }
        ++admitted;
        char err0[256];
        TcIsaProgram prog0 = prog;
        /* p1 joins types where paths meet; p0 dropped a register whose types
           differed. Programs only p1 admits get the checked run alone. */
        bool p0_admits = tisa_check_program(&prog0, err0, sizeof err0);
        p1_only += !p0_admits;
        for (unsigned j = 0; j < inputs; ++j) {
            gen_inputs(&w, &prog);
            uint8_t saved[REGIONS][SPAN]; for (unsigned r = 0; r < REGIONS; ++r) memcpy(saved[r], w.bytes[r], SPAN);
            TcIsaRuntimeFrame frame = w.frame; uint64_t regs[TISA_NUM_VREGS]; memcpy(regs, w.regs, sizeof regs);
            /* p1 (no FUND points, so no allowance is needed); then the
               type-checked build on the same input */
            Result one, zero, typed_run;
            capture(&w, tisa_run(&prog, &w.frame, w.regs), &one);
            for (unsigned r = 0; r < REGIONS; ++r) memcpy(w.bytes[r], saved[r], SPAN);
            w.frame = frame; memcpy(w.regs, regs, sizeof regs);
            capture(&w, tisa_run_checked(&prog, &w.frame, w.regs), &typed_run);
            EXPECT(same_result(&one, &typed_run), "the type-checked build ran differently");
            ++checked_runs;
            if (!p0_admits) continue;
            /* p0 on the same buffers, budget 0 (which p0 read as unbounded) */
            for (unsigned r = 0; r < REGIONS; ++r) memcpy(w.bytes[r], saved[r], SPAN);
            w.frame = frame; w.frame.fuel_budget = 0; memcpy(w.regs, regs, sizeof regs);
            capture(&w, tisa_eval_ref(&prog0, &w.frame, w.regs), &zero);
            ++runs;
            if (same_result(&one, &zero)) { ++agree; ++outcome_counts[one.outcome]; continue; }
            /* The p0-compatible build must agree exactly: then the difference
               is the intended one (SEMANTICS.txt, section 10). */
            Result compat;
            for (unsigned r = 0; r < REGIONS; ++r) memcpy(w.bytes[r], saved[r], SPAN);
            w.frame = frame; memcpy(w.regs, regs, sizeof regs);
            capture(&w, tisa_run_p0compat(&prog, &w.frame, w.regs), &compat);
            if (same_result(&compat, &zero)) { ++intended; continue; }
            if (failures < 20)
                fprintf(stderr, "differ: program %u input %u: p1 outcome %d ret %" PRIx64 ", p0 outcome %d ret %" PRIx64 "\n",
                        k, j, (int)one.outcome, one.ret_val, (int)zero.outcome, zero.ret_val);
            if (failures < 3 && getenv("TISA_DUMP")) {
                dump(prog.root, 2);
                for (uint8_t r = 0; r < prog.nregions; ++r)
                    fprintf(stderr, "  region %u mode %d min %u align %u: base %" PRIx64 " len %" PRIu64 "\n", r,
                            (int)prog.regions[r].mode, prog.regions[r].min_byte_len, prog.regions[r].align_bytes,
                            ((uint64_t *)(void *)&frame)[2 * r], ((uint64_t *)(void *)&frame)[2 * r + 1]);
                for (uint8_t r = 0; r < 6; ++r) fprintf(stderr, "  v%u %s = %" PRIx64 "\n", r, type_names[prog.init_reg_types[r]], regs[r]);
            }
            ++failures;
        }
    }
    printf("differential: %u of %u random programs admitted; %u runs, %u agree with p0 "
           "(fired %u, refused %u, unsupported %u, invalid %u); %u differ only where p1 refuses a non-Boolean word "
           "loaded as BOOL, and agree exactly with a p1 build that keeps p0's low bit there; %u programs p0 accepts are refused by p1, each "
           "with a loop body that changes a register's type or a pointer's region; %u admitted only by p1 (types joined where paths meet); "
           "%u runs of the type-checked build found every typed register holding a value of its type\n",
           admitted, programs, runs, agree, outcome_counts[1], outcome_counts[0], outcome_counts[2], outcome_counts[3],
           intended, p0_only, p1_only, checked_runs);
    world_free(&w);
}

/* ---- 3. Cost laws --------------------------------------------------------- */

static void cost_laws(unsigned programs) {
    static TcIsaStmt items[4096], erased[4096];
    Pool pool = {items, 0, 4096};
    World w; world_init(&w);
    unsigned checked = 0, exhausted_somewhere = 0;
    for (unsigned k = 0; k < programs; ++k) {
        TcIsaProgram prog; TcIsaAdmission adm; char err[256];
        pool.len = 0;
        gen_program(&pool, &prog, true);
        if (!tisa_admit(&prog, &adm, err, sizeof err) || !adm.fund_points) continue;
        EXPECT(adm.max_receipt_fits, "a random program's receipt bound does not fit (program %u)", k);
        if (!adm.max_receipt_fits) continue;
        ++checked;
        gen_inputs(&w, &prog);
        uint8_t saved[REGIONS][SPAN]; for (unsigned r = 0; r < REGIONS; ++r) memcpy(saved[r], w.bytes[r], SPAN);
        TcIsaRuntimeFrame frame = w.frame; uint64_t regs[TISA_NUM_VREGS]; memcpy(regs, w.regs, sizeof regs);
        #define RESET() do { for (unsigned r = 0; r < REGIONS; ++r) memcpy(w.bytes[r], saved[r], SPAN); \
                             w.frame = frame; memcpy(w.regs, regs, sizeof regs); } while (0)
        /* The sufficient allowance (max_receipt), and the same program with
           every FUND erased. */
        Result full, bare;
        RESET(); w.frame.fuel_budget = adm.max_receipt; capture(&w, tisa_run(&prog, &w.frame, w.regs), &full);
        memcpy(erased, items, pool.len * sizeof *items);
        for (size_t s = 0; s < pool.len; ++s) {
            strip_funds(&items[s], &erased[s], items, erased);
            /* Re-point children into the erased copy. */
            TcIsaStmt *e = &erased[s];
            #define MOVE(ptr) do { if (ptr) ptr = erased + ((ptr) - items); } while (0)
            switch (e->kind) {
            case TISA_CTRL_SEQ: MOVE(e->u.seq.first); MOVE(e->u.seq.second); break;
            case TISA_CTRL_IF: MOVE(e->u.if_cond.then_branch); MOVE(e->u.if_cond.else_branch); break;
            case TISA_CTRL_COUNT_LOOP: MOVE(e->u.count_loop.body); break;
            case TISA_CTRL_EARLY_EXIT_LOOP: MOVE(e->u.early_exit_loop.body); break;
            default: break;
            }
        }
        TcIsaProgram bare_prog = prog; bare_prog.root = erased + (prog.root - items);
        RESET(); capture(&w, tisa_run(&bare_prog, &w.frame, w.regs), &bare);
        EXPECT(full.outcome != TISA_OUTCOME_EXHAUSTED && same_result(&full, &bare),
               "erasure: the run at max_receipt differs from the FUND-free program (program %u)", k);
        EXPECT(full.receipt <= adm.max_receipt, "receipt %" PRIu64 " above the static bound %" PRIu64, full.receipt, adm.max_receipt);
        /* Every allowance from 0 to the full receipt: monotone prefixes. */
        Result previous = {0};
        for (uint64_t a = 0; a <= full.receipt; ++a) {
            Result at;
            RESET(); w.frame.fuel_budget = a; capture(&w, tisa_run(&prog, &w.frame, w.regs), &at);
            if (a == 0 && full.receipt > 0)
                EXPECT(at.outcome == TISA_OUTCOME_EXHAUSTED && at.receipt == 0, "zero allowance paid for work");
            if (at.outcome == TISA_OUTCOME_EXHAUSTED) {
                ++exhausted_somewhere;
                EXPECT(at.receipt <= a && at.status == 4 && at.ret_val == 4, "exhaustion at allowance %" PRIu64 " wrong", a);
                EXPECT(a == 0 || at.receipt >= previous.receipt, "receipt shrank as the allowance grew");
            } else EXPECT(same_result(&at, &full) && at.receipt == full.receipt,
                          "a determinate outcome at allowance %" PRIu64 " differs from the sufficient one", a);
            previous = at;
        }
        #undef RESET
    }
    printf("cost laws: %u random programs with FUND points; erasure, static bound, zero allowance and "
           "monotonicity over every allowance up to the receipt (%u exhausted runs)\n", checked, exhausted_somewhere);
    world_free(&w);
}

/* ---- 4. Native code against the reference --------------------------------- */

static void native(unsigned programs, unsigned inputs) {
    static TcIsaStmt items[4096];
    Pool pool = {items, 0, 4096};
    World w; world_init(&w);
    unsigned emitted = 0, runs = 0, outcome_counts[5] = {0};
    unsigned loops = 0, hoisted_loops = 0, hoisted_checks = 0, fund_loops = 0, hoisted_programs = 0, hot_runs = 0;
    const char *reasons[8]; unsigned reason_counts[8] = {0}, nreasons = 0;
    size_t bytes = 0, funds = 0, hoisted_bytes = 0;
    for (unsigned k = 0; k < programs; ++k) {
        TcIsaProgram prog; TcIsaAdmission adm; char err[256];
        pool.len = 0;
        gen_program(&pool, &prog, pick(2));
        if (!tisa_admit(&prog, &adm, err, sizeof err)) continue;
        TcIsaX86 code, fast;
        const TcIsaX86Options hoist = {.hoist_bounds = true};
        if (!tisa_x86_emit(&prog, &code, err, sizeof err) || !tisa_x86_load(&code, err, sizeof err)) {
            ++failures; fprintf(stderr, "emission failed: %s\n", err); continue;
        }
        if (!tisa_x86_emit_with(&prog, &hoist, &fast, err, sizeof err) || !tisa_x86_load(&fast, err, sizeof err)) {
            ++failures; fprintf(stderr, "hoisted emission failed: %s\n", err); tisa_x86_free(&code); continue;
        }
        ++emitted; bytes += code.len; funds += adm.fund_points; hoisted_bytes += fast.len;
        unsigned here = 0;
        for (size_t l = 0; l < fast.nloops; ++l) {
            ++loops;
            if (!fast.loops[l].hoisted) {
                unsigned q = 0;
                while (q < nreasons && strcmp(reasons[q], fast.loops[l].reason)) ++q;
                if (q == nreasons && nreasons < 8) reasons[nreasons++] = fast.loops[l].reason;
                if (q < 8) ++reason_counts[q];
                continue;
            }
            ++here; hoisted_checks += fast.loops[l].hoisted_checks; fund_loops += fast.loops[l].fund_units > 0;
        }
        hoisted_loops += here; hoisted_programs += here > 0;
        EXPECT(code.nloops == fast.nloops, "loop records differ between the emissions");
        if (!here) EXPECT(code.len == fast.len && !memcmp(code.bytes, fast.bytes, code.len),
                          "an image with no hoisted loop differs from the default");
        for (unsigned j = 0; j < inputs; ++j) {
            gen_inputs(&w, &prog);
            /* Allowances below, at and above what the run needs, and a receipt
               carried in from earlier calls. */
            w.frame.fuel_used = pick(3) ? 0 : pick(4);
            uint64_t need = adm.max_receipt;
            w.frame.fuel_budget = w.frame.fuel_used + (pick(3) ? pick((unsigned)(need < 6 ? need + 2 : 8)) : need);
            uint8_t saved[REGIONS][SPAN]; for (unsigned r = 0; r < REGIONS; ++r) memcpy(saved[r], w.bytes[r], SPAN);
            TcIsaRuntimeFrame frame = w.frame; uint64_t regs[TISA_NUM_VREGS]; memcpy(regs, w.regs, sizeof regs);
            Result ref, nat;
            capture(&w, tisa_run(&prog, &w.frame, w.regs), &ref);
            for (unsigned r = 0; r < REGIONS; ++r) memcpy(w.bytes[r], saved[r], SPAN);
            w.frame = frame; memcpy(w.regs, regs, sizeof regs);
            capture(&w, tisa_x86_run(&prog, &code, &w.frame, w.regs), &nat);
            ++runs;
            Result hot = nat;
            if (here) {
                for (unsigned r = 0; r < REGIONS; ++r) memcpy(w.bytes[r], saved[r], SPAN);
                w.frame = frame; memcpy(w.regs, regs, sizeof regs);
                capture(&w, tisa_x86_run(&prog, &fast, &w.frame, w.regs), &hot);
                ++hot_runs;
            }
            if (!same_result(&ref, &hot) || ref.receipt != hot.receipt) {
                if (failures < 10)
                    fprintf(stderr, "hoisted differs: program %u input %u: reference %d ret %" PRIx64 " receipt %" PRIu64
                            ", hoisted %d ret %" PRIx64 " receipt %" PRIu64 "\n", k, j, (int)ref.outcome, ref.ret_val,
                            ref.receipt, (int)hot.outcome, hot.ret_val, hot.receipt);
                if (failures < 2) dump(prog.root, 2);
                ++failures;
            }
            if (same_result(&ref, &nat) && ref.receipt == nat.receipt) { ++outcome_counts[ref.outcome]; continue; }
            if (failures < 10) {
                fprintf(stderr, "native differs: program %u input %u: reference %d ret %" PRIx64 " receipt %" PRIu64
                        ", native %d ret %" PRIx64 " receipt %" PRIu64 "\n", k, j, (int)ref.outcome, ref.ret_val,
                        ref.receipt, (int)nat.outcome, nat.ret_val, nat.receipt);
                if (failures < 2) dump(prog.root, 2);
            }
            ++failures;
        }
        tisa_x86_free(&code); tisa_x86_free(&fast);
    }
    printf("native: %u programs emitted (%zu bytes, %zu FUND points in all); %u runs equal to the reference on outcome, "
           "status, ret_val, receipt and every region byte (fired %u, refused %u, unsupported %u, invalid %u, exhausted %u)\n",
           emitted, bytes, funds, runs, outcome_counts[1], outcome_counts[0], outcome_counts[2], outcome_counts[3],
           outcome_counts[4]);
    printf("hoisted: %u of %u loops in %u programs (%u checks moved to loop entry, %u loops with FUND tested at entry; "
           "%zu bytes against %zu); %u runs of images with a hoisted loop, each equal to the reference\n", hoisted_loops,
           loops, hoisted_programs, hoisted_checks, fund_loops, hoisted_bytes, bytes, hot_runs);
    printf("  not hoisted:");
    for (unsigned q = 0; q < nreasons; ++q) printf("%s %s %u", q ? "," : "", reasons[q], reason_counts[q]);
    putchar('\n');
    world_free(&w);
}

/* ---- 4b. Hoisted bounds, both paths -------------------------------------
 * x from 0 to 16 stores x at word x of region 0, optionally paying 3 per
 * element. With the region and the allowance exactly enough, the entry test
 * passes and the copy without checks runs. One byte or one unit short, the
 * test fails and the template loop runs, failing at the last element after
 * the earlier stores (and payments). Native and reference must agree, and on
 * the values written out here. */
static void hoist_cases(void) {
    TcIsaStmt items[64]; Pool p = {items, 0, 64};
    World w; world_init(&w);
    TcIsaProgram prog; char err[256];
    const uint64_t n = 16;
    for (unsigned paying = 0; paying < 2; ++paying) {
        p.len = 0;
        TcIsaStmt *body = seq(&p, instr(&p, addr(0, 5, 1, 4, 3, 0)), instr(&p, store(8, 0, 5, 0, 4)));
        if (paying) body = seq(&p, body, fund(&p, 3));
        program_init(&prog, seq(&p, count_loop(&p, 4, 3, 64, body), ret(&p, TISA_OUTCOME_FIRED, 3)));
        EXPECT(tisa_admit(&prog, NULL, err, sizeof err), "hoisting case refused: %s", err);
        TcIsaX86 x; const TcIsaX86Options hoist = {.hoist_bounds = true};
        if (!tisa_x86_emit_with(&prog, &hoist, &x, err, sizeof err) || !tisa_x86_load(&x, err, sizeof err)) {
            EXPECT(false, "hoisting case not emitted: %s", err); continue;
        }
        EXPECT(x.nloops == 1 && x.loops[0].hoisted && x.loops[0].hoisted_checks == 2 &&
               x.loops[0].fund_units == (paying ? 3u : 0u), "hoisting case not hoisted as expected");
        for (uint64_t short_by = 0; short_by < 2; ++short_by) {
            Result res[2];
            for (unsigned native = 0; native < 2; ++native) {
                frame_setup(&w, paying ? 128 : 128 - short_by, 16, n);
                if (paying) w.frame.fuel_budget = 3 * n - short_by;
                memset(w.bytes[0], 0xEE, SPAN);
                capture(&w, native ? tisa_x86_run(&prog, &x, &w.frame, w.regs) : tisa_run(&prog, &w.frame, w.regs), &res[native]);
            }
            EXPECT(same_result(&res[0], &res[1]) && res[0].receipt == res[1].receipt,
                   "hoisted run differs from the reference (paying %u, short by %" PRIu64 ")", paying, short_by);
            uint64_t last = n - 1, word;
            TcIsaOutcome want = !short_by ? TISA_OUTCOME_FIRED : paying ? TISA_OUTCOME_EXHAUSTED : TISA_OUTCOME_INVALID_INPUT;
            bool stored_last = !short_by || paying;
            EXPECT(res[1].outcome == want && res[1].receipt == (paying ? 3 * (stored_last && !short_by ? n : last) : 0),
                   "hoisting case outcome %d receipt %" PRIu64 " (paying %u, short by %" PRIu64 ")",
                   (int)res[1].outcome, res[1].receipt, paying, short_by);
            for (uint64_t k = 0; k < n; ++k) {
                memcpy(&word, res[1].bytes[0] + 8 * k, 8);
                bool written = k < last || stored_last;
                EXPECT(written ? word == k : word == UINT64_C(0xEEEEEEEEEEEEEEEE), "hoisting case word %" PRIu64 " wrong", k);
            }
        }
        tisa_x86_free(&x);
    }
    world_free(&w);
    printf("hoisting cases: the copy without checks when the region and allowance suffice; the template loop, "
           "failing at the last element after the earlier stores and payments, when one byte or unit is short\n");
}

/* ---- 5. Corpora for the HOL semantics and the MeTTa emitter ----------------
 * Random admitted programs, drawn with frame loads and RETURN UNSUPPORTED as
 * well. --export-hol writes each with an entry state and this reference's
 * result as one OCaml line, tisa_check "id" `prog` `state` `buffers`
 * `(outcome, status, ret_val, receipt, [buffer contents])`;;, read by
 * hol/tisa_p1_fidelity.ml. --export-sexpr writes each program as an
 * S-expression and, in a second file, the image tisa_x86.c emits for it. */

static void number(FILE *f, const uint8_t *bytes, size_t n) {   /* little-endian bytes as a numeral */
    size_t top = n;
    while (top && !bytes[top - 1]) --top;
    if (!top) { fputc('0', f); return; }
    fputs("0x", f);
    for (size_t k = top; k-- > 0;) fprintf(f, "%02x", bytes[k]);
}

static void hol_state(FILE *f, const World *w, const TcIsaProgram *p) {
    fputs("TState (\\i. ", f);
    for (unsigned r = 0; r < TISA_NUM_VREGS; ++r) fprintf(f, "if i = %u then word %" PRIu64 " else ", r, w->regs[r]);
    fputs("word 0) (", f);
    for (uint8_t r = 0; r < p->nregions; ++r) {
        fprintf(f, "write (bytes(word %" PRIu64 ",%u)) ", (uint64_t)(uintptr_t)w->bytes[r], SPAN);
        number(f, w->bytes[r], SPAN);
        fputs(" (", f);
    }
    fprintf(f, "write (bytes(word %" PRIu64 ",192)) ", (uint64_t)(uintptr_t)&w->frame);
    number(f, (const uint8_t *)&w->frame, sizeof w->frame);
    fputs(" tisa_zero_mem", f);
    for (uint8_t r = 0; r < p->nregions; ++r) fputc(')', f);
    fputc(')', f);
}

typedef struct { unsigned op[10][6], ctrl[7], outcome[5], frame_loads, entry_invalid; } Coverage;

static void cover(Coverage *c, const TcIsaStmt *s) {
    if (!s) return;
    c->ctrl[s->kind]++;
    switch (s->kind) {
    case TISA_CTRL_INSTR:
        c->op[s->u.instr.op][s->u.instr.ty]++;
        if (s->u.instr.op == TISA_OP_LOAD && s->u.instr.region_id == TISA_REGION_FRAME) c->frame_loads++;
        break;
    case TISA_CTRL_SEQ: cover(c, s->u.seq.first); cover(c, s->u.seq.second); break;
    case TISA_CTRL_IF: cover(c, s->u.if_cond.then_branch); cover(c, s->u.if_cond.else_branch); break;
    case TISA_CTRL_COUNT_LOOP: cover(c, s->u.count_loop.body); break;
    case TISA_CTRL_EARLY_EXIT_LOOP: cover(c, s->u.early_exit_loop.body); break;
    default: break;
    }
}

/* True when s contains a 1-byte BOOL load from a region. */
static bool has_bool_byte_load(const TcIsaStmt *s) {
    if (!s) return false;
    switch (s->kind) {
    case TISA_CTRL_INSTR:
        return s->u.instr.op == TISA_OP_LOAD && s->u.instr.ty == TISA_TYPE_BOOL &&
               s->u.instr.subop == 1 && s->u.instr.region_id != TISA_REGION_FRAME;
    case TISA_CTRL_SEQ: return has_bool_byte_load(s->u.seq.first) || has_bool_byte_load(s->u.seq.second);
    case TISA_CTRL_IF: return has_bool_byte_load(s->u.if_cond.then_branch) || has_bool_byte_load(s->u.if_cond.else_branch);
    case TISA_CTRL_COUNT_LOOP: return has_bool_byte_load(s->u.count_loop.body);
    case TISA_CTRL_EARLY_EXIT_LOOP: return has_bool_byte_load(s->u.early_exit_loop.body);
    default: return false;
    }
}

/* --export-images FILE N SEED: N admitted random programs (extended
   generation) as records for the HOL image prover, with what they cover. */
/* With hoist, the images are emitted with bounds hoisting, from array-loop
   programs, and only those with a hoisted loop are written. */
static int export_images(const char *path, unsigned count, bool hoist) {
    FILE *f = fopen(path, "w");
    if (!f) { perror("export"); return 1; }
    static TcIsaStmt items[4096];
    Pool pool = {items, 0, 4096};
    Coverage c; memset(&c, 0, sizeof c);
    extended_generation = true;
    array_generation = hoist;
    const TcIsaX86Options options = {.hoist_bounds = hoist};
    unsigned hoisted_loops = 0;
    unsigned written = 0, funds = 0;
    size_t bytes = 0;
    for (unsigned attempt = 0; written < count && attempt < 50u * count; ++attempt) {
        TcIsaProgram prog; TcIsaAdmission adm; char err[256], name[32];
        pool.len = 0;
        gen_program(&pool, &prog, pick(2));
        if (!tisa_admit(&prog, &adm, err, sizeof err)) continue;
        TcIsaX86 x;
        if (!tisa_x86_emit_with(&prog, &options, &x, err, sizeof err)) { fprintf(stderr, "emit: %s\n", err); return 1; }
        unsigned here = 0;
        for (size_t l = 0; l < x.nloops; ++l) here += x.loops[l].hoisted;
        if (hoist && !here) { tisa_x86_free(&x); continue; }
        hoisted_loops += here;
        snprintf(name, sizeof name, hoist ? "h%u" : "r%u", written);
        if (!tisa_print_image_record(f, name, &prog, &x)) { fprintf(stderr, "record %s failed\n", name); return 1; }
        bytes += x.len; funds += adm.fund_points;
        tisa_x86_free(&x);
        cover(&c, prog.root);
        ++written;
    }
    fclose(f);
    printf("exported %u image records to %s (%zu bytes of code, %u FUND points, %u hoisted loops)\n", written, path,
           bytes, funds, hoisted_loops);
    printf("  IF %u, COUNT_LOOP %u, EARLY_EXIT_LOOP %u, RETURN %u, FUND %u, frame loads %u\n",
           c.ctrl[TISA_CTRL_IF], c.ctrl[TISA_CTRL_COUNT_LOOP], c.ctrl[TISA_CTRL_EARLY_EXIT_LOOP],
           c.ctrl[TISA_CTRL_RETURN], c.ctrl[TISA_CTRL_FUND], c.frame_loads);
    return written == count ? 0 : 1;
}

static int export_corpus(bool hol, const char *path, const char *images_path, unsigned count) {
    FILE *f = fopen(path, "w"), *g = images_path ? fopen(images_path, "w") : NULL;
    if (!f || (images_path && !g)) { perror("export"); return 1; }
    static TcIsaStmt items[4096];
    Pool pool = {items, 0, 4096};
    World w; world_init(&w);
    Coverage c; memset(&c, 0, sizeof c);
    extended_generation = true;
    unsigned written = 0;
    for (unsigned attempt = 0; written < count && attempt < 50u * count; ++attempt) {
        TcIsaProgram prog; TcIsaAdmission adm; char err[256];
        pool.len = 0;
        gen_program(&pool, &prog, pick(2));
        if (!tisa_admit(&prog, &adm, err, sizeof err)) continue;
        if (!hol) {
            TcIsaX86 x;
            if (!tisa_x86_emit(&prog, &x, err, sizeof err)) { fprintf(stderr, "emit: %s\n", err); return 1; }
            fprintf(f, "(tisa-case \"r%u\" ", written);
            if (!tisa_print_program(f, TISA_TEXT_SEXPR, &prog)) { fprintf(stderr, "print failed\n"); return 1; }
            fputs(")\n", f);
            fprintf(g, "r%u ", written);
            for (size_t b = 0; b < x.len; ++b) fprintf(g, "%02x", x.bytes[b]);
            for (size_t k = 0; k < x.nspans; ++k)
                fprintf(g, " %u:%u:%s", x.spans[k].offset, x.spans[k].length, x.spans[k].template_name);
            fputc('\n', g);
            tisa_x86_free(&x);
            cover(&c, prog.root);
            ++written;
            continue;
        }
        /* Every eighth case is a boundary case: a program with a 1-byte BOOL
           load and every region byte 2, the first value such a load refuses. */
        bool boundary = written % 8 == 7;
        if (boundary && !has_bool_byte_load(prog.root)) continue;
        gen_inputs(&w, &prog);
        if (boundary)
            for (uint8_t r = 0; r < prog.nregions; ++r) memset(w.bytes[r], 2, SPAN);
        else if (pick(4) == 0)   /* bytes in {0, 1, 2}: BOOL loads meet 2 */
            for (uint8_t r = 0; r < prog.nregions; ++r) for (unsigned b = 0; b < SPAN; ++b) w.bytes[r][b] = (uint8_t)pick(3);
        if (adm.fund_points) {
            unsigned how = pick(4);
            uint64_t budget = how == 0 ? UINT64_MAX : how == 1 ? adm.max_receipt : (uint64_t)pick((unsigned)adm.max_receipt + 1u);
            w.frame.fuel_budget = budget;
            w.frame.fuel_used = pick(4) == 0 ? (uint64_t)pick((unsigned)(budget < 1000 ? budget : 1000) + 1u) : 0;
            if (budget != UINT64_MAX && w.frame.fuel_used <= budget && pick(3) == 0 && budget >= w.frame.fuel_used + adm.max_receipt)
                w.frame.fuel_used = budget - adm.max_receipt;   /* exactly enough */
        }
        if (pick(30) == 0) { w.frame.fuel_budget = 5; w.frame.fuel_used = 6; }   /* receipt above allowance: entry fails */
        bool entry = tisa_entry_valid(&prog, &w.frame, w.regs);
        fprintf(f, "tisa_check \"r%u\" `", written);
        if (!tisa_print_program(f, TISA_TEXT_HOL, &prog)) { fprintf(stderr, "print failed\n"); return 1; }
        fputs("` `", f);
        hol_state(f, &w, &prog);
        TcIsaOutcome o = tisa_run(&prog, &w.frame, w.regs);
        fputs("` `[", f);
        for (uint8_t r = 0; r < prog.nregions; ++r) fprintf(f, "%s%" PRIu64, r ? "; " : "", (uint64_t)(uintptr_t)w.bytes[r]);
        fprintf(f, "]` `(%u,%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",[", (unsigned)o, w.frame.status, w.frame.ret_val, w.frame.fuel_used);
        for (uint8_t r = 0; r < prog.nregions; ++r) { if (r) fputs("; ", f); number(f, w.bytes[r], SPAN); }
        fputs("])`;;\n", f);
        cover(&c, prog.root);
        c.outcome[o]++;
        if (!entry) c.entry_invalid++;
        ++written;
    }
    fclose(f); if (g) fclose(g);
    world_free(&w);
    printf("exported %u programs to %s\n", written, path);
    static const char *ops[] = {"IMM", "MOV", "BIN", "SHIFT", "EXTRACT", "ADDR", "LOAD", "STORE", "CMP", "SELECT"};
    static const char *types[] = {"-", "U64", "U32Z", "I32S", "BOOL", "PTR"};
    for (unsigned op = 0; op < 10; ++op) {
        printf("  %-8s", ops[op]);
        for (unsigned t = 0; t < 6; ++t) if (c.op[op][t]) printf(" %s:%u", types[t], c.op[op][t]);
        putchar('\n');
    }
    printf("  frame loads %u; IF %u, COUNT_LOOP %u, EARLY_EXIT_LOOP %u, RETURN %u, FUND %u\n", c.frame_loads,
           c.ctrl[TISA_CTRL_IF], c.ctrl[TISA_CTRL_COUNT_LOOP], c.ctrl[TISA_CTRL_EARLY_EXIT_LOOP], c.ctrl[TISA_CTRL_RETURN], c.ctrl[TISA_CTRL_FUND]);
    if (hol) printf("  outcomes: REFUSED %u, FIRED %u, UNSUPPORTED %u, INVALID_INPUT %u (%u at entry), EXHAUSTED %u\n",
                    c.outcome[0], c.outcome[1], c.outcome[2], c.outcome[3], c.entry_invalid, c.outcome[4]);
    return written == count ? 0 : 1;
}

int main(int argc, char **argv) {
    if (argc >= 4 && !strcmp(argv[1], "--export-images")) {
        if (argc > 4) rng = strtoull(argv[4], NULL, 10) | 1u;
        return export_images(argv[2], (unsigned)strtoul(argv[3], NULL, 10), argc > 5 && !strcmp(argv[5], "--hoist"));
    }
    if (argc >= 4 && (!strcmp(argv[1], "--export-hol") || !strcmp(argv[1], "--export-sexpr"))) {
        bool hol = !strcmp(argv[1], "--export-hol");
        unsigned count = (unsigned)strtoul(argv[3], NULL, 10);
        if (argc > 4) rng = strtoull(argv[4], NULL, 10) | 1u;
        char images[4096];
        if (!hol) snprintf(images, sizeof images, "%s.images", argv[2]);
        return export_corpus(hol, argv[2], hol ? NULL : images, count);
    }
    if (argc >= 3 && !strcmp(argv[1], "--hoist")) {
        array_generation = true;
        if (argc > 3) rng = strtoull(argv[3], NULL, 10) | 1u;
        hoist_cases();
        native((unsigned)strtoul(argv[2], NULL, 10), 8);
        if (failures) { printf("%d failures\n", failures); return 1; }
        puts("all passed");
        return 0;
    }
    unsigned programs = argc > 1 ? (unsigned)strtoul(argv[1], NULL, 10) : 2000;
    if (argc > 2) rng = strtoull(argv[2], NULL, 10) | 1u;
    targeted();
    printf("targeted: instructions, bounds, admission refusals, the loop-typing case, funding and entry\n");
    differential(programs, 8);
    cost_laws(programs);
    native(programs, 8);
    hoist_cases();
    if (failures) { printf("%d failures\n", failures); return 1; }
    puts("all passed");
    return 0;
}
