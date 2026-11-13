/*
 * test_records.c -- the record loop (records.S) over the plan driver
 * (driver.S), linked with the proved images of intern16, fnv, leb128 and
 * intern_name, run natively and compared with the record semantics run by
 * the p1 reference evaluator (tisa_ref.c).
 *
 *   test_records INTERN16.txt FNV.txt LEB128.txt NAME.txt DRIVER.bin RECORDS.bin [RUNS] [SEED]
 *
 * The four texts are the leaves' programs; DRIVER.bin and RECORDS.bin the
 * two loops' .text as assembled (the bytes the proofs read come from the
 * same objects). Before any run, the linked bytes are checked: each leaf
 * image must be the one tisa_x86_emit produces from its text, and
 * tisa_drive and tisa_records must hold the two .bin files exactly.
 *
 * The reference side runs a plan as drv_sem says (see test_driver.c) and
 * the record loop as records.S's header says: one unit of fuel per record
 * (EXHAUSTED when the receipt has reached the allowance), the decode plan,
 * the opcode, the handler (UNSUPPORTED when missing), the END word. Both
 * sides start from equal copies of one state; outcomes, receipts, record
 * counts, plan descriptors, control words and region bytes must agree, and
 * guard bytes around every area must survive.
 *
 * The name plan (fnv, then intern_name with the hash fnv returned) is
 * checked against its specification too: FNV-1a 64 of the name, one id per
 * name, REFUSED exactly when the name lies outside the input.
 *
 * Plans are also run on their own, with each outcome that ends a plan: a
 * leaf's REFUSED mid-plan, a receipt above the allowance (INVALID before
 * any call), a leaf's EXHAUSTED. None of the four proved leaves pays fuel
 * (no FUND, no return of 4), so EXHAUSTED comes from a test-only leaf,
 * "meter" (FUND 2, then FIRED with payload 7), emitted by tisa_x86_emit
 * into executable memory at run time; it has no image theorem.
 *
 * The harness prints the process's CET state and stops if user shadow
 * stacks are on (cet_profile.h): the supported profile has SHSTK off.
 *
 * Exit status 0 iff every check passes.
 */
#include "cet_profile.h"
#include "p1_load.h"
#include "tisa_ref.h"
#include "tisa_x86.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    const uint64_t *plan, *plan_end;
    uint64_t       *ctl;
    const uint64_t *bind;
    const uint64_t *leaves;
    uint64_t        budget, used;
    const uint64_t *at;
} TcDrive;

typedef struct {
    const void *drive;
    TcDrive    *decode;
    TcDrive   **table;
    uint64_t    nh;
    uint64_t   *op, *end;
    uint64_t    budget, used, count;
} TcRecords;

uint64_t tisa_drive(TcDrive *d);
uint64_t tisa_records(TcRecords *r);
extern const uint8_t tisa_leaf_intern16[], tisa_leaf_intern16_end[];
extern const uint8_t tisa_leaf_fnv[], tisa_leaf_fnv_end[];
extern const uint8_t tisa_leaf_leb128[], tisa_leaf_leb128_end[];
extern const uint8_t tisa_leaf_name[], tisa_leaf_name_end[];

enum { L_INTERN16, L_FNV, L_LEB128, L_NAME, L_METER, NLEAVES };
enum { STEPW = 18, NCTL = 32, MAXSTEPS = 4, NPLANS = 6, NH = 5, INPUT = 256, GUARD = 64, GB = 0xA5 };
/* Binding words: the input, leb128's out, intern16's rows/table/header,
   intern_name's rows/arena/table/header, the empty region. */
enum { B_INPUT = 0, B_LEBOUT = 2, B_I16 = 4, B_NAME = 10, B_EMPTY = 18, NBIND = 20 };
/* Control words the scenarios use. */
enum { C_POS = 0, C_OP = 1, C_END = 2, C_ONE = 3, C_ZERO = 4, C_OFF = 5, C_LEN = 6, C_H0 = 7,
       C_HASH = 8, C_ID = 9, C_BIG = 10 };

/* The test-only leaf: FUND 2, then FIRED with payload 7. */
static const char METER_TEXT[] =
    "(TProg [] [] (TSeq (TFund 2) (TSeq (TInstr (TImm TyU64 1 (word 7))) (TReturn 1 1))))";
static TcIsaX86 meter;

static uint64_t rng = 0x9E3779B97F4A7C15ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

/* ---- guarded areas ---------------------------------------------------------- */

typedef struct { uint8_t *alloc, *p; size_t len; } Area;

static void area_new(Area *a, size_t len) {
    a->alloc = aligned_alloc(64, (len + 2 * GUARD + 63) / 64 * 64);
    if (!a->alloc) { perror("alloc"); exit(2); }
    a->p = a->alloc + GUARD;
    a->len = len;
    memset(a->alloc, GB, len + 2 * GUARD);
    memset(a->p, 0, len);
}
static int area_guarded(const Area *a) {
    for (size_t k = 0; k < GUARD; ++k)
        if (a->alloc[k] != GB || a->p[a->len + k] != GB) return 0;
    return 1;
}
static uint64_t *W(Area *a) { return (uint64_t *)a->p; }

/* One side: every area a plan or the loop reads or writes. Plans 0..NPLANS-1
   have their steps in plan[k] and their descriptors in desc (word 8k). */
typedef struct {
    Area ctl, input, lebout, i16rows, i16table, i16header, nrows, narena, ntable, nheader;
    Area plan[NPLANS], desc, table, bind, leaves;
    size_t nsteps[NPLANS];
} Side;

/* Every area of a side, in one order. */
static size_t areas(Side *s, Area **l) {
    size_t k = 0;
    l[k++] = &s->ctl; l[k++] = &s->input; l[k++] = &s->lebout;
    l[k++] = &s->i16rows; l[k++] = &s->i16table; l[k++] = &s->i16header;
    l[k++] = &s->nrows; l[k++] = &s->narena; l[k++] = &s->ntable; l[k++] = &s->nheader;
    for (int p = 0; p < NPLANS; ++p) l[k++] = &s->plan[p];
    l[k++] = &s->desc; l[k++] = &s->table; l[k++] = &s->bind; l[k++] = &s->leaves;
    return k;
}
/* The areas holding addresses, which differ between the sides. */
static int addresses(Side *s, Area *a) { return a == &s->desc || a == &s->table || a == &s->bind || a == &s->leaves; }

static void side_new(Side *s) {
    area_new(&s->ctl, 8 * NCTL);
    area_new(&s->input, INPUT);
    area_new(&s->lebout, 16);
    area_new(&s->i16rows, 16 * 64); area_new(&s->i16table, 8 * 128); area_new(&s->i16header, 8);
    area_new(&s->nrows, 16 * 64); area_new(&s->narena, 1024); area_new(&s->ntable, 8 * 128);
    area_new(&s->nheader, 16);
    for (int p = 0; p < NPLANS; ++p) area_new(&s->plan[p], 8 * STEPW * MAXSTEPS);
    area_new(&s->desc, 8 * 8 * NPLANS);
    area_new(&s->table, 8 * NH);
    area_new(&s->bind, 8 * NBIND);
    area_new(&s->leaves, 8 * NLEAVES);
    uint64_t *b = W(&s->bind);
    Area *r[9] = {&s->input, &s->lebout, &s->i16rows, &s->i16table, &s->i16header,
                  &s->nrows, &s->narena, &s->ntable, &s->nheader};
    for (int k = 0; k < 9; ++k) { b[2 * k] = (uint64_t)(uintptr_t)r[k]->p; b[2 * k + 1] = r[k]->len; }
    b[B_EMPTY] = 0; b[B_EMPTY + 1] = 0;
    uint64_t *l = W(&s->leaves);
    l[L_INTERN16] = (uint64_t)(uintptr_t)tisa_leaf_intern16;
    l[L_FNV] = (uint64_t)(uintptr_t)tisa_leaf_fnv;
    l[L_LEB128] = (uint64_t)(uintptr_t)tisa_leaf_leb128;
    l[L_NAME] = (uint64_t)(uintptr_t)tisa_leaf_name;
    l[L_METER] = (uint64_t)(uintptr_t)meter.code;
}

static TcDrive *desc(Side *s, int p) { return (TcDrive *)(void *)(W(&s->desc) + 8 * p); }

/* Plan p's descriptor: its steps, the shared control words, bindings and leaves. */
static void side_plans(Side *s) {
    for (int p = 0; p < NPLANS; ++p) {
        TcDrive *d = desc(s, p);
        d->plan = W(&s->plan[p]); d->plan_end = W(&s->plan[p]) + STEPW * s->nsteps[p];
        d->ctl = W(&s->ctl); d->bind = W(&s->bind); d->leaves = W(&s->leaves);
        d->budget = 0; d->used = 0; d->at = NULL;
    }
}

/* Copies the mutable areas of a to b (plans and descriptors are rebuilt the
   same way on both sides; descriptors hold b's own addresses). */
static void side_copy(Side *b, Side *a) {
    Area *la[64], *lb[64];
    size_t n = areas(a, la);
    (void)areas(b, lb);
    for (size_t k = 0; k < n; ++k)
        if (!addresses(a, la[k])) memcpy(lb[k]->p, la[k]->p, la[k]->len);
    memcpy(b->nsteps, a->nsteps, sizeof a->nsteps);
    side_plans(a); side_plans(b);
    for (int k = 0; k < NH; ++k) {
        uint64_t e = W(&a->table)[k];
        W(&b->table)[k] = e == 0 ? 0 : (uint64_t)(uintptr_t)desc(b, (int)((e - (uint64_t)(uintptr_t)W(&a->desc)) / 64));
    }
}

static int side_guarded(Side *s) {
    Area *l[64];
    size_t n = areas(s, l);
    for (size_t k = 0; k < n; ++k) if (!area_guarded(l[k])) return 0;
    return 1;
}

/* Every byte both sides may change: control words, regions, descriptors
   (the at word as a step index). */
static int side_equal(Side *a, Side *b) {
    Area *la[64], *lb[64];
    size_t n = areas(a, la);
    (void)areas(b, lb);
    for (size_t k = 0; k < n; ++k)
        if (!addresses(a, la[k]) && memcmp(la[k]->p, lb[k]->p, la[k]->len)) return 0;
    for (int p = 0; p < NPLANS; ++p) {
        TcDrive *x = desc(a, p), *y = desc(b, p);
        if (x->budget != y->budget || x->used != y->used) return 0;
        if ((x->at == NULL) != (y->at == NULL)) return 0;
        if (x->at && (x->at - x->plan) != (y->at - y->plan)) return 0;
    }
    return 1;
}

/* ---- the reference --------------------------------------------------------------- */

static P1Program progs[NLEAVES];

typedef struct { uint64_t status, at, used; } Result;

/* A plan as drv_sem says; writes back the descriptor's receipt and at word. */
static Result plan_ref(Side *s, int p, uint64_t budget, uint64_t used) {
    const uint64_t *plan = W(&s->plan[p]), *bind = W(&s->bind);
    uint64_t *ctl = W(&s->ctl);
    TcDrive *d = desc(s, p);
    Result res = {TISA_OUTCOME_FIRED, s->nsteps[p], used};
    for (size_t i = 0; i < s->nsteps[p]; ++i) {
        const uint64_t *st = plan + STEPW * i;
        if (used > budget) { res = (Result){TISA_OUTCOME_INVALID_INPUT, i, used}; break; }
        TcIsaRuntimeFrame f;
        uint64_t *fw = (uint64_t *)&f;
        for (unsigned r = 0; r < 9; ++r) { fw[2 * r] = bind[st[1 + r]]; fw[2 * r + 1] = bind[st[1 + r] + 1]; }
        f.status = 0; f.ret_val = 0; f.fuel_budget = budget; f.fuel_used = used;
        f.arg0 = ctl[st[10]]; f.arg1 = ctl[st[11]];
        uint64_t regs[TISA_NUM_VREGS] = {0};
        regs[0] = (uint64_t)(uintptr_t)&f;
        for (unsigned k = 1; k <= 5; ++k) regs[k] = ctl[st[11 + k]];
        (void)tisa_run(&progs[st[0]].prog, &f, regs);
        ctl[st[17]] = f.ret_val;
        used = f.fuel_used;
        if (f.status != TISA_OUTCOME_FIRED) { res = (Result){f.status, i, used}; break; }
        res.used = used;
    }
    d->used = res.used;
    d->at = plan + STEPW * res.at;
    return res;
}

typedef struct { uint64_t status, count, used; } RecResult;

/* The record loop as records.S's header says. */
static RecResult rec_ref(Side *s, int decode, uint64_t nh, uint64_t budget, uint64_t used) {
    uint64_t *ctl = W(&s->ctl), count = 0;
    for (;;) {
        if (used >= budget) return (RecResult){TISA_OUTCOME_EXHAUSTED, count, used};
        used += 1;
        desc(s, decode)->budget = budget; desc(s, decode)->used = used;
        Result r = plan_ref(s, decode, budget, used);
        used = r.used;
        if (r.status != TISA_OUTCOME_FIRED) return (RecResult){r.status, count, used};
        uint64_t op = ctl[C_OP];
        uint64_t e = op < nh ? W(&s->table)[op] : 0;
        if (e == 0) return (RecResult){TISA_OUTCOME_UNSUPPORTED, count, used};
        int h = (int)((e - (uint64_t)(uintptr_t)W(&s->desc)) / 64);
        desc(s, h)->budget = budget; desc(s, h)->used = used;
        r = plan_ref(s, h, budget, used);
        used = r.used;
        if (r.status != TISA_OUTCOME_FIRED) return (RecResult){r.status, count, used};
        count += 1;
        if (ctl[C_END] != 0) return (RecResult){TISA_OUTCOME_FIRED, count, used};
    }
}

static RecResult rec_native(Side *s, int decode, uint64_t nh, uint64_t budget, uint64_t used) {
    TcRecords r = {(const void *)(uintptr_t)tisa_drive, desc(s, decode), (TcDrive **)(void *)W(&s->table), nh,
                   &W(&s->ctl)[C_OP], &W(&s->ctl)[C_END], budget, used, 0};
    uint64_t status = tisa_records(&r);
    return (RecResult){status, r.count, r.used};
}

/* ---- steps ------------------------------------------------------------------------- */

static uint64_t *step(Side *s, int p, size_t i) { return W(&s->plan[p]) + STEPW * i; }

static void put(uint64_t *st, unsigned leaf, const unsigned regions[9], unsigned a0, unsigned a1,
                unsigned v1, unsigned dst) {
    memset(st, 0, 8 * STEPW);
    st[0] = leaf;
    for (unsigned r = 0; r < 9; ++r) st[1 + r] = regions[r];
    st[10] = a0; st[11] = a1;
    st[12] = v1;
    for (unsigned k = 1; k < 5; ++k) st[12 + k] = next() % NCTL;
    st[17] = dst;
}
static const unsigned R_I16[9] = {B_I16, B_I16 + 2, B_I16 + 4, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY};
static const unsigned R_FNV[9] = {B_INPUT, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY};
static const unsigned R_LEB[9] = {B_INPUT, B_LEBOUT, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY};
static const unsigned R_NAME[9] = {B_INPUT, B_NAME, B_NAME + 2, B_NAME + 4, B_NAME + 6, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY};
static const unsigned R_NONE[9] = {B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY, B_EMPTY};

static void step_intern16(uint64_t *st, unsigned a0, unsigned a1, unsigned dst) { put(st, L_INTERN16, R_I16, a0, a1, next() % NCTL, dst); }
static void step_fnv(uint64_t *st, unsigned off, unsigned len, unsigned h0, unsigned dst) { put(st, L_FNV, R_FNV, off, len, h0, dst); }
static void step_leb(uint64_t *st, unsigned off, unsigned dst) { put(st, L_LEB128, R_LEB, off, next() % NCTL, next() % NCTL, dst); }
static void step_name(uint64_t *st, unsigned off, unsigned len, unsigned hash, unsigned dst) { put(st, L_NAME, R_NAME, off, len, hash, dst); }
static void step_meter(uint64_t *st, unsigned dst) { put(st, L_METER, R_NONE, next() % NCTL, next() % NCTL, next() % NCTL, dst); }

/* A random step over the five leaves, its operands among control words 0..11. */
static void step_random(uint64_t *st, unsigned dst) {
    unsigned a0 = (unsigned)(next() % 12), a1 = (unsigned)(next() % 12), v = (unsigned)(next() % 12);
    switch (next() % 5) {
    case 0: step_intern16(st, a0, a1, dst); break;
    case 1: step_fnv(st, a0, a1, v, dst); break;
    case 2: step_leb(st, a0, dst); break;
    case 3: step_name(st, a0, a1, v, dst); break;
    default: step_meter(st, dst); break;
    }
}

static void fresh_interners(Side *s) {
    memset(s->i16rows.p, 0, s->i16rows.len); memset(s->i16table.p, 0, s->i16table.len);
    memset(s->i16header.p, 0, s->i16header.len);
    memset(s->nrows.p, 0, s->nrows.len); memset(s->narena.p, 0, s->narena.len);
    memset(s->ntable.p, 0, s->ntable.len); memset(s->nheader.p, 0, s->nheader.len);
}

/* ---- checks -------------------------------------------------------------------------- */

static unsigned long checks, failures;
static void check(int ok, const char *what, unsigned long run) {
    ++checks;
    if (!ok) { ++failures; if (failures <= 30) printf("FAIL run %lu: %s\n", run, what); }
}

static uint64_t fnv1a(uint64_t h, const uint8_t *p, size_t n) {
    for (size_t k = 0; k < n; ++k) { h ^= p[k]; h *= 1099511628211ull; }
    return h;
}
static const uint64_t FNV_OFFSET = 14695981039346656037ull;

static Side A, B;

/* One plan on both sides; outcome, end step, receipt and state must agree. */
static Result plan_both(int p, uint64_t budget, uint64_t used, unsigned long run, const char *what,
                        unsigned long outcomes[5]) {
    side_copy(&B, &A);
    TcDrive *d = desc(&A, p);
    d->budget = budget; d->used = used;
    uint64_t status = tisa_drive(d);
    Result rn = {status, (uint64_t)(d->at - d->plan) / STEPW, d->used};
    desc(&B, p)->budget = budget; desc(&B, p)->used = used;
    Result rr = plan_ref(&B, p, budget, used);
    if (outcomes && rr.status < 5) outcomes[rr.status]++;
    check(rn.status == rr.status && rn.at == rr.at && rn.used == rr.used && side_equal(&A, &B) &&
          side_guarded(&A) && side_guarded(&B), what, run);
    return rn;
}

/* The record loop on both sides. */
static RecResult rec_both(int decode, uint64_t nh, uint64_t budget, uint64_t used, unsigned long run,
                          const char *what, unsigned long outcomes[5]) {
    side_copy(&B, &A);
    RecResult rn = rec_native(&A, decode, nh, budget, used);
    RecResult rr = rec_ref(&B, decode, nh, budget, used);
    if (outcomes && rr.status < 5) outcomes[rr.status]++;
    check(rn.status == rr.status && rn.count == rr.count && rn.used == rr.used && side_equal(&A, &B) &&
          side_guarded(&A) && side_guarded(&B), what, run);
    return rn;
}

/* ---- linked bytes ---------------------------------------------------------------------- */

static void *read_file(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); exit(2); }
    fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
    void *b = malloc((size_t)n + 1);
    if (!b || fread(b, 1, (size_t)n, f) != (size_t)n) { perror(path); exit(2); }
    fclose(f);
    *len = (size_t)n;
    return b;
}

static int same_image(const char *name, int leaf, const uint8_t *lo, const uint8_t *hi) {
    char msg[256];
    TcIsaX86 img;
    if (!tisa_x86_emit(&progs[leaf].prog, &img, msg, sizeof msg)) { fprintf(stderr, "emit %s: %s\n", name, msg); exit(2); }
    size_t linked = (size_t)(hi - lo);
    int same = img.len == linked && !memcmp(img.bytes, lo, linked);
    printf("leaf %s: the linked image (%zu bytes) %s the emitted image (%zu bytes)\n",
           name, linked, same ? "equals" : "DIFFERS FROM", img.len);
    tisa_x86_free(&img);
    return same;
}

static int same_bytes(const char *name, const void *fn, const char *path) {
    size_t n;
    uint8_t *b = read_file(path, &n);
    int same = !memcmp(b, fn, n);
    printf("%s: the linked code %s %s (%zu bytes)\n", name, same ? "holds" : "DIFFERS FROM", path, n);
    free(b);
    return same;
}

/* The name plan in plan 0: fnv of the name from the offset basis, then
   intern_name with that hash. */
static void name_plan(Side *s) {
    s->nsteps[0] = 2;
    step_fnv(step(s, 0, 0), C_OFF, C_LEN, C_H0, C_HASH);
    step_name(step(s, 0, 1), C_OFF, C_LEN, C_HASH, C_ID);
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: test_records INTERN16.txt FNV.txt LEB128.txt NAME.txt DRIVER.bin RECORDS.bin [RUNS] [SEED]\n");
        return 2;
    }
    unsigned long runs = argc > 7 ? strtoul(argv[7], NULL, 0) : 20000;
    if (argc > 8) rng = strtoull(argv[8], NULL, 0) | 1;
    if (!cet_profile()) { printf("unsupported profile: user shadow stacks are on\n"); return 2; }
    for (int k = 0; k < L_METER; ++k) {
        TcIsaTextStyle style; P1Error err;
        if (!p1_load_file(argv[1 + k], &progs[k], &style, &err)) { p1_print_error(stderr, argv[1 + k], &err); return 2; }
    }
    {
        P1Error err; char msg[256];
        if (!p1_parse(METER_TEXT, sizeof METER_TEXT - 1, TISA_TEXT_HOL, &progs[L_METER], &err)) {
            fprintf(stderr, "meter: %s at %zu\n", err.message, err.offset); return 2;
        }
        if (!tisa_admit(&progs[L_METER].prog, NULL, msg, sizeof msg)) { fprintf(stderr, "meter: %s\n", msg); return 2; }
        if (!tisa_x86_emit(&progs[L_METER].prog, &meter, msg, sizeof msg) || !tisa_x86_load(&meter, msg, sizeof msg)) {
            fprintf(stderr, "meter: %s\n", msg); return 2;
        }
        printf("leaf meter (test only, no image theorem): %zu bytes emitted at run time\n", meter.len);
    }
    int ok = same_image("intern16", L_INTERN16, tisa_leaf_intern16, tisa_leaf_intern16_end) &
             same_image("fnv", L_FNV, tisa_leaf_fnv, tisa_leaf_fnv_end) &
             same_image("leb128", L_LEB128, tisa_leaf_leb128, tisa_leaf_leb128_end) &
             same_image("intern_name", L_NAME, tisa_leaf_name, tisa_leaf_name_end) &
             same_bytes("tisa_drive", (const void *)(uintptr_t)tisa_drive, argv[5]) &
             same_bytes("tisa_records", (const void *)(uintptr_t)tisa_records, argv[6]);
    if (!ok) return 1;
    side_new(&A); side_new(&B);

    /* ---- the name plan: FNV-1a of the name, then one id per name ---------------- */
    {
        unsigned long refused = 0, fired = 0;
        const char *names[] = {"lambda", "pi", "lambda", "sigma", "pi", "x"};
        uint8_t *in = A.input.p;
        size_t at = 0;
        memset(in, 0, INPUT);
        uint64_t off[6], len[6];
        for (int k = 0; k < 6; ++k) { len[k] = strlen(names[k]); off[k] = at; memcpy(in + at, names[k], len[k]); at += len[k]; }
        fresh_interners(&A);
        name_plan(&A);
        uint64_t ids[6];
        for (int k = 0; k < 6; ++k) {
            uint64_t *c = W(&A.ctl);
            c[C_OFF] = off[k]; c[C_LEN] = len[k]; c[C_H0] = FNV_OFFSET;
            Result r = plan_both(0, 0, 0, (unsigned long)k, "name plan, differential", NULL);
            check(r.status == TISA_OUTCOME_FIRED, "name plan fires", (unsigned long)k);
            check(c[C_HASH] == fnv1a(FNV_OFFSET, in + off[k], len[k]), "name plan: FNV-1a 64 of the name", (unsigned long)k);
            ids[k] = c[C_ID];
            fired += r.status == TISA_OUTCOME_FIRED;
        }
        check(ids[0] == ids[2] && ids[1] == ids[4], "name plan: equal names, equal ids", 0);
        check(ids[0] != ids[1] && ids[0] != ids[3] && ids[1] != ids[3] && ids[5] != ids[0] && ids[5] != ids[1] &&
              ids[5] != ids[3], "name plan: different names, different ids", 0);
        check(W(&A.nheader)[0] == 4, "name plan: four names interned", 0);
        /* A name outside the input: fnv refuses at step 0, nothing is interned. */
        uint64_t *c = W(&A.ctl);
        c[C_OFF] = INPUT - 2; c[C_LEN] = 5;
        uint64_t count0 = W(&A.nheader)[0];
        Result r = plan_both(0, 0, 0, 100, "name plan refused, differential", NULL);
        check(r.status == TISA_OUTCOME_REFUSED && r.at == 0 && c[C_HASH] == 1 && W(&A.nheader)[0] == count0,
              "name plan: REFUSED at fnv for a name outside the input", 100);
        refused += r.status == TISA_OUTCOME_REFUSED;
        /* Random names, inside and outside the input. */
        for (unsigned long run = 1; run <= runs / 4; ++run) {
            for (int k = 0; k < 16; ++k) in[next() % INPUT] = (uint8_t)('a' + next() % 3);
            c[C_OFF] = next() % (INPUT + 8); c[C_LEN] = next() % 6;
            c[C_H0] = next() % 8 == 0 ? next() : FNV_OFFSET;
            uint64_t h = c[C_OFF] + c[C_LEN] <= INPUT ? fnv1a(c[C_H0], in + c[C_OFF], c[C_LEN]) : 1;
            r = plan_both(0, 0, 0, run, "name plan, random", NULL);
            check((r.status == TISA_OUTCOME_REFUSED) == (c[C_OFF] + c[C_LEN] > INPUT), "REFUSED iff outside the input", run);
            if (r.status != TISA_OUTCOME_REFUSED) check(c[C_HASH] == h, "fnv payload is FNV-1a", run);
            refused += r.status == TISA_OUTCOME_REFUSED;
            fired += r.status == TISA_OUTCOME_FIRED;
        }
        printf("name plan: FIRED %lu, REFUSED %lu, %" PRIu64 " names interned\n", fired, refused, W(&A.nheader)[0]);
    }

    /* ---- plans: each outcome ends the plan as drv_sem says ---------------------------------- */
    {
        uint8_t *in = A.input.p;
        uint64_t *c = W(&A.ctl);
        memset(in, 0, INPUT);
        fresh_interners(&A);
        memcpy(in + 10, "abc", 3);
        in[INPUT - 1] = 0x80;                                  /* an integer the input ends inside */
        c[C_OFF] = 10; c[C_LEN] = 3; c[C_H0] = FNV_OFFSET; c[C_POS] = INPUT - 1;
        c[C_HASH] = 0; c[C_OP] = 0xD0D0; c[C_ID] = 0xD1D1;
        uint64_t h = fnv1a(FNV_OFFSET, in + 10, 3);
        /* fnv fires, leb128 refuses, intern_name is not called */
        A.nsteps[0] = 3;
        step_fnv(step(&A, 0, 0), C_OFF, C_LEN, C_H0, C_HASH);
        step_leb(step(&A, 0, 1), C_POS, C_OP);
        step_name(step(&A, 0, 2), C_OFF, C_LEN, C_HASH, C_ID);
        uint64_t names0 = W(&A.nheader)[0];
        Result r = plan_both(0, 10, 4, 2000, "REFUSED mid-plan, differential", NULL);
        printf("plans: %-52s status %" PRIu64 ", at %" PRIu64 ", receipt %" PRIu64 "\n",
               "fnv, leb128 (refuses), intern_name", r.status, r.at, r.used);
        check(r.status == TISA_OUTCOME_REFUSED && r.at == 1 && r.used == 4 && c[C_HASH] == h &&
              c[C_ID] == 0xD1D1 && W(&A.nheader)[0] == names0,
              "REFUSED at step 1 ends the plan; step 2 is not called", 2000);
        /* the receipt above the allowance: INVALID before the first call */
        uint8_t before[8 * NCTL];
        c[C_HASH] = 0; c[C_OP] = 0xD0D0;
        memcpy(before, A.ctl.p, sizeof before);
        r = plan_both(0, 2, 3, 2001, "INVALID before the call, differential", NULL);
        printf("plans: %-52s status %" PRIu64 ", at %" PRIu64 ", receipt %" PRIu64 "\n",
               "the same plan, receipt 3 above the allowance 2", r.status, r.at, r.used);
        check(r.status == TISA_OUTCOME_INVALID_INPUT && r.at == 0 && r.used == 3 &&
              !memcmp(before, A.ctl.p, sizeof before) && W(&A.nheader)[0] == names0,
              "INVALID before the first call; no leaf runs", 2001);
        /* fnv, meter, meter: FUND 2 each */
        A.nsteps[0] = 3;
        step_fnv(step(&A, 0, 0), C_OFF, C_LEN, C_H0, C_HASH);
        step_meter(step(&A, 0, 1), C_ID);
        step_meter(step(&A, 0, 2), C_OP);
        struct { uint64_t budget, used, status, at, receipt, id, op; const char *what; } ex[] = {
            {6, 2, TISA_OUTCOME_FIRED, 3, 6, 7, 7, "fnv, meter, meter: allowance 6, receipt 2"},
            {5, 2, TISA_OUTCOME_EXHAUSTED, 2, 4, 7, 4, "fnv, meter, meter: allowance 5, receipt 2"},
            {3, 2, TISA_OUTCOME_EXHAUSTED, 1, 2, 4, 0xD0D0, "fnv, meter, meter: allowance 3, receipt 2"},
        };
        for (unsigned k = 0; k < sizeof ex / sizeof ex[0]; ++k) {
            c[C_HASH] = 0; c[C_ID] = 0xD1D1; c[C_OP] = 0xD0D0;
            r = plan_both(0, ex[k].budget, ex[k].used, 2010 + k, "EXHAUSTED from a leaf, differential", NULL);
            printf("plans: %-52s status %" PRIu64 ", at %" PRIu64 ", receipt %" PRIu64 "\n",
                   ex[k].what, r.status, r.at, r.used);
            check(r.status == ex[k].status && r.at == ex[k].at && r.used == ex[k].receipt && c[C_HASH] == h &&
                  c[C_ID] == ex[k].id && c[C_OP] == ex[k].op,
                  "a leaf's EXHAUSTED ends the plan; its payload 4 stored, the receipt unchanged", 2010 + k);
        }
        in[INPUT - 1] = 0;
    }

    /* ---- plans: random plans over the five leaves ---------------------------------------------- */
    {
        unsigned long pout[5] = {0};
        for (unsigned long run = 1; run <= runs; ++run) {
            if (run == 1 || next() % 16 == 0) fresh_interners(&A);
            if (next() % 8 == 0) W(&A.i16header)[0] = next() % 70;   /* sometimes at or past intern16's 64 rows */
            uint8_t *in = A.input.p;
            for (int k = 0; k < 8; ++k) in[next() % INPUT] = (uint8_t)(next() % 8 == 0 ? next() : next() % 6);
            uint64_t *c = W(&A.ctl);
            for (unsigned k = 0; k < NCTL; ++k) if (next() % 6 == 0) c[k] = next() % 8 == 0 ? next() : next() % 12;
            A.nsteps[0] = 1 + next() % MAXSTEPS;
            for (size_t i = 0; i < A.nsteps[0]; ++i) step_random(step(&A, 0, i), (unsigned)(next() % 12));
            uint64_t budget = next() % 8, used = next() % 6 == 0 ? budget + 1 + next() % 3 : next() % (budget + 1);
            (void)plan_both(0, budget, used, run, "random plan", pout);
        }
        printf("plans random: %lu plans; reference outcomes FIRED %lu REFUSED %lu UNSUPPORTED %lu INVALID %lu EXHAUSTED %lu\n",
               runs, pout[1], pout[0], pout[2], pout[3], pout[4]);
    }

    /* ---- the record loop: scenarios ------------------------------------------------------- */
    /* Plan 1 decodes: leb128 at offset ctl[POS], the value to ctl[OP].
       Handlers: 0 END (fnv of nothing from ctl[ONE]: 1 to ctl[END]);
       1 intern16 of (ctl[POS], ctl[ONE]), its id to ctl[POS] (the next
       record's offset); 2 the name plan; 3 none; 4 fnv of a range past the
       input (REFUSED). */
    {
        memset(A.input.p, 0, INPUT);
        fresh_interners(&A);
        A.nsteps[1] = 1; step_leb(step(&A, 1, 0), C_POS, C_OP);
        A.nsteps[2] = 1; step_fnv(step(&A, 2, 0), C_ZERO, C_ZERO, C_ONE, C_END);
        A.nsteps[3] = 1; step_intern16(step(&A, 3, 0), C_OFF, C_LEN, C_ID);
        A.nsteps[4] = 2; step_fnv(step(&A, 4, 0), C_OFF, C_LEN, C_H0, C_HASH); step_name(step(&A, 4, 1), C_OFF, C_LEN, C_HASH, C_ID);
        A.nsteps[5] = 1; step_fnv(step(&A, 5, 0), C_POS, C_BIG, C_ONE, C_HASH);
        side_plans(&A);
        uint64_t *t = W(&A.table);
        t[0] = (uint64_t)(uintptr_t)desc(&A, 2); t[1] = (uint64_t)(uintptr_t)desc(&A, 3);
        t[2] = (uint64_t)(uintptr_t)desc(&A, 4); t[3] = 0; t[4] = (uint64_t)(uintptr_t)desc(&A, 5);
        uint64_t *c = W(&A.ctl);
        c[C_ONE] = 1; c[C_ZERO] = 0; c[C_H0] = FNV_OFFSET; c[C_OFF] = 10; c[C_LEN] = 3; c[C_BIG] = INPUT + 1;
        memcpy(A.input.p + 10, "abc", 3);
        /* one key interned first, so new keys get ids from 1 */
        (void)plan_both(3, 0, 0, 999, "a first key, differential", NULL);
        step_intern16(step(&A, 3, 0), C_POS, C_ONE, C_POS);
        struct { uint8_t op; uint64_t pos, status, count; const char *what; } sc[] = {
            {0, 0, TISA_OUTCOME_FIRED, 1, "END at the first record"},
            {3, 0, TISA_OUTCOME_UNSUPPORTED, 0, "a table entry 0: UNSUPPORTED"},
            {7, 0, TISA_OUTCOME_UNSUPPORTED, 0, "an opcode past the table: UNSUPPORTED"},
            {4, 0, TISA_OUTCOME_REFUSED, 0, "the handler refuses: stop mid-record"},
            {0x80, INPUT - 1, TISA_OUTCOME_REFUSED, 0, "the decode refuses: the input ends first"},
        };
        for (unsigned k = 0; k < sizeof sc / sizeof sc[0]; ++k) {
            A.input.p[sc[k].pos] = sc[k].op; c[C_POS] = sc[k].pos; c[C_END] = 0;
            RecResult r = rec_both(1, NH, 100, 0, 1000 + k, sc[k].what, NULL);
            printf("records: %-46s status %" PRIu64 ", count %" PRIu64 ", receipt %" PRIu64 "\n",
                   sc[k].what, r.status, r.count, r.used);
            check(r.status == sc[k].status && r.count == sc[k].count, sc[k].what, 1000 + k);
            A.input.p[sc[k].pos] = 0;
        }
        /* Opcodes 1, 1, 0: two intern16 records, each id the next offset, then END. */
        uint8_t *in = A.input.p;
        in[0] = 1; in[1] = 1; in[2] = 0;
        c[C_POS] = 0; c[C_END] = 0;
        RecResult r = rec_both(1, NH, 100, 0, 1100, "records to END", NULL);
        printf("records: %-46s status %" PRIu64 ", count %" PRIu64 ", receipt %" PRIu64 "\n",
               "opcodes 1, 1, 0: two records, then END", r.status, r.count, r.used);
        check(r.status == TISA_OUTCOME_FIRED && r.count == 3 && r.used == 3 && c[C_POS] == 2, "records to END", 1100);
        /* Fuel: a budget of 2 runs two records of the same stream. */
        c[C_POS] = 0; c[C_END] = 0;
        r = rec_both(1, NH, 2, 0, 1200, "fuel: EXHAUSTED after two records", NULL);
        printf("records: %-46s status %" PRIu64 ", count %" PRIu64 ", receipt %" PRIu64 "\n",
               "the same stream, a budget of 2", r.status, r.count, r.used);
        check(r.status == TISA_OUTCOME_EXHAUSTED && r.count == 2 && r.used == 2, "EXHAUSTED after two records", 1200);
        r = rec_both(1, NH, 5, 7, 1201, "a receipt above the allowance: EXHAUSTED", NULL);
        check(r.status == TISA_OUTCOME_EXHAUSTED && r.count == 0 && r.used == 7, "EXHAUSTED at once", 1201);
    }

    /* ---- the record loop: random record programs ------------------------------------------- */
    unsigned long outcomes[5] = {0};
    for (unsigned long run = 1; run <= runs; ++run) {
        if (run == 1 || next() % 16 == 0) fresh_interners(&A);
        uint8_t *in = A.input.p;
        for (int k = 0; k < 8; ++k) in[next() % INPUT] = (uint8_t)(next() % 8 == 0 ? next() : next() % 6);
        uint64_t *c = W(&A.ctl);
        for (unsigned k = 0; k < NCTL; ++k) if (next() % 6 == 0) c[k] = next() % 8 == 0 ? next() : next() % 12;
        c[C_END] = 0;
        for (int p = 1; p < NPLANS; ++p) {
            A.nsteps[p] = 1 + next() % 3;
            for (size_t i = 0; i < A.nsteps[p]; ++i)
                step_random(step(&A, p, i), next() % 5 == 0 ? C_END : (unsigned)(next() % 12));
        }
        if (next() % 2) { A.nsteps[1] = 1; step_leb(step(&A, 1, 0), C_POS, C_OP); }
        side_plans(&A);
        uint64_t *t = W(&A.table);
        for (int k = 0; k < NH; ++k) t[k] = next() % 5 == 0 ? 0 : (uint64_t)(uintptr_t)desc(&A, 2 + (int)(next() % 4));
        uint64_t nh = next() % (NH + 1), budget = next() % 12, used = next() % 6 == 0 ? budget + next() % 3 : next() % (budget + 1);
        rec_both(1, nh, budget, used, run, "random record program", outcomes);
    }
    printf("records random: %lu programs; reference outcomes FIRED %lu REFUSED %lu UNSUPPORTED %lu INVALID %lu EXHAUSTED %lu\n",
           runs, outcomes[1], outcomes[0], outcomes[2], outcomes[3], outcomes[4]);
    printf("checks %lu, failures %lu\n", checks, failures);
    for (int k = 0; k < NLEAVES; ++k) p1_free(&progs[k]);
    tisa_x86_free(&meter);
    return failures ? 1 : 0;
}
