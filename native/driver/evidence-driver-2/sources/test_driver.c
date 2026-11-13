/*
 * test_driver.c -- the plan driver (driver.S) linked with intern16's proved
 * image, run natively and compared with the plan run by the p1 reference
 * evaluator (tisa_ref.c), step by step.
 *
 *   test_driver PROG.txt DRIVER.bin [RUNS] [SEED]
 *
 * PROG.txt is intern16's program text (intern16b_prog.txt). DRIVER.bin is
 * the driver's .text as assembled (the bytes drv_mc in driver.ml are read
 * from the same object). Before any run, the linked bytes are checked:
 * tisa_drive must hold DRIVER.bin exactly, and tisa_leaf_intern16 must hold
 * the image tisa_x86_emit produces from PROG.txt (and whose bytes are the
 * proved record intern16b.hol, from which the image object is generated).
 *
 * The reference side runs each step as the plan semantics says (driver.ml,
 * drv_sem): the child frame from the step's bindings, status and ret_val 0,
 * the allowance and receipt, args and v1..v5 from control words; a receipt
 * above the allowance ends the plan with INVALID_INPUT before the call;
 * tisa_run; the payload to the step's control word; the receipt carried; the
 * first outcome other than FIRED ends the plan. Both sides start from equal
 * copies of one state; every outcome, receipt, end step, control word and
 * region byte must agree, and guard bytes around every area must survive.
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

uint64_t tisa_drive(TcDrive *d);
extern const uint8_t tisa_leaf_intern16[];
extern const uint8_t tisa_leaf_intern16_end[];

enum { STEPW = 18, NCTL = 32, MAXSTEPS = 8, GUARD = 64, GB = 0xA5 };

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

/* One side's state: the control words, three interners (rows, table,
   header), the bindings. Interner 0's header is control word 20, interner
   2's is control word 21 (a leaf then writes control words); interner 1's
   header is its own area. */
typedef struct {
    Area ctl, rows[3], table[3], header1, plan, bind, leaves;
} Side;

static const size_t ROWS[3] = {512, 64, 4}, SLOTS[3] = {1024, 128, 4};

static void side_new(Side *s) {
    area_new(&s->ctl, 8 * NCTL);
    for (int k = 0; k < 3; ++k) { area_new(&s->rows[k], 16 * ROWS[k]); area_new(&s->table[k], 8 * SLOTS[k]); }
    area_new(&s->header1, 8);
    area_new(&s->plan, 8 * STEPW * MAXSTEPS);
    area_new(&s->bind, 8 * 20);
    area_new(&s->leaves, 8);
}

static void side_copy(Side *d, const Side *s) {
    memcpy(d->ctl.p, s->ctl.p, s->ctl.len);
    for (int k = 0; k < 3; ++k) {
        memcpy(d->rows[k].p, s->rows[k].p, s->rows[k].len);
        memcpy(d->table[k].p, s->table[k].p, s->table[k].len);
    }
    memcpy(d->header1.p, s->header1.p, 8);
    memcpy(d->plan.p, s->plan.p, s->plan.len);
}

static uint64_t *W(Area *a) { return (uint64_t *)a->p; }

/* Binding words: interner k's (rows, table, header) at word 6k; word 18 is
   the empty region (0, 0) for the slots intern16 does not declare. */
static void side_bind(Side *s) {
    uint64_t *b = W(&s->bind);
    for (int k = 0; k < 3; ++k) {
        b[6 * k + 0] = (uint64_t)(uintptr_t)s->rows[k].p;  b[6 * k + 1] = s->rows[k].len;
        b[6 * k + 2] = (uint64_t)(uintptr_t)s->table[k].p; b[6 * k + 3] = s->table[k].len;
        uint64_t *h = k == 0 ? &W(&s->ctl)[20] : k == 1 ? W(&s->header1) : &W(&s->ctl)[21];
        b[6 * k + 4] = (uint64_t)(uintptr_t)h;              b[6 * k + 5] = 8;
    }
    b[18] = 0; b[19] = 0;
    W(&s->leaves)[0] = (uint64_t)(uintptr_t)tisa_leaf_intern16;
}

static int side_guarded(const Side *s) {
    int ok = area_guarded(&s->ctl) && area_guarded(&s->header1) && area_guarded(&s->plan) &&
             area_guarded(&s->bind) && area_guarded(&s->leaves);
    for (int k = 0; k < 3; ++k) ok = ok && area_guarded(&s->rows[k]) && area_guarded(&s->table[k]);
    return ok;
}

static int side_equal(Side *a, Side *b) {
    if (memcmp(a->ctl.p, b->ctl.p, a->ctl.len) || memcmp(a->header1.p, b->header1.p, 8)) return 0;
    for (int k = 0; k < 3; ++k)
        if (memcmp(a->rows[k].p, b->rows[k].p, a->rows[k].len) ||
            memcmp(a->table[k].p, b->table[k].p, a->table[k].len)) return 0;
    return 1;
}

/* ---- the plan, by the reference evaluator ------------------------------------ */

typedef struct { uint64_t status, at, used; } Result;

static Result reference(const TcIsaProgram *prog, Side *s, size_t nsteps, uint64_t budget, uint64_t used) {
    const uint64_t *plan = W(&s->plan), *bind = W(&s->bind);
    uint64_t *ctl = W(&s->ctl);
    for (size_t i = 0; i < nsteps; ++i) {
        const uint64_t *st = plan + STEPW * i;
        if (used > budget) return (Result){TISA_OUTCOME_INVALID_INPUT, i, used};
        TcIsaRuntimeFrame f;
        uint64_t *fw = (uint64_t *)&f;
        for (unsigned r = 0; r < 9; ++r) { fw[2 * r] = bind[st[1 + r]]; fw[2 * r + 1] = bind[st[1 + r] + 1]; }
        f.status = 0; f.ret_val = 0; f.fuel_budget = budget; f.fuel_used = used;
        f.arg0 = ctl[st[10]]; f.arg1 = ctl[st[11]];
        uint64_t regs[TISA_NUM_VREGS] = {0};
        regs[0] = (uint64_t)(uintptr_t)&f;
        for (unsigned k = 1; k <= 5; ++k) regs[k] = ctl[st[11 + k]];
        (void)tisa_run(prog, &f, regs);
        ctl[st[17]] = f.ret_val;
        used = f.fuel_used;
        if (f.status != TISA_OUTCOME_FIRED) return (Result){f.status, i, used};
    }
    return (Result){TISA_OUTCOME_FIRED, nsteps, used};
}

static Result native(Side *s, size_t nsteps, uint64_t budget, uint64_t used) {
    TcDrive d = {W(&s->plan), W(&s->plan) + STEPW * nsteps, W(&s->ctl), W(&s->bind), W(&s->leaves),
                 budget, used, NULL};
    uint64_t status = tisa_drive(&d);
    return (Result){status, (uint64_t)(d.at - W(&s->plan)) / STEPW, d.used};
}

/* ---- plans -------------------------------------------------------------------- */

static void put_step(uint64_t *st, unsigned interner, unsigned a0, unsigned a1, unsigned dst) {
    memset(st, 0, 8 * STEPW);
    st[0] = 0;                                                /* intern16 */
    for (unsigned r = 0; r < 9; ++r) st[1 + r] = r < 3 ? 6 * interner + 2 * r : 18;
    st[10] = a0; st[11] = a1;
    for (unsigned k = 0; k < 5; ++k) st[12 + k] = next() % NCTL;
    st[17] = dst;
}

static void fill_interner(Side *s, unsigned k, int junk) {
    memset(s->rows[k].p, 0, s->rows[k].len);
    memset(s->table[k].p, 0, s->table[k].len);
    uint64_t *h = k == 0 ? &W(&s->ctl)[20] : k == 1 ? W(&s->header1) : &W(&s->ctl)[21];
    *h = 0;
    if (!junk) return;
    uint64_t *rw = W(&s->rows[k]), *tw = W(&s->table[k]);
    for (size_t i = 0; i < 2 * ROWS[k]; ++i) rw[i] = next() % 4;
    for (size_t i = 0; i < SLOTS[k]; ++i) { uint64_t r = next() % 5; tw[i] = r == 0 ? 0 : r == 1 ? next() : 1 + next() % (ROWS[k] + 2); }
    *h = next() % (ROWS[k] + 3);                               /* sometimes above capacity */
}

static unsigned long checks, failures;
static void check(int ok, const char *what, unsigned long run) {
    ++checks;
    if (!ok) { ++failures; if (failures <= 20) printf("FAIL run %lu: %s\n", run, what); }
}

static void compare(const TcIsaProgram *prog, Side *a, Side *b, size_t nsteps, uint64_t budget,
                    uint64_t used, unsigned long run, unsigned long outcomes[5]) {
    side_copy(b, a);
    Result rn = native(a, nsteps, budget, used);
    Result rr = reference(prog, b, nsteps, budget, used);
    if (rr.status < 5) outcomes[rr.status]++;
    check(rn.status == rr.status, "outcome", run);
    check(rn.at == rr.at, "end step", run);
    check(rn.used == rr.used, "receipt", run);
    check(side_equal(a, b), "control words and regions", run);
    check(side_guarded(a) && side_guarded(b), "guard bytes", run);
}

/* ---- linked bytes ----------------------------------------------------------- */

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

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: test_driver PROG.txt DRIVER.bin [RUNS] [SEED]\n"); return 2; }
    unsigned long runs = argc > 3 ? strtoul(argv[3], NULL, 0) : 20000;
    if (argc > 4) rng = strtoull(argv[4], NULL, 0) | 1;
    if (!cet_profile()) { printf("unsupported profile: user shadow stacks are on\n"); return 2; }

    P1Program p; TcIsaTextStyle style; P1Error err;
    if (!p1_load_file(argv[1], &p, &style, &err)) { p1_print_error(stderr, argv[1], &err); return 2; }
    char msg[256];
    TcIsaX86 img;
    if (!tisa_x86_emit(&p.prog, &img, msg, sizeof msg)) { fprintf(stderr, "emit: %s\n", msg); return 2; }
    size_t linked = (size_t)(tisa_leaf_intern16_end - tisa_leaf_intern16);
    int leaf_same = img.len == linked && !memcmp(img.bytes, tisa_leaf_intern16, linked);
    printf("leaf: the linked intern16 image (%zu bytes) %s the emitted image (%zu bytes)\n",
           linked, leaf_same ? "equals" : "DIFFERS FROM", img.len);
    size_t dlen;
    uint8_t *dbytes = read_file(argv[2], &dlen);
    int drv_same = !memcmp(dbytes, (const void *)(uintptr_t)tisa_drive, dlen);
    printf("driver: the linked tisa_drive %s %s (%zu bytes)\n", drv_same ? "holds" : "DIFFERS FROM", argv[2], dlen);
    if (!leaf_same || !drv_same) return 1;

    Side a, b;
    side_new(&a); side_new(&b);
    side_bind(&a); side_bind(&b);
    unsigned long outcomes[5] = {0};

    /* The composition: two keys interned with one image, in interner 1. */
    {
        fill_interner(&a, 1, 0);
        uint64_t *c = W(&a.ctl);
        c[0] = 7919; c[1] = 3; c[2] = 104729; c[3] = 1;
        put_step(W(&a.plan), 1, 0, 1, 5);
        put_step(W(&a.plan) + STEPW, 1, 2, 3, 6);
        side_copy(&b, &a);
        Result rn = native(&a, 2, 100, 0), rr = reference(&p.prog, &b, 2, 100, 0);
        uint64_t *rows = W(&a.rows[1]);
        printf("composition: status %" PRIu64 " (reference %" PRIu64 "), ids %" PRIu64 " %" PRIu64
               ", count %" PRIu64 ", rows (%" PRIu64 ",%" PRIu64 ") (%" PRIu64 ",%" PRIu64 ")\n",
               rn.status, rr.status, W(&a.ctl)[5], W(&a.ctl)[6], W(&a.header1)[0],
               rows[0], rows[1], rows[2], rows[3]);
        check(rn.status == TISA_OUTCOME_FIRED && rr.status == TISA_OUTCOME_FIRED, "composition fired", 0);
        check(W(&a.ctl)[5] == 0 && W(&a.ctl)[6] == 1 && W(&a.header1)[0] == 2, "composition ids", 0);
        check(rows[0] == 7919 && rows[1] == 3 && rows[2] == 104729 && rows[3] == 1, "composition rows", 0);
        check(side_equal(&a, &b) && rn.at == rr.at && rn.used == rr.used, "composition differential", 0);
        /* the same two keys again: the same ids, nothing appended */
        side_copy(&b, &a);
        rn = native(&a, 2, 100, 0); rr = reference(&p.prog, &b, 2, 100, 0);
        check(rn.status == TISA_OUTCOME_FIRED && W(&a.ctl)[5] == 0 && W(&a.ctl)[6] == 1 &&
              W(&a.header1)[0] == 2 && side_equal(&a, &b), "composition idempotent", 0);
        /* one key in two interners: two images of one key, each canonical */
        fill_interner(&a, 0, 0); fill_interner(&a, 2, 0);
        c[0] = 42; c[1] = 43;
        put_step(W(&a.plan), 0, 0, 1, 7);
        put_step(W(&a.plan) + STEPW, 2, 0, 1, 8);
        side_copy(&b, &a);
        rn = native(&a, 2, 100, 0); rr = reference(&p.prog, &b, 2, 100, 0);
        check(rn.status == TISA_OUTCOME_FIRED && W(&a.ctl)[7] == 0 && W(&a.ctl)[8] == 0 &&
              W(&a.ctl)[20] == 1 && W(&a.ctl)[21] == 1 && side_equal(&a, &b), "two interners", 0);
    }

    /* Random plans over the three interners. */
    for (unsigned long run = 1; run <= runs; ++run) {
        int fresh = next() % 8 == 0;
        if (run == 1 || fresh)
            for (unsigned k = 0; k < 3; ++k) fill_interner(&a, k, next() % 3 == 0);
        uint64_t *c = W(&a.ctl);
        for (unsigned k = 0; k < 20; ++k) if (next() % 4 == 0) c[k] = next() % 6;
        size_t nsteps = 1 + next() % 6;
        for (size_t i = 0; i < nsteps; ++i)
            put_step(W(&a.plan) + STEPW * i, next() % 3, next() % 20, next() % 20,
                     next() % 8 == 0 ? 20 + next() % 2 : next() % 20);
        uint64_t budget = next() % 4, used = next() % 4 == 0 ? budget + 1 + next() % 3 : next() % (budget + 1);
        compare(&p.prog, &a, &b, nsteps, budget, used, run, outcomes);
    }
    printf("random: %lu plans; reference outcomes FIRED %lu REFUSED %lu UNSUPPORTED %lu INVALID %lu EXHAUSTED %lu\n",
           runs, outcomes[1], outcomes[0], outcomes[2], outcomes[3], outcomes[4]);
    printf("checks %lu, failures %lu\n", checks, failures);
    tisa_x86_free(&img);
    p1_free(&p);
    return failures ? 1 : 0;
}
