/* The entry control plan: exact linked images, p1 comparison, dirty inputs,
 * refusals, invalid receipts, payload transport and zeroing order. */
#include "cet_profile.h"
#include "p1_load.h"
#include "tisa_ref.h"
#include "control_init_plan.h"
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    const uint64_t *plan, *plan_end;
    uint64_t *ctl;
    const uint64_t *bind, *leaves;
    uint64_t budget, used;
    const uint64_t *at;
} TcDrive;
_Static_assert(sizeof(uintptr_t) == 8 && sizeof(TcDrive) == 64 &&
               offsetof(TcDrive, ctl) == 16 && offsetof(TcDrive, bind) == 24 &&
               offsetof(TcDrive, leaves) == 32 && offsetof(TcDrive, budget) == 40 &&
               offsetof(TcDrive, used) == 48 && offsetof(TcDrive, at) == 56, "driver layout");
uint64_t tisa_drive(TcDrive *descriptor);
extern const uint8_t tisa_leaf_control_init[], tisa_leaf_control_init_end[];
extern const uint8_t tisa_leaf_control_zero[], tisa_leaf_control_zero_end[];

enum { STEPW = 18, GUARD = 64, GB = 0xA5, TABLE_WORDS = 64 };
typedef struct { uint8_t *allocation, *data, *original; size_t length; } Area;
typedef struct { Area ctl, table, plan, bindings, leaves; } Side;
typedef struct { uint64_t status, at, used; } Result;
static uint64_t rng = UINT64_C(0x9E3779B97F4A7C15), cases, checks, failures, outcomes[5];
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static void require(int ok, const char *what) {
    checks++;
    if (!ok && ++failures < 12) fprintf(stderr, "case %" PRIu64 ": %s\n", cases, what);
}
static Area area_new(size_t length) {
    Area a = {0};
    a.allocation = aligned_alloc(64, (length + 2 * GUARD + 63) / 64 * 64);
    a.original = malloc(length);
    if (!a.allocation || !a.original) { perror("allocation"); exit(2); }
    a.data = a.allocation + GUARD; a.length = length;
    memset(a.allocation, GB, length + 2 * GUARD);
    return a;
}
static void save(Area *a) { memcpy(a->original, a->data, a->length); }
static void guarded(const Area *a) {
    for (size_t i = 0; i < GUARD; i++) {
        require(a->allocation[i] == GB, "leading guard");
        require(a->data[a->length + i] == GB, "trailing guard");
    }
}
static void area_free(Area *a) { free(a->original); free(a->allocation); }
static Side side_new(size_t nctl) {
    return (Side){area_new(8 * nctl), area_new(8 * TABLE_WORDS), area_new(8 * 2 * STEPW),
                  area_new(8 * 4), area_new(8 * 2)};
}
static uint64_t *words(Area *a) { return (uint64_t *)a->data; }
static void side_metadata(Side *s) {
    uint64_t *bw = words(&s->bindings), *leaves = words(&s->leaves);
    bw[0] = (uint64_t)(uintptr_t)s->ctl.data; bw[1] = s->ctl.length;
    bw[2] = (uint64_t)(uintptr_t)s->table.data; bw[3] = s->table.length;
    leaves[0] = (uint64_t)(uintptr_t)tisa_leaf_control_init;
    leaves[1] = (uint64_t)(uintptr_t)tisa_leaf_control_zero;
    save(&s->ctl); save(&s->table); save(&s->plan); save(&s->bindings); save(&s->leaves);
}
static void side_free(Side *s) {
    area_free(&s->ctl); area_free(&s->table); area_free(&s->plan);
    area_free(&s->bindings); area_free(&s->leaves);
}
static void side_guards(Side *s) {
    guarded(&s->ctl); guarded(&s->table); guarded(&s->plan); guarded(&s->bindings); guarded(&s->leaves);
    require(!memcmp(s->plan.data, s->plan.original, s->plan.length), "plan frame");
    require(!memcmp(s->bindings.data, s->bindings.original, s->bindings.length), "binding frame");
    require(!memcmp(s->leaves.data, s->leaves.original, s->leaves.length), "leaf-table frame");
}
static int exact(const char *path, const uint8_t *address, size_t size) {
    FILE *f = fopen(path, "rb");
    if (!f) return 0;
    int ch, ok = 1; size_t n = 0;
    while ((ch = fgetc(f)) != EOF) { if (n >= size || address[n] != (uint8_t)ch) ok = 0; n++; }
    ok = ok && n == size && !ferror(f); fclose(f); return ok;
}
static Result reference(const P1Program *programs, Side *s, unsigned nsteps,
                        uint64_t budget, uint64_t used) {
    uint64_t *ctl = words(&s->ctl), *bw = words(&s->bindings), *steps = words(&s->plan);
    for (unsigned i = 0; i < nsteps; i++) {
        if (used > budget) return (Result){3, i, used};
        const uint64_t *st = steps + STEPW * i;
        TcIsaRuntimeFrame frame = {0};
        uint64_t fw[18];
        for (unsigned r = 0; r < 9; r++) { fw[2*r] = bw[st[1+r]]; fw[2*r+1] = bw[st[1+r]+1]; }
        memcpy(&frame, fw, sizeof fw);
        frame.fuel_budget = budget; frame.fuel_used = used;
        frame.arg0 = ctl[st[10]]; frame.arg1 = ctl[st[11]];
        uint64_t regs[TISA_NUM_VREGS] = {(uint64_t)(uintptr_t)&frame};
        for (unsigned r = 1; r <= 5; r++) regs[r] = ctl[st[11+r]];
        (void)tisa_run(&programs[st[0]].prog, &frame, regs);
        ctl[st[17]] = frame.ret_val; used = frame.fuel_used;
        if (frame.status != 1) return (Result){frame.status, i, used};
    }
    return (Result){1, nsteps, used};
}
static void trial(const P1Program *programs, size_t nctl, uint64_t policy, unsigned mode,
                  unsigned receipt, int mutation) {
    Side a = side_new(nctl), b = side_new(nctl);
    uint64_t *cw = words(&a.ctl), *steps = words(&a.plan);
    for (size_t j = 0; j < nctl; j++) cw[j] = next();
    cw[0] = 4; cw[7] = policy;
    for (size_t j = 0; j < a.table.length; j++) a.table.data[j] = (uint8_t)next() | 1;
    memset(steps, 0, a.plan.length);
    if (mode) memcpy(steps, control_zero_step, sizeof control_zero_step);
    uint64_t *init = steps + (mode ? STEPW : 0);
    memcpy(init, control_init_step, sizeof control_init_step);
    unsigned nsteps = mode + 1;
    if (mutation == 1) init[10] = 0;
    if (mutation == 2) init[17] = 0;
    if (mutation == 3) init[1] = 2;
    if (mutation == 4 && mode) {
        uint64_t tmp[STEPW]; memcpy(tmp, steps, sizeof tmp);
        memcpy(steps, steps + STEPW, sizeof tmp); memcpy(steps + STEPW, tmp, sizeof tmp);
    }
    memcpy(b.ctl.data, a.ctl.data, a.ctl.length);
    memcpy(b.table.data, a.table.data, a.table.length);
    memcpy(b.plan.data, a.plan.data, a.plan.length);
    side_metadata(&a); side_metadata(&b);
    uint64_t budget = receipt == 1 ? UINT64_MAX : receipt == 2 ? 17 : 0;
    uint64_t used = receipt == 1 ? UINT64_MAX : receipt == 2 ? 9 : receipt == 3 ? 1 : 0;
    TcDrive d = {steps, steps + nsteps * STEPW, words(&a.ctl), words(&a.bindings),
                 words(&a.leaves), budget, used, NULL};
    Result native = {tisa_drive(&d), 0, 0};
    native.at = (uint64_t)(d.at - steps) / STEPW; native.used = d.used;
    Result ref = reference(programs, &b, nsteps, budget, used);
    cases++;
    if (native.status < 5) outcomes[native.status]++;
    require(native.status == ref.status && native.at == ref.at && native.used == ref.used, "p1 outcomes");
    require(!memcmp(a.ctl.data, b.ctl.data, a.ctl.length), "p1 control words");
    require(!memcmp(a.table.data, b.table.data, a.table.length), "p1 table bytes");
    uint64_t wanted = receipt == 3 ? 3 : policy <= 2 ? 1 : 0;
    unsigned stopped = receipt == 3 ? 0 : policy <= 2 ? nsteps : mode;
    require(native.status == wanted, "specified outcome");
    require(d.at == steps + stopped * STEPW, "specified cursor");
    require(d.used == used && d.budget == budget, "receipt/allowance");
    require(d.plan == steps && d.plan_end == steps + nsteps * STEPW && d.ctl == words(&a.ctl) &&
            d.bind == words(&a.bindings) && d.leaves == words(&a.leaves), "descriptor frame");
    const uint64_t *before = (const uint64_t *)a.ctl.original;
    for (size_t j = 0; j < nctl; j++) {
        uint64_t expected = before[j];
        if (receipt != 3) {
            if (mode && j == 0) expected = TABLE_WORDS;
            if (policy <= 2 && j < 24)
                expected = j <= 6 ? j : j == 7 ? policy : j == 22 ? UINT64_C(14695981039346656037) : 0;
            if (j == 24) expected = policy <= 2 ? policy : 0;
        }
        require(cw[j] == expected, "specified controls");
    }
    for (size_t j = 0; j < a.table.length; j++)
        require(a.table.data[j] == (mode && receipt != 3 ? 0 : a.table.original[j]), "zeroing prefix/frame");
    side_guards(&a); side_guards(&b); side_free(&a); side_free(&b);
}
int main(int argc, char **argv) {
    if (argc < 6 || argc > 7) {
        fprintf(stderr, "usage: test_control_init DRIVER.bin INIT.bin ZERO.bin INIT.txt ZERO.txt [--wrong-arg|--payload-to-core|--wrong-binding|--reverse-order]\n");
        return 2;
    }
    int mutation = 0;
    if (argc == 7) {
        const char *names[] = {"--wrong-arg", "--payload-to-core", "--wrong-binding", "--reverse-order"};
        for (unsigned i = 0; i < 4; i++) if (!strcmp(argv[6], names[i])) mutation = (int)i + 1;
        if (!mutation) return 2;
    }
    if (!cet_profile()) return 2;
    if ((uintptr_t)tisa_leaf_control_init_end - (uintptr_t)tisa_leaf_control_init != 1543 ||
        (uintptr_t)tisa_leaf_control_zero_end - (uintptr_t)tisa_leaf_control_zero != 310 ||
        !exact(argv[1], (const uint8_t *)(uintptr_t)tisa_drive, 522) ||
        !exact(argv[2], tisa_leaf_control_init, 1543) || !exact(argv[3], tisa_leaf_control_zero, 310)) {
        fprintf(stderr, "linked image mismatch\n"); return 2;
    }
    P1Program programs[2]; TcIsaTextStyle style; P1Error err;
    for (unsigned i = 0; i < 2; i++)
        if (!p1_load_file(argv[4+i], &programs[i], &style, &err)) {
            p1_print_error(stderr, argv[4+i], &err); return 2;
        }
    const size_t sizes[] = {25,32,40,64};
    const uint64_t policies[] = {0,1,2,3,4,255,UINT64_MAX,UINT64_C(0x8000000000000000)};
    for (unsigned sample = 0; sample < 16; sample++)
        for (unsigned n = 0; n < sizeof sizes / sizeof *sizes; n++)
            for (unsigned p = 0; p < sizeof policies / sizeof *policies; p++)
                for (unsigned mode = 0; mode < 2; mode++)
                    for (unsigned receipt = 0; receipt < 4; receipt++)
                        trial(programs, sizes[n], policies[p], mode, receipt, mutation);
    p1_free(&programs[0]); p1_free(&programs[1]);
    printf("control_init driver: %" PRIu64 " cases, %" PRIu64 " checks, %" PRIu64
           " failures; FIRED %" PRIu64 ", REFUSED %" PRIu64 ", INVALID %" PRIu64 "\n",
           cases, checks, failures, outcomes[1], outcomes[0], outcomes[3]);
    return failures ? 1 : 0;
}
