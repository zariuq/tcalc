/* Native initialization plans: linked driver/image identity, every prefix,
 * unsupported lengths, receipts, payload transport and guarded memory. */
#include "cet_profile.h"
#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
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

_Static_assert(sizeof(uintptr_t) == 8, "64-bit addresses required");
_Static_assert(sizeof(TcDrive) == 64 && offsetof(TcDrive, ctl) == 16 &&
               offsetof(TcDrive, bind) == 24 && offsetof(TcDrive, leaves) == 32 &&
               offsetof(TcDrive, budget) == 40 && offsetof(TcDrive, used) == 48 &&
               offsetof(TcDrive, at) == 56, "driver layout");

uint64_t tisa_drive(TcDrive *descriptor);
extern const uint8_t tisa_leaf_zero_init[], tisa_leaf_zero_init_end[];

enum { NRANGES = 15, BASE_RANGES = 12, NCTL = 32, NBIND = 64, STEPW = 18, GUARD = 64, GB = 0xA5 };
static const unsigned boot_slots[BASE_RANGES] = {4, 10, 14, 20, 26, 32, 50, 16, 22, 28, 34, 36};
static const unsigned entry_slots[NRANGES] = {4, 10, 14, 20, 26, 32, 50, 16, 22, 28, 34, 2, 8, 48, 36};
static uint64_t rng = UINT64_C(0x9E3779B97F4A7C15);
static uint64_t checks, failures, cases, outcomes[5];

static uint64_t next(void) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    return rng;
}

static void require(int condition, const char *reason) {
    checks++;
    if (!condition) {
        failures++;
        if (failures < 12) fprintf(stderr, "case %" PRIu64 ": %s\n", cases, reason);
    }
}

typedef struct { uint8_t *allocation, *data, *original; size_t length; } Area;

static Area area_new(size_t length) {
    Area area = {0};
    size_t allocated = (length + 2 * GUARD + 63) / 64 * 64;
    area.allocation = aligned_alloc(64, allocated);
    area.original = malloc(length ? length : 1);
    if (!area.allocation || !area.original) { perror("allocation"); exit(2); }
    area.data = area.allocation + GUARD;
    area.length = length;
    memset(area.allocation, GB, allocated);
    for (size_t i = 0; i < length; i++) area.data[i] = (uint8_t)next() | 1;
    memcpy(area.original, area.data, length);
    return area;
}

static void area_save(Area *area) { memcpy(area->original, area->data, area->length); }

static void area_guards(const Area *area) {
    for (size_t i = 0; i < GUARD; i++) {
        require(area->allocation[i] == GB, "leading guard");
        require(area->data[area->length + i] == GB, "trailing guard");
    }
}

static void area_free(Area *area) { free(area->original); free(area->allocation); }

static int exact_image(const char *path, const uint8_t *address, size_t expected) {
    FILE *file = fopen(path, "rb");
    if (!file) return 0;
    size_t i = 0;
    int byte, same = 1;
    while ((byte = fgetc(file)) != EOF) {
        if (i >= expected || address[i] != (uint8_t)byte) same = 0;
        i++;
    }
    same = same && i == expected && !ferror(file);
    fclose(file);
    return same;
}

static void trial(unsigned nsteps, unsigned bad, int invalid_receipt, unsigned round,
                  int mutation, int parent_views) {
    const unsigned nranges = parent_views >= 4 ? NRANGES : BASE_RANGES;
    const unsigned *slots = parent_views >= 4 ? entry_slots : boot_slots;
    Area ranges[NRANGES], control = area_new(8 * NCTL), bindings = area_new(8 * NBIND);
    Area boot = {0};
    size_t clear_bytes[NRANGES], expected_payload[NRANGES];
    Area plan = area_new(8 * STEPW * nranges), leaves = area_new(8);
    uint64_t *cw = (uint64_t *)control.data, *bw = (uint64_t *)bindings.data;
    uint64_t *steps = (uint64_t *)plan.data, *leaf = (uint64_t *)leaves.data;
    memset(bindings.data, 0, bindings.length);
    memset(plan.data, 0, plan.length);
    for (unsigned i = 0; i < nranges; i++) {
        size_t length = i < 6 ? 8 : i == 6 ? 16 : 8 * (next() % 65);
        if (i == bad && i < nsteps) length++;
        if (parent_views >= 2 && i < 7) length += 8 * (next() % 65);
        if (parent_views) length += (round + i) % 8;
        ranges[i] = area_new(length);
        clear_bytes[i] = parent_views ? length - length % 8 : length;
        if (parent_views >= 2 && i < 7) clear_bytes[i] = i < 6 ? 8 : 16;
        expected_payload[i] = clear_bytes[i] / 8;
        bw[slots[i]] = (uint64_t)(uintptr_t)ranges[i].data;
        bw[slots[i] + 1] = clear_bytes[i];
        steps[i * STEPW + 1] = slots[i];
    }
    if (parent_views) {
        boot = area_new(9);
        memcpy(boot.data, "=Aboolfun", 9);
        area_save(&boot);
        bw[62] = (uint64_t)(uintptr_t)boot.data;
        bw[63] = boot.length;
    }
    if ((parent_views == 3 || parent_views == 5) && nsteps > 7) {
        bad = 7 + round % (nsteps - 7);
        /* The count exceeds the loop cap. This aligned range must never be
         * accessed; its length is metadata, not a large allocation. */
        bw[slots[bad]] = UINT64_C(0x100000000000) + (uint64_t)bad * UINT64_C(0x1000000000);
        bw[slots[bad] + 1] = UINT64_C(34359738368);
        /* The implicit loop-cap failure carries its status as payload. */
        expected_payload[bad] = 2;
    }
    if (mutation == 1 && nsteps) steps[1] = 0;
    if (mutation == 2 && nsteps && bw[slots[0] + 1] >= 8) bw[slots[0] + 1] -= 8;
    if (mutation == 3 && parent_views && nsteps) bw[slots[0]] = bw[62];
    if (mutation == 4 && parent_views >= 4 && nsteps > 11) steps[11 * STEPW + 1] = 34;
    if (mutation == 5 && parent_views >= 4 && nsteps > 14) steps[14 * STEPW + 1] = 34;
    leaf[0] = (uint64_t)(uintptr_t)tisa_leaf_zero_init;
    area_save(&control); area_save(&bindings); area_save(&plan); area_save(&leaves);
    uint64_t budget = round % 4 == 0 ? 0 : round % 4 == 1 ? UINT64_MAX : next();
    uint64_t used = round % 3 == 0 ? budget : budget / 2;
    if (invalid_receipt) { budget = 0; used = 1; }
    TcDrive descriptor = {steps, steps + nsteps * STEPW, cw, bw, leaf, budget, used, NULL};
    uint64_t outcome = tisa_drive(&descriptor);
    unsigned done = invalid_receipt && nsteps ? 0 : bad < nsteps ? bad : nsteps;
    uint64_t wanted = invalid_receipt && nsteps ? 3 : done < nsteps ? 2 : 1;
    cases++;
    if (outcome < 5) outcomes[outcome]++;
    require(outcome == wanted, "outcome");
    require(descriptor.used == used, "receipt changed");
    require(descriptor.budget == budget, "allowance changed");
    require(descriptor.at == steps + done * STEPW, "stopping step");
    require(descriptor.plan == steps && descriptor.plan_end == steps + nsteps * STEPW &&
            descriptor.ctl == cw && descriptor.bind == bw && descriptor.leaves == leaf, "descriptor frame");
    for (unsigned i = 0; i < nranges; i++) {
        for (size_t j = 0; j < ranges[i].length; j++)
            require(ranges[i].data[j] == (i < done && j < clear_bytes[i]
                                         ? 0 : ranges[i].original[j]), "range/prefix contents");
        area_guards(&ranges[i]);
        area_free(&ranges[i]);
    }
    uint64_t payload = ((const uint64_t *)control.original)[0];
    if (nsteps && wanted != 3) {
        unsigned last = wanted == 1 ? nsteps - 1 : done;
        payload = expected_payload[last];
    }
    require(cw[0] == payload, "payload transport");
    for (unsigned i = 1; i < NCTL; i++)
        require(cw[i] == ((const uint64_t *)control.original)[i], "control-word frame");
    require(memcmp(plan.data, plan.original, plan.length) == 0, "plan was written");
    require(memcmp(bindings.data, bindings.original, bindings.length) == 0, "bindings were written");
    require(memcmp(leaves.data, leaves.original, leaves.length) == 0, "leaf table was written");
    if (parent_views) {
        require(memcmp(boot.data, boot.original, boot.length) == 0, "boot constant was written");
        area_guards(&boot);
        area_free(&boot);
    }
    area_guards(&control); area_guards(&bindings); area_guards(&plan); area_guards(&leaves);
    area_free(&control); area_free(&bindings); area_free(&plan); area_free(&leaves);
}

int main(int argc, char **argv) {
    if (argc < 3 || argc > 5) {
        fprintf(stderr, "usage: test_zero_init DRIVER.bin ZERO.bin [--boot-views|--boot-minimal|--boot-unsupported|--entry-views|--entry-unsupported] [--mutate-binding|--shorten-range|--alias-boot-constant|--omit-hash-clear|--omit-flags-clear]\n");
        return 2;
    }
    int mutation = 0, parent_views = 0;
    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i], "--boot-views") && !parent_views) parent_views = 1;
        else if (!strcmp(argv[i], "--boot-minimal") && !parent_views) parent_views = 2;
        else if (!strcmp(argv[i], "--boot-unsupported") && !parent_views) parent_views = 3;
        else if (!strcmp(argv[i], "--entry-views") && !parent_views) parent_views = 4;
        else if (!strcmp(argv[i], "--entry-unsupported") && !parent_views) parent_views = 5;
        else if (!strcmp(argv[i], "--mutate-binding") && !mutation) mutation = 1;
        else if (!strcmp(argv[i], "--shorten-range") && !mutation) mutation = 2;
        else if (!strcmp(argv[i], "--alias-boot-constant") && !mutation) mutation = 3;
        else if (!strcmp(argv[i], "--omit-hash-clear") && !mutation) mutation = 4;
        else if (!strcmp(argv[i], "--omit-flags-clear") && !mutation) mutation = 5;
        else return 2;
    }
    if (mutation == 3 && !parent_views) return 2;
    if (mutation >= 4 && parent_views < 4) return 2;
    if (!cet_profile()) return 2;
    size_t leaf_length = (size_t)((uintptr_t)tisa_leaf_zero_init_end - (uintptr_t)tisa_leaf_zero_init);
    if (leaf_length != 310 ||
        !exact_image(argv[1], (const uint8_t *)(uintptr_t)tisa_drive, 522) ||
        !exact_image(argv[2], tisa_leaf_zero_init, 310)) {
        fprintf(stderr, "linked bytes differ from the supplied images\n");
        return 2;
    }
    const unsigned nranges = parent_views >= 4 ? NRANGES : BASE_RANGES;
    for (unsigned round = 0; round < 32; round++) {
        for (unsigned n = 0; n <= nranges; n++) {
            trial(n, nranges, 0, round, mutation, parent_views);
            if (!parent_views) trial(n, n ? n / 2 : nranges, 0, round, mutation, 0);
            trial(n, nranges, 1, round, mutation, parent_views);
        }
    }
    printf("zero_init%s: %" PRIu64 " cases, %" PRIu64 " checks, %" PRIu64 " failures; "
           "FIRED %" PRIu64 ", UNSUPPORTED %" PRIu64 ", INVALID %" PRIu64 "\n",
           parent_views == 5 ? " entry unsupported" : parent_views == 4 ? " entry views" :
           parent_views == 3 ? " boot unsupported" : parent_views == 2 ? " boot minimal" : parent_views ? " boot views" : "",
           cases, checks, failures,
           outcomes[1], outcomes[2], outcomes[3]);
    return failures ? 1 : 0;
}
