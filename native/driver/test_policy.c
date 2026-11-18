/* Native policy plans: prefix publication, refusal, receipts and frames. */
#include "cet_profile.h"
#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error "The driver profile requires little-endian words"
#endif

typedef struct {
    const uint64_t *plan, *plan_end;
    uint64_t *ctl;
    const uint64_t *bind, *leaves;
    uint64_t budget, used;
    const uint64_t *at;
} TcDrive;
_Static_assert(sizeof(TcDrive) == 64 && offsetof(TcDrive, ctl) == 16 &&
               offsetof(TcDrive, bind) == 24 && offsetof(TcDrive, leaves) == 32 &&
               offsetof(TcDrive, budget) == 40 && offsetof(TcDrive, used) == 48 &&
               offsetof(TcDrive, at) == 56, "driver layout");

uint64_t tisa_drive(TcDrive *descriptor);
extern const uint8_t tisa_leaf_policy[], tisa_leaf_policy_end[];
extern const uint8_t tisa_leaf_policy_copy[], tisa_leaf_policy_copy_end[];

enum { NCTL = 32, NBIND = 58, NLEAF = 21, STEPW = 18, GUARD = 8 };
static uint64_t rng = UINT64_C(0x9E3779B97F4A7C15);
static uint64_t cases, checks, failures;

static uint64_t next(void) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    return rng;
}
static void require(int ok, const char *reason) {
    checks++;
    if (!ok) {
        failures++;
        if (failures < 12) fprintf(stderr, "case %" PRIu64 ": %s\n", cases, reason);
    }
}
static int exact_image(const char *path, const uint8_t *address, size_t length) {
    FILE *f = fopen(path, "rb");
    if (!f) return 0;
    int ok = 1, byte;
    size_t i = 0;
    while ((byte = fgetc(f)) != EOF) {
        if (i >= length || address[i] != (uint8_t)byte) ok = 0;
        i++;
    }
    ok = ok && i == length && !ferror(f);
    fclose(f);
    return ok;
}

static void trial(const uint64_t plan[2 * STEPW], uint64_t old, uint64_t policy,
                  size_t prefix, uint64_t budget, uint64_t used, int mutation) {
    uint64_t control[NCTL + 2 * GUARD], before[NCTL], *cw = control + GUARD;
    uint64_t steps[2 * STEPW], saved_steps[2 * STEPW];
    uint64_t bind[NBIND] = {0}, saved_bind[NBIND];
    uint64_t leaves[NLEAF] = {0}, saved_leaves[NLEAF];
    for (size_t i = 0; i < NCTL + 2 * GUARD; i++) control[i] = next();
    for (size_t i = 0; i <= 6; i++) cw[i] = i;
    cw[7] = old; cw[8] = policy;
    uint64_t guards[2 * GUARD];
    memcpy(guards, control, GUARD * sizeof(uint64_t));
    memcpy(guards + GUARD, cw + NCTL, GUARD * sizeof(uint64_t));
    memcpy(before, cw, sizeof before);
    memcpy(steps, plan, sizeof steps);
    if (mutation == 1) steps[17] = 7;               /* publish the refused payload */
    if (mutation == 2) steps[STEPW + 17] = 24;      /* omit the final publication */
    if (mutation == 3) { steps[0] = 3; steps[10] = 8; } /* copy instead of validate */
    memcpy(saved_steps, steps, sizeof steps);
    for (size_t j = 0; j < NLEAF; j++) leaves[j] = (uint64_t)(uintptr_t)tisa_leaf_policy_copy;
    leaves[20] = (uint64_t)(uintptr_t)tisa_leaf_policy;
    memcpy(saved_bind, bind, sizeof bind);
    memcpy(saved_leaves, leaves, sizeof leaves);
    TcDrive d = {steps, steps + prefix * STEPW, cw, bind, leaves, budget, used, NULL};
    uint64_t status = tisa_drive(&d);
    cases++;
    int called = prefix != 0 && used <= budget;
    uint64_t expected_status = !prefix ? 1 : used > budget ? 3 : policy <= 2 ? 1 : 0;
    uint64_t maximum = old > policy ? old : policy;
    size_t stopped = expected_status == 1 ? prefix : 0;
    require(status == expected_status, "outcome");
    require(d.at == steps + stopped * STEPW, "stopping step");
    require(d.used == used && d.budget == budget, "receipt and allowance");
    require(d.plan == steps && d.plan_end == steps + prefix * STEPW && d.ctl == cw &&
            d.bind == bind && d.leaves == leaves, "descriptor frame");
    for (size_t j = 0; j < NCTL; j++) {
        uint64_t expected = before[j];
        if (called && j == 24) expected = policy <= 2 ? maximum : 0;
        if (called && prefix == 2 && policy <= 2 && j == 7) expected = maximum;
        require(cw[j] == expected, j == 7 ? "policy publication or refusal frame" : "control frame");
    }
    require(!memcmp(control, guards, GUARD * sizeof(uint64_t)) &&
            !memcmp(cw + NCTL, guards + GUARD, GUARD * sizeof(uint64_t)), "control guards");
    require(!memcmp(steps, saved_steps, sizeof steps), "plan read-only");
    require(!memcmp(bind, saved_bind, sizeof bind), "bindings read-only");
    require(!memcmp(leaves, saved_leaves, sizeof leaves), "leaf table read-only");
}

int main(int argc, char **argv) {
    if (argc < 5 || argc > 6) {
        fprintf(stderr, "usage: test_policy DRIVER.bin POLICY.bin COPY.bin PLAN.bin [MUTATION]\n");
        return 2;
    }
    int mutation = 0;
    if (argc == 6) {
        if (!strcmp(argv[5], "--early-commit")) mutation = 1;
        else if (!strcmp(argv[5], "--omit-publication")) mutation = 2;
        else if (!strcmp(argv[5], "--bypass-guard")) mutation = 3;
        else return 2;
    }
    if (!cet_profile()) return 2;
    if (!exact_image(argv[1], (const uint8_t *)(uintptr_t)tisa_drive, 522) ||
        !exact_image(argv[2], tisa_leaf_policy,
                     (size_t)((uintptr_t)tisa_leaf_policy_end - (uintptr_t)tisa_leaf_policy)) ||
        !exact_image(argv[3], tisa_leaf_policy_copy,
                     (size_t)((uintptr_t)tisa_leaf_policy_copy_end - (uintptr_t)tisa_leaf_policy_copy))) {
        fprintf(stderr, "linked bytes differ from proof images\n");
        return 2;
    }
    uint64_t plan[2 * STEPW];
    FILE *file = fopen(argv[4], "rb");
    if (!file) return 2;
    int loaded = fread(plan, sizeof(uint64_t), 2 * STEPW, file) == 2 * STEPW &&
                 fgetc(file) == EOF && !ferror(file);
    fclose(file);
    if (!loaded) return 2;
    const uint64_t old[] = {0, 1, 2, UINT64_C(1) << 32, UINT64_MAX};
    const uint64_t proposed[] = {0, 1, 2, 3, 4, UINT64_C(1) << 63, UINT64_MAX};
    for (size_t i = 0; i < sizeof old / sizeof old[0]; i++)
        for (size_t j = 0; j < sizeof proposed / sizeof proposed[0]; j++)
            for (size_t prefix = 0; prefix <= 2; prefix++) {
                trial(plan, old[i], proposed[j], prefix, 0, 0, mutation);
                trial(plan, old[i], proposed[j], prefix, UINT64_MAX, UINT64_MAX, mutation);
                trial(plan, old[i], proposed[j], prefix, 17, 18, mutation);
            }
    for (size_t i = 0; i < 512; i++)
        for (size_t prefix = 0; prefix <= 2; prefix++) {
            uint64_t value = next();
            trial(plan, value, i % 5, prefix, UINT64_MAX, next(), mutation);
            trial(plan, value, next(), prefix, 9, 9, mutation);
        }
    printf("policy plans: %" PRIu64 " cases, %" PRIu64 " checks, %" PRIu64 " failures\n",
           cases, checks, failures);
    return failures ? 1 : 0;
}
