/* Test-only execution of MeTTa-compiled steps through the proved images. */
#include "native_abi.h"
#include "cet_profile.h"
#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef struct {
    const uint64_t *plan, *plan_end;
    uint64_t *ctl;
    const uint64_t *bind, *leaves;
    uint64_t budget, used;
    const uint64_t *at;
} Drive;

typedef struct {
    uint64_t step[TISA_ABI_StepWords];
    unsigned is_call, marker_index;
    uint64_t target;
} CompiledCase;

_Static_assert(sizeof(Drive) == TISA_ABI_DriveWords * TISA_ABI_WordBytes, "descriptor size");
_Static_assert(offsetof(Drive, used) == TISA_ABI_DriveDescriptor_used_OFFSET, "receipt offset");
_Static_assert(offsetof(Drive, at) == TISA_ABI_DriveDescriptor_at_OFFSET, "stopping step offset");

extern uint64_t tisa_drive(Drive *descriptor);
extern const uint8_t procedure_call_image[], relw_image[];

#include "compiled_cases.h"

static uint64_t seed = UINT64_C(0x9E3779B97F4A7C15);
static uint64_t next(void) {
    seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
    return seed;
}

int main(void) {
    if (!cet_profile()) return 2;
    uint64_t runs = 0, failures = 0;
    const uint64_t edges[] = {0, 1, UINT64_C(1) << 32, UINT64_C(1) << 63, UINT64_MAX};
    const uint64_t guard = UINT64_C(0xA55AC33CF00F9669);
    for (unsigned c = 0; c < sizeof(compiled_cases) / sizeof(*compiled_cases); ++c) {
        const CompiledCase *test = compiled_cases + c;
        for (unsigned trial = 0; trial < 64; ++trial) {
            uint64_t ctl[32], before[32], request[TISA_ABI_CallRequestWords];
            uint64_t guarded[TISA_ABI_CallRequestWords + 2];
            uint64_t bindings[42] = {0}, leaves[2];
            for (unsigned j = 0; j < 32; ++j) ctl[j] = next();
            ctl[TISA_ABI_CoreControls_policy] = trial % 3;
            for (unsigned j = 0; j < TISA_ABI_CallArgumentCount; ++j) {
                ctl[8 + j] = trial < 5 ? edges[(trial + j) % 5] : next();
            }
            ctl[10] = trial % 8;
            memcpy(request, ctl + 8, TISA_ABI_CallArgumentCount * sizeof(*ctl));
            request[TISA_ABI_CallRequest_target] = test->target;
            for (unsigned j = 0; j < TISA_ABI_CallRequestWords + 2; ++j) guarded[j] = guard;
            bindings[18] = (uint64_t)(uintptr_t)(guarded + 1);
            bindings[19] = TISA_ABI_CallRequestBytes;
            for (unsigned pid = 0; pid < 10; ++pid) bindings[23 + 2 * pid] = pid;
            leaves[test->marker_index] = (uint64_t)(uintptr_t)procedure_call_image;
            leaves[1 - test->marker_index] = (uint64_t)(uintptr_t)relw_image;
            memcpy(before, ctl, sizeof ctl);
            uint64_t budget = trial < 5 ? edges[trial] : next();
            uint64_t used = trial % 2 ? budget : budget / 2;
            Drive d = {test->step, test->step + TISA_ABI_StepWords, ctl, bindings, leaves,
                       budget, used, 0};
            uint64_t relation = before[8] < before[9] ? 1 : before[8] == before[9] ? 2 : 4;
            uint64_t fired = (before[10] & relation) != 0;
            uint64_t expected = test->is_call ? 2 : fired;
            uint64_t payload = test->is_call || !fired ? 0 : before[8];
            uint64_t result = tisa_drive(&d);
            int ok = result == expected && d.used == used;
            ok = ok && d.at == test->step + (expected == 1 ? TISA_ABI_StepWords : 0);
            ok = ok && guarded[0] == guard && guarded[TISA_ABI_CallRequestWords + 1] == guard;
            for (unsigned j = 0; j < TISA_ABI_CallRequestWords; ++j)
                ok = ok && guarded[1 + j] == (test->is_call ? request[j] : guard);
            for (unsigned j = 0; j < 32; ++j)
                ok = ok && ctl[j] == (j == test->step[TISA_ABI_DriveStep_dst] ? payload : before[j]);
            if (!ok && ++failures <= 4)
                fprintf(stderr, "compiled case %u trial %u: outcome %" PRIu64 ", expected %" PRIu64 "\n",
                        c, trial, result, expected);
            ++runs;
        }
    }
    printf("compiled steps: %" PRIu64 " native runs, %" PRIu64 " failures\n", runs, failures);
    return failures ? 1 : 0;
}
