/* Call requests survive the driver's result write, including aliased slots. */
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

_Static_assert(sizeof(Drive) == TISA_ABI_DriveWords * TISA_ABI_WordBytes, "descriptor size");
_Static_assert(offsetof(Drive, used) == TISA_ABI_DriveDescriptor_used_OFFSET, "receipt offset");
_Static_assert(offsetof(Drive, at) == TISA_ABI_DriveDescriptor_at_OFFSET, "stopping step offset");

extern uint64_t tisa_drive(Drive *descriptor);
extern const uint8_t procedure_call_image[], procedure_call_image_end[];

static uint64_t seed = UINT64_C(0x9E3779B97F4A7C15);
static uint64_t next(void) {
    seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
    return seed;
}

int main(void) {
    if (!cet_profile()) return 2;
    uint64_t failures = 0, runs = 0;
    const uint64_t edges[] = {0, 1, 7, UINT64_C(1) << 32, UINT64_C(1) << 63, UINT64_MAX};
    for (unsigned trial = 0; trial < 512; ++trial) {
        for (unsigned dst = 0; dst < TISA_ABI_CallArgumentCount; ++dst) {
            uint64_t ctl[32], before[32], step[TISA_ABI_StepWords] = {0};
            uint64_t guarded[TISA_ABI_CallRequestWords + 2], request[TISA_ABI_CallRequestWords];
            const uint64_t guard = UINT64_C(0xA55AC33CF00F9669);
            for (unsigned j = 0; j < 32; ++j) ctl[j] = next();
            ctl[TISA_ABI_CoreControls_policy] = trial % 3;
            for (unsigned j = 0; j < TISA_ABI_CallArgumentCount; ++j) {
                ctl[8 + j] = trial < sizeof(edges)/sizeof(*edges) ? edges[(trial + j) % 6] : next();
                request[j] = ctl[8 + j];
                step[TISA_ABI_DriveStep_arg0 + j] = 8 + j;
            }
            request[TISA_ABI_CallRequest_target] = trial < 6 ? edges[trial] : next();
            for (unsigned j = 0; j < TISA_ABI_CallRequestWords + 2; ++j) guarded[j] = guard;
            uint64_t bindings[] = {(uint64_t)(uintptr_t)(guarded + 1), TISA_ABI_CallRequestBytes,
                                   0, 0, 0, request[TISA_ABI_CallRequest_target]};
            uint64_t leaves[] = {(uint64_t)(uintptr_t)procedure_call_image};
            for (unsigned j = 1; j <= TISA_ABI_MaxRegions; ++j) step[j] = 2;
            step[TISA_ABI_DriveStep_region_0] = 0;
            step[TISA_ABI_DriveStep_region_8] = 4;
            step[TISA_ABI_DriveStep_dst] = 8 + dst;
            memcpy(before, ctl, sizeof ctl);
            uint64_t budget = trial < 6 ? edges[trial] : next();
            uint64_t used = trial % 2 ? budget : budget / 2;
            Drive d = {step, step + TISA_ABI_StepWords, ctl, bindings, leaves, budget, used, 0};
            uint64_t result = tisa_drive(&d);
            int ok = result == 2 && d.used == used && d.at == step;
            ok = ok && guarded[0] == guard && guarded[TISA_ABI_CallRequestWords + 1] == guard;
            ok = ok && !memcmp(guarded + 1, request, sizeof request);
            for (unsigned j = 0; j < 32; ++j)
                ok = ok && ctl[j] == (j == 8 + dst ? 0 : before[j]);
            if (!ok && ++failures <= 4)
                fprintf(stderr, "capture trial %u destination %u failed\n", trial, dst);
            ++runs;
        }
    }
    printf("call capture: %" PRIu64 " runs, %" PRIu64 " failures; image %td bytes\n",
           runs, failures, procedure_call_image_end - procedure_call_image);
    return failures ? 1 : 0;
}
