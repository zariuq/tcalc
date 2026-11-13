/*
 * unpack_tests.c -- test descriptions for unpack (p1run's .p1t format), each
 * run with the outcome and ret_val an independent model of pl_unpack_spec
 * (tcalc/native/hol/plans_leaves.ml) gives:
 *
 *   val arg0 MOD 8 = val arg1  ==>  FIRED, ret_val = val arg0 DIV 8
 *   otherwise                  ==>  REFUSED
 *
 * The program also returns 0 with REFUSED (unpack.metta); the model checks
 * that too, as the program's own documented behaviour.
 *
 *   unpack_tests OUT.p1t [SEED [RANDOM]]
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t rng = 0xC2B2AE3D27D4EB4Full;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static FILE *out;
static unsigned long nruns, nfired, nrefused;

static void emit(uint64_t k0, uint64_t tag) {
    if (k0 % 8 == tag) {
        fprintf(out, "expect FIRED %" PRIu64 "\n", k0 / 8);
        nfired++;
    } else {
        fprintf(out, "expect REFUSED 0\n");
        nrefused++;
    }
    fprintf(out, "run arg0=%" PRIu64 " arg1=%" PRIu64 "\n", k0, tag);
    nruns++;
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) { fprintf(stderr, "usage: unpack_tests OUT.p1t [SEED [RANDOM]]\n"); return 2; }
    if (argc > 2) rng ^= strtoull(argv[2], NULL, 0) * 0x2545F4914F6CDD1Dull;
    unsigned long nrandom = argc > 3 ? strtoul(argv[3], NULL, 0) : 20000;
    out = fopen(argv[1], "w");
    if (!out) { perror(argv[1]); return 2; }
    fprintf(out, "# unpack: no regions; arg0 k0, arg1 the tag\ncase unpack\n");
    const uint64_t ks[] = {0, 1, 5, 6, 7, 8, 9, 14, 15, 16, 46, 0x7FFFFFFFFFFFFFFFull, (uint64_t)1 << 63,
                           ((uint64_t)1 << 63) + 6, UINT64_MAX - 8, UINT64_MAX - 1, UINT64_MAX};
    const uint64_t tags[] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 14, 15, 16, (uint64_t)1 << 32, (uint64_t)1 << 63,
                             ((uint64_t)1 << 63) + 6, UINT64_MAX - 1, UINT64_MAX};
    for (size_t i = 0; i < sizeof ks / sizeof ks[0]; i++)
        for (size_t j = 0; j < sizeof tags / sizeof tags[0]; j++) emit(ks[i], tags[j]);
    for (unsigned long t = 0; t < nrandom; t++) {
        uint64_t k0 = next(), tag = next();
        switch (t % 3) {
        case 0: tag = k0 % 8; break;                       /* the right tag */
        case 1: tag %= 10; break;                          /* a small tag */
        default: if (next() % 2) tag += 8 * (next() % 4); break;   /* the right tag plus 8j, or anything */
        }
        emit(k0, tag);
    }
    fclose(out);
    printf("unpack_tests: %lu runs: FIRED %lu, REFUSED %lu\n", nruns, nfired, nrefused);
    return nfired && nrefused ? 0 : 1;
}
