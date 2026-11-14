/*
 * inc_tests.c -- test descriptions for inc (p1run's .p1t format), each run
 * with the outcome and ret_val an independent model of pl_inc_spec
 * (tcalc/native/hol/plans_leaves.ml) gives:
 *
 *   val arg0 + 1 < 2^62  ==>  FIRED, ret_val = arg0 + 1
 *   otherwise            ==>  UNSUPPORTED
 *
 * The model computes in 128-bit arithmetic, so a sum that would wrap shows.
 * The program returns 0 with UNSUPPORTED (inc.metta); the model checks that
 * too, as the program's own documented behaviour.
 *
 *   inc_tests OUT.p1t [SEED [RANDOM]]
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t rng = 0x9E3779B97F4A7C15ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static FILE *out;
static unsigned long nruns, nfired, nunsupported;

static void emit(uint64_t a) {
    unsigned __int128 lim = (unsigned __int128)1 << 62;
    unsigned __int128 s = (unsigned __int128)a + 1;
    if (s < lim) {
        fprintf(out, "expect FIRED %" PRIu64 "\n", (uint64_t)s);
        nfired++;
    } else {
        fprintf(out, "expect UNSUPPORTED 0\n");
        nunsupported++;
    }
    fprintf(out, "run arg0=%" PRIu64 "\n", a);
    nruns++;
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) { fprintf(stderr, "usage: inc_tests OUT.p1t [SEED [RANDOM]]\n"); return 2; }
    if (argc > 2) rng ^= strtoull(argv[2], NULL, 0) * 0x2545F4914F6CDD1Dull;
    unsigned long nrandom = argc > 3 ? strtoul(argv[3], NULL, 0) : 20000;
    out = fopen(argv[1], "w");
    if (!out) { perror(argv[1]); return 2; }
    fprintf(out, "# inc: no regions; arg0 a\ncase inc\n");
    const uint64_t as[] = {0, 1, 2, 7, 1000, ((uint64_t)1 << 32) - 1, (uint64_t)1 << 32,
                           ((uint64_t)1 << 62) - 3, ((uint64_t)1 << 62) - 2, ((uint64_t)1 << 62) - 1,
                           (uint64_t)1 << 62, ((uint64_t)1 << 62) + 1, ((uint64_t)1 << 63) - 1,
                           (uint64_t)1 << 63, UINT64_MAX - 1, UINT64_MAX};
    for (size_t i = 0; i < sizeof as / sizeof as[0]; i++) emit(as[i]);
    for (unsigned long t = 0; t < nrandom; t++) {
        uint64_t a = next();
        switch (t % 4) {
        case 0: a >>= 3; break;                                   /* inside */
        case 1: a = ((uint64_t)1 << 62) - 1 - (next() % 64) + (next() % 64); break;  /* the edge */
        case 2: break;                                            /* anything */
        default: a >>= 2 + next() % 8; break;
        }
        emit(a);
    }
    fclose(out);
    printf("inc_tests: %lu runs: FIRED %lu, UNSUPPORTED %lu\n", nruns, nfired, nunsupported);
    return nfired && nunsupported ? 0 : 1;
}
