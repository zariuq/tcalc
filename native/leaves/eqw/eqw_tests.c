/*
 * eqw_tests.c -- test descriptions for eqw (p1run's .p1t format), each run
 * with the outcome and ret_val an independent model of pl_eqw_spec
 * (tcalc/native/hol/plans_leaves.ml) gives:
 *
 *   arg0 = arg1  ==>  FIRED, ret_val = arg0
 *   otherwise    ==>  REFUSED
 *
 * The program also returns 0 with REFUSED (eqw.metta); the model checks that
 * too, as the program's own documented behaviour.
 *
 *   eqw_tests OUT.p1t [SEED [RANDOM]]
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t rng = 0x165667B19E3779F9ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static FILE *out;
static unsigned long nruns, nfired, nrefused;

static void emit(uint64_t a, uint64_t b) {
    if (a == b) {
        fprintf(out, "expect FIRED %" PRIu64 "\n", a);
        nfired++;
    } else {
        fprintf(out, "expect REFUSED 0\n");
        nrefused++;
    }
    fprintf(out, "run arg0=%" PRIu64 " arg1=%" PRIu64 "\n", a, b);
    nruns++;
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) { fprintf(stderr, "usage: eqw_tests OUT.p1t [SEED [RANDOM]]\n"); return 2; }
    if (argc > 2) rng ^= strtoull(argv[2], NULL, 0) * 0x2545F4914F6CDD1Dull;
    unsigned long nrandom = argc > 3 ? strtoul(argv[3], NULL, 0) : 20000;
    out = fopen(argv[1], "w");
    if (!out) { perror(argv[1]); return 2; }
    fprintf(out, "# eqw: no regions; arg0 and arg1\ncase eqw\n");
    const uint64_t vs[] = {0, 1, 2, 6, 7, 255, 256, ((uint64_t)1 << 32) - 1, (uint64_t)1 << 32,
                           (uint64_t)1 << 63, ((uint64_t)1 << 63) + 1, UINT64_MAX - 1, UINT64_MAX};
    for (size_t i = 0; i < sizeof vs / sizeof vs[0]; i++)
        for (size_t j = 0; j < sizeof vs / sizeof vs[0]; j++) emit(vs[i], vs[j]);
    for (unsigned long t = 0; t < nrandom; t++) {
        uint64_t a = next(), b;
        switch (t % 4) {
        case 0: b = a; break;
        case 1: b = a ^ ((uint64_t)1 << (next() % 64)); break;   /* one bit apart */
        case 2: b = a + 1; break;
        default: b = next(); break;
        }
        emit(a, b);
    }
    fclose(out);
    printf("eqw_tests: %lu runs: FIRED %lu, REFUSED %lu\n", nruns, nfired, nrefused);
    return nfired && nrefused ? 0 : 1;
}
