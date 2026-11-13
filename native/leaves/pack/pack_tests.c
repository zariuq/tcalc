/*
 * pack_tests.c -- test descriptions for pack (p1run's .p1t format), each run
 * with the outcome and ret_val an independent model of pl_pack_spec
 * (tcalc/native/hol/plans_leaves.ml) gives:
 *
 *   val arg0 < 2^60 /\ val arg1 < 8  ==>  FIRED, ret_val = arg1 + 8 arg0
 *   otherwise                         ==>  UNSUPPORTED
 *
 * The model computes in 128-bit arithmetic, so a sum that would wrap shows.
 * The program also returns 0 with UNSUPPORTED (pack.metta); the model checks
 * that too, as the program's own documented behaviour.
 *
 *   pack_tests OUT.p1t [SEED [RANDOM]]
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t rng = 0x9E3779B97F4A7C15ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static FILE *out;
static unsigned long nruns, nfired, nunsupported;

static void emit(uint64_t a, uint64_t tag) {
    unsigned __int128 lim = (unsigned __int128)1 << 60;
    if ((unsigned __int128)a < lim && tag < 8) {
        unsigned __int128 key = (unsigned __int128)tag + 8 * (unsigned __int128)a;
        if (key >> 64) { fprintf(stderr, "pack_tests: the model's key does not fit 64 bits\n"); exit(1); }
        fprintf(out, "expect FIRED %" PRIu64 "\n", (uint64_t)key);
        nfired++;
    } else {
        fprintf(out, "expect UNSUPPORTED 0\n");
        nunsupported++;
    }
    fprintf(out, "run arg0=%" PRIu64 " arg1=%" PRIu64 "\n", a, tag);
    nruns++;
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) { fprintf(stderr, "usage: pack_tests OUT.p1t [SEED [RANDOM]]\n"); return 2; }
    if (argc > 2) rng ^= strtoull(argv[2], NULL, 0) * 0x2545F4914F6CDD1Dull;
    unsigned long nrandom = argc > 3 ? strtoul(argv[3], NULL, 0) : 20000;
    out = fopen(argv[1], "w");
    if (!out) { perror(argv[1]); return 2; }
    fprintf(out, "# pack: no regions; arg0 a, arg1 the tag\ncase pack\n");
    const uint64_t as[] = {0, 1, 2, 7, 8, 1000, ((uint64_t)1 << 32) - 1, (uint64_t)1 << 32,
                           ((uint64_t)1 << 60) - 2, ((uint64_t)1 << 60) - 1, (uint64_t)1 << 60,
                           ((uint64_t)1 << 60) + 1, ((uint64_t)1 << 61) - 1, (uint64_t)1 << 61,
                           (uint64_t)1 << 63, UINT64_MAX - 1, UINT64_MAX};
    const uint64_t tags[] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 255, (uint64_t)1 << 32,
                             (uint64_t)1 << 63, UINT64_MAX - 1, UINT64_MAX, 8 + ((uint64_t)1 << 63)};
    for (size_t i = 0; i < sizeof as / sizeof as[0]; i++)
        for (size_t j = 0; j < sizeof tags / sizeof tags[0]; j++) emit(as[i], tags[j]);
    for (unsigned long t = 0; t < nrandom; t++) {
        uint64_t a = next(), tag = next();
        switch (t % 4) {
        case 0: a >>= 4; tag &= 7; break;               /* inside */
        case 1: a >>= 3 + next() % 8; tag %= 12; break;  /* near the edges */
        case 2: break;                                   /* anything */
        default: a = next() % 3 == 0 ? a : a >> 4; tag = next() % 2 ? tag & 15 : tag; break;
        }
        emit(a, tag);
    }
    fclose(out);
    printf("pack_tests: %lu runs: FIRED %lu, UNSUPPORTED %lu\n", nruns, nfired, nunsupported);
    return nfired && nunsupported ? 0 : 1;
}
