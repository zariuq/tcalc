/*
 * at_end_tests.c -- test descriptions for at_end (p1run's .p1t format), each
 * run with the outcome and ret_val an independent model of pl_at_end_spec
 * (tcalc/native/hol/plans_leaves.ml) gives: region 0 the input, region 1 the
 * reader's state (16 bytes or more; word 0 the cursor); no arguments:
 *
 *   FIRED, ret_val 1, when the cursor is the input's length
 *   REFUSED, ret_val 0, otherwise
 *
 * Cases: inputs of 0 to 9 bytes with the cursor at, below and above the
 * length, and cursors far away (2^62 - 1, 2^63, 2^64 - 1); states of 16 bytes
 * and longer; RANDOM random states.
 *
 *   at_end_tests OUT.p1t [SEED [RANDOM]]
 */
#include "../common/leaf_tests.h"

static void one(uint64_t len, uint64_t nin, uint64_t cursor, uint64_t work) {
    uint64_t w[4] = {cursor, work, leaf_next(), leaf_next()};
    leaf_case("ae", 0);
    fprintf(leaf_out, "region 0 %" PRIu64 "\n", nin);
    if (nin) {
        fprintf(leaf_out, "hex 0 0 ");
        for (uint64_t i = 0; i < nin; i++) fprintf(leaf_out, "%02x", (unsigned)(leaf_next() & 255));
        fputc('\n', leaf_out);
    }
    leaf_region_words(1, len, w, len / 8 < 4 ? len / 8 : 4);
    if (cursor == nin) leaf_expect(1, 1, 1); else leaf_expect(0, 1, 0);
    fprintf(leaf_out, "run\n");
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) { fprintf(stderr, "usage: at_end_tests OUT.p1t [SEED [RANDOM]]\n"); return 2; }
    leaf_seed(argc > 2 ? argv[2] : NULL);
    unsigned long nrandom = argc > 3 ? strtoul(argv[3], NULL, 0) : 3000;
    leaf_out = fopen(argv[1], "w");
    if (!leaf_out) { perror(argv[1]); return 2; }
    fprintf(leaf_out, "# at_end: region 0 the input, region 1 the reader's state (word 0 the cursor); no arguments\n");
    const uint64_t far[] = {((uint64_t)1 << 32) - 1, ((uint64_t)1 << 62) - 1, (uint64_t)1 << 62,
                            (uint64_t)1 << 63, UINT64_MAX - 1, UINT64_MAX};
    const uint64_t lens[] = {16, 17, 23, 24, 32};
    for (uint64_t nin = 0; nin < 10; nin++)
        for (size_t l = 0; l < sizeof lens / sizeof lens[0]; l++) {
            for (uint64_t c = 0; c <= nin + 2; c++) { one(lens[l], nin, c, 0); one(lens[l], nin, c, UINT64_MAX); }
            for (size_t f = 0; f < sizeof far / sizeof far[0]; f++) one(lens[l], nin, far[f], leaf_next());
        }
    for (unsigned long t = 0; t < nrandom; t++) {
        uint64_t nin = leaf_below(10);
        uint64_t c = leaf_below(2) ? nin : (leaf_below(2) ? leaf_below(12) : leaf_next() >> leaf_below(64));
        one(16 + 8 * leaf_below(3), nin, c, leaf_next());
    }
    fclose(leaf_out);
    leaf_summary("at_end_tests");
    return 0;
}
