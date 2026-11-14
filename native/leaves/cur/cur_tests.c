/*
 * cur_tests.c -- test descriptions for cur (p1run's .p1t format), each run
 * with the outcome and ret_val an independent model of pl_cur_spec
 * (tcalc/native/hol/plans_leaves.ml) gives: region 0 the input, region 1 the
 * reader's state (16 bytes or more; word 0 the cursor); no arguments:
 *
 *   FIRED, ret_val = word 0 of the state
 *
 * Cases: cursors of every kind (0, 1, small, 2^62 - 1, 2^63, 2^64 - 1) with
 * work words of every kind, states of 16 bytes and longer, inputs of 0 to 9
 * bytes; RANDOM random states.
 *
 *   cur_tests OUT.p1t [SEED [RANDOM]]
 */
#include "../common/leaf_tests.h"

static void one(uint64_t len, uint64_t cursor, uint64_t work) {
    uint64_t w[4] = {cursor, work, leaf_next(), leaf_next()};
    uint64_t nin = leaf_below(10);
    leaf_case("cu", 0);
    fprintf(leaf_out, "region 0 %" PRIu64 "\n", nin);
    if (nin) {
        fprintf(leaf_out, "hex 0 0 ");
        for (uint64_t i = 0; i < nin; i++) fprintf(leaf_out, "%02x", (unsigned)(leaf_next() & 255));
        fputc('\n', leaf_out);
    }
    leaf_region_words(1, len, w, len / 8 < 4 ? len / 8 : 4);
    leaf_expect(1, 1, cursor);
    fprintf(leaf_out, "run\n");
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) { fprintf(stderr, "usage: cur_tests OUT.p1t [SEED [RANDOM]]\n"); return 2; }
    leaf_seed(argc > 2 ? argv[2] : NULL);
    unsigned long nrandom = argc > 3 ? strtoul(argv[3], NULL, 0) : 3000;
    leaf_out = fopen(argv[1], "w");
    if (!leaf_out) { perror(argv[1]); return 2; }
    fprintf(leaf_out, "# cur: region 0 the input, region 1 the reader's state (word 0 the cursor); no arguments\n");
    const uint64_t cs[] = {0, 1, 2, 39, 1000, ((uint64_t)1 << 32) - 1, ((uint64_t)1 << 62) - 1,
                           (uint64_t)1 << 62, (uint64_t)1 << 63, UINT64_MAX - 1, UINT64_MAX};
    const uint64_t lens[] = {16, 17, 23, 24, 32};
    for (size_t i = 0; i < sizeof cs / sizeof cs[0]; i++)
        for (size_t l = 0; l < sizeof lens / sizeof lens[0]; l++) {
            one(lens[l], cs[i], 0);
            one(lens[l], cs[i], UINT64_MAX);
        }
    for (unsigned long t = 0; t < nrandom; t++) one(16 + 8 * leaf_below(3), leaf_next() >> leaf_below(64), leaf_next());
    fclose(leaf_out);
    leaf_summary("cur_tests");
    return 0;
}
