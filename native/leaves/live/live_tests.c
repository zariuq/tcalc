/*
 * live_tests.c -- test descriptions for live (p1run's .p1t format), each run
 * with the outcome and ret_val an independent model of pl_live_spec
 * (tcalc/native/hol/plans_leaves.ml) gives. Region 0 the count c (word 0),
 * region 1 the marks (one word per id); arg0 the id:
 *
 *   8 c <= len(marks):  id < c /\ mark(id) = 0  ==>  FIRED, ret_val = id
 *                       otherwise               ==>  REFUSED
 *   8 c > len(marks)                            ==>  UNSUPPORTED
 *
 * in unbounded arithmetic (the model uses 128 bits). Cases: marks regions at
 * and around 8 c bytes, lengths that are not a multiple of 8, every id at and
 * past the count, counts near 2^61 and 2^64 (8 c wraps 64 bits), marks of
 * every kind (0, 1, 2^64 - 1, high bits only); RANDOM random spaces.
 *
 *   live_tests OUT.p1t [SEED [RANDOM]]
 */
#include "../common/leaf_tests.h"

static uint64_t marks[4096];

static void run(uint64_t c, uint64_t len1, uint64_t id) {
    if ((u128)8 * c <= len1) {
        if (id < c && marks[id] == 0) leaf_expect(1, 1, id);
        else leaf_expect(0, 1, 0);
    } else leaf_expect(2, 0, 0);
    fprintf(leaf_out, "run arg0=%" PRIu64 "\n", id);
}

static void space(uint64_t c, uint64_t len1) {
    uint64_t nw = len1 / 8;
    if (nw > sizeof marks / sizeof marks[0]) { fprintf(stderr, "live_tests: marks too big\n"); exit(1); }
    for (uint64_t k = 0; k < nw; k++) {
        uint64_t r = leaf_below(8);
        marks[k] = r < 4 ? 0 : r == 4 ? 1 : r == 5 ? UINT64_MAX : r == 6 ? (uint64_t)1 << 63 : leaf_next();
    }
    leaf_case("lv", 0);
    fprintf(leaf_out, "region 0 8\nwords 0 0 %" PRIu64 "\n", c);
    leaf_region_words(1, len1, marks, nw);
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) { fprintf(stderr, "usage: live_tests OUT.p1t [SEED [RANDOM]]\n"); return 2; }
    leaf_seed(argc > 2 ? argv[2] : NULL);
    unsigned long nrandom = argc > 3 ? strtoul(argv[3], NULL, 0) : 3000;
    leaf_out = fopen(argv[1], "w");
    if (!leaf_out) { perror(argv[1]); return 2; }
    fprintf(leaf_out, "# live: region 0 count, region 1 marks; arg0 the id\n");

    /* Counts 0..20 with marks at, below and above 8 c bytes. */
    for (uint64_t c = 0; c <= 20; c++) {
        const uint64_t lens[] = {8 * c, 8 * c + 1, 8 * c + 7, 8 * c + 8, c ? 8 * c - 1 : 0, c ? 8 * c - 8 : 0, 0};
        for (size_t l = 0; l < 7; l++) {
            space(c, lens[l]);
            for (uint64_t id = 0; id <= c + 2; id++) run(c, lens[l], id);
            run(c, lens[l], UINT64_MAX);
            run(c, lens[l], (uint64_t)1 << 61);
            run(c, lens[l], (uint64_t)1 << 63);
        }
    }

    /* Counts whose 8 c reaches or wraps 2^64, and counts near the marks'
     * capacity in words. */
    {
        const uint64_t cs[] = {(uint64_t)1 << 61, ((uint64_t)1 << 61) - 1, ((uint64_t)1 << 61) + 1,
                               (uint64_t)1 << 62, (uint64_t)1 << 63, UINT64_MAX, UINT64_MAX - 1};
        for (size_t q = 0; q < sizeof cs / sizeof cs[0]; q++)
            for (uint64_t len1 = 0; len1 <= 64; len1 += 16) {
                space(cs[q], len1);
                run(cs[q], len1, 0);
                run(cs[q], len1, 1);
                run(cs[q], len1, cs[q] - 1);
                run(cs[q], len1, UINT64_MAX);
            }
    }

    /* Random spaces. */
    for (unsigned long t = 0; t < nrandom; t++) {
        uint64_t c = leaf_below(200);
        uint64_t len1 = leaf_below(5) ? 8 * c + leaf_below(24) : leaf_below(8 * c + 9);
        space(c, len1);
        for (int q = 0; q < 8; q++) run(c, len1, leaf_below(4) ? leaf_below(c + 1) : leaf_below(c + 5));
    }

    fclose(leaf_out);
    leaf_summary("live_tests");
    return leaf_outcomes[0] && leaf_outcomes[1] && leaf_outcomes[2] ? 0 : 1;
}
