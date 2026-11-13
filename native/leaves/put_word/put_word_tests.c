/*
 * put_word_tests.c -- test descriptions for put_word (p1run's .p1t format),
 * each run with the outcome, ret_val and region words an independent model
 * of pl_put_word_spec (tcalc/native/hol/plans_leaves.ml) gives. Region 0 the
 * table, region 1 its count c (word 0); v1 the stride s, v2 the word w,
 * arg0 the row i, arg1 the value x:
 *
 *   i < c /\ w < s /\ 8 s c <= len(table)  ==>  FIRED, ret_val = x, table
 *       word s i + w := x
 *   otherwise                              ==>  UNSUPPORTED, nothing written
 *
 * in unbounded arithmetic (the model uses 128 bits). Chained cases put words
 * one after another; the model keeps the table and every run wants the
 * table's words (all of them when there are at most 60, else the target's
 * neighbourhood and a sample). Cases also cover strides and counts whose
 * product wraps 64 bits, and high halves set.
 *
 *   put_word_tests OUT.p1t [SEED [RANDOM]]
 */
#include "../common/leaf_tests.h"

static uint64_t tab[8192];
static uint64_t ntab, len0, count;

static void table(uint64_t len, uint64_t c, int chain) {
    len0 = len; count = c; ntab = len / 8;
    if (ntab > sizeof tab / sizeof tab[0]) { fprintf(stderr, "put_word_tests: table too big\n"); exit(1); }
    for (uint64_t k = 0; k < ntab; k++) tab[k] = leaf_next();
    leaf_case("pw", chain);
    leaf_region_words(0, len0, tab, ntab);
    fprintf(leaf_out, "region 1 8\nwords 1 0 %" PRIu64 "\n", c);
}

static void run(uint64_t s, uint64_t w, uint64_t i, uint64_t x) {
    int fired = i < count && w < s && (u128)s * count <= (u128)(len0 / 8);
    uint64_t at = 0;
    if (fired) {
        leaf_expect(1, 1, x);
        at = s * i + w;
        tab[at] = x;
    } else leaf_expect(2, 0, 0);
    unsigned nw = 0;
    if (ntab <= 60) {
        for (uint64_t k = 0; k < ntab; k++) { leaf_want(0, k, tab[k]); nw++; }
    } else {
        if (fired)
            for (uint64_t k = at >= 2 ? at - 2 : 0; k <= at + 2 && k < ntab; k++) { leaf_want(0, k, tab[k]); nw++; }
        while (nw < 60) { uint64_t k = leaf_below(ntab); leaf_want(0, k, tab[k]); nw++; }
    }
    fprintf(leaf_out, "run v1=%" PRIu64 " v2=%" PRIu64 " arg0=%" PRIu64 " arg1=%" PRIu64 "\n", s, w, i, x);
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) { fprintf(stderr, "usage: put_word_tests OUT.p1t [SEED [RANDOM]]\n"); return 2; }
    leaf_seed(argc > 2 ? argv[2] : NULL);
    unsigned long nrandom = argc > 3 ? strtoul(argv[3], NULL, 0) : 1500;
    leaf_out = fopen(argv[1], "w");
    if (!leaf_out) { perror(argv[1]); return 2; }
    fprintf(leaf_out, "# put_word: region 0 table, region 1 count; v1 stride, v2 word, arg0 row, arg1 value\n");
    const uint64_t big = UINT64_MAX;

    /* Small tables at and around their exact length; every row and word at
     * and past the bounds. */
    const uint64_t strides[] = {1, 2, 3, 5};
    const uint64_t counts[] = {0, 1, 2, 7};
    for (size_t a = 0; a < 4; a++)
        for (size_t b = 0; b < 4; b++) {
            uint64_t s = strides[a], c = counts[b], exact = 8 * s * c;
            const uint64_t lens[] = {exact, exact ? exact - 1 : 0, exact + 9, exact ? exact - 8 : 0};
            for (size_t l = 0; l < 4; l++) {
                table(lens[l], c, 1);
                const uint64_t is[] = {0, c ? c - 1 : 0, c, big};
                const uint64_t ws[] = {0, s - 1, s, big};
                for (size_t x = 0; x < 4; x++)
                    for (size_t y = 0; y < 4; y++) {
                        run(s, ws[y], is[x], leaf_next());
                        run(s + 1, ws[y], is[x], leaf_next());
                    }
            }
        }

    /* Strides and counts whose product wraps 64 bits, or with high halves. */
    {
        const uint64_t pairs[][2] = {
            {((uint64_t)1 << 62) + 1, 4}, {4, ((uint64_t)1 << 62) + 1}, {(uint64_t)1 << 32, (uint64_t)1 << 32},
            {(uint64_t)1 << 33, (uint64_t)1 << 31}, {((uint64_t)1 << 32) + 1, ((uint64_t)1 << 32) - 1},
            {(uint64_t)1 << 63, 2}, {big, big}, {big, 1}, {1, big}, {(uint64_t)1 << 32, 1}, {1, (uint64_t)1 << 32}};
        for (size_t p = 0; p < sizeof pairs / sizeof pairs[0]; p++) {
            uint64_t s = pairs[p][0], c = pairs[p][1];
            table(64, c, 0);
            run(s, 0, 0, 1);
            run(s, s - 1, c - 1, 2);
            run(s, 1, 1, 3);
        }
    }

    /* Larger tables (strides and counts up to a few thousand words). */
    {
        const uint64_t pairs[][2] = {{1, 4096}, {4096, 1}, {5, 1000}, {2, 2048}, {63, 65}};
        for (size_t p = 0; p < sizeof pairs / sizeof pairs[0]; p++) {
            uint64_t s = pairs[p][0], c = pairs[p][1];
            for (int d = -1; d <= 0; d++) {
                table(8 * s * c + 8 * (uint64_t)(int64_t)d, c, 1);
                for (int q = 0; q < 6; q++) run(s, q % 2 ? s - 1 : leaf_below(s), q < 2 ? c - 1 : leaf_below(c), leaf_next());
            }
        }
    }

    /* Random tables, chained. */
    for (unsigned long t = 0; t < nrandom; t++) {
        uint64_t s = 1 + leaf_below(6), c = leaf_below(10);
        uint64_t exact = 8 * s * c;
        table(leaf_below(4) ? exact + 8 * leaf_below(2) : leaf_below(exact + 9), c, 1);
        for (int q = 0; q < 6; q++) {
            uint64_t sr = leaf_below(8) ? s : 1 + leaf_below(8);
            run(sr, leaf_below(4) ? leaf_below(sr) : leaf_below(sr + 2), leaf_below(4) ? (c ? leaf_below(c) : 0) : leaf_below(c + 2),
                leaf_next());
        }
    }

    fclose(leaf_out);
    leaf_summary("put_word_tests");
    return leaf_outcomes[1] && leaf_outcomes[2] ? 0 : 1;
}
