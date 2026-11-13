/*
 * append_row_tests.c -- test descriptions for append_row (p1run's .p1t
 * format), each run with the outcome, ret_val and region words an
 * independent model of pl_append_row_spec (tcalc/native/hol/plans_leaves.ml)
 * gives. Region 0 the rows, region 1 the count c (word 0); v1 the width w,
 * the row's words arg0, arg1, v2, v3, v4:
 *
 *   1 <= w <= 5 /\ 8 w (c + 1) <= len(rows)  ==>  FIRED, ret_val = c; rows
 *       words w c + j (j < w) the row's words, the count c + 1
 *   otherwise                                ==>  UNSUPPORTED, nothing written
 *
 * in unbounded arithmetic (the model uses 128 bits). Chained cases append
 * row after row until the table is full, with widths 0..7 (every case is
 * chained: each run starts from the state the previous left); the model keeps
 * the table and every run wants the count and the table's words (all of
 * them when there are at most 56, else the new row's and a sample). Cases
 * also cover counts near 2^61 and 2^64 (c + 1 and 8 w (c + 1) wrap 64 bits)
 * and tables whose length is not a multiple of 8.
 *
 *   append_row_tests OUT.p1t [SEED [RANDOM]]
 */
#include "../common/leaf_tests.h"

static uint64_t rows[4096];
static uint64_t nrows_words, len0, count;

static void table(uint64_t len, uint64_t c, int chain) {
    len0 = len; count = c; nrows_words = len / 8;
    if (nrows_words > sizeof rows / sizeof rows[0]) { fprintf(stderr, "append_row_tests: table too big\n"); exit(1); }
    for (uint64_t k = 0; k < nrows_words; k++) rows[k] = leaf_below(3) ? leaf_next() : 0;
    leaf_case("ar", chain);
    leaf_region_words(0, len0, rows, nrows_words);
    fprintf(leaf_out, "region 1 8\nwords 1 0 %" PRIu64 "\n", c);
}

static void run(uint64_t w, uint64_t a0, uint64_t a1, uint64_t x2, uint64_t x3, uint64_t x4) {
    const uint64_t vals[5] = {a0, a1, x2, x3, x4};
    int fired = w >= 1 && w <= 5 && (u128)w * ((u128)count + 1) <= (u128)(len0 / 8);
    uint64_t at = 0;
    if (fired) {
        leaf_expect(1, 1, count);
        at = w * count;
        for (uint64_t j = 0; j < w; j++) rows[at + j] = vals[j];
        count++;
    } else leaf_expect(2, 0, 0);
    leaf_want(1, 0, count);
    unsigned nw = 1;
    if (nrows_words <= 56) {
        for (uint64_t k = 0; k < nrows_words; k++) { leaf_want(0, k, rows[k]); nw++; }
    } else {
        if (fired) for (uint64_t j = 0; j < w; j++) { leaf_want(0, at + j, rows[at + j]); nw++; }
        while (nw < 60) { uint64_t k = leaf_below(nrows_words); leaf_want(0, k, rows[k]); nw++; }
    }
    fprintf(leaf_out, "run v1=%" PRIu64 " v2=%" PRIu64 " v3=%" PRIu64 " v4=%" PRIu64 " arg0=%" PRIu64
            " arg1=%" PRIu64 "\n", w, x2, x3, x4, a0, a1);
}

static void random_run(uint64_t w) { run(w, leaf_next(), leaf_next(), leaf_next(), leaf_next(), leaf_next()); }

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) { fprintf(stderr, "usage: append_row_tests OUT.p1t [SEED [RANDOM]]\n"); return 2; }
    leaf_seed(argc > 2 ? argv[2] : NULL);
    unsigned long nrandom = argc > 3 ? strtoul(argv[3], NULL, 0) : 1500;
    leaf_out = fopen(argv[1], "w");
    if (!leaf_out) { perror(argv[1]); return 2; }
    fprintf(leaf_out, "# append_row: region 0 rows, region 1 count; v1 width, row words arg0 arg1 v2 v3 v4\n");

    /* Every width 0..7 against tables at, below and above the room for one
     * more row, from counts 0..4. */
    for (uint64_t w = 0; w <= 7; w++)
        for (uint64_t c = 0; c <= 4; c++) {
            uint64_t need = 8 * (w ? w : 1) * (c + 1);
            const uint64_t lens[] = {need, need - 1, need + 7, need + 8, need >= 8 ? need - 8 : 0};
            for (size_t l = 0; l < 5; l++) {
                table(lens[l], c, 1);
                random_run(w);
                run(w, 0, UINT64_MAX, 1, (uint64_t)1 << 63, 7);
            }
        }

    /* Chained: rows appended until the table is full, then refused. */
    for (uint64_t w = 1; w <= 5; w++)
        for (uint64_t extra = 0; extra < 3; extra++) {
            uint64_t cap = 6;
            table(8 * w * cap + 3 * extra, 0, 1);
            for (uint64_t q = 0; q < cap + 2; q++) random_run(w);
            random_run(w + 1);
            random_run(0);
        }

    /* Mixed widths in one chained table. */
    for (int t = 0; t < 40; t++) {
        table(8 * (16 + leaf_below(48)) + leaf_below(8), leaf_below(3), 1);
        for (int q = 0; q < 12; q++) random_run(leaf_below(7));
    }

    /* Counts whose c + 1 or 8 w (c + 1) reach or wrap 2^64. */
    {
        const uint64_t cs[] = {(uint64_t)1 << 61, ((uint64_t)1 << 61) - 1, (uint64_t)1 << 62, (uint64_t)1 << 63,
                               UINT64_MAX, UINT64_MAX - 1, ((uint64_t)1 << 60) + 3};
        for (size_t q = 0; q < sizeof cs / sizeof cs[0]; q++) {
            table(64, cs[q], 1);
            for (uint64_t w = 0; w <= 6; w++) random_run(w);
        }
    }

    /* Random tables, chained. */
    for (unsigned long t = 0; t < nrandom; t++) {
        uint64_t w = 1 + leaf_below(5), c = leaf_below(6);
        table(8 * w * (c + leaf_below(4)) + leaf_below(16), c, 1);
        for (int q = 0; q < 4; q++) random_run(leaf_below(6) ? w : leaf_below(8));
    }

    fclose(leaf_out);
    leaf_summary("append_row_tests");
    return leaf_outcomes[1] && leaf_outcomes[2] ? 0 : 1;
}
