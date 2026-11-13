/*
 * row_word_tests.c -- test descriptions for row_word (p1run's .p1t format),
 * each run with the outcome and ret_val an independent model of
 * pl_row_word_spec (tcalc/native/hol/plans_leaves.ml) gives. Region 0 the
 * rows, region 1 the count c (word 0); v1 the stride s, arg0 the row i,
 * arg1 the word w:
 *
 *   i < c /\ w < s /\ 8 s c <= len(rows)  ==>  FIRED, ret_val = rows word s i + w
 *   otherwise                             ==>  UNSUPPORTED
 *
 * in unbounded arithmetic (the model uses 128 bits: s c, compared with
 * len(rows) DIV 8). Cases: small tables at and around their exact length,
 * every row and word index at and past the bounds; strides and counts whose
 * product wraps 64 bits to a small number (a wrapped product must not pass);
 * high halves of s and c set; RANDOM random tables.
 *
 *   row_word_tests OUT.p1t [SEED [RANDOM]]
 */
#include "../common/leaf_tests.h"

static uint64_t rows[1 << 16];

static void run(uint64_t len0, uint64_t c, uint64_t s, uint64_t i, uint64_t w) {
    int fired = i < c && w < s && (u128)s * c <= (u128)(len0 / 8);
    if (fired) leaf_expect(1, 1, rows[s * i + w]);
    else leaf_expect(2, 0, 0);
    fprintf(leaf_out, "run v1=%" PRIu64 " arg0=%" PRIu64 " arg1=%" PRIu64 "\n", s, i, w);
}

/* A case: the rows region of len0 bytes (random words), the count c. */
static void table(uint64_t len0, uint64_t c) {
    uint64_t nw = len0 / 8;
    if (nw > sizeof rows / sizeof rows[0]) { fprintf(stderr, "row_word_tests: table too big\n"); exit(1); }
    for (uint64_t k = 0; k < nw; k++) rows[k] = leaf_next();
    leaf_case("rw", 0);
    leaf_region_words(0, len0, rows, nw);
    fprintf(leaf_out, "region 1 8\nwords 1 0 %" PRIu64 "\n", c);
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) { fprintf(stderr, "usage: row_word_tests OUT.p1t [SEED [RANDOM]]\n"); return 2; }
    leaf_seed(argc > 2 ? argv[2] : NULL);
    unsigned long nrandom = argc > 3 ? strtoul(argv[3], NULL, 0) : 3000;
    leaf_out = fopen(argv[1], "w");
    if (!leaf_out) { perror(argv[1]); return 2; }
    fprintf(leaf_out, "# row_word: region 0 rows, region 1 count; v1 stride, arg0 row, arg1 word\n");
    const uint64_t big = UINT64_MAX;

    /* Small tables at, below and above their exact length. */
    const uint64_t strides[] = {1, 2, 3, 5, 7};
    const uint64_t counts[] = {0, 1, 2, 5, 17};
    for (size_t a = 0; a < 5; a++)
        for (size_t b = 0; b < 5; b++) {
            uint64_t s = strides[a], c = counts[b], exact = 8 * s * c;
            const uint64_t lens[] = {exact, exact ? exact - 1 : 0, exact + 7, exact + 8, exact ? exact - 8 : 0, 0};
            for (size_t l = 0; l < 6; l++) {
                table(lens[l], c);
                const uint64_t is[] = {0, c ? c - 1 : 0, c, c + 1, big};
                const uint64_t ws[] = {0, s - 1, s, big};
                for (size_t x = 0; x < 5; x++)
                    for (size_t y = 0; y < 4; y++) {
                        run(lens[l], c, s, is[x], ws[y]);
                        run(lens[l], c, s + 1, is[x], ws[y]);   /* a stride the table does not have */
                    }
            }
        }

    /* Strides and counts whose product wraps 64 bits, or whose high halves are
     * set: never inside a 64-byte table. */
    {
        const uint64_t pairs[][2] = {
            {((uint64_t)1 << 62) + 1, 4}, {4, ((uint64_t)1 << 62) + 1}, {(uint64_t)1 << 32, (uint64_t)1 << 32},
            {(uint64_t)1 << 33, (uint64_t)1 << 31}, {(uint64_t)1 << 31, (uint64_t)1 << 33},
            {((uint64_t)1 << 32) + 1, ((uint64_t)1 << 32) - 1}, {(uint64_t)1 << 63, 2}, {2, (uint64_t)1 << 63},
            {big, big}, {big, 1}, {1, big}, {(uint64_t)1 << 32, 1}, {1, (uint64_t)1 << 32},
            {((uint64_t)1 << 61) + 1, 8}, {8, ((uint64_t)1 << 61) + 1}, {(uint64_t)1 << 35, (uint64_t)1 << 29}};
        for (size_t p = 0; p < sizeof pairs / sizeof pairs[0]; p++) {
            uint64_t s = pairs[p][0], c = pairs[p][1];
            for (uint64_t len0 = 0; len0 <= 64; len0 += 32) {
                table(len0, c);
                run(len0, c, s, 0, 0);
                run(len0, c, s, c - 1, s - 1);
                run(len0, c, s, 1, 1);
            }
        }
    }

    /* Strides and counts near 2^32 with tables that hold them exactly. */
    {
        const uint64_t pairs[][2] = {{1, 4096}, {4096, 1}, {65536, 1}, {1, 65535}, {255, 257}, {1024, 63}};
        for (size_t p = 0; p < sizeof pairs / sizeof pairs[0]; p++) {
            uint64_t s = pairs[p][0], c = pairs[p][1], exact = 8 * s * c;
            for (int d = -1; d <= 0; d++) {
                uint64_t len0 = exact + 8 * (uint64_t)(int64_t)d;
                table(len0, c);
                for (int q = 0; q < 6; q++) {
                    uint64_t i = q < 2 ? c - 1 : leaf_below(c), w = q % 2 ? s - 1 : leaf_below(s);
                    run(len0, c, s, i, w);
                }
                run(len0, c, s, c, 0);
                run(len0, c, s, 0, s);
            }
        }
    }

    /* Random tables and requests, mostly inside. */
    for (unsigned long t = 0; t < nrandom; t++) {
        uint64_t s = 1 + leaf_below(9), c = leaf_below(40);
        uint64_t exact = 8 * s * c;
        uint64_t len0 = leaf_below(4) ? exact + 8 * leaf_below(3) : (exact ? leaf_below(exact + 16) : 8 * leaf_below(4));
        table(len0, c);
        for (int q = 0; q < 8; q++) {
            uint64_t i = leaf_below(4) ? (c ? leaf_below(c) : 0) : leaf_below(c + 3);
            uint64_t w = leaf_below(4) ? leaf_below(s) : leaf_below(s + 3);
            uint64_t sr = leaf_below(8) ? s : 1 + leaf_below(12);
            run(len0, c, sr, i, w);
        }
    }

    fclose(leaf_out);
    leaf_summary("row_word_tests");
    return leaf_outcomes[1] && leaf_outcomes[2] ? 0 : 1;
}
