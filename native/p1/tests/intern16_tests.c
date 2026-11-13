/*
 * intern16_tests.c -- intern_p1.c's tests for intern16, as p1run test
 * descriptions, so that the program can be run from its text.
 *
 *   intern16_tests DIFF.p1t INTERN.p1t
 *
 * DIFF.p1t: the 24,000-run differential of intern_p1.c (4000 random stores,
 * corrupted tables and headers included, 6 keys each), drawn from the same
 * generator in the same order, so a run here is the run there.
 * INTERN.p1t: interning on a clean store (512 rows, 1024 slots), chained:
 * 64 x 4 keys three times; the first round appends ids 0..255 in order,
 * the later rounds return the same ids, the rows hold the keys, and the
 * count ends at 256.
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t rng = 0x243F6A8885A308D3ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: intern16_tests DIFF.p1t INTERN.p1t\n"); return 2; }
    FILE *f = fopen(argv[1], "w");
    if (!f) { perror(argv[1]); return 2; }
    fprintf(f, "# intern16: intern_p1.c's differential, drawn in its order (regions 0 rows, 1 table, 2 header)\n");
    uint64_t rows[48], table[40];
    for (int t = 0; t < 4000; t++) {
        size_t nrows = 1 + next() % 24, nslots = 1 + next() % 40;
        size_t count = next() % (nrows + 3);              /* sometimes above capacity */
        for (size_t i = 0; i < 2 * nrows; i++) rows[i] = next() % 4;
        for (size_t i = 0; i < nslots; i++) {
            uint64_t r = next() % 5;
            table[i] = r == 0 ? 0 : r == 1 ? next() : 1 + next() % (count + 2);
        }
        fprintf(f, "case d%d\nregion 0 %zu\nwords 0 0", t, 16 * nrows);
        for (size_t i = 0; i < 2 * nrows; i++) fprintf(f, " %" PRIu64, rows[i]);
        fprintf(f, "\nregion 1 %zu\nwords 1 0", 8 * nslots);
        for (size_t i = 0; i < nslots; i++) fprintf(f, " %" PRIu64, table[i]);
        fprintf(f, "\nregion 2 8\nwords 2 0 %zu\n", count);
        for (int q = 0; q < 6; q++) {
            uint64_t k0 = next() % 4, k1 = next() % 4;
            fprintf(f, "run arg0=%" PRIu64 " arg1=%" PRIu64 "\n", k0, k1);
        }
    }
    fclose(f);

    FILE *g = fopen(argv[2], "w");
    if (!g) { perror(argv[2]); return 2; }
    fprintf(g, "# intern16: interning on a clean store, chained runs\ncase intern chain\n"
               "region 0 8192\nregion 1 8192\nregion 2 8\n");
    for (int round = 0; round < 3; round++)
        for (int k0 = 0; k0 < 64; k0++)
            for (int k1 = 0; k1 < 4; k1++) {
                int id = 4 * k0 + k1;
                fprintf(g, "expect FIRED %d\n", id);
                if (round == 2) {
                    fprintf(g, "want 0 %d %d\nwant 0 %d %d\n", 16 * id, k0 * 7919, 16 * id + 8, k1);
                    if (id == 255) fprintf(g, "want 2 0 256\n");
                }
                fprintf(g, "run arg0=%d arg1=%d\n", k0 * 7919, k1);
            }
    fclose(g);
    return 0;
}
