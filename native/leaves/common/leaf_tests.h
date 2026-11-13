/*
 * leaf_tests.h -- what the plan leaves' test generators share: a seeded
 * generator, and the .p1t directives (tcalc/native/p1/p1run.c) for regions
 * of 64-bit words, expectations and wanted words.
 */
#ifndef LEAF_TESTS_H
#define LEAF_TESTS_H

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 u128;

static uint64_t leaf_rng = 0x2545F4914F6CDD1Dull;
__attribute__((unused)) static void leaf_seed(const char *s) { if (s) leaf_rng ^= strtoull(s, NULL, 0) * 0x9E3779B97F4A7C15ull; }
__attribute__((unused)) static uint64_t leaf_next(void) {
    leaf_rng ^= leaf_rng << 13; leaf_rng ^= leaf_rng >> 7; leaf_rng ^= leaf_rng << 17;
    return leaf_rng;
}
/* A value below n (n > 0). */
__attribute__((unused)) static uint64_t leaf_below(uint64_t n) { return leaf_next() % n; }

static FILE *leaf_out;
static unsigned long leaf_ncases, leaf_nruns, leaf_outcomes[5];

__attribute__((unused)) static const char *leaf_outcome_name(int k) {
    static const char *names[] = {"REFUSED", "FIRED", "UNSUPPORTED", "INVALID", "EXHAUSTED"};
    return names[k];
}

__attribute__((unused)) static void leaf_case(const char *prefix, int chain) {
    fprintf(leaf_out, "case %s%lu%s\n", prefix, leaf_ncases++, chain ? " chain" : "");
}

/* Region r of len bytes; the first nw words from w (the rest zero, and the
 * bytes past the last whole word zero). */
__attribute__((unused)) static void leaf_region_words(unsigned r, uint64_t len, const uint64_t *w, size_t nw) {
    fprintf(leaf_out, "region %u %" PRIu64 "\n", r, len);
    for (size_t i = 0; i < nw && 8 * i + 8 <= len; i += 8) {
        fprintf(leaf_out, "words %u %zu", r, 8 * i);
        for (size_t j = i; j < i + 8 && j < nw && 8 * j + 8 <= len; j++) fprintf(leaf_out, " %" PRIu64, w[j]);
        fputc('\n', leaf_out);
    }
}

__attribute__((unused)) static void leaf_expect(int k, int with_ret, uint64_t ret) {
    if (with_ret) fprintf(leaf_out, "expect %s %" PRIu64 "\n", leaf_outcome_name(k), ret);
    else fprintf(leaf_out, "expect %s\n", leaf_outcome_name(k));
    leaf_outcomes[k]++;
    leaf_nruns++;
}

__attribute__((unused)) static void leaf_want(unsigned r, uint64_t word_index, uint64_t value) {
    fprintf(leaf_out, "want %u %" PRIu64 " %" PRIu64 "\n", r, 8 * word_index, value);
}

__attribute__((unused)) static void leaf_summary(const char *name) {
    printf("%s: %lu cases, %lu runs: FIRED %lu, REFUSED %lu, UNSUPPORTED %lu\n", name, leaf_ncases,
           leaf_nruns, leaf_outcomes[1], leaf_outcomes[0], leaf_outcomes[2]);
}

#endif
