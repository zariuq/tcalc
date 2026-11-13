/*
 * fnv_tests.c -- test descriptions for fnv (p1run's .p1t format), each run
 * with its expected outcome.
 *
 *   fnv_tests OUT.p1t [SEED [RANDOM]]
 *
 * The oracle is CeTTa's hk_fnv1a (hol_core.c, extracted by check.sh into
 * cetta_oracle.h), checked here against fnv1a as holr_spec.ml defines it.
 * A range inside the input is FIRED with the state after its bytes; a range
 * that is not (off > length, or n > length - off) is REFUSED 1.
 *
 * Cases: empty ranges and regions; ranges ending at the region's end and one
 * byte past it; offsets and lengths near 2^64 (their sum wraps); initial
 * states 0, 2^64 - 1 and FNV-1a's offset basis; a whole 1 MiB region; the
 * holr.py test vector; and RANDOM random regions and ranges.
 */
#include "cetta_oracle.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t rng = 0xD1B54A32D192ED03ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static FILE *out;
static unsigned long ncases, nruns, nfired, nrefused;

/* fnv1a as holr_spec.ml defines it: h := (h xor b) * 1099511628211 mod 2^64. */
static uint64_t spec_fnv1a(uint64_t h, const uint8_t *b, size_t n) {
    for (size_t i = 0; i < n; i++) h = (uint64_t)(((unsigned __int128)(h ^ b[i]) * 1099511628211u) % ((unsigned __int128)1 << 64));
    return h;
}

static void begin_case(const uint8_t *bytes, size_t n) {
    fprintf(out, "case f%lu\nregion 0 %zu\n", ncases++, n);
    for (size_t i = 0; i < n; i += 4096) {
        size_t m = n - i < 4096 ? n - i : 4096;
        fprintf(out, "hex 0 %zu ", i);
        for (size_t j = 0; j < m; j++) fprintf(out, "%02x", bytes[i + j]);
        fputc('\n', out);
    }
}

static void emit_run(const uint8_t *bytes, size_t n, uint64_t off, uint64_t len, uint64_t h0) {
    if (off <= n && len <= n - off) {
        uint64_t h = hk_fnv1a(bytes + off, (size_t)len, h0);
        if (h != spec_fnv1a(h0, bytes + off, (size_t)len)) {
            fprintf(stderr, "fnv_tests: CeTTa's hk_fnv1a and the format's fnv1a disagree\n");
            exit(1);
        }
        fprintf(out, "expect FIRED %" PRIu64 "\n", h);
        nfired++;
    } else {
        fprintf(out, "expect REFUSED 1\n");
        nrefused++;
    }
    fprintf(out, "run arg0=%" PRIu64 " arg1=%" PRIu64 " v1=%" PRIu64 "\n", off, len, h0);
    nruns++;
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) { fprintf(stderr, "usage: fnv_tests OUT.p1t [SEED [RANDOM]]\n"); return 2; }
    if (argc > 2) rng ^= strtoull(argv[2], NULL, 0) * 0x2545F4914F6CDD1Dull;
    unsigned long nrandom = argc > 3 ? strtoul(argv[3], NULL, 0) : 4000;
    out = fopen(argv[1], "w");
    if (!out) { perror(argv[1]); return 2; }
    fprintf(out, "# fnv: region 0 input; arg0 offset, arg1 length, v1 the initial state\n");
    const uint64_t basis = HOL_FNV_OFFSET;
    const uint64_t states[] = {basis, 0, UINT64_MAX, 1, 0x8000000000000000ull};
    static uint8_t b[1 << 20];

    /* The empty region: only the empty range at 0 is inside. */
    begin_case(b, 0);
    for (size_t s = 0; s < 5; s++) {
        emit_run(b, 0, 0, 0, states[s]);
        emit_run(b, 0, 0, 1, states[s]);
        emit_run(b, 0, 1, 0, states[s]);
        emit_run(b, 0, UINT64_MAX, 0, states[s]);
        emit_run(b, 0, 0, UINT64_MAX, states[s]);
    }

    /* holr.py's vector: "abc" and "bc" from the offset basis. */
    memcpy(b, "abcd", 4);
    begin_case(b, 4);
    emit_run(b, 4, 0, 3, basis);
    emit_run(b, 4, 1, 2, basis);
    emit_run(b, 4, 0, 4, basis);

    /* A small region: every range inside it, one byte past its end, and
     * offsets and lengths whose sum wraps. */
    for (size_t i = 0; i < 37; i++) b[i] = (uint8_t)(i * 151 + 7);
    begin_case(b, 37);
    for (uint64_t off = 0; off <= 38; off++)
        for (uint64_t len = 0; len + off <= 39; len++)
            emit_run(b, 37, off, len, states[(off + len) % 5]);
    const uint64_t big[] = {UINT64_MAX, UINT64_MAX - 1, (uint64_t)1 << 63, ((uint64_t)1 << 32) - 1,
                            (uint64_t)1 << 32, ((uint64_t)1 << 32) + 1};
    for (size_t q = 0; q < sizeof big / sizeof big[0]; q++) {
        emit_run(b, 37, big[q], 0, basis);
        emit_run(b, 37, big[q], 1, basis);
        emit_run(b, 37, 0, big[q], basis);
        emit_run(b, 37, 5, big[q], basis);
        emit_run(b, 37, big[q], big[q], basis);
        emit_run(b, 37, big[q], UINT64_MAX - big[q] + 1, basis);   /* off + len = 2^64 */
        emit_run(b, 37, 36, UINT64_MAX, basis);                     /* off + len wraps to 35 */
    }

    /* A whole 1 MiB region, and its halves. */
    for (size_t i = 0; i < sizeof b; i++) b[i] = (uint8_t)next();
    begin_case(b, sizeof b);
    emit_run(b, sizeof b, 0, sizeof b, basis);
    emit_run(b, sizeof b, 0, sizeof b / 2, basis);
    emit_run(b, sizeof b, sizeof b / 2, sizeof b / 2, UINT64_MAX);
    emit_run(b, sizeof b, 1, sizeof b, basis);

    /* Random regions and ranges, mostly inside. */
    for (unsigned long t = 0; t < nrandom; t++) {
        size_t n = next() % 300;
        for (size_t i = 0; i < n; i++) b[i] = (uint8_t)next();
        begin_case(b, n);
        for (unsigned q = 0; q < 6; q++) {
            uint64_t off = next() % (n + 2), len = next() % (n + 3);
            uint64_t h0 = next() % 3 == 0 ? states[next() % 5] : next();
            emit_run(b, n, off, len, h0);
        }
    }

    fclose(out);
    printf("fnv_tests: %lu cases, %lu runs: FIRED %lu, REFUSED 1 %lu; CeTTa's hk_fnv1a equals the format's fnv1a"
           " on every range inside\n", ncases, nruns, nfired, nrefused);
    return 0;
}
