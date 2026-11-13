/*
 * leb128_tests.c -- test descriptions for leb128 (p1run's .p1t format), each
 * run with CeTTa's verdict on it.
 *
 *   leb128_tests OUT.p1t [SEED [RANDOM]]
 *
 * The oracle is CeTTa's reader itself: cur_uv and its helpers, as the text of
 * hol_stream.c, extracted by check.sh into cetta_oracle.h (compiled with
 * CeTTa's hol_kernel.h). For the bytes from the offset to the input's end
 * (final = false), cur_uv's value and consumed length become FIRED VALUE with
 * out = (VALUE, LENGTH); its integer error becomes REFUSED 1; its need for
 * input becomes REFUSED 2. An offset past the end has no bytes: REFUSED 2.
 *
 * Every verdict is also checked here against the format's own definition
 * (holr_spec.ml): FIRED iff the bytes begin with leb_enc v for some v < 2^62;
 * REFUSED 2 iff they are a proper prefix of such an encoding; REFUSED 1
 * otherwise. A disagreement stops the generator with status 1.
 *
 * Cases: every byte string of lengths 0..2; every value at each length
 * boundary (2^(7k) - 1, 2^(7k), and neighbours), 2^62 - 1, 2^62, 2^63 - 1 and
 * 2^64 - 1, each encoded, in non-minimal forms (padded with 0x80 .. 0x00), cut
 * at every length, and followed by other bytes; nine and ten continuation
 * bytes; offsets at and past the end, up to 2^64 - 1; and RANDOM random
 * regions with bytes drawn toward the interesting ones.
 */
#include "cetta_oracle.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t rng = 0x9E3779B97F4A7C15ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static FILE *out;
static unsigned long ncases, nruns, nfired, nbad, nshort;

/* leb_enc, as holr_spec.ml defines it, for any 64-bit value. */
static size_t leb_enc(uint64_t v, uint8_t *b) {
    size_t n = 0;
    while (v >= 128) { b[n++] = (uint8_t)(v % 128 + 128); v /= 128; }
    b[n++] = (uint8_t)v;
    return n;
}

/* The format's verdict on the bytes c[0..n): 0 FIRED (value, length),
 * 1 malformed, 2 the input ends first. A value v < 2^62 has at most nine
 * bytes, all but the last with the high bit, so the encoding a prefix could
 * be is fixed by its first byte without the high bit. */
static int spec_verdict(const uint8_t *c, size_t n, uint64_t *value, size_t *len) {
    /* FIRED: some v < 2^62 with leb_enc v a prefix of c; decode the candidate
     * the high bits delimit, then compare its encoding byte for byte. */
    size_t k = 0;
    while (k < n && k < 9 && c[k] >= 128) k++;
    if (k < n && k < 9) {
        unsigned __int128 v = 0;
        for (size_t j = 0; j <= k; j++) v += (unsigned __int128)(c[j] & 127) << (7 * j);
        if (v < ((unsigned __int128)1 << 62)) {
            uint8_t e[16];
            size_t m = leb_enc((uint64_t)v, e);
            if (m == k + 1 && !memcmp(e, c, m)) { *value = (uint64_t)v; *len = m; return 0; }
        }
        return 1;
    }
    /* No byte without the high bit among the first min(n, 9). A proper prefix
     * of an encoding: n <= 8 bytes, all with the high bit (append 1: a
     * minimal encoding of at most nine bytes, below 2^57). */
    if (n <= 8) return 2;
    return 1;
}

/* CeTTa's verdict, through cur_uv. */
static int cetta_verdict(const uint8_t *c, size_t n, uint64_t *value, size_t *len) {
    Cur cur = {0};
    cur.p = c; cur.end = c + n; cur.final = false;
    uint64_t v = cur_uv(&cur);
    if (cur.err == 0) { *value = v; *len = (size_t)(cur.p - c); return 0; }
    if (cur.err == 1) return 2;
    if (cur.err == 2 && cur.why == HOL_R_STREAM_INTEGER) return 1;
    fprintf(stderr, "leb128_tests: cur_uv ended with err %d, reason %d\n", cur.err, (int)cur.why);
    exit(2);
}

/* One region, and runs at the given offsets. */
static void emit_case(const uint8_t *bytes, size_t n, const uint64_t *offs, size_t noffs) {
    fprintf(out, "case c%lu\nregion 0 %zu\nregion 1 16\n", ncases++, n);
    if (n) {
        fprintf(out, "hex 0 0 ");
        for (size_t i = 0; i < n; i++) fprintf(out, "%02x", bytes[i]);
        fputc('\n', out);
    }
    for (size_t q = 0; q < noffs; q++) {
        uint64_t off = offs[q], v = 0, sv = 0;
        size_t len = 0, slen = 0;
        int verdict, spec;
        if (off > n) verdict = spec = 2;
        else {
            verdict = cetta_verdict(bytes + off, n - (size_t)off, &v, &len);
            spec = spec_verdict(bytes + off, n - (size_t)off, &sv, &slen);
        }
        if (verdict != spec || (verdict == 0 && (v != sv || len != slen))) {
            fprintf(stderr, "leb128_tests: CeTTa and the format disagree at case c%lu offset %" PRIu64
                    ": %d %" PRIu64 "/%zu vs %d %" PRIu64 "/%zu\n", ncases - 1, off, verdict, v, len, spec, sv, slen);
            exit(1);
        }
        if (verdict == 0) {
            fprintf(out, "expect FIRED %" PRIu64 "\nwant 1 0 %" PRIu64 "\nwant 1 8 %zu\n", v, v, len);
            nfired++;
        } else {
            fprintf(out, "expect REFUSED %d\nwant 1 0 0\nwant 1 8 0\n", verdict);
            if (verdict == 1) nbad++; else nshort++;
        }
        fprintf(out, "run arg0=%" PRIu64 "\n", off);
        nruns++;
    }
}

static void emit_at0(const uint8_t *bytes, size_t n) {
    uint64_t off = 0;
    emit_case(bytes, n, &off, 1);
}

/* The bytes, then every cut of them, each alone in its region. */
static void emit_cuts(const uint8_t *bytes, size_t n) {
    for (size_t k = 0; k <= n; k++) emit_at0(bytes, k);
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) { fprintf(stderr, "usage: leb128_tests OUT.p1t [SEED [RANDOM]]\n"); return 2; }
    if (argc > 2) rng ^= strtoull(argv[2], NULL, 0) * 0x2545F4914F6CDD1Dull;
    unsigned long nrandom = argc > 3 ? strtoul(argv[3], NULL, 0) : 20000;
    out = fopen(argv[1], "w");
    if (!out) { perror(argv[1]); return 2; }
    fprintf(out, "# leb128: regions 0 input, 1 out; arg0 the offset; CeTTa's cur_uv verdicts\n");
    uint8_t b[64] = {0};

    /* Every byte string of lengths 0..2, at offset 0. */
    emit_at0(b, 0);
    for (unsigned x = 0; x < 256; x++) { b[0] = (uint8_t)x; emit_at0(b, 1); }
    for (unsigned x = 0; x < 65536; x++) { b[0] = (uint8_t)(x >> 8); b[1] = (uint8_t)x; emit_at0(b, 2); }

    /* Values at the boundaries, encoded (up to ten bytes), each cut at every
     * length and followed by other bytes. */
    for (unsigned k = 0; k <= 9; k++) {
        uint64_t base = k == 9 ? (uint64_t)1 << 63 : (uint64_t)1 << (7 * k);
        uint64_t vs[] = {base - 2, base - 1, base, base + 1, base | (base >> 1), base * 2 - 1};
        for (size_t q = 0; q < sizeof vs / sizeof vs[0]; q++) {
            size_t n = leb_enc(vs[q], b);
            emit_cuts(b, n);
            b[n] = 0x7f; b[n + 1] = 0x80; emit_at0(b, n + 2);
        }
    }
    uint64_t special[] = {((uint64_t)1 << 62) - 1, (uint64_t)1 << 62, ((uint64_t)1 << 62) + 1,
                          ((uint64_t)1 << 63) - 1, (uint64_t)1 << 63, UINT64_MAX, 0, 1, 127, 128, 300};
    for (size_t q = 0; q < sizeof special / sizeof special[0]; q++) {
        size_t n = leb_enc(special[q], b);
        emit_cuts(b, n);
    }

    /* Non-minimal forms: a value's encoding with its last byte's high bit set,
     * then 0x80 ... and a final 0x00, total length up to 10. */
    for (unsigned k = 1; k <= 9; k++)
        for (uint64_t v = 0; v < 300; v += 37) {
            size_t n = leb_enc(v, b);
            if (n > k) continue;
            b[n - 1] |= 0x80;
            for (size_t j = n; j < k; j++) b[j] = 0x80;
            b[k] = 0x00;
            emit_cuts(b, k + 1);
        }

    /* Nine and ten continuation bytes, with and without a final byte. */
    for (unsigned k = 8; k <= 11; k++) {
        for (size_t j = 0; j < k; j++) b[j] = 0x80 | (uint8_t)(j * 29);
        b[k] = 0x01;
        emit_cuts(b, k + 1);
    }

    /* Offsets inside, at and past the end, on one region. */
    {
        uint8_t r[] = {0x05, 0x96, 0x01, 0xff, 0xff, 0x03, 0x80, 0x00, 0x80, 0x80};
        uint64_t offs[] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 4096, (uint64_t)1 << 32,
                           ((uint64_t)1 << 63) + 3, UINT64_MAX - 1, UINT64_MAX};
        emit_case(r, sizeof r, offs, sizeof offs / sizeof offs[0]);
        emit_case(r, 0, offs, sizeof offs / sizeof offs[0]);
    }

    /* Random regions: bytes drawn toward 0x00, 0x7f, 0x80, 0xff and the high
     * bit; offsets anywhere in the region and a little past it. */
    static const uint8_t pick[] = {0x00, 0x01, 0x3f, 0x40, 0x7f, 0x80, 0x81, 0xc0, 0xff};
    for (unsigned long t = 0; t < nrandom; t++) {
        size_t n = next() % 24;
        for (size_t i = 0; i < n; i++) {
            uint64_t r = next() % 8;
            b[i] = r < 3 ? pick[next() % 9] : r < 6 ? (uint8_t)(0x80 | next()) : (uint8_t)next();
        }
        uint64_t offs[4];
        for (unsigned q = 0; q < 4; q++) offs[q] = next() % (n + 3);
        emit_case(b, n, offs, 4);
    }

    fclose(out);
    printf("leb128_tests: %lu cases, %lu runs: FIRED %lu, REFUSED 1 (malformed) %lu, REFUSED 2 (input ends) %lu;"
           " CeTTa's verdicts equal the format's on every run\n", ncases, nruns, nfired, nbad, nshort);
    return 0;
}
