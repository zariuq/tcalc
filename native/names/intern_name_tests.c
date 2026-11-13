/*
 * intern_name_tests.c -- test descriptions for intern_name (p1run's .p1t
 * format), each run with the outcome the specification gives it.
 *
 *   intern_name_tests DIFF.p1t CHAIN.p1t [SEED [RANDOM]]
 *
 * The expectations come from a model written here from the specification
 * (intern_name.metta's header), not from the program: the name is the arg1
 * bytes of region 0 from offset arg0; the header holds the row count and
 * the arena bytes used; probing starts at the hash in v1. Outcome and
 * ret_val are expected for every run, and after every run of a small store
 * every word of every region is wanted (p1run also compares the reference
 * evaluator's regions with the native code's, byte for byte).
 *
 * DIFF.p1t, one state per case, every run from it:
 *  - names against the input's end: inside, at the end, past it, offsets and
 *    lengths up to 2^64 - 1 (REFUSED 1);
 *  - header words above their regions (UNSUPPORTED 5);
 *  - adversarial tables: stale slots (ids at and above the count, slot
 *    values up to 2^64 - 1), rows of the name's length lying outside the
 *    used arena (UNSUPPORTED 6), rows of other lengths, duplicate slots;
 *  - full regions: rows (UNSUPPORTED 1), arena (UNSUPPORTED 4), every slot
 *    used (UNSUPPORTED 3);
 *  - zero-length names; names whose hashes collide (one hash for every
 *    name, and small tables);
 *  - regions below the declared minimums (INVALID, entry validation);
 *  - RANDOM random stores, corrupted and clean.
 * CHAIN.p1t, chained runs on clean stores with FNV-1a 64 hashes: a pool of
 * names (zero-length, one byte, prefixes of each other, equal bytes at
 * different offsets) interned in rounds; the first sight of a name appends
 * the next id, every later one returns it, and the rows, arena and header
 * end as the model's.
 */
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { REFUSED = 0, FIRED = 1, UNSUPPORTED = 2, INVALID = 3 };
static const char *oname[] = {"REFUSED", "FIRED", "UNSUPPORTED", "INVALID"};
#define CAP 4294967295ull

static uint64_t rng = 0x6A09E667F3BCC909ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

enum { MAXB = 4096 };
typedef struct {
    size_t len[5];        /* region lengths: 0 input, 1 rows, 2 arena, 3 table, 4 header */
    uint8_t b[5][MAXB];   /* region bytes */
} Store;

static uint64_t rd64(const Store *s, int r, uint64_t off) {
    uint64_t v = 0;
    for (int k = 0; k < 8; k++) v |= (uint64_t)s->b[r][off + k] << (8 * k);
    return v;
}
static void wr64(Store *s, int r, uint64_t off, uint64_t v) {
    for (int k = 0; k < 8; k++) s->b[r][off + k] = (uint8_t)(v >> (8 * k));
}

static uint64_t fnv1a(const uint8_t *p, size_t n) {
    uint64_t h = 14695981039346656037ull;
    for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 1099511628211ull; }
    return h;
}

/* The specification, run on s. Returns the outcome; *ret its ret_val. */
static int model(Store *s, uint64_t off, uint64_t n, uint64_t hash, uint64_t *ret) {
    if (s->len[1] < 16 || s->len[2] < 1 || s->len[3] < 8 || s->len[4] < 16) { *ret = 3; return INVALID; }
    uint64_t ilen = s->len[0], alen = s->len[2];
    if (off > ilen || n > ilen - off) { *ret = 1; return REFUSED; }
    uint64_t count = rd64(s, 4, 0), used = rd64(s, 4, 8), rowcap = s->len[1] / 16;
    if (count > rowcap || used > alen) { *ret = 5; return UNSUPPORTED; }
    uint64_t slots = s->len[3] / 8;
    if (slots > CAP) { *ret = 2; return UNSUPPORTED; }
    for (uint64_t x = 0; x < slots; x++) {
        uint64_t p = (hash + x) & (slots - 1);
        uint64_t e = rd64(s, 3, 8 * p);
        if (e == 0) {
            if (count >= rowcap) { *ret = 1; return UNSUPPORTED; }
            if (alen - used < n) { *ret = 4; return UNSUPPORTED; }
            if (n > CAP) { *ret = 2; return UNSUPPORTED; }
            memcpy(s->b[2] + used, s->b[0] + off, n);
            wr64(s, 1, 16 * count, used); wr64(s, 1, 16 * count + 8, n);
            wr64(s, 3, 8 * p, count + 1);
            wr64(s, 4, 0, count + 1); wr64(s, 4, 8, used + n);
            *ret = count; return FIRED;
        }
        uint64_t id = e - 1;
        if (id < count && rd64(s, 1, 16 * id + 8) == n) {
            uint64_t roff = rd64(s, 1, 16 * id);
            if (used < roff || used - roff < n) { *ret = 6; return UNSUPPORTED; }
            if (n > CAP) { *ret = 2; return UNSUPPORTED; }
            if (memcmp(s->b[2] + roff, s->b[0] + off, n) == 0) { *ret = id; return FIRED; }
        }
    }
    *ret = 3; return UNSUPPORTED;
}

static FILE *out;
static unsigned long ncases, nruns, nout[4], nwants;

static void emit_region(const Store *s, int r) {
    fprintf(out, "region %d %zu\n", r, s->len[r]);
    size_t n = s->len[r], k = 0;
    while (k < n && !s->b[r][k]) k++;
    if (k == n) return;
    fprintf(out, "hex %d 0 ", r);
    for (size_t i = 0; i < n; i++) fprintf(out, "%02x", s->b[r][i]);
    fputc('\n', out);
}

/* Want every whole word of regions 1..4 (at most 64), or, for a larger
 * store, the header, the rows and slots the run may write, and the arena
 * words around the bytes used. */
static void emit_wants(const Store *after) {
    size_t words = 0;
    for (int r = 1; r <= 4; r++) words += after->len[r] / 8;
    if (words <= 64) {
        for (int r = 1; r <= 4; r++)
            for (size_t o = 0; o + 8 <= after->len[r]; o += 8) {
                fprintf(out, "want %d %zu %" PRIu64 "\n", r, o, rd64(after, r, o)); nwants++;
            }
        return;
    }
    size_t k = 0;
    for (size_t o = 0; o + 8 <= after->len[4] && k < 4; o += 8, k++) {
        fprintf(out, "want 4 %zu %" PRIu64 "\n", o, rd64(after, 4, o)); nwants++;
    }
}

/* One run from the case's state: its expectations from the model. */
static void emit_run(const Store *s, uint64_t off, uint64_t n, uint64_t hash, bool all_words) {
    Store after = *s;
    uint64_t ret;
    int o = model(&after, off, n, hash, &ret);
    fprintf(out, "expect %s %" PRIu64 "\n", oname[o], ret);
    if (o != INVALID) {
        if (all_words) emit_wants(&after);
        if (o != FIRED && memcmp(&after, s, sizeof after)) { fprintf(stderr, "model wrote on a stop\n"); exit(1); }
    }
    fprintf(out, "run arg0=%" PRIu64 " arg1=%" PRIu64 " v1=%" PRIu64 "\n", off, n, hash);
    nruns++; nout[o]++;
}

static void begin_case(const Store *s, const char *tag) {
    fprintf(out, "case %s%lu\n", tag, ncases++);
    for (int r = 0; r < 5; r++) emit_region(s, r);
}

static void clear(Store *s, size_t ilen, size_t rows, size_t alen, size_t slots, size_t hlen) {
    memset(s, 0, sizeof *s);
    s->len[0] = ilen; s->len[1] = rows; s->len[2] = alen; s->len[3] = slots; s->len[4] = hlen;
}

/* A clean store holding the names given as (offset, length) of the input,
 * interned in order with their FNV-1a hashes. */
static void intern_all(Store *s, const uint64_t (*names)[2], size_t k) {
    for (size_t q = 0; q < k; q++) {
        uint64_t ret;
        model(s, names[q][0], names[q][1], fnv1a(s->b[0] + names[q][0], names[q][1]), &ret);
    }
}

static void fill_input(Store *s, const char *text) {
    size_t n = strlen(text);
    memcpy(s->b[0], text, n);
    s->len[0] = n;
}

int main(int argc, char **argv) {
    if (argc < 3 || argc > 5) { fprintf(stderr, "usage: intern_name_tests DIFF.p1t CHAIN.p1t [SEED [RANDOM]]\n"); return 2; }
    if (argc > 3) rng ^= strtoull(argv[3], NULL, 0) * 0x2545F4914F6CDD1Dull;
    unsigned long nrandom = argc > 4 ? strtoul(argv[4], NULL, 0) : 6000;
    out = fopen(argv[1], "w");
    if (!out) { perror(argv[1]); return 2; }
    fprintf(out, "# intern_name: regions 0 input, 1 rows, 2 arena, 3 table, 4 header; arg0/arg1 the name; v1 its hash\n");
    Store s;

    /* Names against the input's end, on an empty store and a store with rows. */
    {
        static const uint64_t names[][2] = {{0, 3}, {3, 4}, {7, 0}, {0, 7}};
        for (int full = 0; full < 2; full++) {
            clear(&s, 0, 64, 64, 64, 16);
            fill_input(&s, "abcdefgh");
            if (full) intern_all(&s, names, 4);
            begin_case(&s, "range");
            uint64_t offs[] = {0, 1, 7, 8, 9, 4096, (uint64_t)1 << 63, UINT64_MAX};
            uint64_t lens[] = {0, 1, 2, 7, 8, 9, (uint64_t)1 << 63, UINT64_MAX - 3, UINT64_MAX};
            for (size_t a = 0; a < sizeof offs / sizeof offs[0]; a++)
                for (size_t b = 0; b < sizeof lens / sizeof lens[0]; b++)
                    emit_run(&s, offs[a], lens[b], offs[a] <= 8 && lens[b] <= 8 - offs[a]
                             ? fnv1a(s.b[0] + offs[a], lens[b]) : next(), true);
        }
    }

    /* Header words above their regions' capacities. */
    {
        uint64_t counts[] = {0, 3, 4, 5, 1000, UINT64_MAX}, useds[] = {0, 31, 32, 33, UINT64_MAX};
        for (size_t a = 0; a < 6; a++)
            for (size_t b = 0; b < 5; b++) {
                clear(&s, 0, 64, 32, 32, 16);
                fill_input(&s, "header");
                wr64(&s, 4, 0, counts[a]); wr64(&s, 4, 8, useds[b]);
                begin_case(&s, "hdr");
                emit_run(&s, 0, 3, fnv1a(s.b[0], 3), true);
                emit_run(&s, 1, 0, 0, true);
            }
    }

    /* Regions below the declared minimums: entry validation refuses them. */
    {
        size_t bad[][4] = {{8, 8, 8, 16}, {16, 0, 8, 16}, {16, 8, 0, 16}, {16, 8, 4, 16}, {16, 8, 8, 8}, {0, 0, 0, 0}};
        for (size_t q = 0; q < 6; q++) {
            clear(&s, 0, bad[q][0], bad[q][1], bad[q][2], bad[q][3]);
            fill_input(&s, "x");
            begin_case(&s, "entry");
            emit_run(&s, 0, 1, fnv1a(s.b[0], 1), false);
        }
    }

    /* Full regions. Rows: a store whose rows region holds exactly the rows
     * interned; arena: the bytes used reach the arena's end; table: every
     * slot used by other names. */
    {
        static const uint64_t names[][2] = {{0, 2}, {2, 2}, {4, 2}};
        clear(&s, 0, 48, 64, 64, 16);
        fill_input(&s, "aabbccdd");
        intern_all(&s, names, 3);
        begin_case(&s, "rowsfull");
        emit_run(&s, 6, 2, fnv1a(s.b[0] + 6, 2), true);   /* new: rows full */
        emit_run(&s, 2, 2, fnv1a(s.b[0] + 2, 2), true);   /* present: found */
        emit_run(&s, 6, 0, fnv1a(s.b[0] + 6, 0), true);   /* new, empty: rows full */

        clear(&s, 0, 96, 6, 64, 16);
        fill_input(&s, "aabbccdd");
        intern_all(&s, names, 3);
        begin_case(&s, "arenafull");
        emit_run(&s, 6, 2, fnv1a(s.b[0] + 6, 2), true);   /* new: arena full */
        emit_run(&s, 0, 2, fnv1a(s.b[0], 2), true);       /* present: found */
        emit_run(&s, 6, 0, fnv1a(s.b[0] + 6, 0), true);   /* empty name: fits */
        emit_run(&s, 6, 1, fnv1a(s.b[0] + 6, 1), true);   /* new: arena full */

        static const uint64_t four[][2] = {{0, 1}, {1, 1}, {2, 1}, {3, 1}};
        clear(&s, 0, 96, 64, 32, 16);
        fill_input(&s, "abcdefgh");
        intern_all(&s, four, 4);
        begin_case(&s, "tablefull");
        for (uint64_t q = 0; q < 8; q++) emit_run(&s, q, 1, fnv1a(s.b[0] + q, 1), true);
        emit_run(&s, 0, 2, fnv1a(s.b[0], 2), true);
    }

    /* Adversarial tables on a clean store of three names: stale slots (ids
     * at and above the count), slot values up to 2^64 - 1, a row of the
     * name's length outside the used arena, duplicate slots. */
    {
        static const uint64_t names[][2] = {{0, 3}, {3, 3}, {6, 2}};
        uint64_t slotvals[] = {1, 2, 3, 4, 5, 6, 100, (uint64_t)1 << 63, UINT64_MAX, UINT64_MAX - 1};
        for (size_t q = 0; q < sizeof slotvals / sizeof slotvals[0]; q++)
            for (uint64_t pos = 0; pos < 8; pos++) {
                clear(&s, 0, 80, 32, 64, 16);
                fill_input(&s, "foobarbazfoo");
                intern_all(&s, names, 3);
                wr64(&s, 3, 8 * pos, slotvals[q]);
                begin_case(&s, "stale");
                emit_run(&s, 9, 3, pos, true);                       /* "foo" again, probing from pos */
                emit_run(&s, 0, 3, pos, true);
                emit_run(&s, 3, 3, fnv1a(s.b[0] + 3, 3), true);
                emit_run(&s, 1, 2, pos, true);                       /* a new name */
            }
        /* A row of the name's length whose bytes lie outside the used arena. */
        uint64_t roffs[] = {0, 5, 6, 7, 8, 31, 32, 33, UINT64_MAX};
        for (size_t q = 0; q < sizeof roffs / sizeof roffs[0]; q++) {
            clear(&s, 0, 80, 32, 64, 16);
            fill_input(&s, "foobarbazfoo");
            intern_all(&s, names, 3);
            wr64(&s, 1, 16 * 1, roffs[q]);
            begin_case(&s, "badrow");
            emit_run(&s, 3, 3, fnv1a(s.b[0] + 3, 3), true);
            emit_run(&s, 9, 3, fnv1a(s.b[0] + 9, 3), true);
            emit_run(&s, 4, 3, fnv1a(s.b[0] + 3, 3), true);      /* "arb" with bar's hash */
        }
    }

    /* Hashes that collide: every name with one hash, in tables of 1..9 slots. */
    for (size_t slots = 1; slots <= 9; slots++)
        for (uint64_t h = 0; h < 3; h++) {
            clear(&s, 0, 160, 64, 8 * slots, 16);
            fill_input(&s, "abcabcabcxyz");
            begin_case(&s, "collide");
            static const uint64_t probes[][2] = {{0, 3}, {3, 3}, {1, 2}, {9, 3}, {0, 0}, {2, 1}, {5, 1}, {9, 1}};
            Store cur = s;
            for (size_t q = 0; q < 8; q++) {
                emit_run(&cur, probes[q][0], probes[q][1], h * 0x9E3779B97F4A7C15ull, true);
                uint64_t ret;
                model(&cur, probes[q][0], probes[q][1], h * 0x9E3779B97F4A7C15ull, &ret);
                /* the next run of the case starts from the case's state again, so
                 * re-emit the evolved store as its own case */
                begin_case(&cur, "collide");
            }
            emit_run(&cur, 0, 3, h, true);
        }

    /* Random stores: rows, arena, table and header drawn small, corrupted
     * at times (counts above the rows, used above the arena, slots naming
     * any id, rows anywhere); names drawn from the input or from the arena's
     * own rows, with their hashes or random ones. */
    for (unsigned long t = 0; t < nrandom; t++) {
        size_t ilen = next() % 24, nrows = 1 + next() % 6, alen = 1 + next() % 48, nslots = 1 + next() % 8;
        clear(&s, ilen, 16 * nrows + (next() % 4 == 0 ? 8 : 0), alen, 8 * nslots + (next() % 4 == 0 ? 4 : 0),
              16 + (next() % 4 == 0 ? 8 : 0));
        for (size_t i = 0; i < ilen; i++) s.b[0][i] = (uint8_t)("ab\0\377"[next() % 4]);
        bool corrupt = next() % 3 == 0;
        if (!corrupt) {
            /* a clean store: intern a few names */
            uint64_t k = next() % (nrows + 1);
            for (uint64_t q = 0; q < k; q++) {
                uint64_t o = ilen ? next() % (ilen + 1) : 0, n = next() % (ilen - o + 1);
                uint64_t ret;
                model(&s, o, n, fnv1a(s.b[0] + o, n), &ret);
            }
        } else {
            for (size_t i = 0; i < s.len[1]; i += 8) {
                uint64_t r = next() % 6;
                wr64(&s, 1, i, r == 0 ? next() : next() % (alen + 3));
            }
            for (size_t i = 0; i < alen; i++) s.b[2][i] = (uint8_t)("ab\0\377"[next() % 4]);
            for (size_t i = 0; i + 8 <= s.len[3]; i += 8) {
                uint64_t r = next() % 5;
                wr64(&s, 3, i, r == 0 ? 0 : r == 1 ? next() : 1 + next() % (nrows + 3));
            }
            wr64(&s, 4, 0, next() % (nrows + 3));
            wr64(&s, 4, 8, next() % (alen + 4));
        }
        begin_case(&s, "rand");
        for (int q = 0; q < 4; q++) {
            uint64_t o, n, h, r = next() % 6;
            if (r == 0) { o = next() % (ilen + 3); n = next() % 5; }
            else { o = ilen ? next() % (ilen + 1) : 0; n = next() % (ilen - o + 1); }
            h = (r == 1 || o > ilen || n > ilen - o) ? next() % 16 : fnv1a(s.b[0] + o, n);
            emit_run(&s, o, n, h, true);
        }
    }
    fclose(out);
    fprintf(stderr, "intern_name_tests: DIFF %lu cases, %lu runs (REFUSED %lu, FIRED %lu, UNSUPPORTED %lu, INVALID %lu), %lu wants\n",
            ncases, nruns, nout[0], nout[1], nout[2], nout[3], nwants);

    /* CHAIN.p1t: interning in rounds on clean stores, chained. */
    out = fopen(argv[2], "w");
    if (!out) { perror(argv[2]); return 2; }
    fprintf(out, "# intern_name: chained interning with FNV-1a 64 hashes\n");
    ncases = nruns = nwants = 0; memset(nout, 0, sizeof nout);
    static const char *texts[] = {
        "x", "", "a", "ab", "abc", "abcd", "ba", "foo", "bar", "foobar", "oo",
        "=", "bool", "fun", "ind", "T", "F", "!", "?", "/\\", "\\/", "==>", "~",
        "@", "ONE_ONE", "ONTO", "IND_SUC", "IND_0", "NUM_REP", "_0", "SUC_REP",
        "a_very_long_name_with_many_bytes_to_copy_and_compare_0123456789", "ab\377", "\377\377"};
    size_t ntexts = sizeof texts / sizeof texts[0];
    for (int variant = 0; variant < 4; variant++) {
        Store st;
        size_t slots = variant == 0 ? 64 : variant == 1 ? 8 : variant == 2 ? 50 : 128;
        clear(&st, 0, 16 * 64, 2048, 8 * slots, 16);
        /* the input: every text twice, at different offsets */
        size_t at = 0, offs[2][64];
        for (int copy = 0; copy < 2; copy++)
            for (size_t q = 0; q < ntexts; q++) {
                size_t n = strlen(texts[q]);
                offs[copy][q] = at;
                memcpy(st.b[0] + at, texts[q], n);
                at += n + copy;                     /* the second copy is spaced by one byte */
            }
        st.len[0] = at;
        fprintf(out, "case chain%d chain\n", variant);
        for (int r = 0; r < 5; r++) emit_region(&st, r);
        uint64_t seen = 0;
        for (int round = 0; round < 3; round++)
            for (size_t q = 0; q < ntexts && (slots > 8 || q < 8); q++) {
                size_t n = strlen(texts[q]);
                int copy = (round + (int)q) % 2;
                uint64_t off = offs[copy][q], h = fnv1a(st.b[0] + off, n), ret;
                Store before = st;
                int o = model(&st, off, n, h, &ret);
                fprintf(out, "expect %s %" PRIu64 "\n", oname[o], ret);
                if (round == 0 && o == FIRED && ret != seen++) { fprintf(stderr, "chain: id %" PRIu64 " out of order\n", ret); return 1; }
                if (round > 0 && o == FIRED && memcmp(&before, &st, sizeof st)) { fprintf(stderr, "chain: a known name appended\n"); return 1; }
                fprintf(out, "want 4 0 %" PRIu64 "\nwant 4 8 %" PRIu64 "\n", rd64(&st, 4, 0), rd64(&st, 4, 8));
                if (o == FIRED) fprintf(out, "want 1 %" PRIu64 " %" PRIu64 "\nwant 1 %" PRIu64 " %" PRIu64 "\n",
                                        16 * ret, rd64(&st, 1, 16 * ret), 16 * ret + 8, rd64(&st, 1, 16 * ret + 8));
                fprintf(out, "run arg0=%" PRIu64 " arg1=%zu v1=%" PRIu64 "\n", off, n, h);
                nruns++; nout[o]++; nwants += o == FIRED ? 4 : 2;
            }
        /* the arena, word by word, at the end */
        fprintf(out, "expect FIRED 0\n");
        for (size_t w = 0; w + 8 <= rd64(&st, 4, 8) && w < 8 * 60; w += 8) { fprintf(out, "want 2 %zu %" PRIu64 "\n", w, rd64(&st, 2, w)); nwants++; }
        fprintf(out, "run arg0=%zu arg1=1 v1=%" PRIu64 "\n", offs[0][0], fnv1a(st.b[0] + offs[0][0], 1));
        nruns++; nout[FIRED]++;
        ncases++;
    }
    fclose(out);
    fprintf(stderr, "intern_name_tests: CHAIN %lu cases, %lu runs (REFUSED %lu, FIRED %lu, UNSUPPORTED %lu, INVALID %lu), %lu wants\n",
            ncases, nruns, nout[0], nout[1], nout[2], nout[3], nwants);
    return 0;
}
