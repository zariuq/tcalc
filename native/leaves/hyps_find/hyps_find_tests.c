/*
 * hyps_find_tests.c -- test descriptions for hyps_find (p1run's .p1t
 * format), each run with the outcome and ret_val an independent model of
 * pl_hyps_find_spec (tcalc/native/hol/plans_leaves.ml) gives.
 *
 * Regions: 0 rows, 1 slots, 2 header (an interned de Bruijn table, built
 * here with intern16's algorithm, so intern_ok holds), 3 term rows (40
 * bytes: tag, a, b, type, image), 4 term count, 5 marks, 6 operand stack,
 * 7 work (filled with junk). arg0 the first operand s, arg1 their number n.
 * The model, for ts the n operands from s:
 *   if every operand x has x < tc, mark x = 0 and type row 1, and the sorted
 *   list of their images (duplicates removed) is a list row of the table
 *   (a chain of cells (6, a, b) down to the nil row (5, 0, 0), found by
 *   searching the rows below the count, not by hashing)
 *   then FIRED with ret_val that row, else REFUSED.
 * Cases: tables of interned lists (small and large slot tables, full slot
 * tables with no empty slot, slots naming rows past the count), operand
 * lists for every list of the table in random order with repeats, subsets
 * and supersets, images past 2^61, dead, marked and non-bool terms, the
 * empty list with and without the nil row, operands near the stack's end.
 *
 *   hyps_find_tests OUT.p1t [SEED [RANDOM]]
 */
#include "../common/leaf_tests.h"

enum { MAXROWS = 4096, MAXSLOTS = 8192, MAXTERMS = 2048, MAXSTACK = 4096, WORKWORDS = 40 };
static const uint64_t GOLD = 11400714819323198485ull;
static const uint64_t TOP = (uint64_t)1 << 61;

static uint64_t rows[2 * MAXROWS], slots[MAXSLOTS], terms[5 * MAXTERMS], marks[MAXTERMS], stack[MAXSTACK];
static uint64_t count, nslots, nterms, nstack, rows_cap;

static uint64_t hash(uint64_t k0, uint64_t k1) {
    uint64_t h = (k0 ^ k1) * GOLD;
    return h ^ (h >> 29);
}

/* intern16's find-or-make (the tables the tests use are built by it). */
static uint64_t intern(uint64_t k0, uint64_t k1) {
    uint64_t h = hash(k0, k1), mask = nslots - 1;
    for (uint64_t d = 0; d < nslots; d++) {
        uint64_t pos = (h + d) & mask, e = slots[pos];
        if (e == 0) {
            if (count >= rows_cap) { fprintf(stderr, "hyps_find_tests: rows full\n"); exit(1); }
            rows[2 * count] = k0; rows[2 * count + 1] = k1; slots[pos] = count + 1;
            return count++;
        }
        uint64_t id = e - 1;
        if (id < count && rows[2 * id] == k0 && rows[2 * id + 1] == k1) return id;
    }
    fprintf(stderr, "hyps_find_tests: slots full\n");
    exit(1);
}

/* Intern the list of the given elements (sorted, distinct): cells from the
 * tail, the nil row first. Returns the list's row. */
static uint64_t intern_list(const uint64_t *el, size_t n) {
    uint64_t cur = intern(5, 0);
    for (size_t i = n; i-- > 0;) cur = intern(6 + 8 * el[i], cur);
    return cur;
}

/* The model's search: a row of key (k0, k1) below the count, by scanning. */
static int find_row(uint64_t k0, uint64_t k1, uint64_t *id) {
    for (uint64_t i = 0; i < count; i++)
        if (rows[2 * i] == k0 && rows[2 * i + 1] == k1) { *id = i; return 1; }
    return 0;
}

static int cmp_u64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return x < y ? -1 : x > y;
}

/* The specification, for operands s .. s + n - 1 of the stack. */
static int model(uint64_t s, uint64_t n, uint64_t *ret) {
    static uint64_t imgs[MAXSTACK];
    for (uint64_t j = 0; j < n; j++) {
        uint64_t x = stack[s + j];
        if (!(x < nterms) || marks[x] != 0 || terms[5 * x + 3] != 1) return 0;
        imgs[j] = terms[5 * x + 4];
    }
    qsort(imgs, n, sizeof imgs[0], cmp_u64);
    size_t m = 0;
    for (uint64_t j = 0; j < n; j++) if (m == 0 || imgs[m - 1] != imgs[j]) imgs[m++] = imgs[j];
    /* a list row of these elements, increasing: cells (6, a, b) as words
     * k0 = 6 + 8a (a < 2^61 for any row), k1 = b, down to the nil row */
    uint64_t cur;
    if (!find_row(5, 0, &cur)) return 0;
    for (size_t i = m; i-- > 0;) {
        if (imgs[i] >= TOP) return 0;
        if (!find_row(6 + 8 * imgs[i], cur, &cur)) return 0;
    }
    *ret = cur;
    return 1;
}

static void emit_case(uint64_t extra_stack) {
    leaf_case("hf", 0);
    leaf_region_words(0, 16 * rows_cap, rows, 2 * count);
    leaf_region_words(1, 8 * nslots, slots, nslots);
    fprintf(leaf_out, "region 2 8\nwords 2 0 %" PRIu64 "\n", count);
    leaf_region_words(3, 40 * nterms, terms, 5 * nterms);
    fprintf(leaf_out, "region 4 8\nwords 4 0 %" PRIu64 "\n", nterms);
    leaf_region_words(5, 8 * nterms, marks, nterms);
    leaf_region_words(6, 8 * nstack + extra_stack, stack, nstack);
    uint64_t work[WORKWORDS];
    for (int i = 0; i < WORKWORDS; i++) work[i] = leaf_next();
    leaf_region_words(7, 8 * WORKWORDS, work, WORKWORDS);
}

static void run(uint64_t s, uint64_t n) {
    uint64_t ret = 0;
    if (model(s, n, &ret)) leaf_expect(1, 1, ret);
    else leaf_expect(0, 0, 0);
    fprintf(leaf_out, "run arg0=%" PRIu64 " arg1=%" PRIu64 "\n", s, n);
}

/* A table: nlists lists of up to maxlen elements drawn from [0, universe),
 * interned, plus some other rows; terms with those elements as images. */
static uint64_t lists[64][16], lens[64], heads[64];
static size_t nlists;

static void build(uint64_t slotcount, size_t nl, size_t maxlen, uint64_t universe, int with_nil, int stale) {
    count = 0; nslots = slotcount; rows_cap = slotcount; memset(slots, 0, sizeof slots);
    nlists = nl;
    for (size_t l = 0; l < nl; l++) {
        size_t len = leaf_below(maxlen + 1);
        uint64_t tmp[16]; size_t m = 0;
        for (size_t i = 0; i < len; i++) tmp[m++] = leaf_below(universe);
        qsort(tmp, m, sizeof tmp[0], cmp_u64);
        size_t d = 0;
        for (size_t i = 0; i < m; i++) if (d == 0 || tmp[d - 1] != tmp[i]) tmp[d++] = tmp[i];
        memcpy(lists[l], tmp, d * sizeof tmp[0]); lens[l] = d;
    }
    if (with_nil)
        for (size_t l = 0; l < nl; l++) heads[l] = intern_list(lists[l], lens[l]);
    else
        for (size_t l = 0; l < nl; l++) heads[l] = (uint64_t)-1;
    /* other rows: type-like and term-like keys */
    size_t others = leaf_below(6);
    for (size_t i = 0; i < others && count + 1 < nslots; i++) intern(leaf_below(5) + 8 * leaf_below(universe), leaf_below(64));
    if (stale)   /* empty slots naming rows past the count */
        for (uint64_t p = 0; p < nslots; p++)
            if (slots[p] == 0 && leaf_below(3) == 0) slots[p] = count + 1 + leaf_below(1000);
    /* terms: images over the universe and a few others */
    nterms = 8 + leaf_below(40);
    for (uint64_t x = 0; x < nterms; x++) {
        uint64_t r = leaf_below(20);
        terms[5 * x] = leaf_below(4); terms[5 * x + 1] = leaf_next(); terms[5 * x + 2] = leaf_next();
        terms[5 * x + 3] = r == 0 ? 2 : r == 1 ? 0 : 1;
        terms[5 * x + 4] = r == 2 ? TOP + leaf_below(9) : r == 3 ? UINT64_MAX - leaf_below(3) : leaf_below(universe);
        marks[x] = leaf_below(25) == 0 ? 1 + leaf_below(3) : 0;
    }
}

/* Operands for the elements el[0..m): for each element a live bool term with
 * that image (made if missing), in random order with repeats. */
static size_t operands_for(const uint64_t *el, size_t m, uint64_t *ops) {
    size_t n = 0;
    for (size_t i = 0; i < m; i++) {
        uint64_t x = (uint64_t)-1;
        for (uint64_t y = 0; y < nterms; y++)
            if (terms[5 * y + 4] == el[i] && terms[5 * y + 3] == 1 && marks[y] == 0) { x = y; break; }
        if (x == (uint64_t)-1) {
            if (nterms >= MAXTERMS) continue;
            x = nterms++;
            terms[5 * x] = 0; terms[5 * x + 1] = 0; terms[5 * x + 2] = 0; terms[5 * x + 3] = 1;
            terms[5 * x + 4] = el[i]; marks[x] = 0;
        }
        size_t reps = 1 + (leaf_below(4) == 0 ? leaf_below(3) : 0);
        for (size_t r = 0; r < reps; r++) ops[n++] = x;
    }
    for (size_t i = n; i > 1; i--) { size_t j = leaf_below(i); uint64_t t = ops[i - 1]; ops[i - 1] = ops[j]; ops[j] = t; }
    return n;
}

static void lay_out(const uint64_t *ops, size_t n, uint64_t *s) {
    *s = leaf_below(5);
    nstack = *s + n + leaf_below(3);
    for (uint64_t i = 0; i < nstack; i++) stack[i] = leaf_below(nterms + 2);
    for (size_t j = 0; j < n; j++) stack[*s + j] = ops[j];
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) { fprintf(stderr, "usage: hyps_find_tests OUT.p1t [SEED [RANDOM]]\n"); return 2; }
    leaf_seed(argc > 2 ? argv[2] : NULL);
    unsigned long nrandom = argc > 3 ? strtoul(argv[3], NULL, 0) : 400;
    leaf_out = fopen(argv[1], "w");
    if (!leaf_out) { perror(argv[1]); return 2; }
    fprintf(leaf_out, "# hyps_find: regions rows slots header terms tcount marks stack work; arg0 s, arg1 n\n");
    static uint64_t ops[MAXSTACK];

    for (unsigned long t = 0; t < nrandom; t++) {
        int full = t % 7 == 3, with_nil = t % 11 != 5;
        uint64_t slotcount = full ? 16 : (uint64_t)1 << (6 + leaf_below(4));
        size_t nl = full ? 2 : 1 + leaf_below(6);
        size_t maxlen = full ? 3 : 1 + leaf_below(8);
        uint64_t universe = leaf_below(3) ? 12 : 1 + leaf_below(200);
        build(slotcount, nl, maxlen, universe, with_nil, !full && t % 5 == 1);
        if (full) {   /* fill every slot: a probe for an absent key visits all */
            while (count < nslots) intern(7 + 8 * (leaf_next() % 1000), leaf_next());
        }
        /* the operand lists of this table, each with its own stack */
        for (int q = 0; q < 6; q++) {
            uint64_t el[20]; size_t m = 0;
            size_t l = leaf_below(nlists);
            for (size_t i = 0; i < lens[l]; i++) el[m++] = lists[l][i];
            switch (q) {
            case 0: break;                                           /* the list itself */
            case 1: if (m) m--; break;                               /* a prefix */
            case 2: if (m) { el[0] = el[m - 1]; m = 1; } break;      /* one element */
            case 3: el[m++] = leaf_below(universe + 3); break;       /* one more (perhaps) */
            case 4: m = 0; break;                                    /* the empty list */
            default: if (m) el[leaf_below(m)] = TOP + leaf_below(3); break;   /* an image past 2^61 */
            }
            qsort(el, m, sizeof el[0], cmp_u64);
            size_t n = operands_for(el, m, ops);
            uint64_t s;
            lay_out(ops, n, &s);
            emit_case(leaf_below(2) ? 0 : 8 * leaf_below(4));
            run(s, n);
            if (n) {
                run(s + 1, n - 1);                                   /* one operand fewer */
                run(s, n - 1);
            }
            run(s, 0);
            /* a random window of the stack: dead, marked, non-bool operands */
            uint64_t a = leaf_below(nstack + 1), b = leaf_below(nstack - a + 1);
            run(a, b);
        }
    }

    fclose(leaf_out);
    leaf_summary("hyps_find_tests");
    return leaf_outcomes[0] && leaf_outcomes[1] ? 0 : 1;
}
