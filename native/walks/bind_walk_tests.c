/*
 * bind_walk_tests.c -- test descriptions for bind_walk (p1run's .p1t
 * format), each run with the outcome, return value and words a model gives
 * it, and every model run checked against the specification.
 *
 *   bind_walk_tests DIFF.p1t CHAIN.p1t [SEED [RANDOM]]
 *
 * Two models, both written here:
 *  - the algorithm (walk_model): bind_walk.metta's steps on the same bytes,
 *    so that p1run can compare the reference evaluator and the native code
 *    with it (outcome, ret_val, wanted words);
 *  - the specification (check_spec): the rows below a count decoded to
 *    hash-consed trees, hbind on the trees, intern16's table invariant.
 *    Every model run must satisfy it: FIRED returns a row that decodes, in
 *    the rows below the new count, to dbAbs ty (hbind (x,ty) 0 t) whenever
 *    t decodes in the rows below the old count; rows below the old count
 *    are unchanged; any other outcome leaves the header word unchanged;
 *    and a run from a state whose table invariant holds leaves it holding.
 *    A violation stops the generator (exit 3).
 *
 * DIFF.p1t, one state per case, every run from it:
 *  - random de Bruijn DAGs, interned canonically: variables at many depths,
 *    shared subterms, deep nesting (abstraction chains, comb spines), terms
 *    without the variable, the variable at depth 0 only;
 *  - adversarial work regions: random bytes; memo slots naming plausible
 *    log positions; log entries holding real keys with wrong results;
 *  - adversarial rows and tables: garbage above the count, stale slots,
 *    rows whose children lie above the count or wrap the address;
 *  - list rows reached as terms (UNSUPPORTED 9);
 *  - full regions: rows (16), table (14), task stack (10), results (15);
 *  - bad inputs: count above capacity (1), t not below the count (2),
 *    x or ty not below 2^60 (3);
 *  - regions below the declared minimums (INVALID).
 * CHAIN.p1t, chained runs: walks over a growing store, each continuing from
 * the state the last left; the model's store follows, and the table's
 * invariant is checked after every run.
 */
#include <inttypes.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { REFUSED = 0, FIRED = 1, UNSUPPORTED = 2, INVALID = 3 };
static const char *oname[] = {"REFUSED", "FIRED", "UNSUPPORTED", "INVALID"};
#define CAP 4294967295ull
#define GOLD 11400714819323198485ull
#define DCAP 1152921504606846976ull /* 2^60 */

static uint64_t rng = 0x6A09E667F3BCC909ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static uint64_t below(uint64_t n) { return n ? next() % n : 0; }

static void die(const char *what) { fprintf(stderr, "bind_walk_tests: %s\n", what); exit(3); }

/* ---- the store: 0 rows, 1 table, 2 header, 3 work ---------------------------- */

enum { MAXR0 = 16 * 2048, MAXR1 = 8 * 4096, MAXR2 = 64, MAXR3 = 128 * 512 };
typedef struct {
    size_t len[4];
    uint8_t b0[MAXR0], b1[MAXR1], b2[MAXR2], b3[MAXR3];
} Store;
static uint8_t *rb(Store *s, int r) { return r == 0 ? s->b0 : r == 1 ? s->b1 : r == 2 ? s->b2 : s->b3; }
static const uint8_t *rbc(const Store *s, int r) {
    return r == 0 ? s->b0 : r == 1 ? s->b1 : r == 2 ? s->b2 : s->b3;
}
static uint64_t rd(const Store *s, int r, uint64_t off) {
    uint64_t v = 0;
    for (int k = 0; k < 8; k++) v |= (uint64_t)rbc(s, r)[off + k] << (8 * k);
    return v;
}
static void wr(Store *s, int r, uint64_t off, uint64_t v) {
    for (int k = 0; k < 8; k++) rb(s, r)[off + k] = (uint8_t)(v >> (8 * k));
}

/* ---- the algorithm --------------------------------------------------------------
 * Every access is checked as p1 checks it: an ADDR whose middle or end leaves
 * its region, and a LOAD or STORE outside it, are INVALID. Addresses are
 * computed as the program computes them (64-bit words, so an index can wrap).
 */

typedef struct { int out; uint64_t ret; } Result;
#define STOP(o, r) do { res.out = (o); res.ret = (r); return res; } while (0)

/* ADDR r d p i s o: p is base + off0 (an offset into region r); the middle
   off0 + i * 2^s and the end middle + o must lie in [0, len]. */
static bool addr(const Store *s, int r, uint64_t off0, uint64_t i, int sc, int64_t o, uint64_t *res_off) {
    unsigned __int128 m = (unsigned __int128)off0 + ((unsigned __int128)i << sc);
    if (m > s->len[r]) return false;
    __int128 a = (__int128)m + o;
    if (a < 0 || a > (__int128)s->len[r]) return false;
    *res_off = (uint64_t)a;
    return true;
}
static bool inside(const Store *s, int r, uint64_t off, uint64_t w) {
    return off <= s->len[r] && w <= s->len[r] - off;
}

static uint64_t ihash(uint64_t k0, uint64_t k1) {
    uint64_t h = (k0 ^ k1) * GOLD;
    return h ^ (h >> 29);
}

/* The inline interning: returns 0 and *id, or the outcome of a stop. */
static int intern_model(Store *s, uint64_t k0, uint64_t k1, uint64_t *id, uint64_t *ret) {
    uint64_t h = ihash(k0, k1);
    uint64_t slots = s->len[1] >> 3;
    if (slots > CAP) { *ret = 2; return UNSUPPORTED; }
    for (uint64_t j = 0; j < slots; j++) {
        uint64_t pos = (h + j) & (slots - 1), so;
        if (!addr(s, 1, 0, pos, 3, 0, &so) || !inside(s, 1, so, 8)) { *ret = 3; return INVALID; }
        uint64_t e = rd(s, 1, so);
        if (e == 0) {
            if (!inside(s, 3, 0, 8)) { *ret = 3; return INVALID; }
            uint64_t c = rd(s, 3, 0);
            if (!(c < (s->len[0] >> 4))) { *ret = 16; return UNSUPPORTED; }
            uint64_t ro;
            if (!addr(s, 0, 0, c << 1, 3, 0, &ro) || !inside(s, 0, ro, 16)) { *ret = 3; return INVALID; }
            wr(s, 0, ro, k0); wr(s, 0, ro + 8, k1);
            wr(s, 1, so, c + 1);
            wr(s, 3, 0, c + 1);
            *id = c;
            return -1;
        }
        uint64_t idv = e - 1;
        uint64_t c = rd(s, 3, 0);
        if (idv < c) {
            uint64_t ro;
            if (!addr(s, 0, 0, idv << 1, 3, 0, &ro) || !inside(s, 0, ro, 16)) { *ret = 3; return INVALID; }
            if (rd(s, 0, ro) == k0 && rd(s, 0, ro + 8) == k1) { *id = idv; return -1; }
        }
    }
    *ret = 14;
    return UNSUPPORTED;
}

static uint64_t mhash(uint64_t i, uint64_t n, uint64_t mask) {
    uint64_t h = n * GOLD;
    h += i;
    h *= GOLD;
    return (h >> 32) & mask;
}

typedef struct { uint64_t steps, hits, inserts, interned, appended; } Stats;
static Stats stats;

static Result walk_model(Store *s, uint64_t x, uint64_t ty, uint64_t t) {
    Result res = {0, 0};
    if (s->len[0] < 16 || s->len[1] < 8 || s->len[2] < 8 || s->len[3] < 256) STOP(INVALID, 3);
    uint64_t c0 = rd(s, 2, 0);
    if ((s->len[0] >> 4) < c0) STOP(UNSUPPORTED, 1);
    if (!(t < c0)) STOP(UNSUPPORTED, 2);
    if (!(x < DCAP && ty < DCAP)) STOP(UNSUPPORTED, 3);
    uint64_t K = (s->len[3] >> 7) - 1;
    wr(s, 3, 0, c0); wr(s, 3, 32, K); wr(s, 3, 40, t);
    wr(s, 3, 128, 0); wr(s, 3, 136, t); wr(s, 3, 144, 0);
    wr(s, 3, 8, 1); wr(s, 3, 16, 0); wr(s, 3, 24, 0);
    for (uint64_t step = 0; step < CAP; step++) {
        stats.steps++;
        uint64_t tsp = rd(s, 3, 8);
        int need = 0;
        uint64_t k0 = 0, k1 = 0, r5 = 0, mode = 0;
        if (tsp == 0) {
            /* final */
            uint64_t vsp = rd(s, 3, 16);
            if (vsp == 0) STOP(UNSUPPORTED, 5);
            uint64_t vo;
            if (!addr(s, 3, 0, ((K + vsp - 1) << 2), 3, 128, &vo) || !inside(s, 3, vo, 24)) STOP(INVALID, 3);
            if (!(rd(s, 3, vo) == rd(s, 3, 40) && rd(s, 3, vo + 8) == 0)) STOP(UNSUPPORTED, 6);
            k1 = rd(s, 3, vo + 16);
            k0 = (ty << 3) + 4;
            wr(s, 3, 64, 2); mode = 2;
            need = 1;
        } else {
            uint64_t e = tsp - 1;
            wr(s, 3, 8, e);
            uint64_t to;
            if (!addr(s, 3, 0, e << 2, 3, 128, &to) || !inside(s, 3, to, 24)) STOP(INVALID, 3);
            uint64_t kind = rd(s, 3, to), i = rd(s, 3, to + 8), n = rd(s, 3, to + 16);
            wr(s, 3, 48, i); wr(s, 3, 56, n);
            if (kind == 0) {
                /* visit: the memo */
                uint64_t Kw = rd(s, 3, 32);
                uint64_t mask = (Kw << 2) - 1;
                uint64_t sl = mhash(i, n, mask);
                uint64_t so;
                if (!addr(s, 3, 0, (Kw << 3) + (Kw << 2) + sl, 3, 128, &so) || !inside(s, 3, so, 8)) STOP(INVALID, 3);
                uint64_t p = rd(s, 3, so);
                int hit = 0;
                if (p < rd(s, 3, 24)) {
                    uint64_t lo;
                    if (!addr(s, 3, 0, ((Kw << 1) + p) << 2, 3, 128, &lo) || !inside(s, 3, lo, 24)) STOP(INVALID, 3);
                    hit = rd(s, 3, lo) == i && rd(s, 3, lo + 8) == n;
                    r5 = rd(s, 3, lo + 16);
                }
                if (hit) {
                    stats.hits++;
                    wr(s, 3, 64, 0); mode = 0;
                    need = 0;
                } else {
                    uint64_t ro;
                    if (!addr(s, 0, 0, i << 1, 3, 0, &ro) || !inside(s, 0, ro, 16)) STOP(INVALID, 3);
                    uint64_t rk0 = rd(s, 0, ro), rk1 = rd(s, 0, ro + 8);
                    if (rk0 == (x << 3) && rk1 == ty) {
                        if (!(n < DCAP)) STOP(UNSUPPORTED, 8);
                        k0 = (n << 3) + 1; k1 = 0;
                        wr(s, 3, 64, 0); mode = 0;
                        need = 1;
                    } else {
                        uint64_t tag = rk0 & 7;
                        if (tag < 3) {
                            r5 = i;
                            wr(s, 3, 64, 0); mode = 0;
                            need = 0;
                        } else if (tag == 3) {
                            if (rd(s, 3, 32) < e + 3) STOP(UNSUPPORTED, 10);
                            uint64_t a = rk0 >> 3, b = rk1, eo;
                            if (!addr(s, 3, 0, e << 2, 3, 128, &eo)) STOP(INVALID, 3);
                            if (!inside(s, 3, eo, 88)) STOP(INVALID, 3);
                            wr(s, 3, eo, 1);
                            wr(s, 3, eo + 32, 0); wr(s, 3, eo + 40, b); wr(s, 3, eo + 48, n);
                            wr(s, 3, eo + 64, 0); wr(s, 3, eo + 72, a); wr(s, 3, eo + 80, n);
                            wr(s, 3, 8, e + 3);
                            wr(s, 3, 64, 3); mode = 3;
                            need = 0;
                        } else if (tag == 4) {
                            if (rd(s, 3, 32) < e + 2) STOP(UNSUPPORTED, 10);
                            uint64_t b = rk1, eo;
                            if (!addr(s, 3, 0, e << 2, 3, 128, &eo)) STOP(INVALID, 3);
                            if (!inside(s, 3, eo, 56)) STOP(INVALID, 3);
                            wr(s, 3, eo, 2);
                            wr(s, 3, eo + 32, 0); wr(s, 3, eo + 40, b); wr(s, 3, eo + 48, n + 1);
                            wr(s, 3, 8, e + 2);
                            wr(s, 3, 64, 3); mode = 3;
                            need = 0;
                        } else STOP(UNSUPPORTED, 9);
                    }
                }
            } else if (kind == 1 || kind == 2) {
                uint64_t ro;
                if (!addr(s, 0, 0, i << 1, 3, 0, &ro) || !inside(s, 0, ro, 16)) STOP(INVALID, 3);
                uint64_t rk0 = rd(s, 0, ro), b = rd(s, 0, ro + 8);
                if ((rk0 & 7) != (kind == 1 ? 3u : 4u)) STOP(UNSUPPORTED, 11);
                if (kind == 1) {
                    uint64_t a = rk0 >> 3;
                    uint64_t vsp = rd(s, 3, 16);
                    if (vsp < 2) STOP(UNSUPPORTED, 12);
                    vsp -= 2;
                    wr(s, 3, 16, vsp);
                    uint64_t vo;
                    if (!addr(s, 3, 0, (rd(s, 3, 32) + vsp) << 2, 3, 128, &vo) || !inside(s, 3, vo, 56)) STOP(INVALID, 3);
                    bool ok = rd(s, 3, vo) == a && rd(s, 3, vo + 8) == n && rd(s, 3, vo + 32) == b &&
                              rd(s, 3, vo + 40) == n;
                    if (!ok) STOP(UNSUPPORTED, 13);
                    uint64_t ra = rd(s, 3, vo + 16), rbv = rd(s, 3, vo + 48);
                    wr(s, 3, 64, 1); mode = 1;
                    if (ra == a && rbv == b) { r5 = i; need = 0; }
                    else { k0 = (ra << 3) + 3; k1 = rbv; need = 1; }
                } else {
                    if (!(n < DCAP)) STOP(UNSUPPORTED, 8);
                    uint64_t vsp = rd(s, 3, 16);
                    if (vsp == 0) STOP(UNSUPPORTED, 12);
                    vsp -= 1;
                    wr(s, 3, 16, vsp);
                    uint64_t vo;
                    if (!addr(s, 3, 0, (rd(s, 3, 32) + vsp) << 2, 3, 128, &vo) || !inside(s, 3, vo, 24)) STOP(INVALID, 3);
                    if (!(rd(s, 3, vo) == b && rd(s, 3, vo + 8) == n + 1)) STOP(UNSUPPORTED, 13);
                    uint64_t rbv = rd(s, 3, vo + 16);
                    wr(s, 3, 64, 1); mode = 1;
                    if (rbv == b) { r5 = i; need = 0; }
                    else { k0 = rk0; k1 = rbv; need = 1; }
                }
            } else STOP(UNSUPPORTED, 7);
        }
        /* the tail */
        if (need) {
            uint64_t id = 0, ret = 0, c_before = rd(s, 3, 0);
            int o = intern_model(s, k0, k1, &id, &ret);
            stats.interned++;
            if (o < 0 && rd(s, 3, 0) != c_before) stats.appended++;
            if (o >= 0) STOP(o, ret);
            r5 = id;
        }
        mode = rd(s, 3, 64);
        if (mode == 2) {
            wr(s, 2, 0, rd(s, 3, 0));
            STOP(FIRED, r5);
        }
        if (mode < 2) {
            uint64_t vsp = rd(s, 3, 16), Kw = rd(s, 3, 32);
            if (!(vsp < Kw)) STOP(UNSUPPORTED, 15);
            uint64_t vo;
            if (!addr(s, 3, 0, (Kw + vsp) << 2, 3, 128, &vo) || !inside(s, 3, vo, 24)) STOP(INVALID, 3);
            uint64_t si = rd(s, 3, 48), sn = rd(s, 3, 56);
            wr(s, 3, vo, si); wr(s, 3, vo + 8, sn); wr(s, 3, vo + 16, r5);
            wr(s, 3, 16, vsp + 1);
            if (mode == 1) {
                uint64_t lc = rd(s, 3, 24);
                if (lc < Kw) {
                    uint64_t lo, so;
                    if (!addr(s, 3, 0, ((Kw << 1) + lc) << 2, 3, 128, &lo) || !inside(s, 3, lo, 24)) STOP(INVALID, 3);
                    wr(s, 3, lo, si); wr(s, 3, lo + 8, sn); wr(s, 3, lo + 16, r5);
                    uint64_t sl = mhash(si, sn, (Kw << 2) - 1);
                    if (!addr(s, 3, 0, (Kw << 3) + (Kw << 2) + sl, 3, 128, &so) || !inside(s, 3, so, 8)) STOP(INVALID, 3);
                    wr(s, 3, so, lc);
                    wr(s, 3, 24, lc + 1);
                    stats.inserts++;
                }
            }
        }
    }
    STOP(UNSUPPORTED, 4);
}

/* ---- the specification -------------------------------------------------------------
 * Trees, hash-consed: a node (tag, a, b) where a and b are node ids for Comb
 * and the body of Abs, and plain numbers otherwise:
 *   0 Var(name a, type b)  1 Bound(a)  2 Const(name a, type b)
 *   3 Comb(node a, node b)  4 Abs(type a, node b).
 */

enum { MAXN = 1 << 20 };
typedef struct { int tag; uint64_t a, b; } Node;
static Node nodes[MAXN];
static int nnodes;
static int nh[1 << 21];

static int mk(int tag, uint64_t a, uint64_t b) {
    uint64_t h = ((uint64_t)tag * 0x9E3779B97F4A7C15ull) ^ (a * 0xC2B2AE3D27D4EB4Full) ^ (b + 0x165667B19E3779F9ull);
    h ^= h >> 31;
    uint64_t m = (1u << 21) - 1;
    for (uint64_t p = h & m;; p = (p + 1) & m) {
        if (nh[p] == 0) {
            if (nnodes >= MAXN - 1) die("too many tree nodes");
            nodes[++nnodes] = (Node){tag, a, b};
            nh[p] = nnodes;
            return nnodes;
        }
        Node *q = &nodes[nh[p]];
        if (q->tag == tag && q->a == a && q->b == b) return nh[p];
    }
}
static void trees_reset(void) { nnodes = 0; memset(nh, 0, sizeof nh); }

/* Decoding of row i among the first count rows: a node id, or 0 (none). */
enum { MAXROWS = MAXR0 / 16 };
static int dec_memo[MAXROWS];
static uint8_t dec_state[MAXROWS]; /* 0 unknown, 1 in progress, 2 done */

static int decode(const Store *s, uint64_t count, uint64_t i) {
    if (i >= count) return 0;
    if (dec_state[i] == 2) return dec_memo[i];
    if (dec_state[i] == 1) return 0; /* a cycle: no decoding */
    dec_state[i] = 1;
    uint64_t k0 = rd(s, 0, 16 * i), k1 = rd(s, 0, 16 * i + 8);
    uint64_t tag = k0 & 7, a = k0 >> 3, b = k1;
    int r = 0;
    switch (tag) {
    case 0: r = mk(0, a, b); break;
    case 1: r = mk(1, a, 0); break;
    case 2: r = mk(2, a, b); break;
    case 3: { int x = decode(s, count, a), y = decode(s, count, b); r = x && y ? mk(3, (uint64_t)x, (uint64_t)y) : 0; break; }
    case 4: { int y = decode(s, count, b); r = y ? mk(4, a, (uint64_t)y) : 0; break; }
    default: r = 0;
    }
    dec_state[i] = 2;
    dec_memo[i] = r;
    return r;
}
static void decode_reset(uint64_t count) {
    memset(dec_state, 0, count < MAXROWS ? count : MAXROWS);
}

/* hbind (x,ty) n on a tree. */
typedef struct { int node; uint64_t n; int res; } HB;
enum { HBM = 1 << 20 };
static HB hbm[HBM];
static int hbind_t(int node, uint64_t n, uint64_t x, uint64_t ty) {
    Node q = nodes[node];
    uint64_t h = ((uint64_t)node * 0x9E3779B97F4A7C15ull + n) & (HBM - 1);
    if (hbm[h].node == node && hbm[h].n == n) return hbm[h].res;
    int r;
    switch (q.tag) {
    case 0: r = q.a == x && q.b == ty ? mk(1, n, 0) : node; break;
    case 3: r = mk(3, (uint64_t)hbind_t((int)q.a, n, x, ty), (uint64_t)hbind_t((int)q.b, n, x, ty)); break;
    case 4: r = mk(4, q.a, (uint64_t)hbind_t((int)q.b, n + 1, x, ty)); break;
    default: r = node;
    }
    hbm[h] = (HB){node, n, r};
    return r;
}

/* intern16's invariant, intern_ok: rows below the count inside the rows
   region, each reached by probing from its key's hash through non-empty slots
   to a slot holding id + 1, no two rows with one key. */
static bool intern_ok(const Store *s, uint64_t count) {
    if (count > (s->len[0] >> 4)) return false;
    uint64_t slots = s->len[1] >> 3;
    for (uint64_t i = 0; i < count; i++) {
        uint64_t k0 = rd(s, 0, 16 * i), k1 = rd(s, 0, 16 * i + 8), h = ihash(k0, k1);
        bool found = false;
        for (uint64_t d = 0; d < slots; d++) {
            uint64_t e = rd(s, 1, 8 * ((h + d) & (slots - 1)));
            if (e == i + 1) { found = true; break; }
            if (e == 0) break;
        }
        if (!found) return false;
        for (uint64_t j = 0; j < i; j++)
            if (rd(s, 0, 16 * j) == k0 && rd(s, 0, 16 * j + 8) == k1) return false;
    }
    return true;
}

static unsigned long nspec_fired, nspec_decoded;

static void check_spec(const Store *before, const Store *after, Result r, uint64_t x, uint64_t ty, uint64_t t,
                       const char *name) {
    uint64_t c0 = before->len[2] >= 8 ? rd(before, 2, 0) : 0, c1 = after->len[2] >= 8 ? rd(after, 2, 0) : 0;
    bool okb = before->len[2] >= 8 && before->len[0] >= 16 && intern_ok(before, c0);
    char why[256] = "";
    if (r.out != FIRED && before->len[2] >= 8 && c1 != c0) snprintf(why, sizeof why, "header changed on %s", oname[r.out]);
    /* rows below the old count unchanged (the old count is capped by the region) */
    uint64_t lim = c0 < (before->len[0] >> 4) ? c0 : (before->len[0] >> 4);
    if (!*why && r.out != INVALID)
        for (uint64_t k = 0; k < 16 * lim; k++)
            if (before->b0[k] != after->b0[k]) { snprintf(why, sizeof why, "row byte %" PRIu64 " changed", k); break; }
    if (!*why && okb && !intern_ok(after, c1)) snprintf(why, sizeof why, "table invariant broken (%s)", oname[r.out]);
    if (!*why && r.out == FIRED) {
        nspec_fired++;
        if (!(c0 <= c1 && c1 <= (after->len[0] >> 4))) snprintf(why, sizeof why, "count %" PRIu64 " -> %" PRIu64, c0, c1);
        else if (!(r.ret < c1)) snprintf(why, sizeof why, "ret %" PRIu64 " not below the count %" PRIu64, r.ret, c1);
        else {
            trees_reset(); memset(hbm, 0, sizeof hbm);
            decode_reset(c0);
            int T = decode(before, c0, t);
            if (T) {
                nspec_decoded++;
                int want = mk(4, ty, (uint64_t)hbind_t(T, 0, x, ty));
                decode_reset(c1);
                int got = decode(after, c1, r.ret);
                if (got != want) snprintf(why, sizeof why, "FIRED row %" PRIu64 " is not dbAbs ty (hbind (x,ty) 0 t)", r.ret);
            }
        }
    }
    if (*why) { fprintf(stderr, "SPEC VIOLATION in %s: %s\n", name, why); exit(3); }
}

/* ---- building stores ------------------------------------------------------------------ */

static void store_init(Store *s, size_t l0, size_t l1, size_t l2, size_t l3) {
    s->len[0] = l0; s->len[1] = l1; s->len[2] = l2; s->len[3] = l3;
    memset(s->b0, 0, sizeof s->b0); memset(s->b1, 0, sizeof s->b1);
    memset(s->b2, 0, sizeof s->b2); memset(s->b3, 0, sizeof s->b3);
}

/* intern16 on the store, publishing at once: the id, or UINT64_MAX when full. */
static uint64_t intern_pub(Store *s, uint64_t k0, uint64_t k1) {
    uint64_t c = rd(s, 2, 0), slots = s->len[1] >> 3, h = ihash(k0, k1);
    for (uint64_t j = 0; j < slots; j++) {
        uint64_t p = (h + j) & (slots - 1), e = rd(s, 1, 8 * p);
        if (e == 0) {
            if (c >= (s->len[0] >> 4)) return UINT64_MAX;
            wr(s, 0, 16 * c, k0); wr(s, 0, 16 * c + 8, k1);
            wr(s, 1, 8 * p, c + 1); wr(s, 2, 0, c + 1);
            return c;
        }
        if (e - 1 < c && rd(s, 0, 16 * (e - 1)) == k0 && rd(s, 0, 16 * (e - 1) + 8) == k1) return e - 1;
    }
    return UINT64_MAX;
}

/* A pool of term rows built by interning: leaves and combinations of earlier
   rows. nv variables (names 0..nv-1, types 0..1), bound and const leaves,
   combs and abss with sharing; lists sometimes. */
typedef struct { uint64_t id[MAXROWS]; int n; } Pool;

static void pool_add(Pool *p, uint64_t id) { if (id != UINT64_MAX && p->n < MAXROWS) p->id[p->n++] = id; }

static void build_pool(Store *s, Pool *p, int nrows, int nv, int lists, int deep) {
    p->n = 0;
    for (int k = 0; k < nv; k++) pool_add(p, intern_pub(s, (uint64_t)k << 3, (uint64_t)(k % 2)));
    pool_add(p, intern_pub(s, (0ull << 3) + 1, 0));
    pool_add(p, intern_pub(s, (3ull << 3) + 2, 1));
    while ((int)rd(s, 2, 0) < nrows && p->n > 0) {
        uint64_t r = below(100);
        uint64_t a = p->id[below((uint64_t)p->n)], b = p->id[below((uint64_t)p->n)];
        if (deep && p->n > 2) { a = p->id[p->n - 1 - below(2)]; }
        uint64_t id;
        if (r < 8) id = intern_pub(s, (below(nv + 2) << 3) + 0, below(2));
        else if (r < 12) id = intern_pub(s, (below(4) << 3) + 1, 0);
        else if (r < 16) id = intern_pub(s, (below(5) << 3) + 2, below(2));
        else if (r < 60) id = intern_pub(s, (a << 3) + 3, b);
        else if (r < 95 || !lists) id = intern_pub(s, (below(3) << 3) + 4, a);
        else id = intern_pub(s, (a << 3) + (r < 97 ? 5 : 6), b);
        if (id == UINT64_MAX) break;
        pool_add(p, id);
    }
}

/* ---- the descriptions ------------------------------------------------------------------ */

static FILE *out;
static unsigned long ncases, nruns, nout[4], nwants;

static void emit_store(const Store *s) {
    for (int r = 0; r < 4; r++) {
        fprintf(out, "region %d %zu\n", r, s->len[r]);
        for (size_t o = 0; o + 8 <= s->len[r]; o += 8) {
            uint64_t w = rd(s, r, o);
            if (w) fprintf(out, "words %d %zu %" PRIu64 "\n", r, o, w);
        }
        for (size_t o = s->len[r] & ~(size_t)7; o < s->len[r]; o++)
            if (rbc(s, r)[o]) fprintf(out, "bytes %d %zu %u\n", r, o, rbc(s, r)[o]);
    }
}

/* Wants after a run: the header word, the rows below the new count (as many
   as fit), the table when small. */
static void emit_wants(const Store *after, int max) {
    int k = 0;
    if (after->len[2] >= 8) { fprintf(out, "want 2 0 %" PRIu64 "\n", rd(after, 2, 0)); k++; }
    uint64_t c = after->len[2] >= 8 ? rd(after, 2, 0) : 0;
    if (c > (after->len[0] >> 4)) c = after->len[0] >> 4;
    for (uint64_t i = c; i-- > 0 && k + 2 <= max;) {
        fprintf(out, "want 0 %" PRIu64 " %" PRIu64 "\nwant 0 %" PRIu64 " %" PRIu64 "\n", 16 * i, rd(after, 0, 16 * i),
                16 * i + 8, rd(after, 0, 16 * i + 8));
        k += 2;
    }
    for (size_t o = 0; o + 8 <= after->len[1] && k < max; o += 8, k++)
        fprintf(out, "want 1 %zu %" PRIu64 "\n", o, rd(after, 1, o));
    nwants += (unsigned long)k;
}

static Store before, after;

/* One run from s (not changed): model, specification, description. */
static Result one_run(const Store *s, uint64_t x, uint64_t ty, uint64_t t, const char *name, bool wants) {
    memcpy(&after, s, sizeof *s);
    Result r = walk_model(&after, x, ty, t);
    check_spec(s, &after, r, x, ty, t, name);
    fprintf(out, "arg0 %" PRIu64 "\narg1 %" PRIu64 "\n", x, ty);
    fprintf(out, "expect %s %" PRIu64 "\n", oname[r.out], r.ret);
    if (wants) emit_wants(&after, 64);
    fprintf(out, "run v1=%" PRIu64 "\n", t);
    nruns++;
    nout[r.out]++;
    return r;
}

static void new_case(const char *fmt, ...) __attribute__((format(printf, 1, 2)));
static void new_case(const char *fmt, ...) {
    char name[128];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(name, sizeof name, fmt, ap);
    va_end(ap);
    fprintf(out, "case %s\n", name);
    ncases++;
}

/* Variables present in the pool's rows: (name, type) of tag-0 rows. */
static void pick_var(const Store *s, uint64_t *x, uint64_t *ty) {
    uint64_t c = rd(s, 2, 0);
    for (int tries = 0; tries < 64; tries++) {
        uint64_t i = below(c);
        uint64_t k0 = rd(s, 0, 16 * i);
        if ((k0 & 7) == 0) { *x = k0 >> 3; *ty = rd(s, 0, 16 * i + 8); return; }
    }
    *x = below(4); *ty = below(2);
}

static void garble_work(Store *s, int how, const Pool *p) {
    size_t L = s->len[3];
    if (how == 1) for (size_t k = 0; k < L; k++) s->b3[k] = (uint8_t)next();
    if (how == 2 || how == 3) {
        uint64_t K = (L >> 7) - 1;
        /* memo slots naming small log positions; log entries with real keys and
           wrong results; header words with nonsense */
        for (uint64_t sl = 0; sl < 4 * K; sl++) wr(s, 3, 128 + 8 * (12 * K + sl), below(4));
        for (uint64_t q = 0; q < K; q++) {
            uint64_t o = 128 + 32 * (2 * K + q);
            wr(s, 3, o, p->n ? p->id[below((uint64_t)p->n)] : 0);
            wr(s, 3, o + 8, below(3));
            wr(s, 3, o + 16, how == 2 ? below(rd(s, 2, 0) + 1) : next());
        }
        for (int w = 0; w < 16; w++) wr(s, 3, 8 * (uint64_t)w, below(5));
    }
}

static void diff_cases(int nrandom) {
    Pool pool;
    /* 1. bad inputs and minimums */
    {
        static Store s;
        store_init(&s, 16 * 64, 8 * 128, 8, 1024);
        build_pool(&s, &pool, 40, 3, 0, 0);
        new_case("bad_inputs");
        emit_store(&s);
        uint64_t c = rd(&s, 2, 0);
        one_run(&s, 0, 0, c, "t_at_count", true);
        one_run(&s, 0, 0, UINT64_MAX, "t_max", true);
        one_run(&s, DCAP, 0, 0, "x_2^60", true);
        one_run(&s, 0, DCAP, 0, "ty_2^60", true);
        one_run(&s, UINT64_MAX, UINT64_MAX, 0, "x_ty_max", true);
        one_run(&s, DCAP - 1, DCAP - 1, 0, "x_ty_below", true);
        Store *t = &before;
        memcpy(t, &s, sizeof s);
        wr(t, 2, 0, (t->len[0] >> 4) + 1);
        new_case("count_above_capacity");
        emit_store(t);
        one_run(t, 0, 0, 0, "count_above", true);
        for (int r = 0; r < 4; r++) {
            memcpy(t, &s, sizeof s);
            static const size_t small[4] = {8, 0, 0, 248};
            t->len[r] = small[r];
            new_case("below_minimum_%d", r);
            emit_store(t);
            one_run(t, 0, 0, 0, "below_min", false);
        }
    }
    /* 2. random DAGs over several sizes, clean and garbled work regions */
    for (int k = 0; k < nrandom; k++) {
        static Store s;
        size_t rows = 16 + below(48), slots = 1u << (7 + below(3));
        size_t worklen = k % 4 == 1 ? 128 * (2 + below(6)) + below(128) : 128 * (24 + below(100)) + below(128);
        store_init(&s, 16 * (rows + below(24)), 8 * slots, 8 + 8 * below(2), worklen);
        build_pool(&s, &pool, (int)rows, 1 + (int)below(5), k % 7 == 0, k % 5 == 0);
        int garble = (int)below(4);
        garble_work(&s, garble, &pool);
        if (k % 11 == 3) /* garbage above the count, stale slots */ {
            uint64_t c = rd(&s, 2, 0);
            for (uint64_t i = c; i < (s.len[0] >> 4); i++) { wr(&s, 0, 16 * i, next()); wr(&s, 0, 16 * i + 8, next()); }
            for (uint64_t q = 0; q < slots; q++) if (rd(&s, 1, 8 * q) == 0 && below(3) == 0) wr(&s, 1, 8 * q, c + 1 + below(5));
        }
        new_case("random_%d_g%d", k, garble);
        emit_store(&s);
        uint64_t c = rd(&s, 2, 0);
        for (int r = 0; r < 4; r++) {
            uint64_t x, ty;
            pick_var(&s, &x, &ty);
            if (r == 3) { x = 100 + below(5); ty = below(2); }
            uint64_t t = pool.n ? pool.id[below((uint64_t)pool.n)] : 0;
            if (r == 0 && pool.n) t = pool.id[pool.n - 1];
            if (t >= c) t = c ? c - 1 : 0;
            one_run(&s, x, ty, t, "random", true);
        }
    }
    /* 3. deep nesting: abstraction chains and comb spines, the variable at
       every depth; small work regions overflow the task stack */
    for (int depth = 1; depth <= 200; depth += depth < 20 ? 3 : 37) {
        static Store s;
        store_init(&s, 16 * 1024, 8 * 2048, 8, 128 * (4 + (size_t)depth));
        uint64_t v = intern_pub(&s, 5ull << 3, 1), cst = intern_pub(&s, (7ull << 3) + 2, 0);
        uint64_t body = v;
        for (int d = 0; d < depth; d++) {
            uint64_t sh = intern_pub(&s, (body << 3) + 3, d % 3 == 0 ? v : cst);
            body = intern_pub(&s, ((uint64_t)(d % 2) << 3) + 4, d % 4 == 0 ? sh : body);
        }
        uint64_t spine = cst;
        for (int d = 0; d < depth; d++) spine = intern_pub(&s, (spine << 3) + 3, d % 2 ? v : body);
        new_case("deep_%d", depth);
        emit_store(&s);
        one_run(&s, 5, 1, body, "deep_abs", true);
        one_run(&s, 5, 1, spine, "deep_spine", true);
        one_run(&s, 5, 0, spine, "deep_other_type", true);
        one_run(&s, 6, 1, body, "deep_absent", true);
        Store *t = &before;
        memcpy(t, &s, sizeof s);
        t->len[3] = 256 + 128 * below(3);
        new_case("deep_%d_small_work", depth);
        emit_store(t);
        one_run(t, 5, 1, body, "deep_small_abs", true);
        one_run(t, 5, 1, spine, "deep_small_spine", true);
    }
    /* 4. sharing: f (g x x) (g x x) towers, exponential as trees */
    {
        static Store s;
        store_init(&s, 16 * 512, 8 * 1024, 8, 128 * 64);
        uint64_t v = intern_pub(&s, 2ull << 3, 0), f = intern_pub(&s, (1ull << 3) + 2, 0);
        uint64_t t = v;
        for (int d = 0; d < 40; d++) {
            uint64_t ft = intern_pub(&s, (f << 3) + 3, t);
            t = intern_pub(&s, (ft << 3) + 3, t);
            if (d % 9 == 4) t = intern_pub(&s, (0ull << 3) + 4, t);
        }
        new_case("sharing_tower");
        emit_store(&s);
        one_run(&s, 2, 0, t, "tower", true);
        one_run(&s, 2, 1, t, "tower_absent", true);
    }
    /* 5. full regions: rows, table */
    for (int k = 0; k < 40; k++) {
        static Store s;
        size_t slots = 1u << (3 + below(3));
        store_init(&s, 16 * (8 + below(24)), 8 * slots, 8, 128 * (2 + below(8)));
        build_pool(&s, &pool, 1000, 2, 0, k % 2);
        new_case("full_%d", k);
        emit_store(&s);
        for (int r = 0; r < 3; r++) {
            uint64_t x, ty;
            pick_var(&s, &x, &ty);
            uint64_t c = rd(&s, 2, 0), t = pool.n ? pool.id[below((uint64_t)pool.n)] : 0;
            if (t >= c) t = c ? c - 1 : 0;
            one_run(&s, x, ty, t, "full", true);
        }
    }
    /* 6. list rows as terms, children above the count, wrapping children */
    {
        static Store s;
        store_init(&s, 16 * 64, 8 * 128, 8, 2048);
        uint64_t v = intern_pub(&s, 0, 0), nil = intern_pub(&s, 5, 0);
        uint64_t cons = intern_pub(&s, (v << 3) + 6, nil);
        uint64_t bad1 = intern_pub(&s, (cons << 3) + 3, v);
        uint64_t above = intern_pub(&s, (60ull << 3) + 3, v);
        uint64_t wrap = intern_pub(&s, (((1ull << 60) + 1) << 3) + 3, v);
        uint64_t wrapabs = intern_pub(&s, (1ull << 3) + 4, (1ull << 63) + 1);
        uint64_t far = intern_pub(&s, (1ull << 3) + 4, 1ull << 40);
        new_case("malformed");
        emit_store(&s);
        one_run(&s, 0, 0, bad1, "list_child", true);
        one_run(&s, 0, 0, nil, "nil_root", true);
        one_run(&s, 0, 0, above, "child_above", true);
        one_run(&s, 0, 0, wrap, "child_wraps", true);
        one_run(&s, 0, 0, wrapabs, "body_wraps", true);
        one_run(&s, 0, 0, far, "body_far", true);
        one_run(&s, 1, 0, bad1, "list_child_other", true);
    }
}

static void chain_cases(int nchains) {
    Pool pool;
    for (int k = 0; k < nchains; k++) {
        static Store s;
        size_t rows = 200 + below(200);
        store_init(&s, 16 * (rows + 300), 8 * 2048, 8, 128 * (16 + below(64)));
        build_pool(&s, &pool, (int)rows, 2 + (int)below(4), 0, k % 3 == 0);
        if (k % 2) garble_work(&s, 1 + (int)below(3), &pool);
        new_case("chain_%d chain", k);
        emit_store(&s);
        for (int r = 0; r < 12; r++) {
            uint64_t x, ty;
            pick_var(&s, &x, &ty);
            uint64_t c = rd(&s, 2, 0), t = pool.id[below((uint64_t)pool.n)];
            if (t >= c) t = c - 1;
            memcpy(&before, &s, sizeof s);
            Result res = one_run(&before, x, ty, t, "chain", r % 3 == 0);
            memcpy(&s, &after, sizeof s);
            if (res.out == FIRED) pool_add(&pool, res.ret);
            /* the model state must keep the table invariant along the chain */
            if (!intern_ok(&s, rd(&s, 2, 0))) die("chain: table invariant lost");
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: bind_walk_tests DIFF.p1t CHAIN.p1t [SEED [RANDOM]]\n"); return 2; }
    if (argc > 3) rng ^= strtoull(argv[3], NULL, 0) * 0x9E3779B97F4A7C15ull;
    if (!rng) rng = 1;
    int nrandom = argc > 4 ? atoi(argv[4]) : 300;
    out = fopen(argv[1], "w");
    if (!out) return 2;
    diff_cases(nrandom);
    fclose(out);
    fprintf(stderr, "bind_walk_tests: DIFF %lu cases, %lu runs (REFUSED %lu, FIRED %lu, UNSUPPORTED %lu, INVALID %lu), "
                    "%lu wants; spec: %lu FIRED checked, %lu with a decoding body; %lu model steps, %lu memo hits, "
                    "%lu memo inserts, %lu internings (%lu appended)\n",
            ncases, nruns, nout[0], nout[1], nout[2], nout[3], nwants, nspec_fired, nspec_decoded,
            (unsigned long)stats.steps, (unsigned long)stats.hits, (unsigned long)stats.inserts,
            (unsigned long)stats.interned, (unsigned long)stats.appended);
    ncases = nruns = nwants = nspec_fired = nspec_decoded = 0;
    memset(nout, 0, sizeof nout);
    memset(&stats, 0, sizeof stats);
    out = fopen(argv[2], "w");
    if (!out) return 2;
    chain_cases(nrandom / 10 + 1);
    fclose(out);
    fprintf(stderr, "bind_walk_tests: CHAIN %lu cases, %lu runs (REFUSED %lu, FIRED %lu, UNSUPPORTED %lu, INVALID %lu), "
                    "%lu wants; spec: %lu FIRED checked, %lu with a decoding body; %lu model steps, %lu memo hits, "
                    "%lu memo inserts, %lu internings (%lu appended)\n",
            ncases, nruns, nout[0], nout[1], nout[2], nout[3], nwants, nspec_fired, nspec_decoded,
            (unsigned long)stats.steps, (unsigned long)stats.hits, (unsigned long)stats.inserts,
            (unsigned long)stats.interned, (unsigned long)stats.appended);
    return 0;
}
