/* micromath_spec.c: Micromath on the specializer.  The rules of micromath.tcs, compiled by tcs_gen,
 * run beside Micromath's own kernel (tcalc/ref/kernel.c, unchanged) and beside the same rules on
 * the generic route (tcs_instance_of + tr_fire of tcalc_ref).
 *
 * Slots are the control layer: slot i refers to the occurrence of the theorem it holds.  A
 * theorem is a fact thm(out, f, x, y) that stays true; an unwritten slot refers to the default
 * theorem X = X(X, X) (the kernel's empty slot 0 = 0(0, 0)), made once by proj1(X, X); a theorem
 * that no slot refers to any more is forgotten by a firing of `retire`.  So every rule is one
 * firing of one schema, with no case split on which slots coincide.
 *
 *   micromath_spec SEED OPS [SLOTS]   the differential: random operations (drawn as tcalc_ref's
 *                                     micromath.c draws them), then the exhaustive Boolean sweep
 *                                     of both substitutions with wrong-premise calls; every verdict
 *                                     compared, every slot and both states compared every 1,000
 *   micromath_spec --time SEED OPS SLOTS...   the cost of each route
 */
#include "kernel.h"
#include "tcs.h"

#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>

enum { PROJ1, PROJ2, REFL, OPAQUE, DEF, SUB1, SUB2, RETIRE, AXIOM, NRULES };
static const char *rule_names[NRULES] = {"proj1",       "proj2",       "refl",   "opaque", "def",
                                         "substitute1", "substitute2", "retire", "axiom"};
#define CODE_BASE 1000000000ULL

static uint64_t rng;
static uint64_t rnd(uint64_t n) {
  rng ^= rng << 13, rng ^= rng >> 7, rng ^= rng << 17;
  return rng % n;
}
static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}

typedef struct {
  tr_ctx *c;
  tr_state *s;
  bool generic;
  const tcs_compiled_rule *cr[NRULES];
  const tcs_rule *sr[NRULES];
  tcs_instance inst;
  tr_occ *slot;
  size_t nslots;
  uint32_t *ref;
  size_t capref;
  tr_occ dflt;
} route;

static tr_verdict fire(route *m, int rule, const tr_term *p, const tr_occ *o, tr_result *r) {
  if (m->generic) return tr_fire(m->s, tcs_instance_of(&m->inst, m->c, m->sr[rule], p, o), r);
  return m->cr[rule]->decide(m->s, p, o, r, true);
}

static void hold(route *m, tr_occ o) {
  if (o >= m->capref) {
    size_t n = m->capref ? m->capref : 1024;
    while (n <= o) n *= 2;
    m->ref = realloc(m->ref, n * sizeof *m->ref);
    if (!m->ref) abort();
    memset(m->ref + m->capref, 0, (n - m->capref) * sizeof *m->ref);
    m->capref = n;
  }
  m->ref[o]++;
}
static void release(route *m, tr_occ o) {
  if (o == m->dflt || --m->ref[o]) return;
  tr_result r = {0};
  if (fire(m, RETIRE, NULL, &o, &r) != TR_ADMITTED) {
    fputs("micromath_spec: retire refused\n", stderr);
    abort();
  }
}
static tr_occ at(const route *m, uint64_t i) { return i < m->nslots ? m->slot[i] : m->dflt; }
static void put(route *m, uint64_t d, tr_occ o) {
  tr_occ old = m->slot[d];
  hold(m, o);
  m->slot[d] = o;
  release(m, old);
}

static tr_term sym(route *m, uint64_t n) {
  return n < tr_names(m->s) ? tr_name(m->c, (uint32_t)n) : tr_code(m->c, (int64_t)n);
}
static uint64_t unsym(const route *m, tr_term t) {
  return tr_term_kind(m->c, t) == TR_NAME ? tr_term_index(m->c, t) : (uint64_t)tr_term_code(m->c, t);
}

static bool make_into(route *m, int rule, const tr_term *p, const tr_occ *o, uint64_t d) {
  if (d >= m->nslots) return false;
  tr_occ made;
  tr_result r = {.made = &made};
  if (fire(m, rule, p, o, &r) != TR_ADMITTED) return false;
  put(m, d, made);
  return true;
}
static bool m_axiom(route *m, uint64_t o, uint64_t f, uint64_t x, uint64_t y, uint64_t d) {
  tr_term p[4] = {sym(m, o), sym(m, f), sym(m, x), sym(m, y)};
  return make_into(m, AXIOM, p, NULL, d);
}
static bool m_proj1(route *m, uint64_t x, uint64_t y, uint64_t d) {
  tr_term p[2] = {sym(m, x), sym(m, y)};
  return make_into(m, PROJ1, p, NULL, d);
}
static bool m_proj2(route *m, uint64_t x, uint64_t y, uint64_t d) {
  tr_term p[2] = {sym(m, x), sym(m, y)};
  return make_into(m, PROJ2, p, NULL, d);
}
static bool m_refl(route *m, uint64_t a, uint64_t d) {
  tr_term p = sym(m, a);
  return make_into(m, REFL, &p, NULL, d);
}
static uint64_t m_opaque(route *m) {
  tr_result r = {0};
  return fire(m, OPAQUE, NULL, NULL, &r) == TR_ADMITTED ? r.first_name : 0;
}
/* f, x and y are written as names: one never minted is not a term of the frame. */
static uint64_t m_def(route *m, uint64_t f, uint64_t x, uint64_t y, uint64_t d) {
  if (f > UINT32_MAX || x > UINT32_MAX || y > UINT32_MAX || d >= m->nslots) return 0;
  tr_term p[3] = {tr_name(m->c, (uint32_t)f), tr_name(m->c, (uint32_t)x), tr_name(m->c, (uint32_t)y)};
  tr_occ made;
  tr_result r = {.made = &made};
  if (fire(m, DEF, p, NULL, &r) != TR_ADMITTED) return 0;
  put(m, d, made);
  return r.first_name;
}
static bool m_sub(route *m, int which, uint64_t p0, uint64_t p1, uint64_t p2, uint64_t p3, uint64_t d) {
  tr_occ o[4] = {at(m, p0), at(m, p1), at(m, p2), at(m, p3)};
  return make_into(m, which, NULL, o, d);
}
static ThmBody body(const route *m, uint64_t i) {
  tr_term l;
  if (!tr_present(m->s, at(m, i), &l)) {
    fputs("micromath_spec: a slot refers to no theorem\n", stderr);
    abort();
  }
  return (ThmBody){unsym(m, tr_term_arg(m->c, l, 0)), unsym(m, tr_term_arg(m->c, l, 1)), unsym(m, tr_term_arg(m->c, l, 2)),
                   unsym(m, tr_term_arg(m->c, l, 3))};
}

static void route_init(route *m, tr_ctx *c, const tcs_compiled_theory *T, bool generic, size_t nslots) {
  memset(m, 0, sizeof *m);
  m->c = c;
  m->s = tr_state_new(c);
  m->generic = generic;
  const tcs_theory *th = T->schemas();
  for (int k = 0; k < NRULES; k++) {
    for (size_t i = 0; i < T->nrules; i++)
      if (!strcmp(T->rules[i].name, rule_names[k])) m->cr[k] = &T->rules[i];
    m->sr[k] = tcs_find(th, rule_names[k]);
    if (!m->cr[k] || !m->sr[k]) {
      fprintf(stderr, "micromath_spec: no rule %s\n", rule_names[k]);
      exit(2);
    }
  }
  m->nslots = nslots;
  m->slot = calloc(nslots, sizeof *m->slot);
  if (!m->slot) abort();
  m_opaque(m), m_opaque(m); /* X and Y */
  tr_term xx[2] = {tr_name(c, 0), tr_name(c, 0)};
  tr_occ made;
  tr_result r = {.made = &made};
  if (fire(m, PROJ1, xx, NULL, &r) != TR_ADMITTED) abort();
  m->dflt = made;
  for (size_t i = 0; i < nslots; i++) m->slot[i] = m->dflt;
}
static void route_free(route *m) {
  tcs_instance_free(&m->inst);
  tr_state_free(m->s);
  free(m->slot);
  free(m->ref);
}

/* ---- the three machines: Micromath's kernel (K), the generic route (R), the generated code (G) ---- */

static route R, G;
static bool run_k = true, run_r = true, run_g = true;
static long ops, disagree, accepted;

static void verdict(const char *what, uint64_t want, uint64_t r, uint64_t g) {
  ops++;
  accepted += want != 0;
  if (want != r || want != g)
    if (disagree++ < 5)
      fprintf(stderr, "op %ld (%s): kernel %llu, generic %llu, generated %llu\n", ops, what, (unsigned long long)want,
              (unsigned long long)r, (unsigned long long)g);
}

/* One operation on every machine that runs; `call` is written over the route `m`. */
#define ALL3(what, kcall, call)                                         \
  do {                                                                  \
    uint64_t want_ = 0, r_ = 0, g_ = 0;                                 \
    route *m;                                                           \
    if (run_k) want_ = (uint64_t)(kcall);                               \
    if (run_r) m = &R, r_ = (uint64_t)(call);                           \
    if (run_g) m = &G, g_ = (uint64_t)(call);                           \
    if (run_k && run_r && run_g) verdict((what), want_, r_, g_);        \
    else ops++;                                                         \
  } while (0)

static void same_slots(uint64_t nslots) {
  for (uint64_t j = 0; j < nslots; j++) {
    const ThmBody *k = get_thm(j);
    ThmBody r = body(&R, j), g = body(&G, j);
    if (k->out != r.out || k->f != r.f || k->x != r.x || k->y != r.y || memcmp(&r, &g, sizeof r))
      if (disagree++ < 5) fprintf(stderr, "after op %ld slot %llu differs\n", ops, (unsigned long long)j);
  }
  if (!tr_state_equal(R.s, G.s))
    if (disagree++ < 5) fprintf(stderr, "after op %ld the two states differ\n", ops);
}

/* What the operation stream reads back, from the first machine that runs (the kernel when it runs). */
static uint64_t last_symbol(void) { return run_k ? get_last_const() : tr_names((run_g ? &G : &R)->s) - 1; }
static ThmBody theorem(uint64_t i) { return run_k ? *get_thm(i) : body(run_g ? &G : &R, i); }

static uint64_t pick_symbol(void) {
  if (rnd(8) == 0) return CODE_BASE + rnd(4); /* a structural code, from a range minting never reaches */
  return rnd(last_symbol() + 1);              /* a minted name */
}

static void random_ops(uint64_t seed, long nops, size_t nslots, bool check) {
  rng = seed * 6364136223846793005ULL + 1442695040888963407ULL;
  for (long k = 0; k < nops; k++) {
    int op = (int)rnd(8);
    uint64_t i = rnd(nslots), a = pick_symbol(), b = pick_symbol(), f = pick_symbol();
    uint64_t prem[4] = {rnd(nslots), rnd(nslots), rnd(nslots), rnd(nslots)};
    if (rnd(3) == 0) prem[rnd(4)] = i;                /* a premise that is also the destination */
    if (rnd(64) == 0) prem[rnd(4)] = nslots + rnd(4); /* a premise out of range: the empty theorem */
    if (op >= 5 && rnd(2)) {
      /* premises that meet the side conditions, written by refl (each write an operation too) */
      ThmBody main_ = theorem(prem[0]);
      uint64_t want_of[3] = {main_.x, main_.y, main_.out};
      for (int p = 1; p <= (op == 5 ? 3 : 2); p++) {
        if (prem[p] == prem[0] || prem[p] >= nslots) continue;
        ALL3("premise refl", rule_refl(want_of[p - 1], prem[p]), m_refl(m, want_of[p - 1], prem[p]));
      }
      if (op != 5) prem[3] = prem[0];
      if (rnd(4) == 0) prem[1 + rnd(3)] = rnd(nslots); /* a near miss */
    }
    switch (op) {
    case 0: ALL3("proj1", rule_proj1(a, b, i), m_proj1(m, a, b, i)); break;
    case 1: ALL3("proj2", rule_proj2(a, b, i), m_proj2(m, a, b, i)); break;
    case 2: ALL3("refl", rule_refl(a, i), m_refl(m, a, i)); break;
    case 3:
      if (rnd(16) == 0) ALL3("opaque", new_node_opaque(), m_opaque(m));
      break;
    case 4:
      if (rnd(4) == 0) {
        if (rnd(4) == 0) f = last_symbol() + 1; /* an operand not yet minted: refused by all */
        ALL3("def", new_node_def(f, a, b, i), m_def(m, f, a, b, i));
      }
      break;
    case 5:
      ALL3("substitute1", rule_substitute1(prem[0], prem[1], prem[2], prem[3], i),
           m_sub(m, SUB1, prem[0], prem[1], prem[2], prem[3], i));
      break;
    default:
      ALL3("substitute2", rule_substitute2(prem[0], prem[1], prem[2], prem[3], i),
           m_sub(m, SUB2, prem[0], prem[1], prem[2], prem[3], i));
      break;
    }
    if (check && k % 1000 == 999) same_slots(nslots);
  }
}

static unsigned bit(unsigned t, unsigned l, unsigned r) { return (t >> (2 * l + r)) & 1u; }
static unsigned superpose(unsigned o, unsigned l, unsigned r) {
  unsigned res = 0;
  for (unsigned a = 0; a < 2; a++)
    for (unsigned b = 0; b < 2; b++) res |= bit(o, bit(l, a, b), bit(r, a, b)) << (2 * a + b);
  return res;
}
static uint64_t named(unsigned fn) { return fn + 2; } /* the 16 Boolean functions are symbols 2 .. 17 */

static void axiom_all(uint64_t d, uint64_t o, uint64_t f, uint64_t x, uint64_t y) {
  ALL3("axiom", _set_thm(o, f, x, y, d), m_axiom(m, o, f, x, y, d));
}
static void fixture(unsigned t, unsigned u, unsigned v, unsigned a, unsigned b) {
  unsigned x = superpose(t, u, v), ua = superpose(u, a, b), va = superpose(v, a, b), xa = superpose(x, a, b);
  axiom_all(0, named(x), named(t), named(u), named(v));
  axiom_all(1, named(ua), named(u), named(a), named(b));
  axiom_all(2, named(va), named(v), named(a), named(b));
  axiom_all(3, named(xa), named(x), named(a), named(b));
  axiom_all(4, named(xa), named(t), named(ua), named(va));
}

static int differential(uint64_t seed, long nops, size_t nslots) {
  random_ops(seed, nops, nslots, true);
  same_slots(nslots);
  long random = ops;
  while (last_symbol() < 17) ALL3("opaque", new_node_opaque(), m_opaque(m));
  for (unsigned t = 0; t < 16; t++)
    for (unsigned u = 0; u < 16; u++)
      for (unsigned v = 0; v < 16; v++) {
        for (unsigned a = 0; a < 16; a++)
          for (unsigned b = 0; b < 16; b++) {
            fixture(t, u, v, a, b);
            ALL3("sweep substitute1", rule_substitute1(0, 1, 2, 3, 5), m_sub(m, SUB1, 0, 1, 2, 3, 5));
            ALL3("sweep substitute2", rule_substitute2(0, 1, 2, 4, 6), m_sub(m, SUB2, 0, 1, 2, 4, 6));
            ALL3("sweep substitute1 wrong", rule_substitute1(0, 1, 2, 4, 7), m_sub(m, SUB1, 0, 1, 2, 4, 7));
            ALL3("sweep substitute2 wrong", rule_substitute2(0, 1, 2, 3, 7), m_sub(m, SUB2, 0, 1, 2, 3, 7));
            ALL3("sweep substitute1 swapped", rule_substitute1(0, 2, 1, 3, 7), m_sub(m, SUB1, 0, 2, 1, 3, 7));
          }
        same_slots(8);
      }
  printf("micromath seed %llu, %zu slots: %ld random operations, %ld sweep operations; kernel, generic route and "
         "generated code: %ld disagreements in verdicts, slots and states (%ld accepted); names %u, theorems present %zu, "
         "specialized decisions %zu, generic %zu\n",
         (unsigned long long)seed, nslots, random, ops - random, disagree, accepted, tr_names(G.s), tr_present_count(G.s),
         tcs_count.fast, tcs_count.generic);
  return disagree != 0;
}

/* ---- costs ---- */

static double ns(double t, long n) { return 1e9 * t / (double)n; }
static long max_rss_kb(void) {
  struct rusage u;
  getrusage(RUSAGE_SELF, &u);
  return u.ru_maxrss;
}

static void timing(uint64_t seed, long nops, const tcs_compiled_theory *T, tr_ctx *c, int nsizes, char **sizes) {
  const long REP = 2000000;
  volatile uint64_t sink = 0;
  double t0, tk, tr, tg, ar, ag;
  init();
  route_init(&R, c, T, true, 24);
  route_init(&G, c, T, false, 24);
  while (last_symbol() < 17) ALL3("opaque", new_node_opaque(), m_opaque(m));
  fixture(1, 6, 8, 3, 5); /* substitute1(0, 1, 2, 3) holds */
  t0 = now();
  for (long i = 0; i < REP; i++) sink ^= rule_substitute1(0, 1, 2, 3, 5);
  tk = now() - t0;
  t0 = now();
  for (long i = 0; i < REP; i++) sink ^= m_sub(&R, SUB1, 0, 1, 2, 3, 5);
  tr = now() - t0;
  t0 = now();
  for (long i = 0; i < REP; i++) sink ^= m_sub(&G, SUB1, 0, 1, 2, 3, 5);
  tg = now() - t0;
  tr_occ o[4] = {at(&R, 0), at(&R, 1), at(&R, 2), at(&R, 3)};
  tr_result res = {0};
  t0 = now();
  for (long i = 0; i < REP; i++) sink ^= tr_admits(R.s, tcs_instance_of(&R.inst, R.c, R.sr[SUB1], NULL, o), &res);
  ar = now() - t0;
  t0 = now();
  for (long i = 0; i < REP; i++) sink ^= G.cr[SUB1]->decide(G.s, NULL, o, &res, false);
  ag = now() - t0;
  printf("substitute1 with its premises in place (%ld times): kernel %.1f ns; generic route %.1f ns (%.1fx); generated "
         "%.1f ns (%.2fx).  Its admission alone: generic %.1f ns, generated %.1f ns (%.1fx fewer)\n",
         REP, ns(tk, REP), ns(tr, REP), tr / tk, ns(tg, REP), tg / tk, ns(ar, REP), ns(ag, REP), ar / ag);
  t0 = now();
  for (long i = 0; i < REP; i++) sink ^= rule_proj1((uint64_t)i & 7, 1, 9);
  tk = now() - t0;
  t0 = now();
  for (long i = 0; i < REP; i++) sink ^= m_proj1(&R, (uint64_t)i & 7, 1, 9);
  tr = now() - t0;
  t0 = now();
  for (long i = 0; i < REP; i++) sink ^= m_proj1(&G, (uint64_t)i & 7, 1, 9);
  tg = now() - t0;
  printf("proj1 (%ld times): kernel %.1f ns; generic route %.1f ns (%.1fx); generated %.1f ns (%.2fx)\n", REP, ns(tk, REP),
         ns(tr, REP), tr / tk, ns(tg, REP), tg / tk);
  route_free(&R);
  route_free(&G);
  (void)sink;
  /* the random workload, one machine at a time on fresh states, at each size */
  for (int si = 0; si < nsizes; si++) {
    size_t nslots = strtoull(sizes[si], NULL, 10);
    double t[3];
    size_t present = 0;
    for (int which = 0; which < 3; which++) {
      init();
      run_k = which == 0, run_r = which == 1, run_g = which == 2;
      if (run_r) route_init(&R, c, T, true, nslots);
      if (run_g) route_init(&G, c, T, false, nslots);
      ops = 0;
      t0 = now();
      random_ops(seed, nops, nslots, false);
      t[which] = now() - t0;
      if (run_r) present = tr_present_count(R.s), route_free(&R);
      if (run_g) present = tr_present_count(G.s), route_free(&G);
    }
    printf("random workload, %zu slots, %ld operations (%zu theorems present at the end): kernel %.1f ns per "
           "operation; generic route %.1f ns (%.1fx); generated %.1f ns (%.2fx); max RSS %ld KB\n",
           nslots, ops, present, ns(t[0], ops), ns(t[1], ops), t[1] / t[0], ns(t[2], ops), t[2] / t[0], max_rss_kb());
  }
  run_k = run_r = run_g = true;
}

int main(int argc, char **argv) {
  bool time_mode = argc > 1 && !strcmp(argv[1], "--time");
  if (argc < 3 || (time_mode && argc < 5)) {
    fprintf(stderr, "usage: %s SEED OPS [SLOTS] | --time SEED OPS SLOTS...\n", argv[0]);
    return 2;
  }
  const tcs_compiled_theory *T = NULL;
  for (size_t i = 0; i < tcs_ncompiled; i++)
    if (!strcmp(tcs_compiled[i].name, "micromath")) T = &tcs_compiled[i];
  tr_ctx *c = tr_ctx_new();
  if (!T || !init() || !T->link(c)) return 2;
  int rc = 0;
  if (time_mode) timing(strtoull(argv[2], NULL, 10), strtol(argv[3], NULL, 10), T, c, argc - 4, argv + 4);
  else {
    size_t nslots = argc > 3 ? strtoull(argv[3], NULL, 10) : 24;
    if (nslots < 10) nslots = 10;
    route_init(&R, c, T, true, nslots);
    route_init(&G, c, T, false, nslots);
    rc = differential(strtoull(argv[1], NULL, 10), strtol(argv[2], NULL, 10), nslots);
    route_free(&R);
    route_free(&G);
  }
  tr_ctx_free(c);
  return rc;
}
