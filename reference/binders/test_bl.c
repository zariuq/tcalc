/* test_bl.c: the binder layer against named controls and against an independent model.
 *
 *   test_bl [N [SEED]]     controls, then N random cases per operation (default 20000)
 *
 * The model is written separately from the rules: terms are trees, shifting and substitution are
 * the index arithmetic of TAPL (Pierce, 6.2: shift(d, c, t), subst(j, s, t)), and a Miller
 * solution is computed by the fixed formula of Dedukti's solve_miller: a variable n under k
 * binders of the term is n - depth + arity when n >= k + depth (bound outside the pattern),
 * otherwise mapping(n - k) + k, or no solution when mapping(n - k) is undefined.
 * Exit 0 when every control holds and the layer agrees with the model on every case.
 */
#include "bl.h"

#include <stdlib.h>
#include <string.h>

/* ---- the model ---- */
enum { MV, MAPP, MLAM, MPI, MCST, MTYPE, MNONE };
typedef struct mt {
  int k, n;
  struct mt *a, *b;
} mt;
static mt *pool;
static size_t npool, cappool;
static mt *mk(int k, int n, mt *a, mt *b) {
  if (npool == cappool) {
    fputs("test_bl: model pool full\n", stderr);
    exit(2);
  }
  mt *t = &pool[npool++];
  *t = (mt){k, n, a, b};
  return t;
}
static mt *m_shift(int d, int c, mt *t) {
  switch (t->k) {
  case MV: return t->n >= c ? mk(MV, t->n + d, 0, 0) : t;
  case MAPP: return mk(MAPP, 0, m_shift(d, c, t->a), m_shift(d, c, t->b));
  case MLAM:
  case MPI: return mk(t->k, 0, m_shift(d, c, t->a), m_shift(d, c + 1, t->b));
  default: return t;
  }
}
static mt *m_subst(int j, mt *s, mt *t) {
  switch (t->k) {
  case MV: return t->n == j ? s : t;
  case MAPP: return mk(MAPP, 0, m_subst(j, s, t->a), m_subst(j, s, t->b));
  case MLAM:
  case MPI: return mk(t->k, 0, m_subst(j, s, t->a), m_subst(j + 1, m_shift(1, 0, s), t->b));
  default: return t;
  }
}
static mt *m_beta(mt *t, mt *u) { return m_shift(-1, 0, m_subst(0, m_shift(1, 0, u), t)); }
/* Dedukti's solve_miller, fixed: depth, arity, mapping[i] for i < depth (-1: not an argument). */
static mt *m_miller(mt *t, int k, int depth, int arity, const int *mapping, bool *ok) {
  switch (t->k) {
  case MV:
    if (t->n < k) return t;
    if (t->n >= k + depth) return mk(MV, t->n - depth + arity, 0, 0);
    if (mapping[t->n - k] < 0) {
      *ok = false;
      return t;
    }
    return mk(MV, mapping[t->n - k] + k, 0, 0);
  case MAPP: return mk(MAPP, 0, m_miller(t->a, k, depth, arity, mapping, ok), m_miller(t->b, k, depth, arity, mapping, ok));
  case MLAM:
  case MPI:
    return mk(t->k, 0, m_miller(t->a, k, depth, arity, mapping, ok), m_miller(t->b, k + 1, depth, arity, mapping, ok));
  default: return t;
  }
}
static bool m_mentions(mt *t, int k) {
  switch (t->k) {
  case MV: return t->n == k;
  case MAPP: return m_mentions(t->a, k) || m_mentions(t->b, k);
  case MLAM:
  case MPI: return m_mentions(t->a, k) || m_mentions(t->b, k + 1);
  default: return false;
  }
}

/* ---- the layer ---- */
static tr_ctx *C;
static tr_state *S;
static rk_engine E;
static bl *B;
static uint32_t s_app, s_lam, s_pi, s_cst, s_type, s_none;

static tr_term to_tr(mt *t) {
  tr_term a[2];
  switch (t->k) {
  case MV: return bl_var(B, (uint32_t)t->n);
  case MAPP: a[0] = to_tr(t->a), a[1] = to_tr(t->b); return tr_app(C, s_app, a);
  case MLAM: a[0] = to_tr(t->a), a[1] = to_tr(t->b); return tr_app(C, s_lam, a);
  case MPI: a[0] = to_tr(t->a), a[1] = to_tr(t->b); return tr_app(C, s_pi, a);
  case MCST: a[0] = tr_code(C, t->n); return tr_app(C, s_cst, a);
  case MTYPE: return tr_app(C, s_type, NULL);
  default: return tr_app(C, s_none, NULL);
  }
}

static uint64_t rng = 88172645463325252ULL;
static uint32_t rnd(uint32_t n) {
  rng ^= rng << 13, rng ^= rng >> 7, rng ^= rng << 17;
  return (uint32_t)(rng % n);
}
static mt *gen(int depth, int nfree) {
  uint32_t k = rnd(10);
  if (depth == 0 || k < 3) {
    uint32_t c = rnd(nfree + 3);
    if ((int)c < nfree) return mk(MV, (int)c, 0, 0);
    if (c == (uint32_t)nfree) return mk(MCST, (int)rnd(3), 0, 0);
    return c == (uint32_t)nfree + 1 ? mk(MTYPE, 0, 0, 0) : mk(MNONE, 0, 0, 0);
  }
  if (k < 6) return mk(MAPP, 0, gen(depth - 1, nfree), gen(depth - 1, nfree));
  return mk(k < 8 ? MLAM : MPI, 0, gen(depth - 1, nfree), gen(depth - 1, nfree + 1));
}

static int failures;
static void expect(bool cond, const char *what) {
  if (!cond) {
    failures++;
    fprintf(stderr, "FAIL: %s\n", what);
  }
}

/* t[s] by the layer; TR_NONE when it has no value */
static tr_term ev(tr_term t, tr_term s) {
  tr_term r;
  return bl_ev(B, t, s, &r) ? r : TR_NONE;
}
static tr_term rd(const char *text) {
  tr_scope *sc = tr_scope_new();
  tr_term t = tr_read(C, sc, text);
  tr_scope_free(sc);
  if (t == TR_NONE) {
    fprintf(stderr, "test_bl: bad term %s\n", text);
    exit(2);
  }
  return t;
}
static tr_term V(uint32_t n) { return bl_var(B, n); }
static tr_term AP(tr_term f, tr_term x) {
  tr_term a[2] = {f, x};
  return tr_app(C, s_app, a);
}
static tr_term LAM(tr_term body) {
  tr_term a[2] = {tr_app(C, s_none, NULL), body};
  return tr_app(C, s_lam, a);
}

static void controls(void) {
  tr_term c = rd("cst(7)"), q;
  (void)q;
  /* shifting */
  expect(ev(V(0), bl_sh(B)) == V(1), "var 0 shifted is var 1");
  expect(ev(LAM(V(0)), bl_sh(B)) == LAM(V(0)), "a bound variable is not shifted");
  expect(ev(LAM(V(1)), bl_sh(B)) == LAM(V(2)), "a free variable under a binder is shifted");
  expect(ev(LAM(V(1)), bl_sh(B)) != LAM(V(1)), "negative: the free variable must move");
  /* capture: (\y. x)[x := y], in de Bruijn (\. var 1)[var 0 /] */
  tr_term subst0 = bl_cs(B, V(0), bl_id(B));
  expect(ev(LAM(V(1)), subst0) == LAM(V(1)), "substitution under a binder does not capture");
  expect(ev(LAM(V(1)), subst0) != LAM(V(0)), "negative: the captured result is refused");
  expect(ev(AP(V(0), V(1)), bl_cs(B, c, bl_id(B))) == AP(c, V(0)), "beta: var 0 replaced, var 1 moves down");
  /* lifting a cons through two binders */
  expect(ev(LAM(LAM(AP(V(2), V(3)))), bl_cs(B, V(5), bl_id(B))) == LAM(LAM(AP(rd("var(s(s(s(s(s(s(s(z))))))))"), V(2)))),
         "a substituted variable is shifted by the binders it goes under");
  /* Miller, depth 1, arity 0 (the first case of the Dedukti bug): g (u => c q q) and g (u => c u q) */
  tr_term cc = rd("cst(3)");
  tr_term rho10 = bl_rho(B, 1, NULL, 0);
  expect(ev(AP(AP(cc, V(1)), V(1)), rho10) == AP(AP(cc, V(0)), V(0)), "depth 1 arity 0: q is solved, moved down by one");
  expect(ev(AP(AP(cc, V(0)), V(1)), rho10) == TR_NONE, "depth 1 arity 0: u is the pattern's binder, no solution");
  expect(ev(AP(AP(cc, V(1)), V(0)), rho10) == TR_NONE, "depth 1 arity 0: other order, no solution");
  expect(ev(V(0), rho10) == TR_NONE, "depth 1 arity 0: the binder alone, no solution");
  /* Miller, depth 2, arity 1, applied to the outer binder u: h (u => v => c (F u) (F u)) */
  uint32_t ys1[1] = {1};
  tr_term rho21 = bl_rho(B, 2, ys1, 1);
  expect(ev(AP(AP(cc, V(2)), V(1)), rho21) == AP(AP(cc, V(1)), V(0)),
         "depth 2 arity 1: q moves by depth - arity = 1, u becomes the argument");
  expect(ev(AP(AP(cc, V(0)), V(0)), rho21) == TR_NONE, "depth 2 arity 1: v is not an argument, no solution");
  expect(ev(AP(AP(cc, V(2)), V(1)), rho21) != AP(AP(cc, V(2)), V(0)),
         "negative: leaving q's index unchanged (the missing depth - arity shift) is refused");
  /* permuted arguments: X v u at depth 2 */
  uint32_t ys2[2] = {0, 1};
  tr_term rho22 = bl_rho(B, 2, ys2, 2);
  expect(ev(AP(V(1), V(0)), rho22) == AP(V(0), V(1)), "depth 2 arity 2: arguments are renumbered in their order");
  expect(ev(AP(V(2), V(0)), rho22) == AP(V(2), V(1)), "depth 2 arity 2: an outer variable keeps depth - arity = 0");
  /* a lambda inside the solution keeps its own variable */
  expect(ev(LAM(AP(V(0), V(2))), rho10) == LAM(AP(V(0), V(1))), "an internal binder is kept, the outer variable moves");
  expect(ev(LAM(AP(V(0), V(1))), rho10) == TR_NONE, "under an internal binder the pattern's binder is still forbidden");
  /* mentions */
  expect(bl_mentions(B, AP(V(1), LAM(V(1))), 0) != 0, "var 0 occurs (as var 1 under a binder)");
  expect(bl_mentions(B, LAM(V(0)), 0) == 0, "a bound variable is not a free occurrence");
  expect(bl_mentions(B, AP(V(1), V(2)), 0) == 0, "negative: var 0 does not occur");
}

static void differential(int n) {
  for (int i = 0; i < n; i++) {
    npool = 0;
    int nfree = (int)rnd(4) + 1;
    mt *t = gen(5, nfree), *u = gen(3, nfree);
    tr_term T = to_tr(t), U = to_tr(u);
    /* shift */
    if (ev(T, bl_sh(B)) != to_tr(m_shift(1, 0, t))) {
      failures++;
      fprintf(stderr, "FAIL: shift differs (case %d)\n", i);
    }
    /* beta instantiation */
    if (ev(T, bl_cs(B, U, bl_id(B))) != to_tr(m_beta(t, u))) {
      failures++;
      fprintf(stderr, "FAIL: beta instantiation differs (case %d)\n", i);
    }
    /* instantiation under k lifts: t[lf^k(u/)] = shift(-1, k, subst(k, shift(k+1, 0, u), t)) */
    int k = (int)rnd(3);
    tr_term s = bl_cs(B, U, bl_id(B));
    for (int j = 0; j < k; j++) s = bl_lf(B, s);
    mt *want = m_shift(-1, k, m_subst(k, m_shift(k + 1, 0, u), t));
    if (ev(T, s) != to_tr(want)) {
      failures++;
      fprintf(stderr, "FAIL: lifted instantiation differs (case %d, k %d)\n", i, k);
    }
    /* Miller */
    int depth = (int)rnd(4), arity = depth ? (int)rnd((uint32_t)depth + 1) : 0, mapping[8];
    uint32_t ys[8];
    for (int j = 0; j < depth; j++) mapping[j] = -1;
    for (int j = 0; j < arity; j++) {
      int y;
      do y = (int)rnd((uint32_t)depth);
      while (mapping[y] >= 0);
      mapping[y] = arity - 1 - j;
      ys[j] = (uint32_t)y;
    }
    bool ok = true;
    mt *sol = m_miller(t, 0, depth, arity, mapping, &ok);
    tr_term got = ev(T, bl_rho(B, (uint32_t)depth, ys, (uint32_t)arity));
    if (ok ? got != to_tr(sol) : got != TR_NONE) {
      failures++;
      fprintf(stderr, "FAIL: Miller solution differs (case %d, depth %d, arity %d, model %s)\n", i, depth, arity,
              ok ? "solved" : "no solution");
    }
    /* mentions */
    int v = (int)rnd((uint32_t)nfree + 1);
    if ((bl_mentions(B, T, (uint32_t)v) != 0) != m_mentions(t, v)) {
      failures++;
      fprintf(stderr, "FAIL: mentions differs (case %d, var %d)\n", i, v);
    }
    if (failures > 20) break;
  }
}

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 20000;
  if (argc > 2) rng = (uint64_t)strtoull(argv[2], NULL, 10) * 2654435761u + 1;
  if (getenv("BL_FAULT")) bl_fault = atoi(getenv("BL_FAULT"));
  cappool = 1 << 20;
  pool = malloc(cappool * sizeof *pool);
  C = tr_ctx_new();
  S = tr_state_new(C);
  rk_engine_init(&E, C, S);
  static const uint8_t b00[2] = {0, 0}, b01[2] = {0, 1}, bd[1] = {BL_DATA};
  bl_con cons[] = {{"app", 2, b00}, {"lam", 2, b01}, {"pi", 2, b01}, {"cst", 1, bd}, {"type", 0, NULL}, {"none", 0, NULL}};
  B = bl_new(&E, cons, sizeof cons / sizeof *cons);
  s_app = bl_symbol(B, 0), s_lam = bl_symbol(B, 1), s_pi = bl_symbol(B, 2), s_cst = bl_symbol(B, 3);
  s_type = bl_symbol(B, 4), s_none = bl_symbol(B, 5);
  controls();
  int after_controls = failures;
  differential(n);
  printf("test_bl%s: %d control failures, %d differential failures over %d cases; %llu firings admitted, %llu refused, "
         "%zu facts present\n",
         bl_fault ? " (fault planted)" : "", after_controls, failures - after_controls, n,
         (unsigned long long)E.fired, (unsigned long long)E.refused, tr_present_count(S));
  bl_free(B);
  rk_engine_free(&E);
  tr_state_free(S);
  tr_ctx_free(C);
  free(pool);
  return failures ? 1 : 0;
}
