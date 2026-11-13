/* Random differential for conversions (tc_convert with CV_REFL, CV_SYM, CV_CONG, CV_UNFOLD over tc_def
   definitions, and the rho name law), against a naive reference written from tcalc.h:
   "tc_def adds a defined constructor whose unfolding is checked by conversion steps".

   usage: diff_conv FIRST_SEED COUNT

   Reference semantics. A certificate proves l = r:
     REFL      l and r are the same term, or (rho set) their rho normal forms exist and are equal, where
               the rho normal form rewrites quote(drop(n)) to n everywhere, bottom-up;
     SYM(k)    k proves r = l;
     CONG(c,k) l and r both have head c with c's arity, and k[i] proves l_i = r_i;
     UNFOLD(c,k)  l has the defined head c, and k proves (c's body at l's arguments) = r.
   tc_convert(p, cert, t) is admitted iff the certificate proves term(p) = t or t = term(p). Soundness
   is also checked against the definitional (delta, then rho) normal forms: an admitted conversion
   relates two terms with the same normal form. Valid certificates are synthesized by the reference;
   others are mutated. */
#include "ref.h"
#include "tcalc.h"

static uint64_t rng_s;
static uint64_t rnd(void) { rng_s ^= rng_s >> 12; rng_s ^= rng_s << 25; rng_s ^= rng_s >> 27; return rng_s * 0x2545F4914F6CDD1Dull; }
static int rint_(int n) { return n <= 0 ? 0 : (int)(rnd() % (uint64_t)n); }
static bool chance(double p) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0) < p; }

enum { S_D = 1, S_T = 2, S_NM = 3, S_PR = 4 };
/* base constructors: 0 Z:D 1 O:D 2 S:D->D 3 P:D,D->D 4 A1:D->T 5 A2:D,D->T
   rho: 6 QUOTE:Pr->Nm 7 DROP:Nm->Pr 8 NIL:Pr 9 SEND:Nm,Pr->Pr 10 HAS:Nm->T 11 RUN:Pr->T
   definitions (ids 12..15): 12 F(x) := P(x,Z)   13 G(x,y) := S(P(y,x))   14 K := S(O)   15 H(x) := F(S(x)) */
#define NBASE 12
#define NDEF 4
static const RCon BASE[NBASE] = {
  { S_D, 0, { 0 } }, { S_D, 0, { 0 } }, { S_D, 1, { S_D } }, { S_D, 2, { S_D, S_D } }, { S_T, 1, { S_D } }, { S_T, 2, { S_D, S_D } },
  { S_NM, 1, { S_PR } }, { S_PR, 1, { S_NM } }, { S_PR, 0, { 0 } }, { S_PR, 2, { S_NM, S_PR } }, { S_T, 1, { S_NM } }, { S_T, 1, { S_PR } },
};
static const RT *defbody[NDEF]; static int defar[NDEF] = { 1, 2, 0, 1 };
static bool rho_on;
static bool is_def(int c) { return c >= NBASE && c < NBASE + NDEF; }

static const RT *app1(int c, const RT *a) { const RT *x[1] = { a }; return r_app(c, x); }
static const RT *app2(int c, const RT *a, const RT *b) { const RT *x[2] = { a, b }; return r_app(c, x); }
static const RT *unfold(const RT *t) { return r_subst(defbody[t->head - NBASE], t->a); }   /* body at the arguments */
static const RT *dnf(const RT *t) {                          /* delta normal form */
  if (t->kind != RK_APP) return t;
  if (is_def(t->head)) return dnf(unfold(t));
  const RT *a[R_MAXAR];
  for (int i = 0; i < t->n; i++) a[i] = dnf(t->a[i]);
  return r_app(t->head, a);
}
static const RT *rnf(const RT *t) {                          /* rho normal form: quote(drop(n)) -> n, bottom-up */
  if (t->kind != RK_APP) return t;
  const RT *a[R_MAXAR];
  for (int i = 0; i < t->n; i++) a[i] = rnf(t->a[i]);
  if (rho_on && t->head == 6 && a[0]->kind == RK_APP && a[0]->head == 7) return a[0]->a[0];
  return r_app(t->head, a);
}

/* certificates (reference form) */
typedef struct RC { int kind, con, n; struct RC *kid; } RC;
static RC pool[1 << 16]; static int npool;
static RC *mkc(int kind, int con, int n) { if (npool >= (1 << 16)) return NULL; RC *c = &pool[npool++]; c->kind = kind; c->con = con; c->n = n; c->kid = NULL; return c; }
static RC *kids(int n) { if (npool + n > (1 << 16)) return NULL; RC *k = &pool[npool]; npool += n; memset(k, 0, (size_t)n * sizeof *k); return k; }

static bool r_check(const RC *c, const RT *l, const RT *r, int d) {
  if (!c || d > 1000) return false;
  switch (c->kind) {
    case CV_REFL: if (r_equal(l, r)) return true; return rho_on && r_equal(rnf(l), rnf(r));
    case CV_SYM: return r_check(c->kid, r, l, d + 1);
    case CV_CONG:
      if (c->con < 0 || c->con >= NBASE + NDEF || l->kind != RK_APP || r->kind != RK_APP || l->head != c->con || r->head != c->con) return false;
      if (c->n != l->n || (c->n > 0 && !c->kid)) return false;
      for (int i = 0; i < c->n; i++) if (!r_check(&c->kid[i], l->a[i], r->a[i], d + 1)) return false;
      return true;
    case CV_UNFOLD:
      if (!is_def(c->con) || !c->kid || l->kind != RK_APP || l->head != c->con) return false;
      return r_check(c->kid, unfold(l), r, d + 1);
  }
  return false;
}
/* a certificate for l = r when they are delta-equal (it follows the definitions) */
static RC *synth(const RT *l, const RT *r, int d) {
  if (d > 60) return NULL;
  if (r_equal(l, r)) return mkc(CV_REFL, 0, 0);
  if (l->kind == RK_APP && is_def(l->head)) { RC *c = mkc(CV_UNFOLD, l->head, 0); if (c) c->kid = synth(unfold(l), r, d + 1); return c && c->kid ? c : NULL; }
  if (r->kind == RK_APP && is_def(r->head)) { RC *c = mkc(CV_SYM, 0, 0); if (c) c->kid = synth(r, l, d + 1); return c && c->kid ? c : NULL; }
  if (l->kind == RK_APP && r->kind == RK_APP && l->head == r->head) {
    RC *c = mkc(CV_CONG, l->head, l->n); if (!c) return NULL;
    if (l->n) { c->kid = kids(l->n); if (!c->kid) return NULL; for (int i = 0; i < l->n; i++) { RC *k = synth(l->a[i], r->a[i], d + 1); if (!k) return NULL; c->kid[i] = *k; } }
    return c;
  }
  return rho_on ? mkc(CV_REFL, 0, 0) : NULL;              /* left to the rho law */
}
static void mutate(RC *c, int budget) {
  if (!c || budget <= 0) return;
  int x = rint_(6);
  if (x == 0) c->kind = rint_(4);
  else if (x == 1) c->con = rint_(NBASE + NDEF);
  else if (x == 2 && c->kind == CV_CONG) c->n = rint_(3);
  else if (x == 3 && c->kind == CV_CONG && c->n && c->kid) mutate(&c->kid[rint_(c->n)], budget - 1);
  else if (c->kid) mutate(c->kid, budget - 1);
  else c->kind = CV_SYM;
}

/* kernel side */
static int kcon[NBASE + NDEF];
static Term k_of(const RT *t) {
  if (t->kind == RK_HOLE) return tc_v(t->head);
  if (t->kind == RK_NAME) return tc_name(t->sort, t->id);
  Term a[R_MAXAR];
  for (int i = 0; i < t->n; i++) if (!(a[i] = k_of(t->a[i]))) return 0;
  return tc_app(kcon[t->head], t->n ? a : NULL);
}
static Conv kpool[1 << 16]; static int nkpool;
static const Conv *k_cert(const RC *c) {
  if (!c || nkpool >= (1 << 16) - 8) return NULL;
  Conv *k = &kpool[nkpool++]; memset(k, 0, sizeof *k);
  k->kind = (uint8_t)c->kind; k->con = c->con >= 0 && c->con < NBASE + NDEF ? kcon[c->con] : c->con; k->n = c->n;
  if (c->kind == CV_CONG && c->n > 0 && c->kid) {
    Conv *ks = &kpool[nkpool]; nkpool += c->n;
    if (nkpool >= (1 << 16)) return NULL;
    for (int i = 0; i < c->n; i++) { const Conv *s = k_cert(&c->kid[i]); if (!s) return NULL; ks[i] = *s; }
    k->kid = ks;
  } else if (c->kid) k->kid = k_cert(c->kid);
  return k;
}

/* generators */
static const RT *gen_d(int depth) {
  int c = depth <= 0 ? rint_(2) : (chance(0.35) ? NBASE + rint_(NDEF) : rint_(4));
  if (c >= NBASE) {
    const RT *a[2]; for (int i = 0; i < defar[c - NBASE]; i++) a[i] = gen_d(depth - 1);
    return r_app(c, a);
  }
  const RT *a[2]; for (int i = 0; i < BASE[c].arity; i++) a[i] = gen_d(depth - 1);
  return r_app(c, a);
}
static const RT *gen_pr(int depth);
static const RT *gen_nm(int depth) { return chance(0.5) || depth <= 0 ? r_name(S_NM, (uint64_t)rint_(3)) : app1(6, gen_pr(depth - 1)); }
static const RT *gen_pr(int depth) {
  int x = depth <= 0 ? 0 : rint_(3);
  if (x == 0) return r_app(8, NULL);
  if (x == 1) return app1(7, gen_nm(depth - 1));
  return app2(9, gen_nm(depth - 1), gen_pr(depth - 1));
}
static const RT *gen_t(void) {
  int x = rint_(rho_on ? 4 : 2);
  if (x == 0) return app1(4, gen_d(3));
  if (x == 1) return app2(5, gen_d(2), gen_d(2));
  if (x == 2) return app1(10, gen_nm(3));
  return app1(11, gen_pr(3));
}
static const RT *variant(const RT *t, int depth) {           /* a delta (or rho) variant: unfold or fold here and there */
  if (t->kind != RK_APP) return t;
  if (is_def(t->head) && chance(0.4)) return variant(unfold(t), depth + 1);
  if (rho_on && t->sort == S_NM && chance(0.2)) return app1(6, app1(7, t));                 /* n = quote(drop(n)) */
  if (!is_def(t->head) && t->sort == S_D && chance(0.15)) {                                  /* fold: x -> ... */
    if (t->head == 3 && t->a[1]->kind == RK_APP && t->a[1]->head == 0) return app1(NBASE + 0, variant(t->a[0], depth + 1));   /* P(x,Z) <- F(x) */
  }
  const RT *a[R_MAXAR];
  for (int i = 0; i < t->n; i++) a[i] = variant(t->a[i], depth + 1);
  return r_app(t->head, a);
}

static unsigned long n_cmp, n_acc, n_fail, n_valid, n_unsound;
static bool run(uint64_t seed) {
  rng_s = seed * 0x9E3779B97F4A7C15ull + 0x4242ull; for (int i = 0; i < 8; i++) rnd();
  r_na = 0; npool = 0; nkpool = 0;
  rho_on = chance(0.5);
  if (!tc_init(1u << 13, 1u << 9)) return false;
  if (tc_sort(0) != S_D || tc_sort(SORT_PROVABLE) != S_T || tc_sort(0) != S_NM || tc_sort(0) != S_PR) return true;
  r_ncon = NBASE + NDEF;
  for (int i = 0; i < NBASE; i++) {
    r_con[i] = BASE[i];
    Binder b[2]; for (int j = 0; j < BASE[i].arity; j++) b[j] = (Binder){ BASE[i].asort[j], 0, 0 };
    if ((kcon[i] = tc_con(BASE[i].sort, 0, BASE[i].arity, b)) != i) return true;
  }
  for (int i = 0; i < 3; i++) (void)tc_fresh_name();
  /* definitions, each in its own context */
  Binder dd[2] = { { S_D, 0, 0 }, { S_D, 0, 0 } };
  const RT *x = r_hole(0, S_D), *y = r_hole(1, S_D), *zz = r_app(0, NULL), *oo = r_app(1, NULL);
  defbody[0] = app2(3, x, zz); defbody[1] = app1(2, app2(3, y, x)); defbody[2] = app1(2, oo);
  for (int i = 0; i < NDEF; i++) {
    r_con[NBASE + i] = (RCon){ S_D, (uint8_t)defar[i], { S_D, S_D } };
    if (i == 3) defbody[3] = app1(NBASE + 0, app1(2, x));     /* H(x) := F(S(x)) */
    if (!tc_ctx(defar[i], dd)) return true;
    Term body = k_of(defbody[i]);
    if (!body || (kcon[NBASE + i] = tc_def(S_D, 0, defar[i], 0, body)) < 0) { printf("seed %llu: tc_def %d refused\n", (unsigned long long)seed, i); n_fail++; return true; }
  }
  if (rho_on) tc_set_rho_con(kcon[6], kcon[7], false);
  tc_protect(1); tc_seal();
  for (int step = 0; step < 30; step++) {
    const RT *l = gen_t();
    const RT *r = chance(0.7) ? variant(l, 0) : gen_t();
    RC *c = synth(l, r, 0);
    bool valid = c != NULL;
    if (!c || chance(0.35)) { if (!c) c = mkc(rint_(4), rint_(NBASE + NDEF), rint_(3)); else mutate(c, 3); }
    if (!c) continue;
    bool racc = r_check(c, l, r, 0) || r_check(c, r, l, 0);
    Term kl = k_of(l), kr = k_of(r);
    if (!kl || !kr) { printf("seed %llu: could not build terms\n", (unsigned long long)seed); n_fail++; return true; }
    Occ o = tc_post(0, kl);
    if (!o) { n_fail++; printf("seed %llu: post refused\n", (unsigned long long)seed); return true; }
    const Conv *kc = k_cert(c);
    Occ got = kc ? tc_convert(o, kc, kr) : 0;
    n_cmp++; n_valid += valid;
    if ((got != 0) != racc) {
      char a[300], b[300]; r_show(l, a, 300); r_show(r, b, 300);
      printf("DISAGREEMENT seed %llu step %d (rho %d): kernel %s, reference %s; %s = %s; certificate kind %d con %d n %d\n",
             (unsigned long long)seed, step, rho_on, got ? "accepts" : "refuses", racc ? "accepts" : "refuses", a, b, c->kind, c->con, c->n);
      n_fail++; return true;
    }
    if (got) {
      n_acc++;
      if (!r_equal(rnf(dnf(l)), rnf(dnf(r))) && !r_equal(dnf(rnf(l)), dnf(rnf(r)))) { n_unsound++; printf("UNSOUND seed %llu step %d\n", (unsigned long long)seed, step); }
      if (tc_term(got) != kr) { printf("seed %llu: converted occurrence holds another term\n", (unsigned long long)seed); n_fail++; return true; }
    }
  }
  return true;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s FIRST_SEED COUNT\n", argv[0]); return 2; }
  uint64_t first = strtoull(argv[1], NULL, 10), count = strtoull(argv[2], NULL, 10);
  r_cap = 1u << 22; r_arena = malloc(r_cap * sizeof *r_arena);
  if (!r_arena) return 3;
  for (uint64_t s = first; s < first + count; s++) if (!run(s)) { printf("tc_init failed\n"); return 3; }
  printf("summary: seeds %llu..%llu; conversions compared %lu (%lu with a synthesized certificate, %lu admitted); admitted but not definitionally equal %lu; scenarios ended by a disagreement %lu\n",
         (unsigned long long)first, (unsigned long long)(first + count - 1), n_cmp, n_valid, n_acc, n_unsound, n_fail);
  return n_fail || n_unsound ? 1 : 0;
}
