/* Random differential for binders: bound holes, dependency declarations and separation guards,
   against a naive reference written from tcalc.h ("a bound hole x must stay apart from every hole
   that does not depend on x"; binder positions hold bound variables).

   usage: diff_bind FIRST_SEED COUNT

   Reference semantics (keep-only rules, optional hole values). The holes of a rule are declared in
   order: a bound hole (sort V) holds a bound variable; any other hole may declare that it depends on
   earlier bound holes. A firing is admitted iff the keeps match their facts under one assignment that
   agrees with the given values, every bound hole holds a term of its sort (bound holes: a bound
   variable), and for every bound hole h and every other hole j that does not depend on h, the value
   of j does not mention the variable held by h (anywhere, bound or free); the made fact (all its
   holes bound) is added. Bound variables are compared by name; there is no renaming. */
#include "ref.h"
#include "tcalc.h"

static uint64_t rng_s;
static uint64_t rnd(void) { rng_s ^= rng_s >> 12; rng_s ^= rng_s << 25; rng_s ^= rng_s >> 27; return rng_s * 0x2545F4914F6CDD1Dull; }
static int rint_(int n) { return n <= 0 ? 0 : (int)(rnd() % (uint64_t)n); }
static bool chance(double p) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0) < p; }

enum { S_D = 1, S_T = 2, S_V = 3 };
/* 0 Z:D  1 O:D  2 S:D->D  3 P:D,D->D  4 VAR:V->D  5 LAM:(x:V bound),(D over x)->D
   6 A1:D->T  7 A2:D,D->T  8 ALL:(x:V bound),(D over x)->T */
static const RCon THEORY[9] = {
  { S_D, 0, { 0 } }, { S_D, 0, { 0 } }, { S_D, 1, { S_D } }, { S_D, 2, { S_D, S_D } }, { S_D, 1, { S_V } },
  { S_D, 2, { S_V, S_D } }, { S_T, 1, { S_D } }, { S_T, 2, { S_D, S_D } }, { S_T, 2, { S_V, S_D } },
};
#define NCON 9
static bool binder_con(int c) { return c == 5 || c == 8; }
#define BV_BASE (1ull << 60)
static const RT *bv(int i) { return r_name(S_V, BV_BASE + (uint64_t)i); }

typedef struct { int nholes; uint8_t hsort[R_MAXH]; bool bound[R_MAXH]; uint32_t deps[R_MAXH]; int nkeep; const RT *keep[2]; const RT *make; } BRule;
static BRule rules[5]; static int krule[5], nrules;
typedef struct { const RT *t; bool alive; Occ k; } BFact;
static BFact facts[256]; static int nfacts;

static bool mentions(const RT *t, const RT *v) {
  if (t->kind == RK_NAME) return t->sort == v->sort && t->id == v->id;
  for (int i = 0; i < t->n; i++) if (mentions(t->a[i], v)) return true;
  return false;
}
static bool r_fire_bind(const BRule *r, const int *keep, const RT *const *in, const RT **out) {
  const RT *B[R_MAXH];
  for (int h = 0; h < r->nholes; h++) B[h] = in ? in[h] : NULL;
  for (int j = 0; j < r->nkeep; j++) {
    if (keep[j] < 0 || !facts[keep[j]].alive || !r_unify(r->keep[j], facts[keep[j]].t, B)) return false;
  }
  const RT *V[R_MAXH];
  for (int h = 0; h < r->nholes; h++) {
    V[h] = B[h] && r_ground(B[h], B) ? r_subst(B[h], B) : NULL;
    if (!V[h]) continue;
    if (V[h]->sort != r->hsort[h]) return false;
    if (r->bound[h] && !(V[h]->kind == RK_NAME && V[h]->sort == S_V && V[h]->id >= BV_BASE)) return false;
  }
  for (int h = 0; h < r->nholes; h++) if (r->bound[h] && V[h])
    for (int j = 0; j < r->nholes; j++) if (j != h && V[j] && !(r->deps[j] >> h & 1) && mentions(V[j], V[h])) return false;
  if (!r_ground(r->make, B)) return false;
  *out = r_subst(r->make, B);
  return true;
}

static Term k_of(const RT *t) {
  if (t->kind == RK_NAME) return t->sort == S_V && t->id >= BV_BASE ? tc_bv(S_V, (unsigned)(t->id - BV_BASE)) : tc_name(t->sort, t->id);
  if (t->kind == RK_HOLE) return tc_v(t->head);
  Term a[R_MAXAR];
  for (int i = 0; i < t->n; i++) if (!(a[i] = k_of(t->a[i]))) return 0;
  return tc_app(t->head, t->n ? a : NULL);
}
static int k_show(Term t, char *buf, int cap) {
  uint8_t kind; uint32_t head; int ar; const Term *args;
  tc_node(t, &kind, &head, &ar, &args);
  if (kind == K_BV) return snprintf(buf, (size_t)cap, "bv");   /* bound variables: compared through the reference's names below */
  if (kind == K_NAME) return snprintf(buf, (size_t)cap, "n%d#%llu", tc_sort_of(t), (unsigned long long)tc_name_id(t));
  int n = snprintf(buf, (size_t)cap, "c%u", head);
  if (ar) { n += snprintf(buf + n, (size_t)(cap - n), "("); for (int i = 0; i < ar && n < cap - 8; i++) { if (i) buf[n++] = ','; n += k_show(args[i], buf + n, cap - n); } n += snprintf(buf + n, (size_t)(cap - n), ")"); }
  return n;
}

/* generators: bvars 0..2; a binder's first argument is a bound variable (ground) or a bound hole */
static const RT *gen_d(int depth, const BRule *r, uint32_t allowed, int nbv_in_scope) {
  if (r && chance(depth <= 0 ? 0.6 : 0.35)) {
    int c[R_MAXH], n = 0;
    for (int h = 0; h < r->nholes; h++) if ((allowed >> h & 1) && r->hsort[h] == S_D) c[n++] = h;
    if (n) return r_hole(c[rint_(n)], S_D);
  }
  int k = depth <= 0 ? rint_(2) : rint_(6);
  const RT *a[2];
  if (r && (k == 4 || k == 5)) {                           /* a rule pattern holds no concrete bound variable */
    bool any = false;
    for (int h = 0; h < r->nholes; h++) any |= (allowed >> h & 1) && r->bound[h];
    if (!any) k = 2 + rint_(2);
  }
  if (k == 4) {                                            /* VAR(v): a bound variable, or a bound hole */
    int c[R_MAXH], n = 0;
    if (r) for (int h = 0; h < r->nholes; h++) if ((allowed >> h & 1) && r->bound[h]) c[n++] = h;
    a[0] = n ? r_hole(c[rint_(n)], S_V) : bv(rint_(3));
    (void)nbv_in_scope;
    return r_app(4, a);
  }
  if (k == 5) {
    int c[R_MAXH], n = 0;
    if (r) for (int h = 0; h < r->nholes; h++) if ((allowed >> h & 1) && r->bound[h]) c[n++] = h;
    a[0] = n ? r_hole(c[rint_(n)], S_V) : bv(rint_(3));
    a[1] = gen_d(depth - 1, r, allowed, nbv_in_scope + 1);
    return r_app(5, a);
  }
  for (int i = 0; i < THEORY[k].arity; i++) a[i] = gen_d(depth - 1, r, allowed, nbv_in_scope);
  return r_app(k, a);
}
static const RT *gen_t(const BRule *r, uint32_t allowed) {
  int k = 6 + rint_(3);
  const RT *a[2];
  if (r && k == 8) {
    bool any = false;
    for (int h = 0; h < r->nholes; h++) any |= (allowed >> h & 1) && r->bound[h];
    if (!any) k = 6 + rint_(2);
  }
  if (k == 8) {
    int c[R_MAXH], n = 0;
    if (r) for (int h = 0; h < r->nholes; h++) if ((allowed >> h & 1) && r->bound[h]) c[n++] = h;
    a[0] = n ? r_hole(c[rint_(n)], S_V) : bv(rint_(3));
    a[1] = gen_d(1 + rint_(2), r, allowed, 1);
    return r_app(8, a);
  }
  for (int i = 0; i < THEORY[k].arity; i++) a[i] = gen_d(1 + rint_(2), r, allowed, 0);
  return r_app(k, a);
}

static unsigned long n_cmp, n_acc, n_fail, n_setup, n_sep_refused;
static bool run(uint64_t seed) {
  rng_s = seed * 0x9E3779B97F4A7C15ull + 0x3131ull; for (int i = 0; i < 8; i++) rnd();
  r_na = 0; nfacts = 0;
  if (!tc_init(1u << 13, 1u << 9)) return false;
  if (tc_sort(0) != S_D || tc_sort(SORT_PROVABLE) != S_T || tc_sort(0) != S_V) { n_setup++; return true; }
  r_ncon = NCON;
  for (int i = 0; i < NCON; i++) {
    r_con[i] = THEORY[i];
    Binder b[2];
    for (int j = 0; j < THEORY[i].arity; j++) b[j] = (Binder){ THEORY[i].asort[j], 0, 0 };
    if (binder_con(i)) { b[0].bound = 1; b[1].deps = 1; }
    if (tc_con(THEORY[i].sort, 0, THEORY[i].arity, b) != i) { n_setup++; return true; }
  }
  for (int i = 0; i < 3; i++) if (!tc_bv(S_V, (unsigned)i)) { n_setup++; return true; }
  nrules = 2 + rint_(3);
  for (int k = 0; k < nrules; k++) {
    BRule *r = &rules[k]; memset(r, 0, sizeof *r);
    r->nholes = 2 + rint_(4);
    uint32_t boundmask = 0;
    for (int h = 0; h < r->nholes; h++) {
      if (chance(0.4)) { r->hsort[h] = S_V; r->bound[h] = true; boundmask |= 1u << h; }
      else { r->hsort[h] = S_D; r->deps[h] = (uint32_t)(rnd() & boundmask); }
    }
    uint32_t all = (1u << r->nholes) - 1;
    r->nkeep = 1 + rint_(2);
    for (int j = 0; j < r->nkeep; j++) r->keep[j] = gen_t(r, all);
    r->make = gen_t(r, all);
    Binder b[R_MAXH];
    for (int h = 0; h < r->nholes; h++) b[h] = (Binder){ r->hsort[h], (uint8_t)r->bound[h], r->deps[h] };
    if (!tc_ctx(r->nholes, b)) { n_setup++; return true; }
    Rule kr; memset(&kr, 0, sizeof kr); kr.nkeep = (uint8_t)r->nkeep; kr.fresh = -1;
    bool ok = true;
    for (int j = 0; j < r->nkeep; j++) { kr.keep[j] = (Pat){ k_of(r->keep[j]), 0 }; ok &= kr.keep[j].t != 0; }
    kr.make = (Pat){ k_of(r->make), 0 }; ok &= kr.make.t != 0;
    if (!ok || (krule[k] = tc_rule(&kr)) < 0) { n_setup++; return true; }   /* e.g. a binder over a non-bound hole */
  }
  for (int f = 0; f < 12; f++) {
    const RT *t = gen_t(NULL, 0);
    if (f < 12 && chance(0.6)) {                           /* an instance of a premise */
      const BRule *r = &rules[rint_(nrules)];
      const RT *B[R_MAXH];
      for (int h = 0; h < r->nholes; h++) B[h] = r->bound[h] ? bv(rint_(3)) : gen_d(1, NULL, 0, 0);
      t = r_subst(r->keep[rint_(r->nkeep)], B);
    }
    Term kt = k_of(t);
    Occ o = kt ? tc_post(0, kt) : 0;
    if (!o) { n_setup++; return true; }
    facts[nfacts++] = (BFact){ t, true, o };
  }
  for (int step = 0; step < 30 && nfacts < 250; step++) {
    int k = rint_(nrules); const BRule *r = &rules[k];
    int ki[2]; Occ kk[2];
    for (int j = 0; j < r->nkeep; j++) {
      int cand[256], nc = 0;
      for (int f = 0; f < nfacts; f++) { const RT *B2[R_MAXH] = { 0 }; if (facts[f].alive && r_unify(r->keep[j], facts[f].t, B2)) cand[nc++] = f; }
      ki[j] = nc && chance(0.9) ? cand[rint_(nc)] : rint_(nfacts);
      kk[j] = facts[ki[j]].k;
    }
    const RT *in[R_MAXH] = { 0 }; Term kin[R_MAXH] = { 0 }; bool has_in = chance(0.4);
    if (has_in) for (int h = 0; h < r->nholes; h++) if (chance(0.4)) { in[h] = r->bound[h] ? (chance(0.85) ? bv(rint_(3)) : gen_d(1, NULL, 0, 0)) : gen_d(1, NULL, 0, 0); kin[h] = k_of(in[h]); }
    const RT *out = NULL;
    bool racc = r_fire_bind(r, ki, has_in ? in : NULL, &out);
    int v = rint_(3);
    Occ o;
    if (v == 0) o = tc_fire(krule[k], NULL, kk, has_in ? kin : NULL);
    else if (v == 1) { TcPreparedStep ps = { .rule = krule[k], .keep = kk, .inst = has_in ? kin : NULL }; TcAdmissionReceipt rc; o = tc_commit_prepared(&ps, &rc) ? rc.out : 0; }
    else { TcPreparedStep ps = { .rule = krule[k], .keep = kk, .inst = has_in ? kin : NULL }; Term mt[5], ms[5]; uint8_t mm[5], nm; o = 0; if (tc_eval_prepared_ex(&ps, true, true, true, false, true, mt, ms, mm, &nm, &o) != TC_PREP_OK) o = 0; }
    n_cmp++;
    if ((o != 0) != racc) {
      char a[300], b[300];
      printf("DISAGREEMENT seed %llu step %d (entry %d): kernel %s, reference %s; rule %d holes", (unsigned long long)seed, step, v, o ? "accepts" : "refuses", racc ? "accepts" : "refuses", k);
      for (int h = 0; h < r->nholes; h++) printf(" ?%d:%s%s/deps%x", h, r->hsort[h] == S_V ? "V" : "D", r->bound[h] ? "(bound)" : "", r->deps[h]);
      for (int j = 0; j < r->nkeep; j++) { r_show(r->keep[j], a, 300); r_show(facts[ki[j]].t, b, 300); printf("\n      keep %s on %s", a, b); }
      r_show(r->make, a, 300); printf("\n      make %s", a);
      for (int h = 0; h < r->nholes; h++) if (in[h]) { r_show(in[h], a, 300); printf("\n      ?%d := %s", h, a); }
      printf("\n");
      n_fail++; return true;
    }
    if (!racc) continue;
    n_acc++;
    /* compare the made fact: the reference's term, rebuilt in the kernel, is the same node */
    if (k_of(out) != tc_term(o)) {
      char a[300], b[300]; r_show(out, a, 300); k_show(tc_term(o), b, 300);
      printf("DISAGREEMENT seed %llu step %d: made %s in the reference, %s in the kernel\n", (unsigned long long)seed, step, a, b);
      n_fail++; return true;
    }
    facts[nfacts++] = (BFact){ out, true, o };
  }
  return true;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s FIRST_SEED COUNT\n", argv[0]); return 2; }
  uint64_t first = strtoull(argv[1], NULL, 10), count = strtoull(argv[2], NULL, 10);
  r_cap = 1u << 22; r_arena = malloc(r_cap * sizeof *r_arena);
  if (!r_arena) return 3;
  for (uint64_t s = first; s < first + count; s++) if (!run(s)) { printf("tc_init failed\n"); return 3; }
  printf("summary: seeds %llu..%llu; firings compared %lu (%lu admitted); scenarios not set up %lu; scenarios ended by a disagreement %lu\n",
         (unsigned long long)first, (unsigned long long)(first + count - 1), n_cmp, n_acc, n_setup, n_fail);
  (void)n_sep_refused;
  return n_fail ? 1 : 0;
}
