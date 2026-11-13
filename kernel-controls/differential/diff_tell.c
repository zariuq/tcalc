/* Random differential for open tells: rules whose tells and disequations leave holes to unknowns, facts
   that hold unknowns, and caller tells, against a naive reference written from tcalc.h ("K binds
   unknowns (with a trail, for two-way unification) and holds disequations").

   usage: diff_tell FIRST_SEED COUNT

   Reference semantics (one sort of data, so sort constraints never bite). K is a substitution over
   unknowns plus a list of disequations. A firing works on K extended with one variable per rule hole
   (the given values bind some): its premises unify with their facts, its tells unify their sides, its
   disequations are refused when both sides are already the same term and recorded otherwise; it is
   admitted iff every recorded disequation still has two different normal forms, no hole holds an
   unbound unknown (a hole of a sort takes a term of that sort, and an unknown is not yet one), and
   every hole a make uses occurs in a premise, a tell, a disequation or a given value; its makes are
   added with K applied.
   A refusal leaves K as it was. tc_tell / tc_tell_neq are the same operations on K alone. The store is
   compared as a multiset of facts in normal form, each fact's unknowns renamed in order of appearance. */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "tcalc.h"

static uint64_t rng_s;
static uint64_t rnd(void) { rng_s ^= rng_s >> 12; rng_s ^= rng_s << 25; rng_s ^= rng_s >> 27; return rng_s * 0x2545F4914F6CDD1Dull; }
static int rint_(int n) { return n <= 0 ? 0 : (int)(rnd() % (uint64_t)n); }
static bool chance(double p) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0) < p; }

enum { S_D = 1, S_T = 2 };
enum { TA = 1, TV = 2 };                                      /* application, variable (unknown) */
static const struct { uint8_t sort, ar; } CON[6] = { { S_D, 0 }, { S_D, 0 }, { S_D, 1 }, { S_D, 2 }, { S_T, 1 }, { S_T, 2 } };
/* 0 Z  1 O  2 S(D)  3 P(D,D)  4 A1(D):T  5 A2(D,D):T */
typedef struct X { uint8_t kind, head, n; int v; const struct X *a[2]; } X;   /* v: variable id */
static X arena[1 << 21]; static int na_;
static const X *mkv(int v) { X *t = &arena[na_++]; memset(t, 0, sizeof *t); t->kind = TV; t->v = v; return t; }
static const X *mka(int h, const X *a0, const X *a1) { X *t = &arena[na_++]; memset(t, 0, sizeof *t); t->kind = TA; t->head = (uint8_t)h; t->n = CON[h].ar; t->a[0] = a0; t->a[1] = a1; return t; }

/* variables: unknowns 0..NV-1 (global); a firing's holes are fresh variables */
#define NVAR 20000
static const X *bindv[NVAR]; static int trail[NVAR * 2], ntr; static int nvar;
static const X *walk(const X *t) { while (t->kind == TV && bindv[t->v]) t = bindv[t->v]; return t; }
static bool occurs(int v, const X *t) { t = walk(t); if (t->kind == TV) return t->v == v; for (int i = 0; i < t->n; i++) if (occurs(v, t->a[i])) return true; return false; }
static bool unify(const X *a, const X *b) {
  a = walk(a); b = walk(b);
  if (a == b || (a->kind == TV && b->kind == TV && a->v == b->v)) return true;
  if (a->kind == TV) { if (occurs(a->v, b)) return false; bindv[a->v] = b; trail[ntr++] = a->v; return true; }
  if (b->kind == TV) { if (occurs(b->v, a)) return false; bindv[b->v] = a; trail[ntr++] = b->v; return true; }
  if (a->head != b->head) return false;
  for (int i = 0; i < a->n; i++) if (!unify(a->a[i], b->a[i])) return false;
  return true;
}
static void undo_to(int m) { while (ntr > m) bindv[trail[--ntr]] = NULL; }
static bool same_nf(const X *a, const X *b) {
  a = walk(a); b = walk(b);
  if (a->kind == TV || b->kind == TV) return a->kind == TV && b->kind == TV && a->v == b->v;
  if (a->head != b->head) return false;
  for (int i = 0; i < a->n; i++) if (!same_nf(a->a[i], b->a[i])) return false;
  return true;
}
static bool has_var(const X *t) { t = walk(t); if (t->kind == TV) return true; for (int i = 0; i < t->n; i++) if (has_var(t->a[i])) return true; return false; }
static const X *ne[4096][2]; static int nne_;
static bool diseqs_ok(void) { for (int i = 0; i < nne_; i++) if (same_nf(ne[i][0], ne[i][1])) return false; return true; }
static const X *subst_holes(const X *t, const int *hv) {     /* pattern holes are TV with v < 0: -1-h */
  if (t->kind == TV && t->v < 0) return mkv(hv[-1 - t->v]);
  if (t->kind != TA) return t;
  return mka(t->head, t->n > 0 ? subst_holes(t->a[0], hv) : NULL, t->n > 1 ? subst_holes(t->a[1], hv) : NULL);
}
static const X *hole(int h) { return mkv(-1 - h); }
static uint32_t holes_in(const X *t) { if (t->kind == TV) return t->v < 0 ? 1u << (-1 - t->v) : 0; uint32_t m = 0; for (int i = 0; i < t->n; i++) m |= holes_in(t->a[i]); return m; }

/* rules */
typedef struct { int nholes, ntake, nkeep, ntell, nneq, nmake; const X *take[1], *keep[2], *tell[2][2], *neq[2][2], *make[2]; } TRule;
static TRule rules[5]; static int krule[5], nrules;
typedef struct { const X *t; bool alive; Occ k; } TFact;
static TFact facts[512]; static int nfacts;

static bool r_fire(const TRule *r, const int *ti, const int *ki, const X *const *in, bool apply, const X **out) {
  int m = ntr, nem = nne_, hv[8];
  uint32_t touched = 0;
  for (int h = 0; h < r->nholes; h++) { hv[h] = nvar + h; if (in && in[h]) { bindv[hv[h]] = in[h]; trail[ntr++] = hv[h]; touched |= 1u << h; } }
  nvar += r->nholes;
  bool ok = true;
  for (int i = 0; ok && i < r->ntake; i++) {
    ok = ti[i] >= 0 && facts[ti[i]].alive && unify(subst_holes(r->take[i], hv), facts[ti[i]].t);
    touched |= holes_in(r->take[i]);
  }
  for (int i = 0; ok && i < r->nkeep; i++) {
    ok = ki[i] >= 0 && facts[ki[i]].alive && unify(subst_holes(r->keep[i], hv), facts[ki[i]].t);
    for (int j = 0; ok && j < r->ntake; j++) ok = ti[j] != ki[i];
    touched |= holes_in(r->keep[i]);
  }
  for (int i = 0; ok && i < r->ntell; i++) { ok = unify(subst_holes(r->tell[i][0], hv), subst_holes(r->tell[i][1], hv)); touched |= holes_in(r->tell[i][0]) | holes_in(r->tell[i][1]); }
  for (int i = 0; ok && i < r->nneq; i++) {
    const X *a = subst_holes(r->neq[i][0], hv), *b = subst_holes(r->neq[i][1], hv);
    touched |= holes_in(r->neq[i][0]) | holes_in(r->neq[i][1]);
    if (same_nf(a, b)) ok = false;
    else if (has_var(a) || has_var(b)) { ne[nne_][0] = a; ne[nne_][1] = b; nne_++; }
  }
  ok = ok && diseqs_ok();
  /* a hole of a sort takes a term of that sort; an unbound unknown is not yet one */
  for (int h = 0; ok && h < r->nholes; h++) if ((touched >> h & 1) && walk(mkv(hv[h]))->kind == TV) ok = false;
  for (int mk = 0; ok && mk < r->nmake; mk++) if (holes_in(r->make[mk]) & ~touched) ok = false;
  if (ok && apply) {
    for (int mk = 0; mk < r->nmake; mk++) out[mk] = subst_holes(r->make[mk], hv);
    for (int i = 0; i < r->ntake; i++) facts[ti[i]].alive = false;
    return true;
  }
  undo_to(m); nne_ = nem; if (!ok || !apply) nvar -= r->nholes;
  return ok;
}

/* kernel side */
static Term kvar[NVAR];                                       /* reference unknown -> kernel unknown */
static Term k_of(const X *t, bool pattern) {
  if (t->kind == TV) {
    if (t->v < 0) return pattern ? tc_v(-1 - t->v) : 0;
    if (!kvar[t->v]) kvar[t->v] = tc_meta();
    return kvar[t->v];
  }
  Term a[2];
  for (int i = 0; i < t->n; i++) if (!(a[i] = k_of(t->a[i], pattern))) return 0;
  return tc_app(t->head, t->n ? a : NULL);
}
/* a fact in normal form, unknowns renamed in order of appearance */
static int ren[NVAR]; static int ren_gen[NVAR], gen_;
static int show_r(const X *t, char *b, int cap, int *next) {
  t = walk(t);
  if (t->kind == TV) { if (ren_gen[t->v] != gen_) { ren_gen[t->v] = gen_; ren[t->v] = (*next)++; } return snprintf(b, (size_t)cap, "?%d", ren[t->v]); }
  int n = snprintf(b, (size_t)cap, "c%d", t->head);
  if (t->n) { n += snprintf(b + n, (size_t)(cap - n), "("); for (int i = 0; i < t->n; i++) { if (i) b[n++] = ','; n += show_r(t->a[i], b + n, cap - n, next); } n += snprintf(b + n, (size_t)(cap - n), ")"); }
  return n;
}
static Term kids[4096]; static int kidn[4096], nkid;
static int show_k(Term t, char *b, int cap) {
  t = tc_deref(t);
  uint8_t kind; uint32_t head; int ar; const Term *args;
  tc_node(t, &kind, &head, &ar, &args);
  if (kind == K_META) { int i = 0; while (i < nkid && kids[i] != t) i++; if (i == nkid) { kids[nkid++] = t; } return snprintf(b, (size_t)cap, "?%d", i); }
  int n = snprintf(b, (size_t)cap, "c%u", head);
  Term as[2] = { ar > 0 ? args[0] : 0, ar > 1 ? args[1] : 0 };
  if (ar) { n += snprintf(b + n, (size_t)(cap - n), "("); for (int i = 0; i < ar; i++) { if (i) b[n++] = ','; n += show_k(as[i], b + n, cap - n); } n += snprintf(b + n, (size_t)(cap - n), ")"); }
  return n;
}
static int cmps(const void *a, const void *b) { return strcmp((const char *)a, (const char *)b); }
static char ks[600][160], rs[600][160];
static bool stores_agree(char *note, int cap) {
  int nk = 0, nr = 0;
  for (Occ o = 1; o < 4096 && nk < 600; o++) if (tc_alive(o)) { nkid = 0; show_k(tc_term(o), ks[nk++], 160); }
  for (int i = 0; i < nfacts && nr < 600; i++) if (facts[i].alive) { gen_++; int next = 0; show_r(facts[i].t, rs[nr++], 160, &next); }
  qsort(ks, (size_t)nk, 160, cmps); qsort(rs, (size_t)nr, 160, cmps);
  for (int i = 0, j = 0; i < nk || j < nr;) {
    int c = i == nk ? 1 : j == nr ? -1 : strcmp(ks[i], rs[j]);
    if (!c) { i++; j++; continue; }
    snprintf(note, (size_t)cap, c < 0 ? "kernel has %s, reference does not" : "reference has %s, kernel does not", c < 0 ? ks[i] : rs[j]);
    return false;
  }
  return true;
}

/* generators */
static const X *gen_d(int depth, int nholes, int nunk) {
  int x = rint_(10);
  if (nholes && x < 4) return hole(rint_(nholes));
  if (nunk && x < 6) return mkv(rint_(nunk));
  int c = depth <= 0 ? rint_(2) : rint_(4);
  return mka(c, CON[c].ar > 0 ? gen_d(depth - 1, nholes, nunk) : NULL, CON[c].ar > 1 ? gen_d(depth - 1, nholes, nunk) : NULL);
}
static const X *gen_fact(int nholes, int nunk) { int c = 4 + rint_(2); return mka(c, gen_d(1, nholes, nunk), c == 5 ? gen_d(1, nholes, nunk) : NULL); }

static unsigned long n_cmp, n_acc, n_fail, n_ktell;
static bool run(uint64_t seed) {
  rng_s = seed * 0x9E3779B97F4A7C15ull + 0x9191ull; for (int i = 0; i < 8; i++) rnd();
  na_ = 0; nfacts = 0; ntr = 0; nne_ = 0; nvar = 0; memset(bindv, 0, sizeof bindv); memset(kvar, 0, sizeof kvar);
  if (!tc_init(1u << 14, 1u << 10)) return false;
  if (tc_sort(0) != S_D || tc_sort(SORT_PROVABLE) != S_T) return true;
  for (int i = 0; i < 6; i++) {
    Binder b[2] = { { S_D, 0, 0 }, { S_D, 0, 0 } };
    if (tc_con(CON[i].sort, 0, CON[i].ar, CON[i].ar ? b : NULL) != i) return true;
  }
  nrules = 2 + rint_(4);
  for (int k = 0; k < nrules; k++) {
    TRule *r = &rules[k]; memset(r, 0, sizeof *r);
    r->nholes = 1 + rint_(4);
    r->ntake = rint_(2); r->nkeep = rint_(3); r->ntell = rint_(3); r->nneq = chance(0.4) ? 1 + rint_(2) : 0; r->nmake = 1 + rint_(2);
    for (int i = 0; i < r->ntake; i++) r->take[i] = gen_fact(r->nholes, 0);
    for (int i = 0; i < r->nkeep; i++) r->keep[i] = gen_fact(r->nholes, 0);
    for (int i = 0; i < r->ntell; i++) { r->tell[i][0] = gen_d(2, r->nholes, 0); r->tell[i][1] = gen_d(2, r->nholes, 0); }
    for (int i = 0; i < r->nneq; i++) { r->neq[i][0] = gen_d(1, r->nholes, 0); r->neq[i][1] = gen_d(1, r->nholes, 0); }
    for (int i = 0; i < r->nmake; i++) r->make[i] = gen_fact(r->nholes, 0);
    Binder b[8]; for (int h = 0; h < r->nholes; h++) b[h] = (Binder){ S_D, 0, 0 };
    if (!tc_ctx(r->nholes, b)) return true;
    Rule kr; memset(&kr, 0, sizeof kr);
    kr.ntake = (uint8_t)r->ntake; kr.nkeep = (uint8_t)r->nkeep; kr.ntell = (uint8_t)r->ntell; kr.nneq = (uint8_t)r->nneq; kr.nmake_extra = (uint8_t)(r->nmake - 1); kr.fresh = -1;
    for (int i = 0; i < r->ntake; i++) kr.take[i] = (Pat){ k_of(r->take[i], true), 0 };
    for (int i = 0; i < r->nkeep; i++) kr.keep[i] = (Pat){ k_of(r->keep[i], true), 0 };
    for (int i = 0; i < r->ntell; i++) { kr.tell[i][0] = k_of(r->tell[i][0], true); kr.tell[i][1] = k_of(r->tell[i][1], true); }
    for (int i = 0; i < r->nneq; i++) { kr.neq[i][0] = k_of(r->neq[i][0], true); kr.neq[i][1] = k_of(r->neq[i][1], true); }
    kr.make = (Pat){ k_of(r->make[0], true), 0 };
    if (r->nmake > 1) kr.make_extra[0] = (Pat){ k_of(r->make[1], true), 0 };
    if ((krule[k] = tc_rule(&kr)) < 0) return true;
  }
  /* initial unknowns and facts (some hold unknowns) */
  nvar = 4 + rint_(6);
  int nunk0 = nvar;                                        /* the caller's unknowns, made by tc_meta on both sides */
  for (int f = 0; f < 6 + rint_(8); f++) {
    const X *t = gen_fact(0, nvar);
    Term kt = k_of(t, false);
    Occ o = kt ? tc_post(0, kt) : 0;
    if (!o) { printf("seed %llu: post refused\n", (unsigned long long)seed); n_fail++; return true; }
    facts[nfacts++] = (TFact){ t, true, o };
  }
  char note[300];
  for (int step = 0; step < 30 && nfacts < 500 && nvar < NVAR - 64 && na_ < (1 << 21) - 4096; step++) {
    if (chance(0.15)) {                                    /* a caller tell or disequation */
      const X *a = gen_d(1, 0, nunk0), *b = gen_d(1, 0, nunk0);   /* only unknowns both sides share by name */
      bool isneq = chance(0.4);
      int m = ntr, nem = nne_; bool racc;
      if (isneq) { if (same_nf(a, b)) racc = false; else { if (has_var(a) || has_var(b)) { ne[nne_][0] = a; ne[nne_][1] = b; nne_++; } racc = diseqs_ok(); } }
      else racc = unify(a, b) && diseqs_ok();
      if (!racc) { undo_to(m); nne_ = nem; }
      Term ka = k_of(a, false), kb = k_of(b, false);
      bool kacc = isneq ? tc_tell_neq(ka, kb) : tc_tell(ka, kb);
      n_ktell++;
      if (kacc != racc) {
        char sa[160], sb[160]; int nx = 0; gen_++; show_r(a, sa, 160, &nx); show_r(b, sb, 160, &nx);
        printf("DISAGREEMENT seed %llu step %d: tc_tell%s(%s, %s) kernel %s, reference %s (%d disequations)\n", (unsigned long long)seed, step, isneq ? "_neq" : "", sa, sb, kacc ? "accepts" : "refuses", racc ? "accepts" : "refuses", nne_);
        n_fail++; return true;
      }
      if (!stores_agree(note, sizeof note)) { printf("DISAGREEMENT seed %llu step %d after tell: %s\n", (unsigned long long)seed, step, note); n_fail++; return true; }
      continue;
    }
    int k = rint_(nrules); const TRule *r = &rules[k];
    int ti[1] = { -1 }, ki[2] = { -1, -1 }; Occ tk[1] = { 0 }, kk[2] = { 0, 0 };
    for (int i = 0; i < r->ntake; i++) { ti[i] = rint_(nfacts); tk[i] = facts[ti[i]].k; }
    for (int i = 0; i < r->nkeep; i++) { ki[i] = rint_(nfacts); kk[i] = facts[ki[i]].k; }
    const X *in[8] = { 0 }; Term kin[8] = { 0 }; bool has_in = chance(0.3);
    if (has_in) for (int h = 0; h < r->nholes; h++) if (chance(0.4)) { in[h] = gen_d(1, 0, chance(0.3) ? 0 : 0); kin[h] = k_of(in[h], false); }
    int v = rint_(4);
    const X *out[2];
    bool racc = r_fire(r, ti, ki, has_in ? in : NULL, false, NULL);
    Occ o = 0; bool kacc;
    TcPreparedStep ps = { .rule = krule[k], .take = r->ntake ? tk : NULL, .keep = r->nkeep ? kk : NULL, .inst = has_in ? kin : NULL };
    if (v == 0) { o = tc_fire(krule[k], ps.take, ps.keep, ps.inst); kacc = o != 0; }
    else if (v == 1) { TcAdmissionReceipt rc; kacc = tc_commit_prepared(&ps, &rc); o = kacc ? rc.out : 0; }
    else if (v == 2) kacc = tc_eval_prepared_ex(&ps, true, true, true, false, true, NULL, NULL, NULL, NULL, &o) == TC_PREP_OK && o;
    else {
      bool dacc = tc_eval_prepared_ex(&ps, true, true, true, false, false, NULL, NULL, NULL, NULL, NULL) == TC_PREP_OK;
      if (dacc != racc || !stores_agree(note, sizeof note)) { printf("DISAGREEMENT seed %llu step %d: dry run kernel %s, reference %s\n", (unsigned long long)seed, step, dacc ? "accepts" : "refuses", racc ? "accepts" : "refuses"); n_fail++; return true; }
      o = tc_fire(krule[k], ps.take, ps.keep, ps.inst); kacc = o != 0;
    }
    n_cmp++;
    if (kacc != racc) { printf("DISAGREEMENT seed %llu step %d (entry %d): kernel %s, reference %s (rule %d: take %d keep %d tell %d neq %d make %d)\n", (unsigned long long)seed, step, v, kacc ? "accepts" : "refuses", racc ? "accepts" : "refuses", k, r->ntake, r->nkeep, r->ntell, r->nneq, r->nmake); n_fail++; return true; }
    if (kacc) {
      n_acc++;
      r_fire(r, ti, ki, has_in ? in : NULL, true, out);
      facts[nfacts++] = (TFact){ out[0], true, o };
      if (r->nmake > 1) facts[nfacts++] = (TFact){ out[1], true, tc_last_extra(0) };
      /* the kernel's new unknowns stay unmapped: facts are compared by structure with renamed unknowns */
    }
    if (!stores_agree(note, sizeof note)) { printf("DISAGREEMENT seed %llu step %d (entry %d, %s): %s\n", (unsigned long long)seed, step, v, kacc ? "admitted" : "refused", note); n_fail++; return true; }
  }
  return true;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s FIRST_SEED COUNT\n", argv[0]); return 2; }
  uint64_t first = strtoull(argv[1], NULL, 10), count = strtoull(argv[2], NULL, 10);
  for (uint64_t s = first; s < first + count; s++) if (!run(s)) { printf("tc_init failed\n"); return 3; }
  printf("summary: seeds %llu..%llu; firings compared %lu (%lu admitted); caller tells compared %lu; scenarios ended by a disagreement %lu\n",
         (unsigned long long)first, (unsigned long long)(first + count - 1), n_cmp, n_acc, n_ktell, n_fail);
  return n_fail ? 1 : 0;
}
