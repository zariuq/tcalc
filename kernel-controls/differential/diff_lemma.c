/* Random differential for lemma checking (tc_lemma, tc_lemma_hyp, tc_lemma_step, tc_lemma_end) and for
   firing the installed lemma, against a naive reference written from the statement in tcalc.h:
   "check a proof script once against its context and install it as a rule".

   usage: diff_lemma FIRST_SEED COUNT [--verbose]

   Reference semantics. A lemma over the context's variables (rigid symbols while it is checked) has
   hypotheses in its space and a list of steps. A rule step cites a pure rule, premises (earlier steps
   or hypotheses, each in the space the rule's premise names), optional values for its holes and an
   optional target. It is admitted iff the premises match the rule's premise patterns under one
   assignment of the holes that agrees with the given values, every bound hole holds a term of its
   sort, and the result (the target if given, which must match the rule's conclusion pattern under the
   same assignment; else the conclusion instantiated, all of whose holes must be bound) is recorded in
   the rule's conclusion space. A refused step ends the lemma. Installing a step or hypothesis needs it
   to lie in the lemma's space; the installed rule keeps the hypotheses and makes the conclusion, with
   the context's variables as its holes. Firing it is then an ordinary firing (ref.h). */
#include "ref.h"
#include "tcalc.h"

static uint64_t rng_s;
static uint64_t rnd(void) { rng_s ^= rng_s >> 12; rng_s ^= rng_s << 25; rng_s ^= rng_s >> 27; return rng_s * 0x2545F4914F6CDD1Dull; }
static int rint_(int n) { return n <= 0 ? 0 : (int)(rnd() % (uint64_t)n); }
static bool chance(double p) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0) < p; }

enum { S_D = 1, S_N = 2, S_T = 3 };
static const RCon THEORY[10] = {
  { S_D, 0, { 0 } }, { S_D, 0, { 0 } }, { S_D, 1, { S_D } }, { S_D, 2, { S_D, S_D } }, { S_D, 1, { S_N } },
  { S_T, 1, { S_D } }, { S_T, 2, { S_D, S_D } }, { S_T, 1, { S_D } }, { S_T, 2, { S_N, S_D } }, { S_T, 0, { 0 } },
};
#define NCON 10
#define VAR_BASE (1ull << 61)                                /* context variable i is the rigid symbol VAR_BASE + i */
static const RT *cvar(int i, int sort) { return r_name(sort, VAR_BASE + (uint64_t)i); }

/* rules: pure, keep-only */
typedef struct { int nholes; uint8_t hsort[R_MAXH]; int nkeep; const RT *keep[2]; int kspace[2]; const RT *make; int mspace; } PRule;
static PRule rules[6]; static int krule[6], nrules, npremint;
static int nctx; static uint8_t csort[R_MAXH];

static const RT *gen_pat(int sort, int depth, const PRule *r, uint32_t allowed, bool lemma_vars) {
  int c[R_MAXH], n = 0;
  int nh = lemma_vars ? nctx : r->nholes;
  for (int h = 0; h < nh; h++) if ((lemma_vars ? csort[h] : r->hsort[h]) == sort && (allowed >> h & 1)) c[n++] = h;
  if (n && chance(depth <= 0 ? 0.75 : 0.4)) { int h = c[rint_(n)]; return lemma_vars ? cvar(h, sort) : r_hole(h, sort); }
  if (sort == S_N) return r_name(S_N, (uint64_t)rint_(npremint));
  const RT *a[R_MAXAR];
  int k = sort == S_D ? (depth <= 0 ? rint_(2) : rint_(5)) : 5 + rint_(NCON - 5);
  for (int i = 0; i < THEORY[k].arity; i++) a[i] = gen_pat(THEORY[k].asort[i], depth - 1, r, allowed, lemma_vars);
  return r_app(k, a);
}
static Term k_of(const RT *t) {
  if (t->kind == RK_NAME) return t->id >= VAR_BASE && t->id < VAR_BASE + 64 ? tc_v((int)(t->id - VAR_BASE)) : tc_name(t->sort, t->id);
  if (t->kind == RK_HOLE) return tc_v(t->head);
  Term a[R_MAXAR];
  for (int i = 0; i < t->n; i++) if (!(a[i] = k_of(t->a[i]))) return 0;
  return tc_app(t->head, t->n ? a : NULL);
}
static const RT *to_holes(const RT *t) {                    /* context variables become rule holes */
  if (t->kind == RK_NAME && t->id >= VAR_BASE && t->id < VAR_BASE + 64) return r_hole((int)(t->id - VAR_BASE), t->sort);
  if (t->kind != RK_APP) return t;
  const RT *a[R_MAXAR];
  for (int i = 0; i < t->n; i++) a[i] = to_holes(t->a[i]);
  return r_app(t->head, a);
}

/* the reference lemma checker */
static const RT *lres[16]; static int lsp[16], nres; static const RT *lhyp[4]; static int nhyp, lspace; static bool lok;
static bool ref_step(const PRule *r, const int *prem, const RT *const *in, const RT *target) {
  const RT *B[R_MAXH];
  for (int h = 0; h < r->nholes; h++) B[h] = in ? in[h] : NULL;
  for (int j = 0; j < r->nkeep; j++) {
    int q = prem[j];
    if (q >= nres || q < -nhyp) return false;
    const RT *pt = q >= 0 ? lres[q] : lhyp[-1 - q];
    int sp = q >= 0 ? lsp[q] : lspace;
    if (sp != r->kspace[j] || !r_unify(r->keep[j], pt, B)) return false;
  }
  if (target && !r_unify(r->make, target, B)) return false;
  for (int h = 0; h < r->nholes; h++) if (B[h] && (!r_ground(B[h], B) || r_subst(B[h], B)->sort != r->hsort[h])) return false;
  const RT *out = target;
  if (!out) { if (!r_ground(r->make, B)) return false; out = r_subst(r->make, B); }
  lres[nres] = out; lsp[nres++] = r->mspace;
  return true;
}

static RStore st0;                                            /* the board, for firing installed lemmas */
static bool verbose;
static unsigned long n_steps_cmp, n_steps_acc, n_ends_cmp, n_ends_acc, n_fires, n_fires_acc, n_fail;

static void show_rt(const char *label, const RT *t) { char b[300]; r_show(t, b, sizeof b); printf("%s%s", label, b); }

static bool run(uint64_t seed) {
  rng_s = seed * 0x9E3779B97F4A7C15ull + 0x7777ull; for (int i = 0; i < 8; i++) rnd();
  r_na = 0; memset(&st0, 0, sizeof st0);
  if (!tc_init(1u << 13, 1u << 9)) return false;
  if (tc_sort(0) != S_D || tc_sort(0) != S_N || tc_sort(SORT_PROVABLE) != S_T) return true;
  r_ncon = NCON;
  for (int i = 0; i < NCON; i++) {
    r_con[i] = THEORY[i];
    Binder b[R_MAXAR];
    for (int j = 0; j < THEORY[i].arity; j++) b[j] = (Binder){ THEORY[i].asort[j], 0, 0 };
    if (tc_con(THEORY[i].sort, 0, THEORY[i].arity, b) != i) return true;
  }
  npremint = 2 + rint_(3);
  for (int i = 0; i < npremint; i++) (void)tc_fresh_name();
  st0.next_name = (uint64_t)npremint;
  nrules = 3 + rint_(4);
  for (int k = 0; k < nrules; k++) {
    PRule *r = &rules[k]; memset(r, 0, sizeof *r);
    r->nholes = 1 + rint_(4);
    for (int h = 0; h < r->nholes; h++) r->hsort[h] = chance(0.75) ? S_D : S_N;
    uint32_t all = (1u << r->nholes) - 1, seen = 0;
    r->nkeep = rint_(3);
    for (int j = 0; j < r->nkeep; j++) { r->keep[j] = gen_pat(S_T, 1 + rint_(2), r, all, false); r->kspace[j] = chance(0.8) ? 0 : 1; }
    for (int j = 0; j < r->nkeep; j++) { const RT *t = r->keep[j]; (void)t; }
    for (int j = 0; j < r->nkeep; j++) {                  /* holes the premises bind */
      const RT *stack[64]; int sp = 0; stack[sp++] = r->keep[j];
      while (sp) { const RT *t = stack[--sp]; if (t->kind == RK_HOLE) seen |= 1u << t->head; for (int i = 0; i < t->n && sp < 60; i++) stack[sp++] = t->a[i]; }
    }
    r->make = gen_pat(S_T, 1 + rint_(2), r, chance(0.8) && seen ? seen : all, false);
    r->mspace = chance(0.8) ? 0 : 1;
    Binder b[R_MAXH];
    for (int h = 0; h < r->nholes; h++) b[h] = (Binder){ r->hsort[h], 0, 0 };
    if (!tc_ctx(r->nholes, b)) return true;
    Rule kr; memset(&kr, 0, sizeof kr);
    kr.nkeep = (uint8_t)r->nkeep; kr.fresh = -1;
    for (int j = 0; j < r->nkeep; j++) kr.keep[j] = (Pat){ k_of(r->keep[j]), (uint8_t)r->kspace[j] };
    kr.make = (Pat){ k_of(r->make), (uint8_t)r->mspace };
    if ((krule[k] = tc_rule(&kr)) < 0) return true;
  }
  /* a few ground facts on the board, for firing installed lemmas */
  for (int f = 0; f < 10; f++) {
    nctx = 0;
    const RT *t = gen_pat(S_T, 1 + rint_(2), &rules[0], 0, true);
    int s = chance(0.7) ? 0 : 1;
    Occ o = tc_post((uint8_t)s, k_of(t));
    if (!o) return true;
    st0.f[st0.n++] = (RFact){ t, (uint8_t)s, true, -1, f, o };
  }
  for (int lem = 0; lem < 4; lem++) {
    nctx = 1 + rint_(4);
    for (int i = 0; i < nctx; i++) csort[i] = chance(0.75) ? S_D : S_N;
    Binder b[R_MAXH];
    for (int i = 0; i < nctx; i++) b[i] = (Binder){ csort[i], 0, 0 };
    if (!tc_ctx(nctx, b)) return true;
    lspace = chance(0.8) ? 0 : 1;
    nhyp = rint_(4); nres = 0; lok = true;
    uint32_t allv = (1u << nctx) - 1;
    bool klok = tc_lemma(nctx, (uint8_t)lspace);
    if (!klok) { printf("seed %llu: tc_lemma refused\n", (unsigned long long)seed); n_fail++; return true; }
    for (int i = 0; i < nhyp; i++) {
      lhyp[i] = gen_pat(S_T, 1 + rint_(2), NULL, allv, true);
      if (!tc_lemma_hyp(k_of(lhyp[i]))) { printf("seed %llu: tc_lemma_hyp refused a well-formed hypothesis\n", (unsigned long long)seed); n_fail++; return true; }
    }
    int nsteps = 1 + rint_(6);
    for (int s = 0; s < nsteps; s++) {
      int ri = rint_(nrules); const PRule *r = &rules[ri];
      int prem[2] = { 0, 0 };
      const RT *B[R_MAXH] = { 0 };
      for (int j = 0; j < r->nkeep; j++) {                /* guided premise choice */
        int cand[24], nc = 0;
        for (int q = -nhyp; q < nres; q++) {
          const RT *pt = q >= 0 ? lres[q] : lhyp[-1 - q];
          int sp = q >= 0 ? lsp[q] : lspace;
          const RT *B2[R_MAXH]; memcpy(B2, B, sizeof B2);
          if (sp == r->kspace[j] && r_unify(r->keep[j], pt, B2) && nc < 24) cand[nc++] = q;
        }
        prem[j] = nc && chance(0.9) ? cand[rint_(nc)] : rint_(nres + nhyp + 1) - nhyp;
        if (prem[j] < nres && prem[j] >= -nhyp) { const RT *pt = prem[j] >= 0 ? lres[prem[j]] : lhyp[-1 - prem[j]]; r_unify(r->keep[j], pt, B); }
      }
      const RT *in[R_MAXH] = { 0 }; bool has_in = chance(0.5);
      if (has_in) for (int h = 0; h < r->nholes; h++) {
        if (!chance(0.5)) continue;
        if (B[h] && r_ground(B[h], B) && chance(0.7)) in[h] = r_subst(B[h], B);
        else in[h] = gen_pat(chance(0.9) ? r->hsort[h] : (r->hsort[h] == S_D ? S_N : S_D), 1, NULL, allv, true);
      }
      const RT *target = NULL;
      if (chance(0.4)) {
        const RT *B3[R_MAXH]; memcpy(B3, B, sizeof B3);
        for (int h = 0; h < r->nholes; h++) if (in[h] && !B3[h]) B3[h] = in[h];
        target = r_ground(r->make, B3) && chance(0.7) ? r_subst(r->make, B3) : gen_pat(S_T, 1 + rint_(2), NULL, allv, true);
      }
      bool racc = lok && ref_step(r, prem, has_in ? in : NULL, target);
      if (!racc) lok = false;
      Term kin[R_MAXH] = { 0 };
      for (int h = 0; h < r->nholes; h++) if (in[h]) kin[h] = k_of(in[h]);
      Step ks; memset(&ks, 0, sizeof ks);
      ks.kind = ST_RULE; ks.rule = krule[ri]; ks.prem[0] = prem[0]; ks.prem[1] = prem[1];
      ks.inst = has_in ? kin : NULL; ks.target = target ? k_of(target) : 0;
      int got = tc_lemma_step(&ks);
      bool kacc = got >= 0;
      n_steps_cmp++; n_steps_acc += kacc;
      if (kacc != racc) {
        printf("DISAGREEMENT seed %llu lemma %d step %d: kernel %s, reference %s; rule %d:", (unsigned long long)seed, lem, s, kacc ? "accepts" : "refuses", racc ? "accepts" : "refuses", ri);
        for (int j = 0; j < r->nkeep; j++) { show_rt(" keep ", r->keep[j]); printf("@%d", r->kspace[j]); }
        show_rt(" make ", r->make); printf("@%d; prem", r->mspace);
        for (int j = 0; j < r->nkeep; j++) printf(" %d", prem[j]);
        for (int h = 0; h < r->nholes; h++) if (in[h]) { printf(" ?%d:=", h); show_rt("", in[h]); }
        if (target) show_rt("; target ", target);
        printf("\n");
        n_fail++; return true;
      }
      if (!racc) break;
    }
    int ref = rint_(nres + nhyp + 1) - nhyp;
    if (chance(0.7) && nres) ref = nres - 1;
    bool rend = lok && ref < nres && ref >= -nhyp && (ref >= 0 ? lsp[ref] : lspace) == lspace;
    int lid = tc_lemma_end(ref);
    n_ends_cmp++; n_ends_acc += lid >= 0;
    if ((lid >= 0) != rend) {
      printf("DISAGREEMENT seed %llu lemma %d: tc_lemma_end(%d) kernel %s, reference %s\n", (unsigned long long)seed, lem, ref, lid >= 0 ? "installs" : "refuses", rend ? "installs" : "refuses");
      n_fail++; return true;
    }
    if (lid < 0) continue;
    /* the installed lemma as a rule: keep the hypotheses, make the conclusion, in the lemma's space */
    RRule dr; memset(&dr, 0, sizeof dr);
    dr.nholes = nctx; for (int i = 0; i < nctx; i++) dr.hsort[i] = csort[i];
    dr.fresh = -1; dr.nkeep = nhyp; dr.nmake = 1;
    for (int i = 0; i < nhyp; i++) dr.keep[i] = (RPat){ to_holes(lhyp[i]), (uint8_t)lspace };
    dr.make[0] = (RPat){ to_holes(ref >= 0 ? lres[ref] : lhyp[-1 - ref]), (uint8_t)lspace };
    for (int t = 0; t < 6; t++) {
      int ki[8]; Occ kk[8];
      const RT *B[R_MAXH] = { 0 };
      for (int i = 0; i < nhyp; i++) {
        int cand[64], nc = 0;
        for (int f = 0; f < st0.n && nc < 64; f++) if (st0.f[f].alive && st0.f[f].space == lspace) { const RT *B2[R_MAXH]; memcpy(B2, B, sizeof B2); if (r_unify(dr.keep[i].t, st0.f[f].t, B2)) cand[nc++] = f; }
        ki[i] = nc && chance(0.85) ? cand[rint_(nc)] : rint_(st0.n);
        if (ki[i] >= 0) r_unify(dr.keep[i].t, st0.f[ki[i]].t, B);
        kk[i] = st0.f[ki[i]].kocc;
      }
      const RT *in[R_MAXH] = { 0 }; Term kin[R_MAXH] = { 0 }; bool has_in = chance(0.6);
      int nh = dr.nholes;
      if (has_in) for (int h = 0; h < nh; h++) if (chance(0.5)) { nctx = 0; in[h] = gen_pat(csort[h], 1, NULL, 0, true); nctx = nh; kin[h] = k_of(in[h]); }
      RVerdict rv = r_fire(&st0, &dr, NULL, ki, has_in ? in : NULL, false, 100 + t, NULL);
      Occ o = tc_fire(lid, NULL, nhyp ? kk : NULL, has_in ? kin : NULL);
      n_fires++;
      if (rv == RV_OUT) continue;
      if ((o != 0) != (rv == RV_ACCEPT)) {
        printf("DISAGREEMENT seed %llu lemma %d: firing the installed lemma, kernel %s, reference %s\n", (unsigned long long)seed, lem, o ? "accepts" : "refuses", rv == RV_ACCEPT ? "accepts" : "refuses");
        n_fail++; return true;
      }
      if (o) {
        int made[1]; r_fire(&st0, &dr, NULL, ki, has_in ? in : NULL, true, 100 + t, made);
        st0.f[made[0]].kocc = o; n_fires_acc++;
        if (o != st0.f[made[0]].kocc || k_of(st0.f[made[0]].t) != tc_term(o)) { printf("DISAGREEMENT seed %llu lemma %d: installed lemma made a different fact\n", (unsigned long long)seed, lem); n_fail++; return true; }
      }
    }
  }
  return true;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s FIRST_SEED COUNT [--verbose]\n", argv[0]); return 2; }
  uint64_t first = strtoull(argv[1], NULL, 10), count = strtoull(argv[2], NULL, 10);
  verbose = argc > 3 && !strcmp(argv[3], "--verbose");
  r_cap = 1u << 22; r_arena = malloc(r_cap * sizeof *r_arena);
  if (!r_arena) return 3;
  for (uint64_t s = first; s < first + count; s++) if (!run(s)) { printf("tc_init failed\n"); return 3; }
  printf("summary: seeds %llu..%llu; lemma steps compared %lu (%lu admitted); lemma installs compared %lu (%lu installed); firings of installed lemmas %lu (%lu admitted); scenarios ended by a disagreement %lu\n",
         (unsigned long long)first, (unsigned long long)(first + count - 1), n_steps_cmp, n_steps_acc, n_ends_cmp, n_ends_acc, n_fires, n_fires_acc, n_fail);
  return n_fail ? 1 : 0;
}
