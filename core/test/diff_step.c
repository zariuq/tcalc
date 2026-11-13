/* The tc0 step against a naive reference written from the contract in tc0.h, on random theories.
   The reference keeps facts as plain records and decides a firing by brute force: a hole that
   occurs in premises must hold the same atom at every occurrence; a hole that occurs in no premise
   is an input, or the fresh name; a hole for minted names only takes a generative name.  Every
   firing's verdict, written fact and name counter must agree with tc0. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include "tc0.h"

enum { NSLOT = 10, MAXSLOT = 12, NCON = 3, NH = 5 };
typedef struct { int kind; uint64_t id; } Atom;                 /* kind TC0_K_GEN or TC0_K_CODE */
typedef struct { int con, ar; Atom a[3]; } Fact;
typedef struct { int con, ar; int hole[3]; Atom a[3]; } Pat;    /* hole[j] >= 0, or the atom a[j] */
typedef struct { int nkeep, fresh; Pat keep[3], make; uint8_t kind[TC0_HOLES]; int id; } RuleM;

static const int arity[NCON] = { 2, 3, 1 };
static int con[NCON];
static uint64_t rng = 88172645463325252ull;
static uint64_t rnd(uint64_t m) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng % m; }
static Fact slot[MAXSLOT], dflt;
static bool written[MAXSLOT];
static uint64_t last_gen;

static Term term_of(Atom a) { return a.kind == TC0_K_GEN ? tc0_gen(a.id) : tc0_code(a.id); }
static Atom rand_atom(void) { return rnd(2) ? (Atom){ TC0_K_CODE, rnd(4) } : (Atom){ TC0_K_GEN, rnd(last_gen + 1) }; }
static Term fact_term(const Fact *f) { Term a[3]; for (int j = 0; j < f->ar; j++) a[j] = term_of(f->a[j]); return tc0_app(con[f->con], a); }
static Term pat_term(const Pat *p) {
  Term a[3];
  for (int j = 0; j < p->ar; j++) a[j] = p->hole[j] >= 0 ? tc0_hole(p->hole[j]) : term_of(p->a[j]);
  return tc0_app(con[p->con], a);
}
static bool same_atom(Atom x, Atom y) { return x.kind == y.kind && x.id == y.id; }
static Fact rand_fact(void) { Fact f = { (int)rnd(NCON), 0, { { 0, 0 } } }; f.ar = arity[f.con]; for (int j = 0; j < f.ar; j++) f.a[j] = rand_atom(); return f; }
static Pat rand_pat(int holes_from, int holes_to) {
  Pat p = { (int)rnd(NCON), 0, { -1, -1, -1 }, { { 0, 0 } } }; p.ar = arity[p.con];
  for (int j = 0; j < p.ar; j++) {
    if (rnd(4)) p.hole[j] = holes_from + (int)rnd((uint64_t)(holes_to - holes_from)); else p.a[j] = rand_atom();
  }
  return p;
}
static bool occurs(const Pat *p, int h) { for (int j = 0; j < p->ar; j++) if (p->hole[j] == h) return true; return false; }

/* The reference: the fact the rule makes, or false. */
static bool ref_fire(const RuleM *r, const uint64_t *keep, const Atom *in, const bool *given, Fact *out, bool *minted) {
  Atom val[NH]; bool bound[NH] = { false };
  for (int i = 0; i < r->nkeep; i++) {
    const Fact *f = keep[i] < MAXSLOT && written[keep[i]] ? &slot[keep[i]] : &dflt;
    if (f->con != r->keep[i].con) return false;
    for (int j = 0; j < f->ar; j++) {
      int h = r->keep[i].hole[j];
      if (h < 0) { if (!same_atom(f->a[j], r->keep[i].a[j])) return false; continue; }
      for (int i2 = 0; i2 < r->nkeep; i2++)                      /* every occurrence of h holds this atom */
        for (int j2 = 0; j2 < r->keep[i2].ar; j2++) {
          const Fact *f2 = keep[i2] < MAXSLOT && written[keep[i2]] ? &slot[keep[i2]] : &dflt;
          if (r->keep[i2].hole[j2] == h && (f2->con != r->keep[i2].con || !same_atom(f2->a[j2], f->a[j]))) return false;
        }
      val[h] = f->a[j]; bound[h] = true;
    }
  }
  for (int h = 0; h < NH; h++) {
    if (bound[h] || h == r->fresh || !occurs(&r->make, h)) continue;
    if (!given[h]) return false;
    val[h] = in[h]; bound[h] = true;
  }
  for (int h = 0; h < NH; h++) if (bound[h] && r->kind[h] == TC0_GEN_ONLY && val[h].kind != TC0_K_GEN) return false;
  *minted = r->fresh >= 0;
  if (*minted) val[r->fresh] = (Atom){ TC0_K_GEN, last_gen + 1 };
  out->con = r->make.con; out->ar = r->make.ar;
  for (int j = 0; j < out->ar; j++) out->a[j] = r->make.hole[j] >= 0 ? val[r->make.hole[j]] : r->make.a[j];
  return true;
}

static bool same_as_tc0(const Fact *f, Term t) {
  int c, ar; const Term *a = tc0_args(t, &c, &ar);
  if (!a || c != con[f->con] || ar != f->ar) return false;
  for (int j = 0; j < ar; j++) if (tc0_kind(a[j]) != f->a[j].kind || tc0_id(a[j]) != f->a[j].id) return false;
  return true;
}

int main(int argc, char **argv) {
  uint64_t theories = argc > 1 ? strtoull(argv[1], NULL, 10) : 4000, firings = 0, admitted = 0;
  for (uint64_t th = 0; th < theories; th++) {
    tc0_init(NSLOT);
    for (int c = 0; c < NCON; c++) con[c] = tc0_con(arity[c]);
    for (int i = 0; i < 3; i++) tc0_mint();
    last_gen = 2;
    RuleM rules[6]; int nrules = 0;
    for (int k = 0; k < 6; k++) {
      RuleM r; r.nkeep = (int)rnd(4); r.fresh = -1;
      for (int i = 0; i < r.nkeep; i++) r.keep[i] = rand_pat(0, 3);  /* premises use holes 0..2 */
      r.make = rand_pat(0, NH);                                      /* the conclusion also 3 (input), 4 (fresh) */
      if (occurs(&r.make, 4) && rnd(2)) r.fresh = 4;
      for (int h = 0; h < TC0_HOLES; h++) r.kind[h] = rnd(5) ? TC0_ANY : TC0_GEN_ONLY;
      Term kt[3]; for (int i = 0; i < r.nkeep; i++) kt[i] = pat_term(&r.keep[i]);
      r.id = tc0_rule(r.nkeep, kt, pat_term(&r.make), r.fresh, r.kind);
      if (r.id < 0) { fprintf(stderr, "rule refused\n"); return 1; }
      rules[nrules++] = r;
    }
    RuleM d0 = { 0, -1, { { 0 } }, { 0, 2, { -1, -1, -1 }, { { TC0_K_CODE, 0 }, { TC0_K_CODE, 0 } } }, { 0 }, 0 };
    d0.id = tc0_rule(0, NULL, pat_term(&d0.make), -1, NULL);
    if (d0.id < 0 || !tc0_default(d0.id, NULL)) { fprintf(stderr, "default refused\n"); return 1; }
    dflt = (Fact){ 0, 2, { { TC0_K_CODE, 0 }, { TC0_K_CODE, 0 } } };   /* what the default rule makes */
    tc0_seal();
    for (int s = 0; s < MAXSLOT; s++) written[s] = false;
    for (int s = 0; s < 8; s++) { slot[s] = rand_fact(); written[s] = tc0_put((uint64_t)s, fact_term(&slot[s])); }
    for (int step = 0; step < 60; step++) {
      const RuleM *r = &rules[rnd((uint64_t)nrules)];
      uint64_t keep[3]; for (int i = 0; i < 3; i++) keep[i] = rnd(MAXSLOT);
      Atom in[NH]; bool given[NH]; Term tin[TC0_HOLES] = { 0 };
      for (int h = 0; h < NH; h++) { given[h] = rnd(6) != 0; in[h] = rand_atom(); if (given[h]) tin[h] = term_of(in[h]); }
      uint64_t dest = rnd(MAXSLOT);
      Fact want; bool minted = false;
      bool rv = ref_fire(r, keep, in, given, &want, &minted) && dest < NSLOT;
      bool tv = tc0_fire(r->id, keep, tin, dest);
      ++firings;
      if (rv != tv || (tv && !same_as_tc0(&want, tc0_slot(dest)))) {
        fprintf(stderr, "DISAGREEMENT theory %" PRIu64 " step %d: reference %d, tc0 %d\n", th, step, rv, tv);
        return 1;
      }
      if (tv) { admitted++; slot[dest] = want; written[dest] = true; if (minted) last_gen++; }
      if (tc0_last_gen() != last_gen) { fprintf(stderr, "name counter differs\n"); return 1; }
    }
  }
  printf("step differential: %" PRIu64 " random theories, %" PRIu64 " firings, %" PRIu64 " admitted, 0 disagreements with the naive reference\n",
         theories, firings, admitted);
  return 0;
}
