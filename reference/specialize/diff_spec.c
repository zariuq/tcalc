/* diff_spec.c: the specializer's law, tested.  For every theory compiled into this binary, the
 * generated code and the generic route (tcs_instance_of + tr_admits / tr_fire of tcalc_ref) run on
 * two states kept in lockstep.  Each step draws a rule, parameters and occurrences, then compares
 *   admission alone   the same verdict, reason, failing guard and first name, and the state unchanged;
 *   the firing        the same result (and made identities), and tr_state_equal states.
 * Every 150 steps a side trip leaves the ground fragment on clones of both states (a frame variable,
 * a stored schema, a live disequation) for 25 steps, so the generated code's declines are compared too.
 *
 *   usage: diff_spec SEED STEPS_PER_THEORY
 * Exit status 1 on any disagreement.
 */
#include "tcs.h"

#include <stdlib.h>
#include <string.h>

static uint64_t rng;
static uint64_t rnd(uint64_t n) {
  rng ^= rng << 13, rng ^= rng >> 7, rng ^= rng << 17;
  return rng % n;
}

static long disagree, compared, admitted, refused[5], noverdict, restarts;
#define MAXUSE 8
#define MAXMAKE 8

static tr_term pool[16];
static size_t npool;
static uint32_t sym_p, sym_q, sym_r, sym_f, sym_g;
static tr_term cst_e, cst_a, cst_b;

static tr_term ground(tr_ctx *c, int depth) {
  switch (rnd(depth > 0 ? 7 : 5)) {
  case 0: return tr_code(c, (int64_t)rnd(3));
  case 1: return tr_name(c, (uint32_t)rnd(2));
  case 2: return cst_a;
  case 3: return cst_b;
  case 4: return tr_code(c, (int64_t)rnd(3));
  case 5: {
    tr_term x = ground(c, depth - 1);
    return tr_app(c, sym_f, &x);
  }
  default: {
    tr_term x[2] = {ground(c, depth - 1), ground(c, depth - 1)};
    return tr_app(c, sym_g, x);
  }
  }
}

static tr_term ground_label(tr_ctx *c) {
  tr_term a[3] = {ground(c, 1), ground(c, 1), ground(c, 1)};
  switch (rnd(9)) {
  case 7: return ground(c, 1); /* a code, a name, a constant or f(..), g(..) as a label */
  case 8: return tr_code(c, (int64_t)rnd(3));
  case 0: return cst_e;
  case 1: case 2: return tr_app(c, sym_p, a);
  case 3: case 4: return tr_app(c, sym_q, a);
  default: return tr_app(c, sym_r, a);
  }
}

static void both(tr_state *x, tr_state *y, const tr_firing *f) {
  tr_fire(x, f, NULL);
  tr_fire(y, f, NULL);
}

static void make_both(tr_state *x, tr_state *y, tr_term label) {
  tr_make m = {label, 0, 0};
  tr_firing f = {.makes = &m, .nmakes = 1};
  both(x, y, &f);
}

static size_t present(const tr_state *s, tr_occ *ids, size_t cap) {
  size_t n = 0;
  for (tr_occ o = tr_next_present(s, 0, NULL); o && n < cap; o = tr_next_present(s, o, NULL)) ids[n++] = o;
  return n;
}

static void print_result(const char *who, tr_verdict v, const tr_result *r) {
  fprintf(stderr, "    %s: verdict %d reason %d guard %zu first_name %u\n", who, (int)v, (int)r->reason, r->guard,
          r->first_name);
}

static void report(const char *what, const tcs_compiled_theory *T, size_t ri, long step, const tr_term *params, size_t np,
                   const tr_occ *occs, size_t nuse, tr_ctx *c) {
  if (++disagree > 8) return;
  fprintf(stderr, "DISAGREEMENT (%s): theory %s rule %s step %ld\n    params:", what, T->name, T->rules[ri].name, step);
  for (size_t k = 0; k < np; k++) fputc(' ', stderr), tr_print(stderr, c, params[k]);
  fprintf(stderr, "\n    occurrences:");
  for (size_t k = 0; k < nuse; k++) fprintf(stderr, " %llu", (unsigned long long)occs[k]);
  fputc('\n', stderr);
}

/* A ground instance of a rule's term: parameters as given, every other local one random ground
 * term for the whole step (so repeated locals agree), a fresh name some ground term. */
static tr_term ground_instance(tr_ctx *c, const tcs_rule *R, tr_term t, const tr_term *params, tr_term *env) {
  switch (tr_term_kind(c, t)) {
  case TR_LOCAL: {
    uint32_t i = tr_term_index(c, t);
    if (i < R->nparams) return params[i];
    if (!env[i]) env[i] = ground(c, rnd(2));
    return env[i];
  }
  case TR_FRESH: return ground(c, 0);
  case TR_APP: {
    uint32_t n = tr_term_arity(c, t);
    tr_term a[8];
    if (!n || n > 8) return t;
    for (uint32_t i = 0; i < n; i++) a[i] = ground_instance(c, R, tr_term_arg(c, t, i), params, env);
    return tr_app(c, tr_term_symbol(c, t), a);
  }
  default: return t;
  }
}

/* One step on states sg (generated code) and sr (generic route); false on a disagreement. */
static bool step(const tcs_compiled_theory *T, const tcs_theory *th, tr_ctx *c, tr_state *sg, tr_state *sr, long k,
                 tcs_instance *inst) {
  size_t ri = (size_t)rnd(th->nrules);
  const tcs_rule *R = &th->rules[ri];
  size_t nuse = R->ntakes + R->nreads;
  if (nuse > MAXUSE || R->nmakes > MAXMAKE || R->nlocals > 64) return true;
  tr_term params[4] = {0};
  for (uint32_t i = 0; i < R->nparams && i < 4; i++) params[i] = pool[rnd(npool)];
  tr_occ ids[64], occs[MAXUSE];
  size_t n = present(sr, ids, 64);
  for (size_t i = 0; i < nuse; i++) {
    uint64_t x = rnd(100);
    if (x < 78 && n) occs[i] = ids[rnd(n)];
    else if (x < 90 && i) occs[i] = occs[rnd(i)];
    else occs[i] = rnd(5) == 0 ? 0 : rnd(40);
  }
  if (rnd(2)) { /* prepare: facts that match the patterns under one binding, made on both states */
    tr_term env[64] = {0};
    for (size_t i = 0; i < nuse; i++) {
      if (rnd(8) == 0) continue;
      tr_term pat = i < R->ntakes ? R->takes[i] : R->reads[i - R->ntakes];
      tr_make m = {ground_instance(c, R, pat, params, env), 0, 0};
      tr_occ made = 0;
      tr_result rr = {.made = &made};
      tr_firing f = {.makes = &m, .nmakes = 1};
      if (tr_fire(sr, &f, &rr) == TR_ADMITTED) {
        tr_fire(sg, &f, NULL);
        occs[i] = made;
      }
    }
  }
  tr_term locals_g[64], locals_r[64];
  bool want_locals = rnd(20) == 0 && R->nlocals - R->nparams <= 64;
  const tr_firing *f = tcs_instance_of(inst, c, R, params, occs);

  /* admission alone */
  tr_result ga = {.first_name = 77777}, ra = {.first_name = 77777};
  tr_verdict vg = T->rules[ri].decide(sg, params, occs, &ga, false);
  bool ok = tr_state_equal(sg, sr);
  if (!ok) report("admission changed the state", T, ri, k, params, R->nparams, occs, nuse, c);
  tr_verdict vr = tr_admits(sr, f, &ra);
  compared++;
  if (vg != vr || ga.reason != ra.reason || ga.guard != ra.guard || ga.first_name != ra.first_name) {
    report("admission", T, ri, k, params, R->nparams, occs, nuse, c);
    print_result("generated", vg, &ga);
    print_result("generic  ", vr, &ra);
    ok = false;
  }

  /* the firing */
  tr_occ made_g[MAXMAKE], made_r[MAXMAKE];
  memset(made_g, 0, sizeof made_g);
  memset(made_r, 0, sizeof made_r);
  tr_result gf = {.made = made_g, .first_name = 77777}, rf = {.made = made_r, .first_name = 77777};
  if (want_locals) gf.locals = locals_g, rf.locals = locals_r;
  vg = T->rules[ri].decide(sg, params, occs, &gf, true);
  vr = tr_fire(sr, f, &rf);
  compared++;
  bool same = vg == vr && gf.reason == rf.reason && gf.guard == rf.guard && gf.first_name == rf.first_name &&
              !memcmp(made_g, made_r, sizeof made_g);
  if (same && want_locals && vr == TR_ADMITTED)
    for (uint32_t i = 0; i < R->nlocals - R->nparams; i++) same &= locals_g[i] == locals_r[i];
  if (!same) {
    report("firing", T, ri, k, params, R->nparams, occs, nuse, c);
    print_result("generated", vg, &gf);
    print_result("generic  ", vr, &rf);
    ok = false;
  }
  if (!tr_state_equal(sg, sr)) {
    report("states after the firing", T, ri, k, params, R->nparams, occs, nuse, c);
    ok = false;
  }
  if (vr == TR_ADMITTED) admitted++;
  else if (vr == TR_REFUSED) refused[rf.reason]++;
  else noverdict++;
  return ok;
}

/* Host predicates (decided at every solution, read through the view). */
static int h_lt(tr_view *v, const tr_term *a, size_t n) {
  int64_t x, y;
  if (n != 2) return 0;
  if (tr_view_code(v, a[0], &x) && tr_view_code(v, a[1], &y)) return x < y;
  return tr_view_ground(v, a[0]) && tr_view_ground(v, a[1]) ? 0 : -1; /* not two codes, or open */
}
static int h_isname(tr_view *v, const tr_term *a, size_t n) {
  if (n != 1 || !tr_view_ground(v, a[0])) return n == 1 ? -1 : 0;
  return tr_term_kind(tr_view_ctx(v), tr_view_resolve(v, a[0])) == TR_NAME;
}
static int h_maybe(tr_view *v, const tr_term *a, size_t n) { /* no verdict on the code 2 */
  int64_t x;
  return n == 1 && tr_view_code(v, a[0], &x) && x == 2 ? -1 : 1;
}

/* Leaves the ground fragment on both states. */
static void side_trip(tr_ctx *c, tr_state *x, tr_state *y) {
  tr_term L0 = tr_local(c, 0);
  switch (rnd(3)) {
  case 0: { /* a frame variable in a label */
    tr_make m = {tr_app(c, sym_p, &L0), 0, 0};
    tr_firing f = {.locals = 1, .makes = &m, .nmakes = 1};
    both(x, y, &f);
    break;
  }
  case 1: { /* a stored schema */
    tr_term qa[2] = {L0, cst_a};
    tr_make m = {tr_app(c, sym_q, qa), 0, 1};
    tr_firing f = {.makes = &m, .nmakes = 1};
    both(x, y, &f);
    break;
  }
  default: { /* a live disequation */
    tr_make m = {tr_app(c, sym_p, &L0), 0, 0};
    tr_eq ap = {L0, cst_a};
    tr_firing f = {.locals = 1, .makes = &m, .nmakes = 1, .apart = &ap, .napart = 1};
    both(x, y, &f);
    break;
  }
  }
}

int main(int argc, char **argv) {
  if (argc < 3) {
    fprintf(stderr, "usage: %s SEED STEPS_PER_THEORY\n", argv[0]);
    return 2;
  }
  uint64_t seed = strtoull(argv[1], NULL, 10);
  long steps = strtol(argv[2], NULL, 10);
  rng = seed * 6364136223846793005ULL + 1442695040888963407ULL;
  const tcs_host hosts[] = {{"lt", h_lt}, {"isname", h_isname}, {"maybe", h_maybe}};
  tcs_register_hosts(hosts, 3);
  size_t nrules = 0, nspec = 0;
  for (size_t ti = 0; ti < tcs_ncompiled; ti++) {
    const tcs_compiled_theory *T = &tcs_compiled[ti];
    tr_ctx *c = tr_ctx_new();
    if (!T->link(c)) return 2;
    const tcs_theory *th = T->schemas();
    nrules += th->nrules;
    for (size_t i = 0; i < th->nrules; i++) nspec += T->rules[i].specialized;
    sym_p = tr_symbol(c, "p", 1), sym_q = tr_symbol(c, "q", 2), sym_r = tr_symbol(c, "r", 3);
    sym_f = tr_symbol(c, "f", 1), sym_g = tr_symbol(c, "g", 2);
    cst_e = tr_const(c, "e"), cst_a = tr_const(c, "a"), cst_b = tr_const(c, "b");
    if (tcs_head_keys_differ(c)) { /* the generated code's head keys must be the reference's */
      fprintf(stderr, "head keys differ from tcalc_ref's head_key\n");
      return 1;
    }
    npool = 0;
    for (int i = 0; i < 3; i++) pool[npool++] = tr_code(c, i);
    for (uint32_t i = 0; i < 4; i++) pool[npool++] = tr_name(c, i);
    pool[npool++] = cst_a, pool[npool++] = cst_b;
    pool[npool++] = tr_app(c, sym_f, &pool[0]);
    pool[npool++] = tr_app(c, sym_f, &pool[6]); /* f(@3): a name not yet minted inside */
    tr_term ga1[2] = {cst_a, pool[4]};
    pool[npool++] = tr_app(c, sym_g, ga1);
    tr_state *sg = tr_state_new(c), *sr = tr_state_new(c);
    tr_firing mint = {.fresh = 3}; /* @0, @1, @2; @3 is minted only by a fresh rule */
    both(sg, sr, &mint);
    for (int i = 0; i < 6; i++) make_both(sg, sr, ground_label(c));
    tcs_instance inst = {0};
    long k = 0;
    while (k < steps) {
      if (k % 150 == 149) { /* a side trip outside the fragment, on clones */
        tr_state *xg = tr_state_clone(sg), *xr = tr_state_clone(sr);
        side_trip(c, xg, xr);
        for (int j = 0; j < 25; j++, k++)
          if (!step(T, th, c, xg, xr, k, &inst)) break;
        tr_state_free(xg);
        tr_state_free(xr);
      }
      if (!step(T, th, c, sg, sr, k, &inst)) { /* start the theory again from the generic state */
        tr_state_free(sg);
        sg = tr_state_clone(sr);
      }
      k++;
      if (tr_vars(sr) || tr_apart_count(sr)) { /* a rule outside the fragment left it: start again */
        tr_state_free(sg);
        tr_state_free(sr);
        sg = tr_state_new(c), sr = tr_state_new(c);
        both(sg, sr, &mint);
        for (int i = 0; i < 6; i++) make_both(sg, sr, ground_label(c));
        restarts++;
      }
      if (rnd(4) == 0) make_both(sg, sr, ground_label(c));
      if (tr_present_count(sr) > 40) { /* forget one occurrence */
        tr_occ ids[64];
        size_t n = present(sr, ids, 64);
        tr_use u = {tr_local(c, 0), ids[rnd(n)]};
        tr_firing f = {.locals = 1, .takes = &u, .ntakes = 1};
        both(sg, sr, &f);
      }
    }
    tcs_instance_free(&inst);
    tr_state_free(sg);
    tr_state_free(sr);
    tr_ctx_free(c);
  }
  printf("diff_spec seed %llu: %zu theories, %zu rules (%zu specialized); %ld decisions compared: admitted %ld, refused "
         "shapes %ld fits %ld unsolvable %ld guard %ld, no verdict %ld; specialized path %zu, generic route %zu; "
         "%ld restarts after leaving the fragment; %ld disagreements\n",
         (unsigned long long)seed, tcs_ncompiled, nrules, nspec, compared, admitted, refused[TR_SHAPES], refused[TR_FITS],
         refused[TR_UNSOLVABLE], refused[TR_GUARD], noverdict, tcs_count.fast, tcs_count.generic, restarts, disagree);
  return disagree != 0;
}
