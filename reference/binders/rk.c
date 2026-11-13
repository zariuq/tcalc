/* rk.c: rules as data, fired on tcalc_ref's step (see rk.h). */
#include "rk.h"

#include <stdlib.h>
#include <string.h>

static void *rk_xrealloc(void *p, size_t n) {
  void *q = realloc(p, n ? n : 1);
  if (!q) {
    fputs("rk: out of memory\n", stderr);
    exit(2);
  }
  return q;
}
#define RK_PUSH(arr, len, cap, x)                                         \
  do {                                                                    \
    if ((len) >= (cap)) {                                                 \
      (cap) = (cap) ? 2 * (cap) : 8;                                      \
      (arr) = rk_xrealloc((arr), (size_t)(cap) * sizeof *(arr));          \
    }                                                                     \
    (arr)[(len)++] = (x);                                                 \
  } while (0)

void rk_init(rk_rule *r, const char *what, uint32_t locals) {
  memset(r, 0, sizeof *r);
  r->what = what;
  r->locals = locals;
  r->fast = -1;
}
void rk_take(rk_rule *r, tr_term t) { RK_PUSH(r->takes, r->ntakes, r->captakes, t); }
void rk_read(rk_rule *r, tr_term t) { RK_PUSH(r->reads, r->nreads, r->capreads, t); }
void rk_make(rk_rule *r, tr_term t) { RK_PUSH(r->makes, r->nmakes, r->capmakes, t); }
void rk_param(rk_rule *r, uint32_t l) { RK_PUSH(r->params, r->nparams, r->capparams, l); }
void rk_apart(rk_rule *r, tr_term a, tr_term b) {
  tr_eq e = {a, b};
  RK_PUSH(r->apart, r->napart, r->capapart, e);
}
void rk_guard(rk_rule *r, tr_guard g) { RK_PUSH(r->guards, r->nguards, r->capguards, g); }
void rk_absent(rk_rule *r, tr_term t) { rk_guard(r, (tr_guard){.kind = TR_G_ABSENT, .a = t}); }
void rk_free(rk_rule *r) {
  free(r->takes);
  free(r->reads);
  free(r->makes);
  free(r->params);
  free(r->apart);
  free(r->guards);
  memset(r, 0, sizeof *r);
}

void rk_engine_init(rk_engine *e, tr_ctx *ctx, tr_state *st) {
  memset(e, 0, sizeof *e);
  e->ctx = ctx;
  e->st = st;
}
void rk_engine_free(rk_engine *e) {
  free(e->uses);
  free(e->eqs);
  free(e->mks);
  free(e->made);
  memset(e, 0, sizeof *e);
}

tr_occ rk_fire(rk_engine *e, const rk_rule *r, const tr_occ *occs, const tr_term *vals, tr_occ *made,
               uint32_t *first_name) {
  size_t nuse = r->ntakes + r->nreads;
  if (r->fast >= 0 && e->decide) { /* the compiled decision of the same rule */
    if (r->nmakes > e->capmks) {
      e->capmks = r->nmakes;
      e->mks = rk_xrealloc(e->mks, r->nmakes * sizeof *e->mks);
      e->made = rk_xrealloc(e->made, r->nmakes * sizeof *e->made);
    }
    tr_result res = {.made = e->made};
    e->fast_decisions++;
    if (e->decide(r->fast, e->st, vals, occs, &res) != TR_ADMITTED) {
      e->refused++;
      return 0;
    }
    e->fired++;
    if (tr_vars(e->st) != 0) {
      fprintf(stderr, "rk: rule '%s' left a local unbound: a schematic fact was made\n", r->what);
      exit(3);
    }
    if (made) memcpy(made, e->made, r->nmakes * sizeof *made);
    if (first_name) *first_name = res.first_name;
    return r->nmakes ? e->made[0] : 1;
  }
  if (nuse > e->capuses) e->capuses = nuse, e->uses = rk_xrealloc(e->uses, nuse * sizeof *e->uses);
  if (r->nparams > e->capeqs) e->capeqs = r->nparams, e->eqs = rk_xrealloc(e->eqs, r->nparams * sizeof *e->eqs);
  if (r->nmakes > e->capmks) {
    e->capmks = r->nmakes;
    e->mks = rk_xrealloc(e->mks, r->nmakes * sizeof *e->mks);
    e->made = rk_xrealloc(e->made, r->nmakes * sizeof *e->made);
  }
  for (size_t i = 0; i < nuse; i++) {
    e->uses[i].pattern = i < r->ntakes ? r->takes[i] : r->reads[i - r->ntakes];
    e->uses[i].occ = occs[i];
  }
  for (size_t i = 0; i < r->nparams; i++) e->eqs[i] = (tr_eq){tr_local(e->ctx, r->params[i]), vals[i]};
  for (size_t i = 0; i < r->nmakes; i++) e->mks[i] = (tr_make){r->makes[i], 0, 0};
  tr_firing f = {.locals = r->locals,
                 .fresh = r->fresh,
                 .takes = e->uses,
                 .ntakes = r->ntakes,
                 .reads = e->uses + r->ntakes,
                 .nreads = r->nreads,
                 .makes = e->mks,
                 .nmakes = r->nmakes,
                 .tells = e->eqs,
                 .ntells = r->nparams,
                 .apart = r->apart,
                 .napart = r->napart,
                 .guards = r->guards,
                 .nguards = r->nguards};
  tr_result res = {.made = e->made};
  tr_verdict v = tr_fire(e->st, &f, &res);
  if (v != TR_ADMITTED) {
    e->refused++;
    return 0;
  }
  e->fired++;
  if (tr_vars(e->st) != 0) {
    fprintf(stderr, "rk: rule '%s' left a local unbound: a schematic fact was made\n", r->what);
    exit(3);
  }
  if (made) memcpy(made, e->made, r->nmakes * sizeof *made);
  if (first_name) *first_name = res.first_name;
  return r->nmakes ? e->made[0] : 1;
}

/* t with LOCAL i written LOCAL map[i]. */
static tr_term relocal(tr_ctx *c, tr_term t, const uint32_t *map) {
  tr_kind k = tr_term_kind(c, t);
  if (k == TR_LOCAL) return tr_local(c, map[tr_term_index(c, t)]);
  if (k != TR_APP) return t;
  uint32_t n = tr_term_arity(c, t);
  if (!n) return t;
  tr_term small[8], *a = n <= 8 ? small : rk_xrealloc(NULL, n * sizeof *a);
  for (uint32_t i = 0; i < n; i++) a[i] = relocal(c, tr_term_arg(c, t, i), map);
  tr_term out = tr_app(c, tr_term_symbol(c, t), a);
  if (a != small) free(a);
  return out;
}

void rk_to_schema(tr_ctx *c, const rk_rule *r, tr_firing *out, uint32_t *nparams) {
  uint32_t *map = rk_xrealloc(NULL, (r->locals + 1) * sizeof *map);
  bool *is_param = rk_xrealloc(NULL, r->locals + 1);
  memset(is_param, 0, r->locals + 1);
  uint32_t next = 0;
  for (size_t i = 0; i < r->nparams; i++) map[r->params[i]] = next++, is_param[r->params[i]] = true;
  for (uint32_t l = 0; l < r->locals; l++)
    if (!is_param[l]) map[l] = next++;
  memset(out, 0, sizeof *out);
  out->locals = r->locals;
  out->fresh = r->fresh;
  tr_use *uses = rk_xrealloc(NULL, (r->ntakes + r->nreads + 1) * sizeof *uses);
  for (size_t i = 0; i < r->ntakes + r->nreads; i++)
    uses[i] = (tr_use){relocal(c, i < r->ntakes ? r->takes[i] : r->reads[i - r->ntakes], map), 0};
  out->takes = uses, out->ntakes = r->ntakes;
  out->reads = uses + r->ntakes, out->nreads = r->nreads;
  tr_make *mk = rk_xrealloc(NULL, (r->nmakes + 1) * sizeof *mk);
  for (size_t i = 0; i < r->nmakes; i++) mk[i] = (tr_make){relocal(c, r->makes[i], map), 0, 0};
  out->makes = mk, out->nmakes = r->nmakes;
  tr_eq *ap = rk_xrealloc(NULL, (r->napart + 1) * sizeof *ap);
  for (size_t i = 0; i < r->napart; i++) ap[i] = (tr_eq){relocal(c, r->apart[i].left, map), relocal(c, r->apart[i].right, map)};
  out->apart = ap, out->napart = r->napart;
  tr_guard *gs = rk_xrealloc(NULL, (r->nguards + 1) * sizeof *gs);
  for (size_t i = 0; i < r->nguards; i++) {
    gs[i] = r->guards[i];
    if (gs[i].a) gs[i].a = relocal(c, gs[i].a, map);
    if (gs[i].b) gs[i].b = relocal(c, gs[i].b, map);
  }
  out->guards = gs, out->nguards = r->nguards;
  *nparams = (uint32_t)r->nparams;
  free(map);
  free(is_param);
}

void rk_schema_free(tr_firing *f) {
  free((void *)f->takes);
  free((void *)f->makes);
  free((void *)f->apart);
  free((void *)f->guards);
  memset(f, 0, sizeof *f);
}

tr_term rk_label(rk_engine *e, tr_occ o) {
  tr_term l;
  if (!tr_present(e->st, o, &l)) {
    fprintf(stderr, "rk: fact %llu is not present\n", (unsigned long long)o);
    exit(3);
  }
  return l;
}

tr_term rk_arg(rk_engine *e, tr_occ o, uint32_t i) { return tr_term_arg(e->ctx, rk_label(e, o), i); }
