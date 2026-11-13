/* tcs_gen.c: the specializer.  Reads theories (firing schemas in the text form of tcs.h) and writes
 * C that decides each rule's instances on tcalc_ref's own states, with the rule folded in.
 *
 *   usage: tcs_gen [--fault N] OUT.c THEORY.tcs ...
 *
 * The law the written code must keep, for every rule R, state s, parameters p and occurrences o:
 *   R(s, p, o, r, commit) and tr_fire / tr_admits (s, inst(R, p, o), r) give the same verdict,
 *   reason, failing guard, first name and made identities, and leave tr_state_equal states;
 *   a refusal, and every admission without commit, changes nothing.
 *
 * How.  The fast path is the ground fragment (tcs_inside.h): every present label is ground, so the
 * information is solved by one-way matching.  The unification of the rule's patterns with the
 * selected labels and of its tells is done here, at generation time, as a mode analysis in the
 * manner of a WAM compiler: each local is FREE, RT (held by a C variable naming a ground term at
 * run time) or ALIAS (bound to a term of the rule).  Run-time checks are emitted only where a
 * value is known only at run time; a clash between two terms of the rule becomes an unconditional
 * refusal, placed after the Shapes and Fits checks so the reason stays the reference's.  A rule
 * that would leave a local unbound in what it makes or tells apart (the result would gain frame
 * variables) is outside the fragment: its code is the generic route.  At run time the code calls
 * the generic route whenever the state or the parameters leave the fragment: frame variables,
 * live disequations, open heads, a stored schema selected or scanned, parameters that are not
 * ground, or a request for the locals' values.
 *
 * Guards at every solution (tcalc_ref.c, "Guards at every solution"), on a ground store:
 *   ask a = b         a and b identical under the bindings (free locals equal only themselves);
 *   count p n         without free locals: n present labels identical to p, and nothing possible;
 *                     with free (guard-only) locals: any label that matches is possible, so the
 *                     guard fails; it holds iff nothing matches and n = 0.  Absence is count 0.
 *
 * --fault N plants one bug in the written code, so the tests can show they catch it:
 *   1 skip the equality of a repeated local      7 take before the guards (a refusal leaves a trace)
 *   2 count only at the most general unifier     8 swap two arguments of a made label
 *   3 skip the distinctness of takes             9 fresh names one too high
 *   4 skip the minting check of parameters      10 skip the separation of told disequations
 *   5 skip "nothing both taken and read"        11 a static clash reported as a guard failure
 *   6 a Fits failure reported as Shapes         12 a ground count counts every label of the head
 *                                               13 a host's "no verdict" taken as "holds"
 *
 * Host guards (tcs.h): the code fills the state's local environment with the bindings, builds the
 * view the generic route would build, calls the same host predicate, and empties the environment
 * again.  A rule with host guards is specialized only when every local ends bound to a ground
 * value, so the host sees exactly the generic route's bindings.
 */
#include "tcs.h"

#include <ctype.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

static int FAULT;

static void *xrealloc(void *p, size_t n) {
  void *q = realloc(p, n ? n : 1);
  if (!q) {
    fputs("tcs_gen: out of memory\n", stderr);
    abort();
  }
  return q;
}

/* ---- strings ---- */

typedef struct {
  char *s;
  size_t n, cap;
} sb;

static void sbf(sb *b, const char *fmt, ...) {
  va_list ap, aq;
  va_start(ap, fmt);
  va_copy(aq, ap);
  int k = vsnprintf(NULL, 0, fmt, aq);
  va_end(aq);
  if (b->n + (size_t)k + 1 > b->cap) {
    b->cap = 2 * (b->n + (size_t)k + 1);
    b->s = xrealloc(b->s, b->cap);
  }
  vsnprintf(b->s + b->n, (size_t)k + 1, fmt, ap);
  b->n += (size_t)k;
  va_end(ap);
}

static char *str(const char *fmt, ...) {
  va_list ap, aq;
  va_start(ap, fmt);
  va_copy(aq, ap);
  int k = vsnprintf(NULL, 0, fmt, aq);
  va_end(aq);
  char *s = xrealloc(NULL, (size_t)k + 1);
  vsnprintf(s, (size_t)k + 1, fmt, ap);
  va_end(ap);
  return s;
}

/* Conditions are strings; "0" and "1" fold. */
static bool is0(const char *e) { return !strcmp(e, "0"); }
static bool is1(const char *e) { return !strcmp(e, "1"); }
static char *AND(char *a, char *b) {
  if (is0(a) || is0(b)) {
    free(a);
    free(b);
    return str("0");
  }
  if (is1(a)) {
    free(a);
    return b;
  }
  if (is1(b)) {
    free(b);
    return a;
  }
  char *r = str("%s && %s", a, b);
  free(a);
  free(b);
  return r;
}

/* ---- a theory: its symbols and constants, linked into the run-time context ---- */

typedef struct {
  tr_ctx *c;
  char *pfx;
  size_t index; /* which theory of its file */
  size_t *symidx, nsymidx;   /* generation-time symbol -> S index + 1 */
  size_t *constidx, nconstidx; /* generation-time term -> K index + 1 */
  size_t nsyms, nconsts;
  sb link;
  size_t specialized, generic;
  size_t nhosts; /* host predicates looked up at link: H[k] */
} tg;

static size_t sym_index(tg *T, uint32_t sym) {
  if (sym >= T->nsymidx) {
    size_t n = T->nsymidx ? T->nsymidx : 16;
    while (n <= sym) n *= 2;
    T->symidx = xrealloc(T->symidx, n * sizeof *T->symidx);
    memset(T->symidx + T->nsymidx, 0, (n - T->nsymidx) * sizeof *T->symidx);
    T->nsymidx = n;
  }
  if (!T->symidx[sym]) {
    sbf(&T->link, "  %s_S[%zu] = tr_symbol(c, \"%s\", %" PRIu32 ");\n", T->pfx, T->nsyms, tr_symbol_name(T->c, sym),
        tr_symbol_arity(T->c, sym));
    T->symidx[sym] = ++T->nsyms;
  }
  return T->symidx[sym] - 1;
}

static bool is_const(tr_ctx *c, tr_term t) {
  switch (tr_term_kind(c, t)) {
  case TR_APP:
    for (uint32_t i = 0; i < tr_term_arity(c, t); i++)
      if (!is_const(c, tr_term_arg(c, t, i))) return false;
    return true;
  case TR_CODE:
  case TR_NAME:
    return true;
  default:
    return false;
  }
}

static size_t const_index(tg *T, tr_term t) {
  if (t >= T->nconstidx) {
    size_t n = T->nconstidx ? T->nconstidx : 64;
    while (n <= t) n *= 2;
    T->constidx = xrealloc(T->constidx, n * sizeof *T->constidx);
    memset(T->constidx + T->nconstidx, 0, (n - T->nconstidx) * sizeof *T->constidx);
    T->nconstidx = n;
  }
  if (T->constidx[t]) return T->constidx[t] - 1;
  tr_ctx *c = T->c;
  switch (tr_term_kind(c, t)) {
  case TR_APP: {
    uint32_t n = tr_term_arity(c, t);
    size_t s = sym_index(T, tr_term_symbol(c, t));
    size_t *idx = xrealloc(NULL, (n + 1) * sizeof *idx);
    for (uint32_t i = 0; i < n; i++) idx[i] = const_index(T, tr_term_arg(c, t, i));
    if (!n) sbf(&T->link, "  %s_K[%zu] = tr_app(c, %s_S[%zu], NULL);\n", T->pfx, T->nconsts, T->pfx, s);
    else {
      sbf(&T->link, "  {\n    tr_term a[%" PRIu32 "] = {", n);
      for (uint32_t i = 0; i < n; i++) sbf(&T->link, "%s%s_K[%zu]", i ? ", " : "", T->pfx, idx[i]);
      sbf(&T->link, "};\n    %s_K[%zu] = tr_app(c, %s_S[%zu], a);\n  }\n", T->pfx, T->nconsts, T->pfx, s);
    }
    free(idx);
    break;
  }
  case TR_CODE: {
    int64_t v = tr_term_code(c, t);
    if (v == INT64_MIN) sbf(&T->link, "  %s_K[%zu] = tr_code(c, INT64_MIN);\n", T->pfx, T->nconsts);
    else sbf(&T->link, "  %s_K[%zu] = tr_code(c, INT64_C(%" PRId64 "));\n", T->pfx, T->nconsts, v);
    break;
  }
  default: /* TR_NAME */
    sbf(&T->link, "  %s_K[%zu] = tr_name(c, %" PRIu32 ");\n", T->pfx, T->nconsts, tr_term_index(c, t));
    break;
  }
  T->constidx[t] = ++T->nconsts;
  return T->nconsts - 1;
}

/* ---- a rule ---- */

typedef enum { B_FREE, B_RT, B_ALIAS } bst;
typedef struct {
  bst st;
  int cv;
  tr_term alias;
} bnd;
typedef struct {
  int cv;    /* >= 0: the C variable v<cv> holds a ground term at run time */
  tr_term t; /* otherwise a term of the rule */
} val;

typedef struct {
  tg *T;
  tr_ctx *c;
  const tcs_rule *r;
  size_t ri;
  sb body;
  bnd *B;
  uint32_t *uses; /* occurrences of each local in the rule's terms */
  int ncv, ntmp;
  bool dead;
  const char *unsolvable; /* the reason written for a refusal of the information */
  bool load_all;          /* a rule with host guards: every local gets its value */
  const char *fresh_base; /* where FRESH 0 is minted: s->nnames while deciding, first at the result */
} rg;

static val RT(int cv) { return (val){cv, TR_NONE}; }
static val TM(tr_term t) { return (val){-1, t}; }

static val deref(rg *g, val v) {
  while (v.cv < 0 && tr_term_kind(g->c, v.t) == TR_LOCAL) {
    bnd *b = &g->B[tr_term_index(g->c, v.t)];
    if (b->st == B_RT) return RT(b->cv);
    if (b->st == B_FREE) break;
    v.t = b->alias;
  }
  return v;
}

static bool is_free(rg *g, val v) { return v.cv < 0 && tr_term_kind(g->c, v.t) == TR_LOCAL; }

/* No free local below v: the value is the same ground term at every solution. */
static bool determined(rg *g, val v) {
  v = deref(g, v);
  if (v.cv >= 0) return true;
  switch (tr_term_kind(g->c, v.t)) {
  case TR_LOCAL:
    return false;
  case TR_APP:
    for (uint32_t i = 0; i < tr_term_arity(g->c, v.t); i++)
      if (!determined(g, TM(tr_term_arg(g->c, v.t, i)))) return false;
    return true;
  default:
    return true;
  }
}

static bool occurs(rg *g, uint32_t local, val v) {
  v = deref(g, v);
  if (v.cv >= 0) return false;
  switch (tr_term_kind(g->c, v.t)) {
  case TR_LOCAL:
    return tr_term_index(g->c, v.t) == local;
  case TR_APP:
    for (uint32_t i = 0; i < tr_term_arity(g->c, v.t); i++)
      if (occurs(g, local, TM(tr_term_arg(g->c, v.t, i)))) return true;
    return false;
  default:
    return false;
  }
}

/* A free local that occurs once in the rule: matching it needs no value (unless a host guard will
 * read every local's value). */
static bool wildcard(rg *g, val v) {
  v = deref(g, v);
  return !g->load_all && is_free(g, v) && g->uses[tr_term_index(g->c, v.t)] == 1;
}

static int newcv(rg *g, const char *init) {
  int cv = g->ncv++;
  sbf(&g->body, "  tr_term v%d = %s;\n  (void)v%d;\n", cv, init, cv);
  return cv;
}

static void refuse_if(rg *g, const char *cond, const char *reason) {
  if (g->dead || is0(cond)) return;
  if (is1(cond)) {
    sbf(&g->body, "  return tcs_refuse(r, %s, 0);\n", reason);
    g->dead = true;
  } else
    sbf(&g->body, "  if (%s) return tcs_refuse(r, %s, 0);\n", cond, reason);
}

static void clash(rg *g) { refuse_if(g, "1", g->unsolvable); }

static void unify(rg *g, val x, val y);

/* The ground term held by v<cv> against a term of the rule that is not a free local. */
static void match_rt(rg *g, int cv, tr_term t) {
  tr_ctx *c = g->c;
  if (is_const(c, t)) {
    char *e = str("v%d != %s_K[%zu]", cv, g->T->pfx, const_index(g->T, t));
    refuse_if(g, e, g->unsolvable);
    free(e);
    return;
  }
  switch (tr_term_kind(c, t)) {
  case TR_APP: {
    char *e = str("ND(c, v%d)->kind != TR_APP || ND(c, v%d)->val != %s_S[%zu]", cv, cv, g->T->pfx,
                  sym_index(g->T, tr_term_symbol(c, t)));
    refuse_if(g, e, g->unsolvable);
    free(e);
    for (uint32_t i = 0; i < tr_term_arity(c, t) && !g->dead; i++) {
      val a = TM(tr_term_arg(c, t, i));
      if (wildcard(g, a)) continue;
      char *init = str("ARG(c, v%d, %" PRIu32 ")", cv, i);
      int sub = newcv(g, init);
      free(init);
      unify(g, RT(sub), a);
    }
    return;
  }
  default: /* a fresh name: no present label and no parameter holds one */
    clash(g);
    return;
  }
}

static void bind_free(rg *g, tr_term local, val v) {
  uint32_t i = tr_term_index(g->c, local);
  if (v.cv >= 0) {
    g->B[i] = (bnd){B_RT, v.cv, TR_NONE};
    return;
  }
  if (tr_term_kind(g->c, v.t) == TR_LOCAL && tr_term_index(g->c, v.t) == i) return;
  if (occurs(g, i, v)) {
    clash(g);
    return;
  }
  g->B[i] = (bnd){B_ALIAS, -1, v.t};
}

static void unify(rg *g, val x, val y) {
  if (g->dead) return;
  x = deref(g, x);
  y = deref(g, y);
  if (x.cv >= 0 && y.cv >= 0) {
    if (x.cv != y.cv && FAULT != 1) {
      char *e = str("v%d != v%d", x.cv, y.cv);
      refuse_if(g, e, g->unsolvable);
      free(e);
    }
    return;
  }
  if (is_free(g, x)) {
    bind_free(g, x.t, y);
    return;
  }
  if (is_free(g, y)) {
    bind_free(g, y.t, x);
    return;
  }
  if (x.cv >= 0 || y.cv >= 0) {
    match_rt(g, x.cv >= 0 ? x.cv : y.cv, x.cv >= 0 ? y.t : x.t);
    return;
  }
  if (x.t == y.t) return;
  tr_ctx *c = g->c;
  if (tr_term_kind(c, x.t) == TR_APP && tr_term_kind(c, y.t) == TR_APP && tr_term_symbol(c, x.t) == tr_term_symbol(c, y.t)) {
    for (uint32_t i = 0; i < tr_term_arity(c, x.t); i++) unify(g, TM(tr_term_arg(c, x.t, i)), TM(tr_term_arg(c, y.t, i)));
    return;
  }
  clash(g);
}

/* Conditions: the run-time ground term `e` is identical to v under the bindings ("0" when it
 * cannot be: a free local or a fresh name is never a present ground term). */
static char *eq_rt(rg *g, const char *e, val v) {
  tr_ctx *c = g->c;
  v = deref(g, v);
  if (v.cv >= 0) return str("%s == v%d", e, v.cv);
  if (is_const(c, v.t)) return str("%s == %s_K[%zu]", e, g->T->pfx, const_index(g->T, v.t));
  if (tr_term_kind(c, v.t) != TR_APP) return str("0");
  char *out = str("ND(c, %s)->kind == TR_APP && ND(c, %s)->val == %s_S[%zu]", e, e, g->T->pfx,
                  sym_index(g->T, tr_term_symbol(c, v.t)));
  for (uint32_t i = 0; i < tr_term_arity(c, v.t); i++) {
    char *sub = str("ARG(c, %s, %" PRIu32 ")", e, i);
    out = AND(out, eq_rt(g, sub, TM(tr_term_arg(c, v.t, i))));
    free(sub);
  }
  return out;
}

/* x and y identical under the bindings (tcalc_ref.c, same). */
static char *eq_vals(rg *g, val x, val y) {
  tr_ctx *c = g->c;
  x = deref(g, x);
  y = deref(g, y);
  if (x.cv >= 0 || y.cv >= 0) {
    if (x.cv >= 0 && y.cv >= 0) return x.cv == y.cv ? str("1") : str("v%d == v%d", x.cv, y.cv);
    char *e = str("v%d", x.cv >= 0 ? x.cv : y.cv);
    char *out = eq_rt(g, e, x.cv >= 0 ? y : x);
    free(e);
    return out;
  }
  if (x.t == y.t) return str("1");
  if (tr_term_kind(c, x.t) == TR_APP && tr_term_kind(c, y.t) == TR_APP && tr_term_symbol(c, x.t) == tr_term_symbol(c, y.t)) {
    char *out = str("1");
    for (uint32_t i = 0; i < tr_term_arity(c, x.t); i++)
      out = AND(out, eq_vals(g, TM(tr_term_arg(c, x.t, i)), TM(tr_term_arg(c, y.t, i))));
    return out;
  }
  return str("0");
}

/* Matching a present label against a guard pattern with free locals, as statements that
 * `break` out of the enclosing do-while on a mismatch.  Each free class gets a temporary at its
 * first occurrence; classes that occur once in the pattern need none. */
typedef struct {
  uint32_t local;
  int tmp;
} ftmp;

static void count_classes(rg *g, val v, uint32_t *n) {
  v = deref(g, v);
  if (v.cv >= 0) return;
  tr_ctx *c = g->c;
  if (tr_term_kind(c, v.t) == TR_LOCAL) n[tr_term_index(c, v.t)]++;
  else if (tr_term_kind(c, v.t) == TR_APP)
    for (uint32_t i = 0; i < tr_term_arity(c, v.t); i++) count_classes(g, TM(tr_term_arg(c, v.t, i)), n);
}

static void match_stmts(rg *g, const char *e, val v, const uint32_t *n, ftmp *tmps, size_t *ntmps) {
  tr_ctx *c = g->c;
  v = deref(g, v);
  if (v.cv >= 0) {
    sbf(&g->body, "      if (%s != v%d) break;\n", e, v.cv);
    return;
  }
  if (is_const(c, v.t)) {
    sbf(&g->body, "      if (%s != %s_K[%zu]) break;\n", e, g->T->pfx, const_index(g->T, v.t));
    return;
  }
  switch (tr_term_kind(c, v.t)) {
  case TR_LOCAL: {
    uint32_t l = tr_term_index(c, v.t);
    if (n[l] < 2) return;
    for (size_t i = 0; i < *ntmps; i++)
      if (tmps[i].local == l) {
        sbf(&g->body, "      if (%s != g%d) break;\n", e, tmps[i].tmp);
        return;
      }
    int t = g->ntmp++;
    sbf(&g->body, "      tr_term g%d = %s;\n      (void)g%d;\n", t, e, t);
    tmps[(*ntmps)++] = (ftmp){l, t};
    return;
  }
  case TR_APP: {
    sbf(&g->body, "      if (ND(c, %s)->kind != TR_APP || ND(c, %s)->val != %s_S[%zu]) break;\n", e, e, g->T->pfx,
        sym_index(g->T, tr_term_symbol(c, v.t)));
    for (uint32_t i = 0; i < tr_term_arity(c, v.t); i++) {
      val a = deref(g, TM(tr_term_arg(c, v.t, i)));
      if (is_free(g, a) && n[tr_term_index(c, a.t)] < 2) continue;
      int t = g->ntmp++;
      sbf(&g->body, "      tr_term g%d = ARG(c, %s, %" PRIu32 ");\n      (void)g%d;\n", t, e, i, t);
      char *sub = str("g%d", t);
      match_stmts(g, sub, a, n, tmps, ntmps);
      free(sub);
    }
    return;
  }
  default: /* a fresh name is in no present label */
    sbf(&g->body, "      break;\n");
    return;
  }
}

/* Builds the value of v at the result; returns the C expression. */
static char *build(rg *g, val v, bool *swapped) {
  tr_ctx *c = g->c;
  v = deref(g, v);
  if (v.cv >= 0) return str("v%d", v.cv);
  if (is_const(c, v.t)) return str("%s_K[%zu]", g->T->pfx, const_index(g->T, v.t));
  int t = g->ntmp++;
  if (tr_term_kind(c, v.t) == TR_FRESH) {
    sbf(&g->body, "  tr_term t%d = tr_name(c, %s + %" PRIu32 "%s);\n", t, g->fresh_base, tr_term_index(c, v.t),
        FAULT == 9 ? " + 1" : "");
    return str("t%d", t);
  }
  uint32_t n = tr_term_arity(c, v.t); /* an application with a local or fresh name below */
  char **args = xrealloc(NULL, n * sizeof *args);
  for (uint32_t i = 0; i < n; i++) args[i] = build(g, TM(tr_term_arg(c, v.t, i)), swapped);
  if (FAULT == 8 && !*swapped && n >= 2 && strcmp(args[0], args[1])) {
    char *x = args[0];
    args[0] = args[1];
    args[1] = x;
    *swapped = true;
  }
  sbf(&g->body, "  tr_term t%d_a[%" PRIu32 "] = {", t, n);
  for (uint32_t i = 0; i < n; i++) {
    sbf(&g->body, "%s%s", i ? ", " : "", args[i]);
    free(args[i]);
  }
  free(args);
  sbf(&g->body, "};\n  tr_term t%d = tr_app(c, %s_S[%zu], t%d_a);\n", t, g->T->pfx, sym_index(g->T, tr_term_symbol(c, v.t)), t);
  return str("t%d", t);
}

/* A term as the generic instance writes it (tcs_instance_of): parameters given, the other locals
 * renumbered from 0; returns the C expression. */
static char *inst_term(rg *g, tr_term t) {
  tr_ctx *c = g->c;
  switch (tr_term_kind(c, t)) {
  case TR_LOCAL: {
    uint32_t i = tr_term_index(c, t);
    return i < g->r->nparams ? str("p[%" PRIu32 "]", i) : str("tr_local(c, %" PRIu32 ")", i - g->r->nparams);
  }
  case TR_FRESH:
    return str("tr_fresh(c, %" PRIu32 ")", tr_term_index(c, t));
  default:
    break;
  }
  if (is_const(c, t)) return str("%s_K[%zu]", g->T->pfx, const_index(g->T, t));
  uint32_t n = tr_term_arity(c, t); /* an application with a local or a fresh name below */
  char **a = xrealloc(NULL, n * sizeof *a);
  for (uint32_t k = 0; k < n; k++) a[k] = inst_term(g, tr_term_arg(c, t, k));
  int x = g->ntmp++;
  sbf(&g->body, "  tr_term i%d_a[%" PRIu32 "] = {", x, n);
  for (uint32_t k = 0; k < n; k++) sbf(&g->body, "%s%s", k ? ", " : "", a[k]), free(a[k]);
  free(a);
  sbf(&g->body, "};\n  tr_term i%d = tr_app(c, %s_S[%zu], i%d_a);\n", x, g->T->pfx, sym_index(g->T, tr_term_symbol(c, t)), x);
  return str("i%d", x);
}

/* Every term of the rule, for the scans below.  opened: the step opens the term at the target
 * frame (its Shapes check); a host guard's terms are handed to the host as written, not opened. */
static void each_term(const tcs_rule *r, void (*f)(void *, tr_term, bool), void *env) {
  for (size_t i = 0; i < r->ntakes; i++) f(env, r->takes[i], true);
  for (size_t i = 0; i < r->nreads; i++) f(env, r->reads[i], true);
  for (size_t i = 0; i < r->nmakes; i++) f(env, r->makes[i], true);
  for (size_t i = 0; i < r->ntells; i++) f(env, r->tells[i].left, true), f(env, r->tells[i].right, true);
  for (size_t i = 0; i < r->napart; i++) f(env, r->apart[i].left, true), f(env, r->apart[i].right, true);
  for (size_t i = 0; i < r->nguards; i++) {
    bool host = r->guards[i].kind == TCS_HOST;
    f(env, r->guards[i].a, !host);
    if (r->guards[i].kind == TCS_ASK) f(env, r->guards[i].b, true);
  }
}

typedef struct {
  tr_ctx *c;
  uint32_t *uses, *opened, fresh, maxname; /* uses: every occurrence; opened: in opened terms */
  bool var, bad_fresh;
} scan;

static void scan_term(void *env, tr_term t, bool open) {
  scan *sc = env;
  switch (tr_term_kind(sc->c, t)) {
  case TR_LOCAL:
    sc->uses[tr_term_index(sc->c, t)]++;
    sc->opened[tr_term_index(sc->c, t)] += open;
    break;
  case TR_VAR: sc->var = true; break;
  case TR_FRESH: sc->bad_fresh |= open && tr_term_index(sc->c, t) >= sc->fresh; break;
  case TR_NAME:
    if (open && tr_term_index(sc->c, t) + 1 > sc->maxname) sc->maxname = tr_term_index(sc->c, t) + 1;
    break;
  case TR_APP:
    for (uint32_t i = 0; i < tr_term_arity(sc->c, t); i++) scan_term(env, tr_term_arg(sc->c, t, i), open);
    break;
  default: break;
  }
}

static void generic_rule(tg *T, size_t ri, sb *out) {
  sbf(out,
      "static tr_verdict %s_r%zu(tr_state *s, const tr_term *p, const tr_occ *o, tr_result *r, bool commit) {\n"
      "  return %s_generic(%zu, s, p, o, r, commit);\n}\n\n",
      T->pfx, ri, T->pfx, ri);
  T->generic++;
}

/* Writes the function of rule ri; returns whether it is specialized. */
static bool gen_rule(tg *T, size_t ri, const tcs_rule *r, sb *out) {
  tr_ctx *c = T->c;
  uint32_t nl = r->nlocals;
  uint32_t *uses = xrealloc(NULL, (nl + 1) * sizeof *uses), *opened = xrealloc(NULL, (nl + 1) * sizeof *opened);
  memset(uses, 0, (nl + 1) * sizeof *uses);
  memset(opened, 0, (nl + 1) * sizeof *opened);
  scan sc = {c, uses, opened, r->fresh, 0, false, false};
  each_term(r, scan_term, &sc);
  if (sc.var) { /* a frame variable written in a rule: the generic route decides */
    free(uses);
    free(opened);
    generic_rule(T, ri, out);
    return false;
  }
  bool hosts = false;
  for (size_t i = 0; i < r->nguards; i++) hosts |= r->guards[i].kind == TCS_HOST;
  rg g = {T, c, r, ri, {0}, xrealloc(NULL, (nl + 1) * sizeof(bnd)), uses, 0, 0, false,
          FAULT == 11 ? "TR_GUARD" : "TR_UNSOLVABLE", hosts, "s->nnames"};
  for (uint32_t i = 0; i <= nl; i++) g.B[i] = (bnd){B_FREE, -1, TR_NONE};
  const char *P = T->pfx;
  size_t nuse = r->ntakes + r->nreads;
  sb *b = &g.body;
  sbf(b, "/* rule %s */\n", r->name);
  sbf(b, "static tr_verdict %s_r%zu(tr_state *s, const tr_term *p, const tr_occ *o, tr_result *r, bool commit) {\n", P, ri);
  sbf(b, "  tr_ctx *c = s->ctx;\n  tr_result scratch = {0};\n  if (!r) r = &scratch;\n  (void)p;\n  (void)o;\n");
  sbf(b, "  if (c != %s_ctx) {\n    fputs(\"tcs: theory %s is not linked to this context\\n\", stderr);\n    abort();\n  }\n", P, P);
  sbf(b, "  if (!tcs_ground_state(s) || (commit && r->locals)");
  for (uint32_t k = 0; k < r->nparams; k++)
    if (uses[k]) sbf(b, " || !tcs_ground_param(c, p[%" PRIu32 "])", k);
  sbf(b, ")\n    return %s_generic(%zu, s, p, o, r, commit);\n", P, ri);
  sbf(b, "  tcs_count.fast++;\n  r->verdict = TR_REFUSED;\n  r->reason = TR_OK;\n  r->guard = 0;\n");

  /* ---- Shapes ---- */
  if (sc.bad_fresh) refuse_if(&g, "1", "TR_SHAPES");
  if (r->fresh) {
    char *e = str("(uint64_t)s->nnames + %" PRIu32 " > UINT32_MAX", r->fresh);
    refuse_if(&g, e, "TR_SHAPES");
    free(e);
  }
  if (sc.maxname) {
    char *e = str("s->nnames < %" PRIu32, sc.maxname);
    refuse_if(&g, e, "TR_SHAPES");
    free(e);
  }
  for (uint32_t k = 0; k < r->nparams; k++)
    if (opened[k] && FAULT != 4) { /* a parameter in an opened term must be a term of the frame */
      char *e = str("tcs_maxname(c, p[%" PRIu32 "]) > s->nnames", k);
      refuse_if(&g, e, "TR_SHAPES");
      free(e);
    }
  for (size_t i = 0; i < r->ntakes; i++) {
    char *e = str("!o[%zu]", i);
    refuse_if(&g, e, "TR_SHAPES");
    free(e);
    for (size_t j = 0; j < i && FAULT != 3; j++) {
      e = str("o[%zu] == o[%zu]", i, j);
      refuse_if(&g, e, "TR_SHAPES");
      free(e);
    }
  }
  for (uint32_t k = 0; k < r->nparams; k++)
    if (uses[k] && !g.dead) {
      char *init = str("p[%" PRIu32 "]", k);
      g.B[k] = (bnd){B_RT, newcv(&g, init), TR_NONE};
      free(init);
    }
  for (size_t i = 0; i < r->napart; i++) { /* a told disequation must form a frame: not identical */
    char *e = eq_vals(&g, TM(r->apart[i].left), TM(r->apart[i].right));
    refuse_if(&g, e, "TR_SHAPES");
    free(e);
  }

  /* ---- Fits ---- */
  const char *fits = FAULT == 6 ? "TR_SHAPES" : "TR_FITS";
  for (size_t i = 0; i < nuse && !g.dead; i++) {
    sbf(b, "  uint32_t a%zu = find_slot(s, o[%zu]);\n  (void)a%zu;\n", i, i, i);
    char *e = str("a%zu == NIL", i);
    refuse_if(&g, e, fits);
    free(e);
  }
  for (size_t j = r->ntakes; j < nuse && FAULT != 5; j++)
    for (size_t i = 0; i < r->ntakes; i++) {
      char *e = str("o[%zu] == o[%zu]", j, i);
      refuse_if(&g, e, fits);
      free(e);
    }
  /* a stored schema is opened at a scope of its own: the generic route */
  for (size_t i = 0; i < nuse && !g.dead; i++) sbf(b, "  if (s->sl[a%zu].schema) return %s_generic(%zu, s, p, o, r, commit);\n", i, P, ri);

  /* ---- Solvable: the selected labels, the tells, then separation ---- */
  for (size_t i = 0; i < nuse && !g.dead; i++) {
    tr_term pat = i < r->ntakes ? r->takes[i] : r->reads[i - r->ntakes];
    if (wildcard(&g, TM(pat))) continue;
    char *init = str("s->sl[a%zu].label", i);
    int cv = newcv(&g, init);
    free(init);
    unify(&g, RT(cv), TM(pat));
  }
  for (size_t i = 0; i < r->ntells && !g.dead; i++) unify(&g, TM(r->tells[i].left), TM(r->tells[i].right));
  if (!g.dead) {
    bool inside = true;
    for (size_t i = 0; i < r->nmakes; i++) inside &= determined(&g, TM(r->makes[i]));
    for (size_t i = 0; i < r->napart; i++) inside &= determined(&g, TM(r->apart[i].left)) && determined(&g, TM(r->apart[i].right));
    /* a host reads the solutions through a view: the generated code gives it exactly the generic
     * route's bindings only when every local is bound to a ground value */
    for (uint32_t i = r->nparams; hosts && i < nl; i++) inside &= determined(&g, TM(tr_local(c, i)));
    if (!inside) { /* the result would gain frame variables, or a host would see free locals */
      free(g.body.s);
      free(g.B);
      free(uses);
      free(opened);
      generic_rule(T, ri, out);
      return false;
    }
  }
  for (size_t i = 0; i < r->napart && FAULT != 10 && !g.dead; i++) {
    char *e = eq_vals(&g, TM(r->apart[i].left), TM(r->apart[i].right));
    refuse_if(&g, e, g.unsolvable);
    free(e);
  }

  /* fault 7: the takes leave before the guards are decided */
  if (FAULT == 7 && !g.dead)
    for (size_t i = 0; i < r->ntakes; i++) sbf(b, "  remove_occ(s, a%zu);\n", i);

  /* ---- Entails: every guard at every solution ---- */
  if (hosts && !g.dead) sbf(b, "  int undet = 0;\n  (void)undet;\n");
  for (size_t gi = 0; gi < r->nguards && !g.dead; gi++) {
    const tcs_guard *gd = &r->guards[gi];
    if (gd->kind == TCS_HOST) { /* the host, on a view of the bindings (tcalc_ref.c, struct tr_view) */
      uint32_t locals = nl - r->nparams, n = tr_term_arity(c, gd->a);
      size_t h = T->nhosts++;
      sbf(&T->link, "  %s_H[%zu] = tcs_host_find(\"%s\");\n", P, h, tr_symbol_name(c, tr_term_symbol(c, gd->a)));
      sbf(b, "  {\n");
      if (locals) sbf(b, "  ensure_env(s, %" PRIu32 ");\n", locals);
      for (uint32_t i = 0; i < locals; i++) {
        bool sw = false;
        char *e = build(&g, TM(tr_local(c, r->nparams + i)), &sw);
        sbf(b, "  s->env[%" PRIu32 "] = %s;\n", i, e);
        free(e);
      }
      char **args = xrealloc(NULL, (n + 1) * sizeof *args);
      for (uint32_t k = 0; k < n; k++) args[k] = inst_term(&g, tr_term_arg(c, gd->a, k));
      sbf(b, "  tr_term ha%zu[%" PRIu32 "] = {", gi, n ? n : 1);
      for (uint32_t k = 0; k < n; k++) sbf(b, "%s%s", k ? ", " : "", args[k]), free(args[k]);
      free(args);
      sbf(b, "%s};\n", n ? "" : "0");
      sbf(b, "  tr_view hv = {s, (opening){%" PRIu32 ", s->nnames, %" PRIu32 ", 0}, %" PRIu32 "};\n", locals, r->fresh, locals);
      sbf(b, "  int e = %s_H[%zu] ? %s_H[%zu](&hv, ha%zu, %" PRIu32 ") : -1;\n", P, h, P, h, gi, n);
      for (uint32_t i = 0; i < locals; i++) sbf(b, "  s->env[%" PRIu32 "] = TR_NONE;\n", i);
      sbf(b, "  if (e == 0) return tcs_refuse(r, TR_GUARD, %zu);\n  undet |= %s;\n  }\n", gi, FAULT == 13 ? "0" : "e < 0");
      continue;
    }
    if (gd->kind == TCS_ASK) {
      char *e = eq_vals(&g, TM(gd->a), TM(gd->b)), *ne = str("!(%s)", e);
      if (is0(e)) sbf(b, "  return tcs_refuse(r, TR_GUARD, %zu);\n", gi), g.dead = true;
      else if (!is1(e)) sbf(b, "  if (%s) return tcs_refuse(r, TR_GUARD, %zu);\n", ne, gi);
      free(e);
      free(ne);
      continue;
    }
    size_t number = gd->kind == TCS_COUNT ? gd->number : 0;
    val pv = deref(&g, TM(gd->a));
    bool open = !determined(&g, pv);
    char *loop = NULL;
    if (pv.cv >= 0) loop = str("tcs_bucket_first(s, head_key(s, v%d)); i != NIL; i = s->sl[i].hnext", pv.cv);
    else if (is_const(c, pv.t))
      loop = str("tcs_bucket_first(s, head_key(s, %s_K[%zu])); i != NIL; i = s->sl[i].hnext", P, const_index(T, pv.t));
    else if (tr_term_kind(c, pv.t) == TR_APP)
      loop = str("tcs_bucket_first(s, tcs_app_key(%s_S[%zu])); i != NIL; i = s->sl[i].hnext", P,
                 sym_index(T, tr_term_symbol(c, pv.t)));
    else if (tr_term_kind(c, pv.t) == TR_LOCAL) loop = str("s->first; i != NIL; i = s->sl[i].next");
    /* else a fresh name: no present label has it as head */
    if (!open) {
      sbf(b, "  {\n    size_t n = 0;\n");
      if (loop) {
        char *e = FAULT == 12 ? str("1") : eq_rt(&g, "l", pv);
        sbf(b, "    for (uint32_t i = %s) {\n      if (s->sl[i].schema) return %s_generic(%zu, s, p, o, r, commit);\n", loop, P, ri);
        sbf(b, "      tr_term l = s->sl[i].label;\n      (void)l;\n");
        if (!is0(e)) sbf(b, "      if (%s) n++;\n", e);
        sbf(b, "    }\n");
        free(e);
      }
      sbf(b, "    if (n != %zu) return tcs_refuse(r, TR_GUARD, %zu);\n  }\n", number, gi);
    } else {
      uint32_t *n = xrealloc(NULL, (nl + 1) * sizeof *n);
      memset(n, 0, (nl + 1) * sizeof *n);
      count_classes(&g, pv, n);
      ftmp *tmps = xrealloc(NULL, (nl + 1) * sizeof *tmps);
      size_t ntmps = 0;
      sbf(b, "  for (uint32_t i = %s) {\n    if (s->sl[i].schema) return %s_generic(%zu, s, p, o, r, commit);\n", loop, P, ri);
      sbf(b, "    tr_term l = s->sl[i].label;\n    (void)l;\n    do {\n");
      match_stmts(&g, "l", pv, n, tmps, &ntmps);
      if (FAULT != 2) sbf(b, "      return tcs_refuse(r, TR_GUARD, %zu); /* possible: equal at some solution */\n", gi);
      sbf(b, "    } while (0);\n  }\n");
      if (number) sbf(b, "  return tcs_refuse(r, TR_GUARD, %zu);\n", gi), g.dead = true;
      free(n);
      free(tmps);
    }
    free(loop);
  }

  /* ---- the result ---- */
  if (!g.dead) {
    if (hosts) sbf(b, "  if (undet) {\n    r->verdict = TR_NO_VERDICT;\n    return TR_NO_VERDICT;\n  }\n");
    sbf(b, "  r->verdict = TR_ADMITTED;\n  r->first_name = s->nnames;\n  if (!commit) return TR_ADMITTED;\n");
    sbf(b, "  uint32_t first = s->nnames;\n  (void)first;\n");
    g.fresh_base = "first";
    bool swapped = false;
    for (size_t i = 0; i < r->nmakes; i++) {
      char *e = build(&g, TM(r->makes[i]), &swapped);
      sbf(b, "  tr_term m%zu = %s;\n", i, e);
      free(e);
    }
    if (r->fresh) sbf(b, "  s->nnames += %" PRIu32 ";\n", r->fresh);
    if (FAULT != 7)
      for (size_t i = 0; i < r->ntakes; i++) sbf(b, "  remove_occ(s, a%zu);\n", i);
    for (size_t i = 0; i < r->nmakes; i++)
      sbf(b, "  {\n    tr_occ id = s->next_id++;\n    add_occ(s, id, m%zu, 0);\n    if (r->made) r->made[%zu] = id;\n  }\n", i, i);
    sbf(b, "  return TR_ADMITTED;\n");
  }
  sbf(b, "}\n\n");
  sbf(out, "%s", g.body.s);
  free(g.body.s);
  free(g.B);
  free(uses);
  free(opened);
  T->specialized++;
  return true;
}

/* ---- files ---- */

static char *slurp(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) return NULL;
  sb b = {0};
  char buf[65536];
  size_t n;
  while ((n = fread(buf, 1, sizeof buf, f)) > 0) {
    if (b.n + n + 1 > b.cap) {
      b.cap = 2 * (b.n + n + 1);
      b.s = xrealloc(b.s, b.cap);
    }
    memcpy(b.s + b.n, buf, n);
    b.n += n;
  }
  fclose(f);
  if (!b.s) b.s = xrealloc(NULL, 1);
  b.s[b.n] = 0;
  return b.s;
}

static void c_string(FILE *out, const char *s) {
  fputs("\"", out);
  for (; *s; s++) {
    if (*s == '\n') fputs("\\n\"\n  \"", out);
    else if (*s == '"' || *s == '\\') fprintf(out, "\\%c", *s);
    else if ((unsigned char)*s < 32) fprintf(out, "\\%03o", (unsigned char)*s);
    else fputc(*s, out);
  }
  fputs("\"", out);
}

int main(int argc, char **argv) {
  int a = 1;
  if (a + 1 < argc && !strcmp(argv[a], "--fault")) {
    FAULT = atoi(argv[a + 1]);
    a += 2;
  }
  if (argc - a < 2) {
    fprintf(stderr, "usage: %s [--fault N] OUT.c THEORY.tcs ...\n", argv[0]);
    return 2;
  }
  FILE *out = fopen(argv[a], "w");
  if (!out) {
    perror(argv[a]);
    return 2;
  }
  fprintf(out, "/* Generated by tcs_gen%s from", FAULT ? " WITH A PLANTED FAULT" : "");
  for (int i = a + 1; i < argc; i++) fprintf(out, " %s", argv[i]);
  fprintf(out, ".  Do not edit. */\n#include \"tcs_inside.h\"\n\ntcs_counts tcs_count;\n"
               "size_t tcs_head_keys_differ(tr_ctx *c) { return tcs_inside_selfcheck(c); }\n\n");
  sb table = {0};
  size_t ntheories = 0, nrules = 0, nspec = 0;
  for (int fi = a + 1; fi < argc; fi++) {
    char *text = slurp(argv[fi]);
    if (!text) {
      perror(argv[fi]);
      return 2;
    }
    tr_ctx *c = tr_ctx_new();
    tcs_theory *th;
    char err[256];
    int n = tcs_read(c, text, &th, err, sizeof err);
    if (n < 0) {
      fprintf(stderr, "%s: %s\n", argv[fi], err);
      return 2;
    }
    fprintf(out, "static const char tcs_text%d[] =\n  ", fi);
    c_string(out, text);
    fprintf(out, ";\n\n");
    for (int ti = 0; ti < n; ti++) {
      tg T = {.c = c, .index = (size_t)ti};
      T.pfx = str("tcs%zu", ntheories);
      sb rules = {0};
      bool *spec = xrealloc(NULL, (th[ti].nrules + 1) * sizeof *spec);
      for (size_t ri = 0; ri < th[ti].nrules; ri++) spec[ri] = gen_rule(&T, ri, &th[ti].rules[ri], &rules);
      const char *P = T.pfx;
      fprintf(out, "/* ==== theory %s ==== */\n", th[ti].name);
      fprintf(out, "static uint32_t %s_S[%zu];\nstatic tr_term %s_K[%zu];\nstatic tcs_host_fn %s_H[%zu];\n", P, T.nsyms + 1, P,
              T.nconsts + 1, P, T.nhosts + 1);
      fprintf(out, "static tr_ctx *%s_ctx;\nstatic tcs_theory *%s_th;\nstatic int %s_nth;\nstatic tcs_instance %s_inst;\n", P, P, P, P);
      fprintf(out, "static const tcs_theory *%s_schemas(void) { return %s_th ? &%s_th[%d] : NULL; }\n", P, P, P, ti);
      fprintf(out,
              "static tr_verdict %s_generic(size_t rule, tr_state *s, const tr_term *p, const tr_occ *o, tr_result *r, bool commit) {\n"
              "  if (s->ctx != %s_ctx) {\n    fputs(\"tcs: theory %s is not linked to this context\\n\", stderr);\n    abort();\n  }\n"
              "  tcs_count.generic++;\n"
              "  const tr_firing *f = tcs_instance_of(&%s_inst, s->ctx, &%s_th[%d].rules[rule], p, o);\n"
              "  return commit ? tr_fire(s, f, r) : tr_admits(s, f, r);\n}\n\n",
              P, P, P, P, P, ti);
      fputs(rules.s ? rules.s : "", out);
      fprintf(out, "static bool %s_link(tr_ctx *c) {\n  char err[256];\n  if (%s_th) tcs_free(%s_th, %s_nth);\n", P, P, P, P);
      fprintf(out, "  %s_th = NULL;\n  %s_nth = tcs_read(c, tcs_text%d, &%s_th, err, sizeof err);\n", P, P, fi, P);
      fprintf(out, "  if (%s_nth <= %d) {\n    fprintf(stderr, \"tcs: theory %s: %%s\\n\", err);\n    return false;\n  }\n", P, ti, th[ti].name);
      fprintf(out, "  %s_ctx = c;\n  (void)%s_S;\n  (void)%s_K;\n  (void)%s_H;\n%s  return true;\n}\n", P, P, P, P,
              T.link.s ? T.link.s : "");
      fprintf(out, "static const tcs_compiled_rule %s_rules[] = {\n", P);
      for (size_t ri = 0; ri < th[ti].nrules; ri++) {
        const tcs_rule *r = &th[ti].rules[ri];
        fprintf(out, "  {\"%s\", %s_r%zu, %s, %" PRIu32 ", %zu, %zu},\n", r->name, P, ri, spec[ri] ? "true" : "false", r->nparams,
                r->ntakes, r->nreads);
      }
      if (!th[ti].nrules) fprintf(out, "  {\"\", NULL, false, 0, 0, 0},\n");
      fprintf(out, "};\n\n");
      sbf(&table, "  {\"%s\", %s_link, %s_schemas, %zu, %s_rules},\n", th[ti].name, P, P, th[ti].nrules, P);
      ntheories++;
      nrules += th[ti].nrules;
      nspec += T.specialized;
      free(spec);
      free(rules.s);
      free(T.link.s);
      free(T.symidx);
      free(T.constidx);
      free(T.pfx);
    }
    tcs_free(th, n);
    tr_ctx_free(c);
    free(text);
  }
  fprintf(out, "const tcs_compiled_theory tcs_compiled[] = {\n%s};\nconst size_t tcs_ncompiled = %zu;\n", table.s ? table.s : "",
          ntheories);
  free(table.s);
  fclose(out);
  fprintf(stderr, "tcs_gen: %zu theories, %zu rules, %zu specialized, %zu by the generic route%s\n", ntheories, nrules, nspec,
          nrules - nspec, FAULT ? " (planted fault)" : "");
  return 0;
}
