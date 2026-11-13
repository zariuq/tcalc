/* mm0_ref.c: Metamath Zero proof files (.mmu) checked as firings of tcalc_ref's step.
 *
 *   usage: mm0_ref FILE.mmu        (the proof file alone: a .mm0 specification is not read)
 *
 * Every inference is one firing, and every fact the checker relies on was made by an admitted
 * firing.  The facts:
 *   sort(s) pure(s) strict(s) provable(s) free(s)   a sort and its modifiers
 *   term.NAME assert.NAME                            a declared term or assertion (a head each)
 *   bv(x, s, b)     x is a bound variable of sort s; b is its bit
 *   wf(e, s, v)     e is well formed of sort s; v is the set of bound variables in it, Vars(e)
 *   dwf(e, s, v)    the same inside a definition, with v = FV(e) (binders bind)
 *   pf(e)           |- e
 *   cv(l, r, s)     l and r are definitionally equal expressions of sort s
 * Sorts, terms and assertions are codes of their names; the variables of each statement are
 * names the step mints for it; bit sets are codes.
 *
 * The rules, built as data from the declarations (tcalc_ref decides every firing):
 *   decl_sort, decl_term, decl_def, decl_axiom, qed   no duplicate; no term in a pure sort; no
 *                    bound variable in a strict sort; a definition's FV within its declared
 *                    dependencies; a theorem's proof proves exactly its statement
 *   ctx              a statement's variables: minted, sorts declared, bound ones not strict,
 *                    dummies neither strict nor free
 *   wf_f, dwf_f      one per term: argument sorts, bound arguments are bound variables, and the bit
 *                    set the reader proposes is the one Vars (FV) gives (a host guard)
 *   assume, goal     a hypothesis or conclusion is a well formed expression of a provable sort
 *   apply_A          one per axiom or theorem: the substitution's sorts, bound binders get bound
 *                    variables, the disjoint-variable conditions (a host guard, as mm0-c checks
 *                    them), the hypotheses proved; it makes the conclusion
 *   refl, cong_f, sym, unfold_t, conv   conversions; unfold_t substitutes into the definition's
 *                    body by unification and keeps its dummies disjoint (a host guard)
 *   retire           a statement's facts are taken at its end
 * The C part is the reader (characters, identifiers, parentheses, sort modifiers in order, names,
 * arities and argument counts, dependency lists, the bound-variable budget), the order (which
 * firing next; a memo of facts already made, by term), and installing a declaration's rules once
 * its declaration firing is admitted (the statement's names abstracted to the rule's locals).
 */
#include "../tcalc_ref.h"

#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <sys/resource.h>
#include <time.h>

static void *xrealloc(void *p, size_t n) {
  void *q = realloc(p, n ? n : 1);
  if (!q) {
    fputs("mm0_ref: out of memory\n", stderr);
    exit(2);
  }
  return q;
}
#define GROW(arr, len, cap)                                   \
  do {                                                        \
    if ((len) >= (cap)) {                                     \
      (cap) = (cap) ? 2 * (cap) : 16;                         \
      (arr) = xrealloc((arr), (size_t)(cap) * sizeof *(arr)); \
    }                                                         \
  } while (0)

static const char *where = "the start";
static const char *who = "reader"; /* "step" while a firing's refusal is reported */
static void die(const char *fmt, ...) {
  va_list ap;
  fprintf(stderr, "FAIL (%s) at %s: ", who, where);
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}

/* The readers recurse on nesting.  They run on a thread with a large stack (main), and every
 * recursive entry checks the room left: past it the answer is "no verdict" (exit 2), a resource
 * limit, never a refusal and never a crash. */
#define STACK_SIZE ((size_t)1 << 30)
static char *stack_base;
static size_t stack_room;
static void deep(void) {
  char here;
  size_t used = stack_base > &here ? (size_t)(stack_base - &here) : (size_t)(&here - stack_base);
  if (stack_base && used > stack_room) {
    fprintf(stderr, "NO VERDICT at %s: nesting too deep for this reader's stack\n", where);
    exit(2);
  }
}

/* ============================================================================================
 * The reader: s-expressions over [0-9a-zA-Z_:]+ and parentheses; whitespace is space and
 * newline; comments run from -- to the end of the line; any other character is refused.
 * ========================================================================================== */

typedef struct {
  int atom; /* >= 0: a name; -1: a list */
  int kid, next;
} sx;
static sx *X;
static int nx, capx;

typedef struct {
  char *s;
  int sort, term, assert; /* index + 1 */
  int var;                /* index + 1 among the variables of the statement being read */
  tr_occ hyp;             /* a proof fact named in the theorem being read */
  /* the specification (.mm0): its terms and variables, and a math token's notation */
  int sterm, svar;          /* index + 1 */
  int nkind, nterm, nprec, nidx;
} name;
static name *N;
static int nn, capn;
static int *ntab;
static size_t capntab;

static uint64_t hash(const char *s, size_t n) {
  uint64_t h = 1469598103934665603ULL;
  for (size_t i = 0; i < n; i++) h = (h ^ (unsigned char)s[i]) * 1099511628211ULL;
  return h;
}
static int intern(const char *s, size_t n) {
  if (2 * ((size_t)nn + 1) > capntab) {
    size_t cap = capntab ? 2 * capntab : 4096;
    int *t = xrealloc(NULL, cap * sizeof *t);
    for (size_t i = 0; i < cap; i++) t[i] = -1;
    for (int i = 0; i < nn; i++) {
      size_t j = (size_t)hash(N[i].s, strlen(N[i].s)) & (cap - 1);
      while (t[j] >= 0) j = (j + 1) & (cap - 1);
      t[j] = i;
    }
    free(ntab);
    ntab = t;
    capntab = cap;
  }
  size_t j = (size_t)hash(s, n) & (capntab - 1);
  for (; ntab[j] >= 0; j = (j + 1) & (capntab - 1))
    if (strlen(N[ntab[j]].s) == n && !memcmp(N[ntab[j]].s, s, n)) return ntab[j];
  GROW(N, nn, capn);
  memset(&N[nn], 0, sizeof N[nn]);
  N[nn].s = xrealloc(NULL, n + 1);
  memcpy(N[nn].s, s, n);
  N[nn].s[n] = 0;
  ntab[j] = nn;
  return nn++;
}

static const char *src;
static size_t pos, len;

static bool tokchar(char c) {
  return c == '_' || c == ':' || (c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
}
static void skip(void) {
  for (;;) {
    while (pos < len && (src[pos] == ' ' || src[pos] == '\n')) pos++;
    if (pos + 1 < len && src[pos] == '-' && src[pos + 1] == '-') {
      while (pos < len && src[pos] != '\n') pos++;
      continue;
    }
    return;
  }
}
static int mk(int atom) {
  GROW(X, nx, capx);
  X[nx] = (sx){atom, -1, -1};
  return nx++;
}
/* One s-expression; -1 at the end of the file. */
static int parse(void) {
  deep();
  skip();
  if (pos >= len) return -1;
  if (src[pos] == '(') {
    pos++;
    int l = mk(-1), last = -1;
    for (;;) {
      skip();
      if (pos >= len) die("unexpected end of file");
      if (src[pos] == ')') {
        pos++;
        return l;
      }
      int c = parse();
      if (last < 0) X[l].kid = c;
      else X[last].next = c;
      last = c;
    }
  }
  size_t s = pos;
  while (pos < len && tokchar(src[pos])) pos++;
  if (pos == s) die("character %u is not allowed (byte %zu)", (unsigned char)src[pos], pos);
  return mk(intern(src + s, pos - s));
}

static bool atom(int x) { return x >= 0 && X[x].atom >= 0; }
static bool list(int x) { return x >= 0 && X[x].atom < 0; }
static int nth(int l, int n) {
  if (!list(l)) return -1;
  int c = X[l].kid;
  while (c >= 0 && n--) c = X[c].next;
  return c;
}
static int count(int l) {
  int n = 0;
  for (int c = list(l) ? X[l].kid : -1; c >= 0; c = X[c].next) n++;
  return n;
}
static bool is(int x, const char *s) { return atom(x) && !strcmp(N[X[x].atom].s, s); }
static const char *str(int x) { return atom(x) ? N[X[x].atom].s : "(...)"; }
/* An identifier: [a-zA-Z_][a-zA-Z0-9_]*, not "_". */
static bool ident(int x) {
  if (!atom(x)) return false;
  const char *s = N[X[x].atom].s;
  if ((s[0] >= '0' && s[0] <= '9') || !strcmp(s, "_")) return false;
  return !strchr(s, ':');
}

/* ============================================================================================
 * The step: one context, one state.  A rule is a firing with holes: its reads select the
 * occurrences the caller gives, and its told locals are bound to the values the caller gives.
 * ========================================================================================== */

static tr_ctx *C;
static tr_state *S;
static uint32_t f_sort, f_pure, f_strict, f_provable, f_free, f_bv, f_wf, f_dwf, f_pf, f_cv;
static long firings;

/* MM0_REF_LIE makes the reader propose something false, to show the step refuses it:
 *   1 every term's bit set is empty     2 every hypothesis is proved by the first one given
 *   3 every statement's sort is said provable by the first provable sort's fact */
static int LIE;

/* A declared term or assertion is a fact with a head of its own (term.NAME, assert.NAME), so the
 * head index answers "already declared?" in O(1): an absence of a ground fact reads one head
 * bucket, and a bucket shared by every declaration would make the declarations quadratic. */
static tr_term named_fact(const char *kind, int id) {
  size_t a = strlen(kind), b = strlen(N[id].s);
  char *s = xrealloc(NULL, a + b + 2);
  memcpy(s, kind, a);
  s[a] = '.';
  memcpy(s + a + 1, N[id].s, b + 1);
  tr_term t = tr_const(C, s);
  free(s);
  return t;
}

typedef struct {
  const char *what;
  uint32_t locals, fresh;
  tr_term *reads;
  size_t nreads;
  tr_term *makes;
  size_t nmakes;
  uint32_t *told;
  size_t ntold;
  tr_guard *guards;
  size_t nguards;
} rule;

static tr_term L(uint32_t i) { return tr_local(C, i); }
static tr_term K(uint64_t v) { return tr_code(C, (int64_t)v); }
static tr_term A1(uint32_t f, tr_term a) { return tr_app(C, f, &a); }
static tr_term A3(uint32_t f, tr_term a, tr_term b, tr_term c) {
  tr_term x[3] = {a, b, c};
  return tr_app(C, f, x);
}

/* The facts of the statement being read, retired at its end. */
static tr_occ *ctxocc;
static size_t nctx, capctx;
static bool in_ctx;

static const char *reason_text(tr_reason r) {
  switch (r) {
  case TR_SHAPES: return "shapes";
  case TR_FITS: return "a selected fact is not present";
  case TR_UNSOLVABLE: return "the selected facts do not unify with the rule";
  case TR_GUARD: return "a guard fails";
  default: return "no verdict";
  }
}

/* Fires rule r on occurrences occs and values vals.  made: room for r->nmakes, or NULL.
 * Returns the first occurrence made (1 when the rule makes nothing). */
static tr_occ fire(const rule *r, const tr_occ *occs, const tr_term *vals, tr_occ *made, uint32_t *first_name) {
  static tr_use *uses;
  static tr_eq *tells;
  static tr_make *mks;
  static tr_occ *mbuf;
  static size_t capu, capt, capm;
  if (r->nreads > capu) capu = r->nreads, uses = xrealloc(uses, capu * sizeof *uses);
  if (r->ntold > capt) capt = r->ntold, tells = xrealloc(tells, capt * sizeof *tells);
  if (r->nmakes > capm) {
    capm = r->nmakes;
    mks = xrealloc(mks, capm * sizeof *mks);
    mbuf = xrealloc(mbuf, capm * sizeof *mbuf);
  }
  for (size_t i = 0; i < r->nreads; i++) uses[i] = (tr_use){r->reads[i], occs[i]};
  for (size_t i = 0; i < r->ntold; i++) tells[i] = (tr_eq){L(r->told[i]), vals[i]};
  for (size_t i = 0; i < r->nmakes; i++) mks[i] = (tr_make){r->makes[i], 0, 0};
  tr_firing f = {.locals = r->locals, .fresh = r->fresh, .reads = uses, .nreads = r->nreads, .makes = mks,
                 .nmakes = r->nmakes, .tells = tells, .ntells = r->ntold, .guards = r->guards, .nguards = r->nguards};
  tr_result res = {.made = mbuf};
  firings++;
  tr_verdict v = tr_fire(S, &f, &res);
  if (v != TR_ADMITTED) {
    who = "step";
    if (v == TR_NO_VERDICT) die("%s: no verdict", r->what);
    if (res.reason == TR_GUARD) die("%s refused: its guard %zu fails", r->what, res.guard);
    die("%s refused: %s", r->what, reason_text(res.reason));
  }
  if (first_name) *first_name = res.first_name;
  if (made) memcpy(made, mbuf, r->nmakes * sizeof *made);
  if (in_ctx)
    for (size_t i = 0; i < r->nmakes; i++) {
      GROW(ctxocc, nctx, capctx);
      ctxocc[nctx++] = mbuf[i];
    }
  return r->nmakes ? mbuf[0] : 1;
}

/* A rule under construction. */
typedef struct {
  rule r;
  size_t capr, capm, capt, capg;
} rb;
static void rb_init(rb *b, const char *what, uint32_t locals) {
  memset(b, 0, sizeof *b);
  b->r.what = what;
  b->r.locals = locals;
}
static void rb_read(rb *b, tr_term t) {
  GROW(b->r.reads, b->r.nreads, b->capr);
  b->r.reads[b->r.nreads++] = t;
}
static void rb_make(rb *b, tr_term t) {
  GROW(b->r.makes, b->r.nmakes, b->capm);
  b->r.makes[b->r.nmakes++] = t;
}
static void rb_tell(rb *b, uint32_t local) {
  GROW(b->r.told, b->r.ntold, b->capt);
  b->r.told[b->r.ntold++] = local;
}
static void rb_guard(rb *b, tr_guard g) {
  GROW(b->r.guards, b->r.nguards, b->capg);
  b->r.guards[b->r.nguards++] = g;
}
static void rb_absent(rb *b, tr_term t) { rb_guard(b, (tr_guard){.kind = TR_G_ABSENT, .a = t}); }
static void rule_free(rule *r) {
  free(r->reads);
  free(r->makes);
  free(r->told);
  free(r->guards);
}

/* ---- host guards: bit sets, read at every solution ---- */

static bool code_of(tr_view *v, uint32_t local, uint64_t *out) {
  int64_t x;
  if (!tr_view_code(v, L(local), &x)) return false;
  *out = (uint64_t)x;
  return true;
}

/* Arguments k = 0 .. n-1, bound or regular; bits[k]: the local holding the argument's bit (bound)
 * or its Vars / FV (regular); deps[k]: the bound arguments a regular one depends on (by argument
 * index); retdeps: the bound arguments the result depends on; target: the local of the result. */
typedef struct {
  uint32_t n, target;
  uint32_t *bits;
  bool *bound;
  uint64_t *deps;
  uint64_t retdeps;
  bool def; /* FV (inside a definition) or Vars */
} bitspec;

static uint64_t bits_of(const bitspec *b, const uint64_t *x) {
  uint64_t acc = 0;
  for (uint32_t k = 0; k < b->n; k++) {
    if (b->bound[k]) {
      if (!b->def) acc |= x[k];
      continue;
    }
    uint64_t d = x[k];
    if (b->def)
      for (uint32_t j = 0; j < b->n; j++)
        if (b->bound[j] && (b->deps[k] >> j & 1)) d &= ~x[j];
    acc |= d;
  }
  if (b->def)
    for (uint32_t j = 0; j < b->n; j++)
      if (b->bound[j] && (b->retdeps >> j & 1)) acc |= x[j];
  return acc;
}

/* The bit set of an application is the one Vars (or FV) gives (mm0-c, CMD_PROOF_TERM). */
static int g_bits(tr_view *v, void *env) {
  const bitspec *b = env;
  uint64_t want, x[64];
  if (b->n > 64 || !code_of(v, b->target, &want)) return 0;
  for (uint32_t k = 0; k < b->n; k++)
    if (!code_of(v, b->bits[k], &x[k])) return 0;
  return bits_of(b, x) == want;
}

/* The disjoint-variable conditions of applying an assertion (mm0-c, CMD_PROOF_THM): a bound
 * binder's variable is in no earlier substitution; a regular binder's substitution contains no
 * variable of a bound binder it does not depend on. */
static int g_dv(tr_view *v, void *env) {
  const bitspec *b = env;
  uint64_t x[64];
  if (b->n > 64) return 0;
  for (uint32_t k = 0; k < b->n; k++)
    if (!code_of(v, b->bits[k], &x[k])) return 0;
  for (uint32_t i = 0; i < b->n; i++) {
    if (b->bound[i]) {
      for (uint32_t j = 0; j < i; j++)
        if (x[j] & x[i]) return 0;
    } else
      for (uint32_t j = 0; j < b->n; j++)
        if (b->bound[j] && !(b->deps[i] >> j & 1) && (x[j] & x[i])) return 0;
  }
  return 1;
}

/* Unfolding: each dummy's variable is in no argument and in no earlier dummy (mm0-c, UDummy).
 * bits: the arguments, then the dummies; target: the number of arguments. */
static int g_dummies(tr_view *v, void *env) {
  const bitspec *b = env;
  uint64_t x[128];
  if (b->n > 128) return 0;
  for (uint32_t k = 0; k < b->n; k++)
    if (!code_of(v, b->bits[k], &x[k])) return 0;
  for (uint32_t i = b->target; i < b->n; i++)
    for (uint32_t j = 0; j < i; j++)
      if (x[j] & x[i]) return 0;
  return 1;
}

/* A definition's free variables are among its declared dependencies (mm0-c: "type has
 * unaccounted dependencies"). */
static int g_within(tr_view *v, void *env) {
  const bitspec *b = env;
  uint64_t fv;
  return code_of(v, b->target, &fv) && (fv & ~b->retdeps) == 0;
}

/* ============================================================================================
 * Declarations and their rules.
 * ========================================================================================== */

enum { M_PURE = 1, M_STRICT = 2, M_PROVABLE = 4, M_FREE = 8 };
typedef struct {
  int name;
  tr_occ fact, provable;
} sortinfo;
static sortinfo *SORTS;
static int nsorts, capsorts;
static tr_term SK(int sort) { return K((uint64_t)SORTS[sort].name); }

typedef struct {
  int name; /* a variable's name, or -1 for _ */
  int sort; /* index */
  bool bound;
  uint64_t deps; /* regular: the bound binders it depends on, by binder index */
} binder;

typedef struct {
  int name;
  uint32_t n, nd; /* arguments; dummies of a definition */
  binder *b;      /* the n arguments, then the nd dummies */
  int sort;
  uint64_t retdeps; /* by binder index */
  bool def;
  uint32_t sym;
  rule wf, dwf, cong, unfold;
  bitspec *wfb, *dwfb, *dumb;
} terminfo;
static terminfo *TERMS;
static int nterms, capterms;

typedef struct {
  int name;
  uint32_t n, nh;
  binder *b;
  rule apply;
  bitspec *dv;
} assertinfo;
static assertinfo *ASSERTS;
static int nasserts, capasserts;

static rule R_assume, R_goal, R_refl, R_sym, R_conv;

/* A guard's environment lives as long as its rule, apart from the tables that grow. */
static bitspec *spec_of(const binder *b, uint32_t n, uint32_t first_bits, uint32_t target, uint64_t retdeps, bool def) {
  bitspec *s = xrealloc(NULL, sizeof *s);
  *s = (bitspec){n, target, xrealloc(NULL, (n + 1) * sizeof(uint32_t)), xrealloc(NULL, (n + 1) * sizeof(bool)),
                 xrealloc(NULL, (n + 1) * sizeof(uint64_t)), retdeps, def};
  for (uint32_t k = 0; k < n; k++) s->bits[k] = first_bits + k, s->bound[k] = b[k].bound, s->deps[k] = b[k].deps;
  return s;
}

/* The rules of a term or definition; `body` is over locals (binder k is LOCAL k, dummy i is
 * LOCAL n + i). */
static void install_term(terminfo *t, tr_term body) {
  uint32_t n = t->n, nd = t->nd;
  tr_term *xs = xrealloc(NULL, (n + 1) * sizeof *xs), *rs = xrealloc(NULL, (n + 1) * sizeof *rs);
  for (int def = 0; def < 2; def++) { /* wf_f (Vars) and dwf_f (FV): X_k, C_k, then the bit set */
    rb b;
    rb_init(&b, def ? "a term inside a definition" : "a term", 2 * n + 1);
    for (uint32_t k = 0; k < n; k++) {
      xs[k] = L(k);
      rb_read(&b, A3(t->b[k].bound ? f_bv : def ? f_dwf : f_wf, L(k), SK(t->b[k].sort), L(n + k)));
    }
    rb_make(&b, A3(def ? f_dwf : f_wf, tr_app(C, t->sym, xs), SK(t->sort), L(2 * n)));
    rb_tell(&b, 2 * n);
    bitspec *bs = spec_of(t->b, n, n, 2 * n, t->retdeps, def);
    if (def) t->dwfb = bs;
    else t->wfb = bs;
    rb_guard(&b, (tr_guard){.kind = TR_G_HOST, .entailed = g_bits, .env = bs});
    if (def) t->dwf = b.r;
    else t->wf = b.r;
  }
  { /* cong_f: L_k = R_k; a bound argument is the same bound variable on both sides */
    rb b;
    rb_init(&b, "a congruence", 3 * n);
    for (uint32_t k = 0; k < n; k++) {
      xs[k] = L(k);
      rs[k] = t->b[k].bound ? L(k) : L(n + k);
      rb_read(&b, t->b[k].bound ? A3(f_bv, L(k), SK(t->b[k].sort), L(2 * n + k)) : A3(f_cv, L(k), L(n + k), SK(t->b[k].sort)));
    }
    rb_make(&b, A3(f_cv, tr_app(C, t->sym, xs), tr_app(C, t->sym, rs), SK(t->sort)));
    t->cong = b.r;
  }
  if (t->def) { /* unfold_t: X_k and D_i, their bits, R: t(X) = R when body[X, D] = R */
    rb b;
    uint32_t m = n + nd;
    rb_init(&b, "an unfolding", 2 * m + 1);
    for (uint32_t k = 0; k < m; k++)
      rb_read(&b, A3(k >= n || t->b[k].bound ? f_bv : f_wf, L(k), SK(t->b[k].sort), L(m + k)));
    rb_read(&b, A3(f_cv, body, L(2 * m), SK(t->sort)));
    for (uint32_t k = 0; k < n; k++) xs[k] = L(k);
    rb_make(&b, A3(f_cv, tr_app(C, t->sym, xs), L(2 * m), SK(t->sort)));
    t->dumb = spec_of(t->b, m, m, n, 0, false);
    rb_guard(&b, (tr_guard){.kind = TR_G_HOST, .entailed = g_dummies, .env = t->dumb});
    t->unfold = b.r;
  }
  free(xs);
  free(rs);
}

/* apply_A: E_k and C_k (bit or Vars) per binder, then the hypotheses; makes the conclusion. */
static void install_assert(assertinfo *a, const tr_term *hyps, tr_term concl) {
  uint32_t n = a->n;
  rb b;
  rb_init(&b, N[a->name].s, 2 * n);
  for (uint32_t k = 0; k < n; k++) rb_read(&b, A3(a->b[k].bound ? f_bv : f_wf, L(k), SK(a->b[k].sort), L(n + k)));
  for (uint32_t j = 0; j < a->nh; j++) rb_read(&b, A1(f_pf, hyps[j]));
  rb_make(&b, A1(f_pf, concl));
  a->dv = spec_of(a->b, n, n, 0, 0, false);
  rb_guard(&b, (tr_guard){.kind = TR_G_HOST, .entailed = g_dv, .env = a->dv});
  a->apply = b.r;
}

/* ============================================================================================
 * A statement's variables, its facts, and the memo of facts made, by term.
 * ========================================================================================== */

typedef struct {
  int sort;
  bool bound;
  uint64_t bits; /* bound: its bit; regular: its dependencies */
  tr_term t;
  tr_occ wf, dwf, bv;
} var;
static var *V;
static uint32_t nv, capv, ctx_first;

/* The memo of the statement being read: term -> the occurrence of its wf (dwf) fact.  Entries
 * of earlier statements are stale by their generation, so a new statement clears nothing:
 * O(1) per statement, O(1) expected per lookup. */
typedef struct {
  tr_term key;
  uint32_t gen;
  tr_occ occ;
} memo;
static memo *MEMO[2]; /* wf, dwf */
static size_t capmemo[2], nmemo[2];
static uint32_t memo_gen = 1;

static bool live(const memo *e) { return e->key && e->gen == memo_gen; }
static tr_occ memo_get(int m, tr_term t) {
  if (!capmemo[m]) return 0;
  for (size_t j = (size_t)t * 2654435761u & (capmemo[m] - 1);; j = (j + 1) & (capmemo[m] - 1)) {
    if (!live(&MEMO[m][j])) return 0;
    if (MEMO[m][j].key == t) return MEMO[m][j].occ;
  }
}
static void memo_put(int m, tr_term t, tr_occ o) {
  if (2 * (nmemo[m] + 1) > capmemo[m]) {
    size_t cap = capmemo[m] ? 2 * capmemo[m] : 1024;
    memo *nw = xrealloc(NULL, cap * sizeof *nw);
    memset(nw, 0, cap * sizeof *nw);
    for (size_t i = 0; i < capmemo[m]; i++)
      if (live(&MEMO[m][i])) {
        size_t j = (size_t)MEMO[m][i].key * 2654435761u & (cap - 1);
        while (nw[j].key) j = (j + 1) & (cap - 1);
        nw[j] = MEMO[m][i];
      }
    free(MEMO[m]);
    MEMO[m] = nw;
    capmemo[m] = cap;
  }
  size_t j = (size_t)t * 2654435761u & (capmemo[m] - 1);
  while (live(&MEMO[m][j]) && MEMO[m][j].key != t) j = (j + 1) & (capmemo[m] - 1);
  if (!live(&MEMO[m][j])) nmemo[m]++;
  MEMO[m][j] = (memo){t, memo_gen, o};
}
static void memo_clear(void) {
  if (++memo_gen == 0) { /* the stamps wrapped: clear for real, once in 2^32 statements */
    for (int i = 0; i < 2; i++)
      if (capmemo[i]) memset(MEMO[i], 0, capmemo[i] * sizeof *MEMO[i]);
    memo_gen = 1;
  }
  nmemo[0] = nmemo[1] = 0;
}

static int sort_named(int x) {
  if (!atom(x) || !N[X[x].atom].sort) die("unknown sort %s", str(x));
  return N[X[x].atom].sort - 1;
}

static binder *B;
static uint32_t capb;

/* Reads a binder list into B from index `first`; with `named`, the names become variables of the
 * statement (dependency lists may name only earlier bound variables). */
static uint32_t read_binders(int l, uint32_t first, bool named) {
  if (!list(l)) die("bad binder list");
  uint32_t n = first;
  for (int c = X[l].kid; c >= 0; c = X[c].next, n++) {
    int nm = nth(c, 0), s = nth(c, 1), d = nth(c, 2);
    if (!list(c) || count(c) < 2 || count(c) > 3 || !atom(nm) || (d >= 0 && !list(d))) die("bad binder");
    if (!is(nm, "_") && !ident(nm)) die("bad variable name %s", str(nm));
    if (n >= 128) die("too many binders");
    if (n >= capb) {
      capb = capb ? 2 * capb : 16;
      B = xrealloc(B, capb * sizeof *B);
    }
    binder *b = &B[n];
    *b = (binder){is(nm, "_") ? -1 : X[nm].atom, sort_named(s), d < 0, 0};
    for (int e = d >= 0 ? X[d].kid : -1; e >= 0; e = X[e].next) {
      int k = atom(e) ? N[X[e].atom].var : 0;
      if (!k || k - 1 >= (int)n || !B[k - 1].bound) die("dependency %s is not an earlier bound variable", str(e));
      b->deps |= 1ULL << (k - 1);
    }
    if (named && b->name >= 0) {
      if (N[b->name].var) die("variable %s declared twice", N[b->name].s);
      N[b->name].var = (int)n + 1;
    }
  }
  return n;
}
static void name_binders(uint32_t from, uint32_t to) {
  for (uint32_t k = from; k < to; k++)
    if (B[k].name >= 0) {
      if (N[B[k].name].var) die("variable %s declared twice", N[B[k].name].s);
      N[B[k].name].var = (int)k + 1;
    }
}
static void forget_binders(uint32_t m) {
  for (uint32_t k = 0; k < m; k++)
    if (B[k].name >= 0) N[B[k].name].var = 0;
}

/* The context of a statement with n binders and nd dummies: one firing mints its variables and
 * makes their facts. */
static void open_ctx(uint32_t n, uint32_t nd) {
  uint32_t m = n + nd, nbound = 0;
  for (uint32_t k = 0; k < m; k++) nbound += k >= n || B[k].bound;
  if (nbound > 63) die("too many bound variables");
  nctx = 0;
  memo_clear();
  rb r;
  rb_init(&r, "the statement's variables", 0);
  r.r.fresh = m;
  tr_occ *occs = xrealloc(NULL, (m + 1) * sizeof *occs);
  memset(occs, 0, (m + 1) * sizeof *occs);
  nv = 0;
  uint64_t bitof[128] = {0}, next = 1;
  for (uint32_t k = 0; k < m; k++) {
    bool bound = k >= n || B[k].bound;
    rb_read(&r, A1(f_sort, SK(B[k].sort)));
    occs[k] = SORTS[B[k].sort].fact;
    if (bound) rb_absent(&r, A1(f_strict, SK(B[k].sort)));
    if (k >= n) rb_absent(&r, A1(f_free, SK(B[k].sort)));
    uint64_t bits = 0;
    if (bound) bits = bitof[k] = next, next <<= 1;
    else
      for (uint32_t j = 0; j < k; j++)
        if (B[k].deps >> j & 1) bits |= bitof[j];
    tr_term x = tr_fresh(C, k);
    if (bound) rb_make(&r, A3(f_bv, x, SK(B[k].sort), K(bits)));
    rb_make(&r, A3(f_wf, x, SK(B[k].sort), K(bits)));
    rb_make(&r, A3(f_dwf, x, SK(B[k].sort), K(bits)));
    GROW(V, nv, capv);
    V[nv++] = (var){B[k].sort, bound, bits, TR_NONE, 0, 0, 0};
  }
  tr_occ *made = xrealloc(NULL, (r.r.nmakes + 1) * sizeof *made);
  in_ctx = true;
  fire(&r.r, occs, NULL, made, &ctx_first);
  size_t at = 0;
  for (uint32_t k = 0; k < m; k++) {
    V[k].t = tr_name(C, ctx_first + k);
    if (V[k].bound) V[k].bv = made[at++];
    V[k].wf = made[at++];
    V[k].dwf = made[at++];
    memo_put(0, V[k].t, V[k].wf);
    memo_put(1, V[k].t, V[k].dwf);
  }
  free(made);
  free(occs);
  rule_free(&r.r);
}

/* Retires the statement's facts: one firing takes them all. */
static void close_ctx(void) {
  in_ctx = false;
  if (!nctx) return;
  tr_use *takes = xrealloc(NULL, nctx * sizeof *takes);
  for (size_t i = 0; i < nctx; i++) takes[i] = (tr_use){L((uint32_t)i), ctxocc[i]};
  tr_firing f = {.locals = (uint32_t)nctx, .takes = takes, .ntakes = nctx};
  firings++;
  if (tr_fire(S, &f, NULL) != TR_ADMITTED) die("retiring the statement's facts refused");
  free(takes);
  nctx = 0;
}

/* t with the statement's variables written as locals (variable k is LOCAL k). */
static tr_term abstract(tr_term t) {
  deep();
  switch (tr_term_kind(C, t)) {
  case TR_NAME: {
    uint32_t i = tr_term_index(C, t);
    return i >= ctx_first && i < ctx_first + nv ? L(i - ctx_first) : t;
  }
  case TR_APP: {
    uint32_t n = tr_term_arity(C, t);
    if (!n) return t;
    tr_term small[16], *a = n <= 16 ? small : xrealloc(NULL, n * sizeof *a);
    bool changed = false;
    for (uint32_t i = 0; i < n; i++) {
      tr_term x = tr_term_arg(C, t, i);
      a[i] = abstract(x);
      changed |= a[i] != x;
    }
    tr_term out = changed ? tr_app(C, tr_term_symbol(C, t), a) : t;
    if (a != small) free(a);
    return out;
  }
  default:
    return t;
  }
}

static var *var_named(int x) {
  if (!atom(x) || !N[X[x].atom].var) return NULL;
  return &V[N[X[x].atom].var - 1];
}

/* ---- expressions: the wf (or dwf) fact of an expression, made bottom-up ---- */

typedef struct {
  tr_occ occ;
  tr_term t;
  uint64_t bits;
} fact;

static tr_term label_of(tr_occ o) {
  tr_term l;
  if (!tr_present(S, o, &l)) die("a fact went missing");
  return l;
}
static uint64_t code_arg(tr_occ o, uint32_t i) { return (uint64_t)tr_term_code(C, tr_term_arg(C, label_of(o), i)); }

static fact expr(int x, int def) {
  deep();
  if (atom(x)) {
    var *v = var_named(x);
    if (!v) die("unknown variable %s", str(x));
    return (fact){def ? v->dwf : v->wf, v->t, v->bits};
  }
  int h = nth(x, 0);
  if (!atom(h) || !N[X[h].atom].term) die("unknown term %s", str(h));
  terminfo *t = &TERMS[N[X[h].atom].term - 1];
  if ((uint32_t)count(x) != t->n + 1) die("%s takes %u arguments", N[t->name].s, t->n);
  if (t->n > 64) die("too many arguments");
  tr_occ occs[64];
  tr_term args[64];
  uint64_t bits[64];
  int c = X[h].next;
  for (uint32_t k = 0; k < t->n; k++, c = X[c].next) {
    var *v = t->b[k].bound ? var_named(c) : NULL;
    if (v && v->bound) occs[k] = v->bv, args[k] = v->t, bits[k] = v->bits;
    else {
      fact f = expr(c, def);
      occs[k] = f.occ, args[k] = f.t, bits[k] = f.bits;
    }
  }
  tr_term e = tr_app(C, t->sym, args);
  tr_occ m = memo_get(def, e);
  if (m) return (fact){m, e, code_arg(m, 2)};
  /* the bit set the reader proposes; the rule's guard decides it */
  tr_term val = K(LIE == 1 ? 0 : bits_of(def ? t->dwfb : t->wfb, bits));
  tr_occ o = fire(def ? &t->dwf : &t->wf, occs, &val, NULL, NULL);
  memo_put(def, e, o);
  return (fact){o, e, (uint64_t)tr_term_code(C, val)};
}

static tr_term term_of(int x) {
  deep();
  if (atom(x)) {
    var *v = var_named(x);
    if (!v) die("unknown variable %s", str(x));
    return v->t;
  }
  int h = nth(x, 0);
  if (!atom(h) || !N[X[h].atom].term) die("unknown term %s", str(h));
  terminfo *t = &TERMS[N[X[h].atom].term - 1];
  if ((uint32_t)count(x) != t->n + 1) die("%s takes %u arguments", N[t->name].s, t->n);
  if (t->n > 64) die("too many arguments");
  tr_term args[64];
  int c = X[h].next;
  for (uint32_t k = 0; k < t->n; k++, c = X[c].next) args[k] = term_of(c);
  return tr_app(C, t->sym, args);
}

/* An expression in a bound position: its bv fact when it is a bound variable, otherwise its wf
 * fact, which the rule's bv pattern refuses. */
static tr_occ binder_fact(int x, bool bound) {
  if (bound) {
    var *v = var_named(x);
    if (v && v->bound) return v->bv;
  }
  return expr(x, 0).occ;
}

/* ---- conversions and proofs ---- */

static tr_occ conv(int x) {
  deep();
  if (atom(x)) {
    tr_occ o = expr(x, 0).occ;
    return fire(&R_refl, &o, NULL, NULL, NULL);
  }
  int h = nth(x, 0);
  if (is(h, ":sym")) {
    if (count(x) != 2) die("bad :sym");
    tr_occ o = conv(nth(x, 1));
    return fire(&R_sym, &o, NULL, NULL, NULL);
  }
  if (is(h, ":unfold")) {
    int tn = nth(x, 1), es = nth(x, 2), ds = nth(x, 3), c = nth(x, 4);
    if (count(x) != 5 || !atom(tn) || !N[X[tn].atom].term || !list(es) || !list(ds)) die("bad :unfold");
    terminfo *t = &TERMS[N[X[tn].atom].term - 1];
    if (!t->def) die(":unfold of %s, which is not a definition", N[t->name].s);
    if ((uint32_t)count(es) != t->n || (uint32_t)count(ds) != t->nd)
      die(":unfold of %s: wrong number of arguments or dummies", N[t->name].s);
    tr_occ *occs = xrealloc(NULL, (t->n + t->nd + 2) * sizeof *occs);
    int e = X[es].kid;
    for (uint32_t k = 0; k < t->n; k++, e = X[e].next) occs[k] = binder_fact(e, t->b[k].bound);
    e = X[ds].kid;
    for (uint32_t k = 0; k < t->nd; k++, e = X[e].next) occs[t->n + k] = binder_fact(e, true);
    occs[t->n + t->nd] = conv(c);
    tr_occ o = fire(&t->unfold, occs, NULL, NULL, NULL);
    free(occs);
    return o;
  }
  if (!atom(h) || !N[X[h].atom].term) die("conversion over unknown term %s", str(h));
  terminfo *t = &TERMS[N[X[h].atom].term - 1];
  if ((uint32_t)count(x) != t->n + 1) die("%s takes %u arguments", N[t->name].s, t->n);
  if (t->n > 64) die("too many arguments");
  tr_occ occs[64];
  int c = X[h].next;
  for (uint32_t k = 0; k < t->n; k++, c = X[c].next) occs[k] = t->b[k].bound ? binder_fact(c, true) : conv(c);
  return fire(&t->cong, occs, NULL, NULL, NULL);
}

static tr_occ proof(int x) {
  deep();
  if (atom(x)) {
    tr_occ o = N[X[x].atom].hyp;
    if (!o) die("unknown hypothesis %s", str(x));
    return o;
  }
  int h = nth(x, 0);
  if (is(h, ":let")) {
    int nm = nth(x, 1);
    if (count(x) != 4 || !ident(nm)) die("bad :let");
    if (N[X[nm].atom].hyp) die("subproof name %s shadows another", str(nm));
    tr_occ p = proof(nth(x, 2)), old = N[X[nm].atom].hyp;
    N[X[nm].atom].hyp = p;
    tr_occ out = proof(nth(x, 3));
    N[X[nm].atom].hyp = old;
    return out;
  }
  if (is(h, ":conv")) {
    if (count(x) != 4) die("bad :conv");
    tr_term target = term_of(nth(x, 1));
    tr_occ occs[2] = {proof(nth(x, 3)), conv(nth(x, 2))};
    return fire(&R_conv, occs, &target, NULL, NULL);
  }
  if (!atom(h) || !N[X[h].atom].assert) die("unknown assertion %s", str(h));
  assertinfo *a = &ASSERTS[N[X[h].atom].assert - 1];
  int es = nth(x, 1);
  if (!list(es) || (uint32_t)count(es) != a->n) die("%s takes %u substitutions", N[a->name].s, a->n);
  if ((uint32_t)count(x) != 2 + a->nh) die("%s takes %u hypotheses", N[a->name].s, a->nh);
  tr_occ *occs = xrealloc(NULL, (a->n + a->nh + 1) * sizeof *occs);
  int e = X[es].kid;
  for (uint32_t k = 0; k < a->n; k++, e = X[e].next) occs[k] = binder_fact(e, a->b[k].bound);
  e = X[es].next;
  for (uint32_t j = 0; j < a->nh; j++, e = X[e].next) occs[a->n + j] = LIE == 2 && j ? occs[a->n] : proof(e);
  tr_occ o = fire(&a->apply, occs, NULL, NULL, NULL);
  free(occs);
  return o;
}

#include "mm0_spec.c" /* the specification (.mm0): its reader and the matching, all reader */

/* ============================================================================================
 * Directives.
 * ========================================================================================== */

static long n_sorts, n_terms, n_defs, n_axioms, n_theorems;

/* A hypothesis or conclusion: a well formed expression of a provable sort (rule assume or goal). */
static fact statement(int x, const rule *r) {
  fact f = expr(x, 0);
  int s = N[code_arg(f.occ, 1)].sort - 1;
  tr_occ occs[2] = {f.occ, SORTS[s].provable};
  for (int i = 0; LIE == 3 && i < nsorts; i++)
    if (SORTS[i].provable) {
      occs[1] = SORTS[i].provable;
      break;
    }
  tr_occ made = fire(r, occs, NULL, NULL, NULL);
  return (fact){made, f.t, f.bits};
}

/* Reads the hypotheses (theorem: (name expr) pairs) of an assertion into abstracted terms. */
static uint32_t hypotheses(int hl, bool named, tr_term **out, int **names) {
  if (!list(hl)) die("bad hypothesis list");
  uint32_t nh = (uint32_t)count(hl);
  *out = xrealloc(NULL, (nh + 1) * sizeof **out);
  *names = xrealloc(NULL, (nh + 1) * sizeof **names);
  uint32_t j = 0;
  for (int c = X[hl].kid; c >= 0; c = X[c].next, j++) {
    int e = c;
    (*names)[j] = -1;
    if (named) {
      int hn = nth(c, 0);
      if (!list(c) || count(c) != 2 || !atom(hn) || (!is(hn, "_") && !ident(hn))) die("bad hypothesis");
      e = nth(c, 1);
      if (!is(hn, "_")) {
        if (N[X[hn].atom].hyp) die("hypothesis %s named twice", str(hn));
        (*names)[j] = X[hn].atom;
      }
    }
    fact f = statement(e, named ? &R_assume : &R_goal);
    if ((*names)[j] >= 0) N[(*names)[j]].hyp = f.occ;
    (*out)[j] = abstract(f.t);
  }
  return nh;
}

static void declare_assert(int id, uint32_t n, uint32_t nh, const tr_term *hyps, tr_term concl) {
  GROW(ASSERTS, nasserts, capasserts);
  assertinfo *a = &ASSERTS[nasserts];
  memset(a, 0, sizeof *a);
  a->name = id, a->n = n, a->nh = nh;
  a->b = xrealloc(NULL, (n + 1) * sizeof *a->b);
  if (n) memcpy(a->b, B, n * sizeof *B);
  install_assert(a, hyps, concl);
  N[id].assert = ++nasserts;
}

static void directive(int d) {
  if (!list(d)) die("a directive is a list");
  int k = nth(d, 0), off = 0;
  if (is(k, "local")) {
    k = nth(d, 1), off = 1;
    if (!is(k, "def") && !is(k, "theorem")) die("local only on def or theorem");
  }
  if (is(k, "input") || is(k, "output")) {
    if (count(d) != 2) die("bad %s", str(k));
    return;
  }
  int nm = nth(d, 1 + off);
  where = atom(nm) ? str(nm) : "a directive";
  if (!ident(nm)) die("bad identifier %s", str(nm));
  int id = X[nm].atom;

  if (is(k, "sort")) {
    unsigned mods = 0;
    int last = -1;
    static const char *mod[4] = {"pure", "strict", "provable", "free"};
    for (int c = X[nm].next; c >= 0; c = X[c].next) {
      int m = 0;
      while (m < 4 && !is(c, mod[m])) m++;
      if (m == 4 || m <= last) die("bad sort modifier %s (pure strict provable free, in this order)", str(c));
      last = m, mods |= 1u << m;
    }
    rb r;
    rb_init(&r, "a sort declaration", 0);
    tr_term s = K((uint64_t)id);
    rb_absent(&r, A1(f_sort, s));
    rb_make(&r, A1(f_sort, s));
    uint32_t f[4] = {f_pure, f_strict, f_provable, f_free};
    for (int m = 0; m < 4; m++)
      if (mods >> m & 1) rb_make(&r, A1(f[m], s));
    tr_occ made[5];
    fire(&r.r, NULL, NULL, made, NULL);
    rule_free(&r.r);
    GROW(SORTS, nsorts, capsorts);
    SORTS[nsorts] = (sortinfo){id, made[0], 0};
    if (mods & M_PROVABLE) SORTS[nsorts].provable = made[1 + !!(mods & M_PURE) + !!(mods & M_STRICT)];
    N[id].sort = ++nsorts;
    spec_sort(id, mods);
    n_sorts++;
    return;
  }

  if (is(k, "term") || is(k, "def")) {
    bool def = is(k, "def");
    if (count(d) != (def ? 6 : 4) + off) die("bad %s", str(k));
    uint32_t n = read_binders(nth(d, 2 + off), 0, true);
    int ret = nth(d, 3 + off);
    if (!list(ret) || count(ret) != 2 || !list(nth(ret, 1))) die("bad return type");
    int rs = sort_named(nth(ret, 0));
    uint64_t retdeps = 0;
    for (int e = X[nth(ret, 1)].kid; e >= 0; e = X[e].next) {
      int j = atom(e) ? N[X[e].atom].var : 0;
      if (!j || !B[j - 1].bound) die("return dependency %s is not a bound variable", str(e));
      retdeps |= 1ULL << (j - 1);
    }
    uint32_t m = def ? read_binders(nth(d, 4 + off), n, true) : n;
    for (uint32_t i = n; i < m; i++) B[i].bound = true;
    if (n > 64) die("too many arguments");
    rb r;
    rb_init(&r, def ? "the definition" : "the term declaration", 2);
    tr_occ occs[130];
    size_t no = 0;
    for (uint32_t i = 0; i < n; i++) {
      rb_read(&r, A1(f_sort, SK(B[i].sort)));
      occs[no++] = SORTS[B[i].sort].fact;
      if (B[i].bound) rb_absent(&r, A1(f_strict, SK(B[i].sort)));
    }
    rb_read(&r, A1(f_sort, SK(rs)));
    occs[no++] = SORTS[rs].fact;
    rb_absent(&r, named_fact("term", id));
    rb_absent(&r, A1(f_pure, SK(rs)));
    tr_term body = TR_NONE;
    bitspec within = {0};
    if (def) { /* the body, in the definition's own context, with FV */
      open_ctx(n, m - n);
      fact f = expr(nth(d, 5 + off), 1);
      uint64_t mask = 0;
      for (uint32_t j = 0; j < n; j++)
        if (retdeps >> j & 1) mask |= V[j].bits;
      rb_read(&r, A3(f_dwf, L(1), SK(rs), L(0))); /* the body is of the return sort */
      occs[no++] = f.occ;
      within = (bitspec){.target = 0, .retdeps = mask};
      rb_guard(&r, (tr_guard){.kind = TR_G_HOST, .entailed = g_within, .env = &within});
      body = abstract(f.t);
    }
    rb_make(&r, named_fact("term", id));
    in_ctx = false;
    fire(&r.r, occs, NULL, NULL, NULL);
    in_ctx = def;
    rule_free(&r.r);
    if (def) close_ctx();
    GROW(TERMS, nterms, capterms);
    terminfo *t = &TERMS[nterms];
    memset(t, 0, sizeof *t);
    t->name = id, t->n = n, t->nd = m - n, t->sort = rs, t->retdeps = retdeps, t->def = def;
    t->b = xrealloc(NULL, (m + 1) * sizeof *t->b);
    if (m) memcpy(t->b, B, m * sizeof *B);
    char *sn = xrealloc(NULL, strlen(N[id].s) + 3); /* "t." + name: never a fact's symbol */
    memcpy(sn, "t.", 2);
    strcpy(sn + 2, N[id].s);
    t->sym = tr_symbol(C, sn, n);
    free(sn);
    if (!off) spec_term(id, def, n, m - n, B, rs, retdeps, body);
    install_term(t, body);
    forget_binders(m);
    N[id].term = ++nterms;
    if (def) n_defs++;
    else n_terms++;
    return;
  }

  if (is(k, "axiom")) {
    if (count(d) != 5) die("bad axiom");
    uint32_t n = read_binders(nth(d, 2), 0, true);
    open_ctx(n, 0);
    tr_term *hyps;
    int *hn;
    uint32_t nh = hypotheses(nth(d, 3), false, &hyps, &hn);
    fact c = statement(nth(d, 4), &R_goal);
    tr_term concl = abstract(c.t);
    rb r;
    rb_init(&r, "the axiom declaration", 0);
    rb_absent(&r, named_fact("assert", id));
    rb_make(&r, named_fact("assert", id));
    in_ctx = false;
    fire(&r.r, NULL, NULL, NULL, NULL);
    in_ctx = true;
    rule_free(&r.r);
    close_ctx();
    spec_assert(id, false, n, B, nh, hyps, concl);
    declare_assert(id, n, nh, hyps, concl);
    forget_binders(n);
    free(hyps);
    free(hn);
    n_axioms++;
    return;
  }

  if (is(k, "theorem")) {
    if (count(d) != 7 + off) die("bad theorem");
    uint32_t n = read_binders(nth(d, 2 + off), 0, true);
    uint32_t m = read_binders(nth(d, 5 + off), n, false); /* dummies: named after the statement */
    for (uint32_t i = n; i < m; i++) B[i].bound = true;
    open_ctx(n, m - n);
    tr_term *hyps;
    int *hn;
    uint32_t nh = hypotheses(nth(d, 3 + off), true, &hyps, &hn);
    fact c = statement(nth(d, 4 + off), &R_goal);
    tr_term concl = abstract(c.t);
    name_binders(n, m);
    tr_occ root = proof(nth(d, 6 + off));
    rb r; /* qed: the proof proves exactly the statement */
    rb_init(&r, "the theorem's conclusion", 1);
    rb_tell(&r, 0);
    rb_read(&r, A1(f_pf, L(0)));
    rb_absent(&r, named_fact("assert", id));
    rb_make(&r, named_fact("assert", id));
    in_ctx = false;
    fire(&r.r, &root, &c.t, NULL, NULL);
    in_ctx = true;
    rule_free(&r.r);
    for (uint32_t j = 0; j < nh; j++)
      if (hn[j] >= 0) N[hn[j]].hyp = 0;
    close_ctx();
    if (!off) spec_assert(id, true, n, B, nh, hyps, concl);
    declare_assert(id, n, nh, hyps, concl);
    forget_binders(m);
    free(hyps);
    free(hn);
    n_theorems++;
    return;
  }
  die("unknown directive %s", str(k));
}

/* ============================================================================================ */

static void generic_rules(void) {
  rb b;
  rb_init(&b, "a hypothesis of a provable sort", 3);
  rb_read(&b, A3(f_wf, L(0), L(1), L(2)));
  rb_read(&b, A1(f_provable, L(1)));
  rb_make(&b, A1(f_pf, L(0)));
  R_assume = b.r;
  rb_init(&b, "a statement of a provable sort", 3);
  rb_read(&b, A3(f_wf, L(0), L(1), L(2)));
  rb_read(&b, A1(f_provable, L(1)));
  R_goal = b.r;
  rb_init(&b, "a reflexivity", 3);
  rb_read(&b, A3(f_wf, L(0), L(1), L(2)));
  rb_make(&b, A3(f_cv, L(0), L(0), L(1)));
  R_refl = b.r;
  rb_init(&b, "a symmetry", 3);
  rb_read(&b, A3(f_cv, L(0), L(1), L(2)));
  rb_make(&b, A3(f_cv, L(1), L(0), L(2)));
  R_sym = b.r;
  rb_init(&b, "a conversion", 3); /* (:conv e c p): p proves l, and c proves e = l */
  rb_tell(&b, 1);
  rb_read(&b, A1(f_pf, L(0)));
  rb_read(&b, A3(f_cv, L(1), L(0), L(2)));
  rb_make(&b, A1(f_pf, L(1)));
  R_conv = b.r;
}

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}

static int run(int argc, char **argv) {
  long first = -1; /* --first N: only the first N directives (for measuring scaling) */
  if (argc >= 4 && !strcmp(argv[1], "--first")) {
    first = strtol(argv[2], NULL, 10);
    argv += 2, argc -= 2;
  }
  if (argc < 2) {
    fprintf(stderr, "usage: %s [--first N] FILE.mmu [SPEC.mm0 | --proof-only]\n", argv[0]);
    return 2;
  }
  double t0 = now();
  /* The specification: given, or FILE.mm0 beside the proof file; --proof-only reads none. */
  const char *spec = argc > 2 ? argv[2] : NULL;
  char *beside = NULL;
  if (!spec) {
    size_t n = strlen(argv[1]);
    beside = xrealloc(NULL, n + 5);
    memcpy(beside, argv[1], n + 1);
    if (n > 4 && !strcmp(beside + n - 4, ".mmu")) beside[n - 4] = 0;
    strcat(beside, ".mm0");
    FILE *g = fopen(beside, "rb");
    if (!g) where = argv[1], die("no specification: give FILE.mm0 or --proof-only");
    fclose(g);
    spec = beside;
  }
  FILE *f = fopen(argv[1], "rb");
  if (!f) {
    perror(argv[1]);
    return 2;
  }
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  fseek(f, 0, SEEK_SET);
  char *buf = xrealloc(NULL, (size_t)sz + 1);
  if (sz < 0 || fread(buf, 1, (size_t)sz, f) != (size_t)sz) {
    fputs("read error\n", stderr);
    return 2;
  }
  fclose(f);
  buf[sz] = 0;
  src = buf, len = (size_t)sz;
  C = tr_ctx_new();
  S = tr_state_new(C);
  f_sort = tr_symbol(C, "sort", 1), f_pure = tr_symbol(C, "pure", 1), f_strict = tr_symbol(C, "strict", 1);
  f_provable = tr_symbol(C, "provable", 1), f_free = tr_symbol(C, "free", 1);
  f_bv = tr_symbol(C, "bv", 3), f_wf = tr_symbol(C, "wf", 3);
  f_dwf = tr_symbol(C, "dwf", 3), f_pf = tr_symbol(C, "pf", 1), f_cv = tr_symbol(C, "cv", 3);
  generic_rules();
  LIE = getenv("MM0_REF_LIE") ? atoi(getenv("MM0_REF_LIE")) : 0;
  if (strcmp(spec, "--proof-only")) spec_load(spec);
  where = "the start";
  long ndir = 0;
  for (int d; (first < 0 || ndir < first) && (nx = 0, d = parse()) >= 0; ndir++) directive(d);
  if (first < 0) spec_end();
  printf("verified %s%s: %ld sorts, %ld terms, %ld definitions, %ld axioms, %ld theorems; %ld firings; %zu facts "
         "present, %zu terms; %s [%.2f s]\n",
         argv[1], first >= 0 ? " (a prefix)" : "", n_sorts, n_terms, n_defs, n_axioms, n_theorems, firings,
         tr_present_count(S), tr_ctx_terms(C),
         have_spec ? "matches its specification" : "NOT CHECKED AGAINST A .mm0 SPECIFICATION", now() - t0);
  free(beside);
  return 0;
}

typedef struct {
  int argc;
  char **argv;
  int rc;
} job;
static void *run_job(void *p) {
  job *j = p;
  char base;
  stack_base = &base;
  j->rc = run(j->argc, j->argv);
  return NULL;
}

int main(int argc, char **argv) {
  job j = {argc, argv, 2};
  pthread_attr_t a;
  pthread_t th;
  stack_room = STACK_SIZE - ((size_t)8 << 20); /* set before the thread reads it */
  if (!pthread_attr_init(&a) && !pthread_attr_setstacksize(&a, STACK_SIZE) && !pthread_create(&th, &a, run_job, &j)) {
    pthread_join(th, NULL);
    return j.rc;
  }
  /* no large stack: the main thread's, with its own limit */
  struct rlimit rl;
  stack_room = getrlimit(RLIMIT_STACK, &rl) == 0 && rl.rlim_cur != RLIM_INFINITY && rl.rlim_cur > ((rlim_t)2 << 20)
                   ? (size_t)rl.rlim_cur - ((size_t)1 << 20)
                   : (size_t)7 << 20;
  run_job(&j);
  return j.rc;
}
