/* tcs.c: firing schemas, their text form and their instances (tcs.h).  Public tcalc_ref API only. */
#include "tcs.h"

#include <ctype.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

static void *xrealloc(void *p, size_t n) {
  void *q = realloc(p, n ? n : 1);
  if (!q) {
    fputs("tcs: out of memory\n", stderr);
    abort();
  }
  return q;
}

/* ---- host predicates ---- */

struct tcs_hostenv {
  tcs_host_fn fn;
  tr_term *args;
  size_t nargs, cap;
};
static tcs_host *HOSTS;
static size_t NHOSTS;

void tcs_register_hosts(const tcs_host *hosts, size_t n) {
  free(HOSTS);
  HOSTS = n ? xrealloc(NULL, n * sizeof *HOSTS) : NULL;
  if (n) memcpy(HOSTS, hosts, n * sizeof *HOSTS);
  NHOSTS = n;
}
tcs_host_fn tcs_host_find(const char *name) {
  for (size_t i = 0; i < NHOSTS; i++)
    if (!strcmp(HOSTS[i].name, name)) return HOSTS[i].fn;
  return NULL;
}
/* An unregistered host gives no verdict. */
static int host_adapter(tr_view *v, void *env) {
  const tcs_hostenv *e = env;
  return e->fn ? e->fn(v, e->args, e->nargs) : -1;
}
int tcs_named_host(tr_view *v, void *env) {
  const tcs_host_ref *h = env;
  tcs_host_fn fn = h ? tcs_host_find(h->name) : NULL;
  return fn ? fn(v, h->args, h->nargs) : -1;
}

static char *dupstr(const char *s, size_t n) {
  char *d = xrealloc(NULL, n + 1);
  memcpy(d, s, n);
  d[n] = 0;
  return d;
}

/* ---- the reader ---- */

typedef struct {
  tr_ctx *c;
  tcs_theory *th;
  int nth, capth;
  size_t caprules;
  tcs_rule *r; /* the rule being read, or NULL */
  tr_scope *sc;
  size_t cap[6]; /* takes, reads, makes, tells, apart, guards */
  int line;
  char *err;
  size_t errlen;
} rd;

static int fail(rd *d, const char *fmt, ...) {
  va_list ap;
  int n = snprintf(d->err, d->errlen, "line %d: ", d->line);
  va_start(ap, fmt);
  if (n >= 0 && (size_t)n < d->errlen) vsnprintf(d->err + n, d->errlen - (size_t)n, fmt, ap);
  va_end(ap);
  return -1;
}

static tr_term term(rd *d, const char *s, size_t n) {
  char *t = dupstr(s, n);
  tr_term x = tr_read(d->c, d->sc, t);
  free(t);
  return x;
}

#define PUSH(d, arr, len, capi, val)                                     \
  do {                                                                   \
    if ((len) >= (d)->cap[capi]) {                                       \
      (d)->cap[capi] = (d)->cap[capi] ? 2 * (d)->cap[capi] : 4;          \
      (arr) = xrealloc((arr), (d)->cap[capi] * sizeof *(arr));           \
    }                                                                    \
    (arr)[(len)++] = (val);                                              \
  } while (0)

/* "T = U": both sides; `last` splits at the last '=' (count P = N). */
static int split(rd *d, const char *s, const char **rhs, size_t *lhslen, bool last) {
  const char *eq = last ? strrchr(s, '=') : strchr(s, '=');
  if (!eq) return fail(d, "expected T = U");
  *lhslen = (size_t)(eq - s);
  *rhs = eq + 1;
  return 0;
}

static int statement(rd *d, const char *kw, size_t kwlen, const char *rest) {
#define IS(w) (kwlen == strlen(w) && !memcmp(kw, w, kwlen))
  size_t restlen = strlen(rest);
  while (restlen && isspace((unsigned char)rest[restlen - 1])) restlen--;
  if (IS("theory")) {
    if (d->r) return fail(d, "theory inside a rule");
    if (d->nth >= d->capth) {
      d->capth = d->capth ? 2 * d->capth : 4;
      d->th = xrealloc(d->th, (size_t)d->capth * sizeof *d->th);
    }
    d->th[d->nth++] = (tcs_theory){dupstr(rest, restlen), NULL, 0};
    d->caprules = 0;
    return 0;
  }
  if (IS("rule")) {
    if (d->r) return fail(d, "rule inside a rule");
    if (!d->nth) return fail(d, "rule before any theory");
    tcs_theory *t = &d->th[d->nth - 1];
    if (t->nrules >= d->caprules) {
      d->caprules = d->caprules ? 2 * d->caprules : 8;
      t->rules = xrealloc(t->rules, d->caprules * sizeof *t->rules);
    }
    d->r = &t->rules[t->nrules++];
    memset(d->r, 0, sizeof *d->r);
    d->r->name = dupstr(rest, restlen);
    memset(d->cap, 0, sizeof d->cap);
    d->sc = tr_scope_new();
    return 0;
  }
  if (!d->r) return fail(d, "statement outside a rule");
  tcs_rule *r = d->r;
  if (IS("end")) {
    r->nlocals = tr_scope_size(d->sc);
    tr_scope_free(d->sc);
    d->sc = NULL;
    d->r = NULL;
    return 0;
  }
  if (IS("params")) {
    if (tr_scope_size(d->sc) || r->nparams) return fail(d, "params must come first");
    for (const char *p = rest; *p;) {
      while (isspace((unsigned char)*p)) p++;
      const char *q = p;
      while (*q && !isspace((unsigned char)*q)) q++;
      if (q == p) break;
      if (!isupper((unsigned char)*p)) return fail(d, "a parameter is written as a local");
      size_t before = tr_scope_size(d->sc);
      if (term(d, p, (size_t)(q - p)) == TR_NONE || tr_scope_size(d->sc) != before + 1)
        return fail(d, "bad or repeated parameter");
      r->nparams++;
      p = q;
    }
    return 0;
  }
  if (IS("locals")) { /* fixes the numbering of the rule's own locals */
    if (tr_scope_size(d->sc) != r->nparams) return fail(d, "locals must come right after params");
    for (const char *p = rest; *p;) {
      while (isspace((unsigned char)*p)) p++;
      const char *q = p;
      while (*q && !isspace((unsigned char)*q)) q++;
      if (q == p) break;
      if (!isupper((unsigned char)*p)) return fail(d, "a local is written with a capital letter");
      size_t before = tr_scope_size(d->sc);
      if (term(d, p, (size_t)(q - p)) == TR_NONE || tr_scope_size(d->sc) != before + 1)
        return fail(d, "bad or repeated local");
      p = q;
    }
    return 0;
  }
  if (IS("fresh")) {
    char *end;
    unsigned long n = strtoul(rest, &end, 10);
    if (end == rest || n > 1000000) return fail(d, "bad fresh count");
    r->fresh = (uint32_t)n;
    return 0;
  }
  if (IS("take") || IS("read") || IS("make") || IS("absent") || IS("host")) {
    tr_term t = term(d, rest, restlen);
    if (t == TR_NONE) return fail(d, "bad term");
    if (IS("host") && tr_term_kind(d->c, t) != TR_APP) return fail(d, "a host guard is NAME(terms)");
    if (IS("take")) PUSH(d, r->takes, r->ntakes, 0, t);
    else if (IS("read")) PUSH(d, r->reads, r->nreads, 1, t);
    else if (IS("make")) PUSH(d, r->makes, r->nmakes, 2, t);
    else PUSH(d, r->guards, r->nguards, 5, ((tcs_guard){IS("host") ? TCS_HOST : TCS_ABSENT, t, TR_NONE, 0}));
    return 0;
  }
  if (IS("tell") || IS("apart") || IS("ask") || IS("count")) {
    const char *rhs;
    size_t lhslen;
    if (split(d, rest, &rhs, &lhslen, IS("count")) < 0) return -1;
    tr_term a = term(d, rest, lhslen);
    if (a == TR_NONE) return fail(d, "bad term");
    if (IS("count")) {
      char *end;
      unsigned long n = strtoul(rhs, &end, 10);
      while (isspace((unsigned char)*end)) end++;
      if (end == rhs || *end) return fail(d, "bad count");
      PUSH(d, r->guards, r->nguards, 5, ((tcs_guard){TCS_COUNT, a, TR_NONE, n}));
      return 0;
    }
    tr_term b = term(d, rhs, strlen(rhs));
    if (b == TR_NONE) return fail(d, "bad term");
    if (IS("tell")) PUSH(d, r->tells, r->ntells, 3, ((tr_eq){a, b}));
    else if (IS("apart")) PUSH(d, r->apart, r->napart, 4, ((tr_eq){a, b}));
    else PUSH(d, r->guards, r->nguards, 5, ((tcs_guard){TCS_ASK, a, b, 0}));
    return 0;
  }
  return fail(d, "unknown statement");
#undef IS
}

int tcs_read(tr_ctx *c, const char *text, tcs_theory **out, char *err, size_t errlen) {
  rd d = {.c = c, .err = err, .errlen = errlen};
  int rc = 0;
  for (const char *p = text; *p && rc == 0;) {
    const char *eol = strchr(p, '\n');
    size_t n = eol ? (size_t)(eol - p) : strlen(p);
    char *line = dupstr(p, n);
    d.line++;
    char *hash = strchr(line, '#'); /* a comment, unless it is a fresh name #j */
    while (hash && isdigit((unsigned char)hash[1])) hash = strchr(hash + 1, '#');
    if (hash) *hash = 0;
    char *s = line;
    while (isspace((unsigned char)*s)) s++;
    if (*s) {
      char *kw = s;
      while (*s && !isspace((unsigned char)*s)) s++;
      size_t kwlen = (size_t)(s - kw);
      while (isspace((unsigned char)*s)) s++;
      rc = statement(&d, kw, kwlen, s);
    }
    free(line);
    p = eol ? eol + 1 : p + n;
  }
  if (rc == 0 && d.r) rc = fail(&d, "rule %s has no end", d.r->name);
  if (rc < 0) {
    tr_scope_free(d.sc);
    if (d.r) d.r->nlocals = 0;
    tcs_free(d.th, d.nth);
    return -1;
  }
  *out = d.th;
  return d.nth;
}

void tcs_free(tcs_theory *th, int n) {
  for (int i = 0; i < n; i++) {
    for (size_t j = 0; j < th[i].nrules; j++) {
      tcs_rule *r = &th[i].rules[j];
      free(r->name);
      free(r->takes);
      free(r->reads);
      free(r->makes);
      free(r->tells);
      free(r->apart);
      free(r->guards);
    }
    free(th[i].rules);
    free(th[i].name);
  }
  free(th);
}

const tcs_rule *tcs_find(const tcs_theory *t, const char *name) {
  for (size_t i = 0; i < t->nrules; i++)
    if (!strcmp(t->rules[i].name, name)) return &t->rules[i];
  return NULL;
}

/* ---- rules from the reference's own data ---- */

#define COPY(dst, src, n) ((dst) = (n) ? memcpy(xrealloc(NULL, (n) * sizeof *(dst)), (src), (n) * sizeof *(dst)) : NULL)

bool tcs_rule_from_firing(tr_ctx *c, const char *name, const tr_firing *f, uint32_t nparams, tcs_rule *r, char *err,
                          size_t errlen) {
  memset(r, 0, sizeof *r);
  if (nparams > f->locals) return snprintf(err, errlen, "%s: more parameters than locals", name), false;
  for (size_t i = 0; i < f->nmakes; i++)
    if (f->makes[i].id || f->makes[i].schema_locals)
      return snprintf(err, errlen, "%s: a make with an identity or a stored schema", name), false;
  for (size_t i = 0; i < f->nguards; i++) {
    const tr_guard *g = &f->guards[i];
    if (g->kind == TR_G_QUERY || (g->kind == TR_G_HOST && (g->entailed != tcs_named_host || !g->env)))
      return snprintf(err, errlen, "%s: guard %zu is a predicate query or an unnamed host", name, i), false;
  }
  r->name = dupstr(name, strlen(name));
  r->nparams = nparams, r->nlocals = f->locals, r->fresh = f->fresh;
  r->ntakes = f->ntakes, r->nreads = f->nreads, r->nmakes = f->nmakes, r->ntells = f->ntells, r->napart = f->napart;
  r->takes = f->ntakes ? xrealloc(NULL, f->ntakes * sizeof *r->takes) : NULL;
  r->reads = f->nreads ? xrealloc(NULL, f->nreads * sizeof *r->reads) : NULL;
  r->makes = f->nmakes ? xrealloc(NULL, f->nmakes * sizeof *r->makes) : NULL;
  for (size_t i = 0; i < f->ntakes; i++) r->takes[i] = f->takes[i].pattern;
  for (size_t i = 0; i < f->nreads; i++) r->reads[i] = f->reads[i].pattern;
  for (size_t i = 0; i < f->nmakes; i++) r->makes[i] = f->makes[i].label;
  COPY(r->tells, f->tells, f->ntells);
  COPY(r->apart, f->apart, f->napart);
  r->nguards = f->nguards;
  r->guards = f->nguards ? xrealloc(NULL, f->nguards * sizeof *r->guards) : NULL;
  for (size_t i = 0; i < f->nguards; i++) {
    const tr_guard *g = &f->guards[i];
    tcs_guard *h = &r->guards[i];
    if (g->kind == TR_G_HOST) {
      const tcs_host_ref *ref = g->env;
      *h = (tcs_guard){TCS_HOST, tr_app(c, tr_symbol(c, ref->name, (uint32_t)ref->nargs), ref->args), TR_NONE, 0};
    } else
      *h = (tcs_guard){g->kind == TR_G_EQUAL ? TCS_ASK : g->kind == TR_G_ABSENT ? TCS_ABSENT : TCS_COUNT, g->a,
                       g->kind == TR_G_EQUAL ? g->b : TR_NONE, g->kind == TR_G_COUNT ? g->number : 0};
  }
  return true;
}

tcs_theory *tcs_theory_from_firings(tr_ctx *c, const char *name, size_t n, const char *const *names,
                                    const tr_firing *firings, const uint32_t *nparams, char *err, size_t errlen) {
  tcs_theory *t = xrealloc(NULL, sizeof *t);
  t->name = dupstr(name, strlen(name));
  t->rules = xrealloc(NULL, (n + 1) * sizeof *t->rules);
  t->nrules = 0;
  for (size_t i = 0; i < n; i++, t->nrules++)
    if (!tcs_rule_from_firing(c, names[i], &firings[i], nparams[i], &t->rules[i], err, errlen)) {
      tcs_free(t, 1);
      return NULL;
    }
  return t;
}

/* ---- the text form, written ---- */

static bool lower_ident(const char *s) {
  if (!(*s >= 'a' && *s <= 'z')) return false;
  for (; *s; s++)
    if (!(*s == '_' || (*s >= 'a' && *s <= 'z') || (*s >= 'A' && *s <= 'Z') || (*s >= '0' && *s <= '9'))) return false;
  return true;
}
static bool write_term(FILE *out, const tr_ctx *c, tr_term t) {
  switch (tr_term_kind(c, t)) {
  case TR_CODE: fprintf(out, "%lld", (long long)tr_term_code(c, t)); return true;
  case TR_NAME: fprintf(out, "@%u", tr_term_index(c, t)); return true;
  case TR_VAR: fprintf(out, "$%u", tr_term_index(c, t)); return true;
  case TR_LOCAL: fprintf(out, "X%u", tr_term_index(c, t)); return true;
  case TR_FRESH: fprintf(out, "#%u", tr_term_index(c, t)); return true;
  case TR_APP: {
    const char *s = tr_symbol_name(c, tr_term_symbol(c, t));
    if (!lower_ident(s)) return false;
    fputs(s, out);
    uint32_t n = tr_term_arity(c, t);
    for (uint32_t i = 0; i < n; i++) {
      fputs(i ? ", " : "(", out);
      if (!write_term(out, c, tr_term_arg(c, t, i))) return false;
    }
    if (n) fputs(")", out);
    return true;
  }
  }
  return false;
}
static bool line(FILE *out, const tr_ctx *c, const char *kw, tr_term a, const char *mid, tr_term b) {
  fprintf(out, "  %s ", kw);
  bool ok = write_term(out, c, a);
  if (mid) fputs(mid, out), ok &= write_term(out, c, b);
  fputs("\n", out);
  return ok;
}

bool tcs_write(FILE *out, const tr_ctx *c, const tcs_theory *th, int n) {
  bool ok = true;
  for (int ti = 0; ti < n; ti++) {
    fprintf(out, "theory %s\n", th[ti].name);
    for (size_t ri = 0; ri < th[ti].nrules; ri++) {
      const tcs_rule *r = &th[ti].rules[ri];
      fprintf(out, "rule %s\n", r->name);
      if (r->nparams) {
        fputs("  params", out);
        for (uint32_t i = 0; i < r->nparams; i++) fprintf(out, " X%u", i);
        fputs("\n", out);
      }
      if (r->nlocals > r->nparams) {
        fputs("  locals", out);
        for (uint32_t i = r->nparams; i < r->nlocals; i++) fprintf(out, " X%u", i);
        fputs("\n", out);
      }
      if (r->fresh) fprintf(out, "  fresh %u\n", r->fresh);
      for (size_t i = 0; i < r->ntakes; i++) ok &= line(out, c, "take", r->takes[i], NULL, TR_NONE);
      for (size_t i = 0; i < r->nreads; i++) ok &= line(out, c, "read", r->reads[i], NULL, TR_NONE);
      for (size_t i = 0; i < r->ntells; i++) ok &= line(out, c, "tell", r->tells[i].left, " = ", r->tells[i].right);
      for (size_t i = 0; i < r->napart; i++) ok &= line(out, c, "apart", r->apart[i].left, " = ", r->apart[i].right);
      for (size_t i = 0; i < r->nguards; i++) {
        const tcs_guard *g = &r->guards[i];
        if (g->kind == TCS_ASK) ok &= line(out, c, "ask", g->a, " = ", g->b);
        else if (g->kind == TCS_HOST) ok &= line(out, c, "host", g->a, NULL, TR_NONE);
        else if (g->kind == TCS_ABSENT) ok &= line(out, c, "absent", g->a, NULL, TR_NONE);
        else {
          fputs("  count ", out);
          ok &= write_term(out, c, g->a);
          fprintf(out, " = %zu\n", g->number);
        }
      }
      for (size_t i = 0; i < r->nmakes; i++) ok &= line(out, c, "make", r->makes[i], NULL, TR_NONE);
      fputs("end\n", out);
    }
  }
  return ok;
}

/* ---- instances ---- */

/* t with LOCAL i < np written as params[i] and LOCAL i >= np as LOCAL i - np. */
static tr_term subst(tr_ctx *c, tr_term t, const tr_term *params, uint32_t np) {
  switch (tr_term_kind(c, t)) {
  case TR_LOCAL: {
    uint32_t i = tr_term_index(c, t);
    return i < np ? params[i] : tr_local(c, i - np);
  }
  case TR_APP: {
    uint32_t n = tr_term_arity(c, t);
    if (!n) return t;
    tr_term small[8], *args = n <= 8 ? small : xrealloc(NULL, n * sizeof *args);
    bool changed = false;
    for (uint32_t i = 0; i < n; i++) {
      tr_term a = tr_term_arg(c, t, i);
      args[i] = subst(c, a, params, np);
      changed |= args[i] != a;
    }
    tr_term out = changed ? tr_app(c, tr_term_symbol(c, t), args) : t;
    if (args != small) free(args);
    return out;
  }
  default:
    return t;
  }
}

#define ROOM(in, arr, cap, n)                                   \
  do {                                                          \
    if ((n) > (in)->cap) {                                      \
      (in)->cap = (n);                                          \
      (in)->arr = xrealloc((in)->arr, (n) * sizeof *(in)->arr); \
    }                                                           \
  } while (0)

const tr_firing *tcs_instance_of(tcs_instance *in, tr_ctx *c, const tcs_rule *r, const tr_term *params,
                                 const tr_occ *occs) {
  uint32_t np = r->nparams;
  size_t nuse = r->ntakes + r->nreads, neq = r->ntells + r->napart;
  ROOM(in, uses, cap_uses, nuse);
  ROOM(in, makes, cap_makes, r->nmakes);
  ROOM(in, eqs, cap_eqs, neq);
  if (r->nguards > in->cap_guards) {
    in->hosts = xrealloc(in->hosts, r->nguards * sizeof *in->hosts);
    memset(in->hosts + in->cap_guards, 0, (r->nguards - in->cap_guards) * sizeof *in->hosts);
  }
  ROOM(in, guards, cap_guards, r->nguards);
#define S(t) (np ? subst(c, (t), params, np) : (t))
  for (size_t i = 0; i < r->ntakes; i++) in->uses[i] = (tr_use){S(r->takes[i]), occs[i]};
  for (size_t i = 0; i < r->nreads; i++) in->uses[r->ntakes + i] = (tr_use){S(r->reads[i]), occs[r->ntakes + i]};
  for (size_t i = 0; i < r->nmakes; i++) in->makes[i] = (tr_make){S(r->makes[i]), 0, 0};
  for (size_t i = 0; i < r->ntells; i++) in->eqs[i] = (tr_eq){S(r->tells[i].left), S(r->tells[i].right)};
  for (size_t i = 0; i < r->napart; i++)
    in->eqs[r->ntells + i] = (tr_eq){S(r->apart[i].left), S(r->apart[i].right)};
  for (size_t i = 0; i < r->nguards; i++) {
    const tcs_guard *g = &r->guards[i];
    tr_guard *h = &in->guards[i];
    memset(h, 0, sizeof *h);
    if (g->kind == TCS_HOST) { /* NAME(args): the host's terms as written in the firing */
      tcs_hostenv *e = &in->hosts[i];
      uint32_t n = tr_term_arity(c, g->a);
      if (n > e->cap) e->cap = n, e->args = xrealloc(e->args, n * sizeof *e->args);
      for (uint32_t k = 0; k < n; k++) e->args[k] = S(tr_term_arg(c, g->a, k));
      e->nargs = n;
      e->fn = tcs_host_find(tr_symbol_name(c, tr_term_symbol(c, g->a)));
      h->kind = TR_G_HOST, h->entailed = host_adapter, h->env = e;
      continue;
    }
    h->kind = g->kind == TCS_ASK ? TR_G_EQUAL : g->kind == TCS_ABSENT ? TR_G_ABSENT : TR_G_COUNT;
    h->a = S(g->a);
    if (g->kind == TCS_ASK) h->b = S(g->b);
    h->number = g->number;
  }
#undef S
  in->firing = (tr_firing){.locals = r->nlocals - np,
                           .fresh = r->fresh,
                           .takes = in->uses,
                           .ntakes = r->ntakes,
                           .reads = in->uses + r->ntakes,
                           .nreads = r->nreads,
                           .makes = in->makes,
                           .nmakes = r->nmakes,
                           .tells = in->eqs,
                           .ntells = r->ntells,
                           .apart = in->eqs + r->ntells,
                           .napart = r->napart,
                           .guards = in->guards,
                           .nguards = r->nguards};
  return &in->firing;
}

void tcs_instance_free(tcs_instance *in) {
  for (size_t i = 0; i < in->cap_guards && in->hosts; i++) free(in->hosts[i].args);
  free(in->hosts);
  free(in->uses);
  free(in->makes);
  free(in->eqs);
  free(in->guards);
  memset(in, 0, sizeof *in);
}
