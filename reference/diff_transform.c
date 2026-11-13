/* diff_transform.c: random store programs run by tcalc_ref and by CeTTa's transform.
 *
 * The shared fragment: ground facts; one transform call takes, reads and checks absence, then
 * makes.  A bare transform fires every match of its snapshot, each admitted where the previous
 * ones left the store (a match whose absence fails at the snapshot is not one).  The order of
 * the matches is not part of the meaning (spaces are unordered), so this client computes every
 * final store the calculus reaches when each call's matches fire in some order, every firing
 * decided by tr_fire, and checks that CeTTa's final store, as a bag, is one of them.  Programs
 * with a single possible final store are an exact comparison.
 *
 * usage: diff_transform CETTA SEED COUNT [FAULT [DIR]]
 *   FAULT 0 none; 1 the control layer drops absence guards; 2 reads consume.
 */
#include "tcalc_ref.h"

#include <stdlib.h>
#include <string.h>

enum { NPRED = 4, NVAR = 3, MAXSRC = 4, MAXTPL = 2, MAXCALL = 5, MAXFACT = 8, MAXMATCH = 10 };
static const char *pred[NPRED] = {"a", "b", "c", "d"};
static const int arity[NPRED] = {1, 1, 1, 2};

typedef struct {
  int pred;
  int arg[2]; /* >= 0: the code; -1-i: variable i (x, y, z); -10-i: an absence-local variable */
} atom;
typedef struct {
  int kind; /* 0 take, 1 read, 2 absent */
  atom a;
} source;
typedef struct {
  int nsrc, ntpl;
  source src[MAXSRC];
  atom tpl[MAXTPL];
} call;
typedef struct {
  int nfact, ncall;
  atom fact[MAXFACT];
  call calls[MAXCALL];
} program;

static uint64_t rng;
static unsigned rnd(unsigned n) {
  rng ^= rng << 13, rng ^= rng >> 7, rng ^= rng << 17;
  return (unsigned)(rng % n);
}

static void gen(program *p) {
  memset(p, 0, sizeof *p);
  p->nfact = 3 + (int)rnd(MAXFACT - 2);
  for (int i = 0; i < p->nfact; i++) p->fact[i] = (atom){(int)rnd(NPRED), {(int)rnd(3) + 1, (int)rnd(3) + 1}};
  p->ncall = 2 + (int)rnd(MAXCALL - 1);
  for (int c = 0; c < p->ncall; c++) {
    call *k = &p->calls[c];
    int npos = 1 + (int)rnd(2), nabs = rnd(2) ? 1 + (int)rnd(2) : 0;
    bool bound[NVAR] = {false};
    for (int i = 0; i < npos; i++) {
      source *s = &k->src[k->nsrc++];
      s->kind = (int)rnd(2);
      s->a.pred = (int)rnd(NPRED);
      for (int j = 0; j < arity[s->a.pred]; j++) {
        if (rnd(3)) { int v = (int)rnd(NVAR); s->a.arg[j] = -1 - v; bound[v] = true; }
        else s->a.arg[j] = (int)rnd(3) + 1;
      }
    }
    for (int i = 0; i < nabs && k->nsrc < MAXSRC; i++) {
      source *s = &k->src[k->nsrc++];
      s->kind = 2;
      s->a.pred = (int)rnd(NPRED);
      for (int j = 0; j < arity[s->a.pred]; j++) {
        int r = (int)rnd(4), v = (int)rnd(NVAR);
        if (r <= 1 && bound[v]) s->a.arg[j] = -1 - v;
        else if (r == 2) s->a.arg[j] = -10 - (i * 2 + j);
        else s->a.arg[j] = (int)rnd(3) + 1;
      }
    }
    k->ntpl = 1 + (int)rnd(MAXTPL);
    for (int i = 0; i < k->ntpl; i++) {
      atom *t = &k->tpl[i];
      t->pred = (int)rnd(NPRED);
      for (int j = 0; j < arity[t->pred]; j++) {
        int v = (int)rnd(NVAR);
        t->arg[j] = rnd(2) && bound[v] ? -1 - v : (int)rnd(3) + 1;
      }
    }
  }
}

/* ---- MeTTa text ---- */
static void put_arg(FILE *o, int a) {
  if (a >= 0) fprintf(o, " %d", a);
  else if (a > -10) fprintf(o, " $%c", "xyz"[-1 - a]);
  else fprintf(o, " $w%d", -10 - a);
}
static void put_atom(FILE *o, const atom *a) {
  fprintf(o, "(%s", pred[a->pred]);
  for (int j = 0; j < arity[a->pred]; j++) put_arg(o, a->arg[j]);
  fputc(')', o);
}
static void put_program(FILE *o, int id, const program *p) {
  fprintf(o, "!(bind! &s%d (new-space))\n", id);
  for (int i = 0; i < p->nfact; i++) {
    fprintf(o, "!(add-atom &s%d ", id);
    put_atom(o, &p->fact[i]);
    fputs(")\n", o);
  }
  for (int c = 0; c < p->ncall; c++) {
    const call *k = &p->calls[c];
    fprintf(o, "!(collapse (transform &s%d ", id);
    if (k->nsrc > 1) fputs("(,", o);
    for (int i = 0; i < k->nsrc; i++) {
      fputs(k->nsrc > 1 ? " " : "", o);
      if (k->src[i].kind == 0) fputs("(take ", o);
      if (k->src[i].kind == 2) fputs("(absent ", o);
      put_atom(o, &k->src[i].a);
      if (k->src[i].kind != 1) fputc(')', o);
    }
    if (k->nsrc > 1) fputc(')', o);
    fputc(' ', o);
    if (k->ntpl > 1) fputs("(,", o);
    for (int i = 0; i < k->ntpl; i++) {
      fputs(k->ntpl > 1 ? " " : "", o);
      put_atom(o, &k->tpl[i]);
    }
    if (k->ntpl > 1) fputc(')', o);
    fprintf(o, " &s%d))\n", id);
  }
  fprintf(o, "!(final %d (collapse (match &s%d $a $a)))\n", id, id);
}

/* ---- the program on tcalc_ref ---- */

/* The atom as a term: variables become the firing's locals, or codes when `bind` gives them. */
static tr_term term_of(tr_ctx *c, const atom *a, const int *bind) {
  tr_term args[2];
  for (int j = 0; j < arity[a->pred]; j++) {
    int v = a->arg[j];
    if (v >= 0) args[j] = tr_code(c, v);
    else if (v > -10) args[j] = bind && bind[-1 - v] ? tr_code(c, bind[-1 - v]) : tr_local(c, (uint32_t)(-1 - v));
    else args[j] = tr_local(c, (uint32_t)(NVAR + (-10 - v)));
  }
  return tr_app(c, tr_symbol(c, pred[a->pred], (uint32_t)arity[a->pred]), args);
}

/* One-way match of a positive source against a ground label, extending bind (0 = unbound). */
static bool match(tr_ctx *c, const atom *a, tr_term label, int *bind) {
  if (tr_term_symbol(c, label) != tr_symbol(c, pred[a->pred], (uint32_t)arity[a->pred])) return false;
  for (int j = 0; j < arity[a->pred]; j++) {
    int64_t v = tr_term_code(c, tr_term_arg(c, label, (uint32_t)j));
    int x = a->arg[j];
    if (x >= 0) { if (v != x) return false; }
    else {
      if (bind[-1 - x] && bind[-1 - x] != v) return false;
      bind[-1 - x] = (int)v;
    }
  }
  return true;
}

static bool absent_at(tr_ctx *c, const atom *a, const int *bind, const tr_term *labels, size_t n) {
  for (size_t i = 0; i < n; i++) {
    tr_term l = labels[i];
    if (tr_term_symbol(c, l) != tr_symbol(c, pred[a->pred], (uint32_t)arity[a->pred])) continue;
    bool all = true;
    for (int j = 0; j < arity[a->pred] && all; j++) {
      int x = a->arg[j];
      int64_t v = tr_term_code(c, tr_term_arg(c, l, (uint32_t)j));
      if (x >= 0) all = v == x;
      else if (x > -10) all = v == bind[-1 - x];
    }
    if (all) return false;
  }
  return true;
}

typedef struct {
  int (*binds)[NVAR];
  size_t n, cap;
} matches;

/* The snapshot's matches: tuples of present labels for the positive sources (a label may serve
 * several sources), kept when every absence holds at the snapshot. */
static void enumerate(tr_ctx *c, const call *k, int i, int *bind, const tr_term *labels, size_t n, matches *m) {
  int npos = 0;
  while (npos < k->nsrc && k->src[npos].kind != 2) npos++;
  if (i == npos) {
    for (int a = npos; a < k->nsrc; a++)
      if (!absent_at(c, &k->src[a].a, bind, labels, n)) return;
    if (m->n == m->cap) m->binds = realloc(m->binds, (m->cap = m->cap ? 2 * m->cap : 16) * sizeof *m->binds);
    memcpy(m->binds[m->n++], bind, sizeof(int) * NVAR);
    return;
  }
  for (size_t o = 0; o < n; o++) {
    int saved[NVAR];
    memcpy(saved, bind, sizeof saved);
    if (match(c, &k->src[i].a, labels[o], bind)) enumerate(c, k, i + 1, bind, labels, n, m);
    memcpy(bind, saved, sizeof saved);
  }
}

static void snapshot_matches(tr_state *s, const call *k, matches *m) {
  size_t n = tr_present_count(s);
  tr_term *labels = malloc((n + 1) * sizeof *labels);
  tr_occ o = 0;
  for (size_t i = 0; i < n; i++) o = tr_next_present(s, o, &labels[i]);
  int bind[NVAR] = {0};
  m->n = 0;
  enumerate(tr_state_ctx(s), k, 0, bind, labels, n, m);
  free(labels);
}

static size_t admitted, refused;

/* One match as one firing: copies chosen by content (takes, then reads among the copies not
 * taken); the step decides. */
static void fire_match(tr_state *s, const call *k, const int *bind, int fault) {
  tr_ctx *c = tr_state_ctx(s);
  tr_use takes[MAXSRC], reads[MAXSRC];
  tr_make makes[MAXTPL];
  tr_guard guards[MAXSRC];
  size_t nt = 0, nr = 0, ng = 0;
  for (int i = 0; i < k->nsrc; i++)
    if (k->src[i].kind == 2 && fault != 1) guards[ng++] = (tr_guard){.kind = TR_G_ABSENT, .a = term_of(c, &k->src[i].a, NULL)};
  for (int pass = 0; pass < 2; pass++)
    for (int i = 0; i < k->nsrc; i++) {
      const source *src = &k->src[i];
      bool take = src->kind == 0 || fault == 2;
      if (src->kind == 2 || take != (pass == 0)) continue;
      tr_term want = term_of(c, &src->a, bind), l;
      tr_occ pick = 0;
      for (tr_occ q = tr_next_candidate(s, want, 0, &l); q && !pick; q = tr_next_candidate(s, want, q, &l)) {
        bool used = false;
        for (size_t t = 0; t < nt; t++) used |= takes[t].occ == q;
        if (l == want && !used) pick = q;
      }
      if (!pick) { refused++; return; } /* no copy: the match is not enabled */
      tr_use u = {term_of(c, &src->a, NULL), pick};
      if (take) takes[nt++] = u;
      else reads[nr++] = u;
    }
  for (int i = 0; i < k->ntpl; i++) makes[i] = (tr_make){term_of(c, &k->tpl[i], NULL), 0, 0};
  tr_firing f = {.locals = NVAR + 4, .takes = takes, .ntakes = nt, .reads = reads, .nreads = nr,
                 .makes = makes, .nmakes = (size_t)k->ntpl, .guards = guards, .nguards = ng};
  if (tr_fire(s, &f, NULL) == TR_ADMITTED) admitted++;
  else refused++;
}

static int cmpstr(const void *a, const void *b) { return strcmp(*(char *const *)a, *(char *const *)b); }

static char *bag_text(char **items, size_t n) {
  qsort(items, n, sizeof *items, cmpstr);
  size_t total = 1;
  for (size_t i = 0; i < n; i++) total += strlen(items[i]) + 1;
  char *out = calloc(total, 1);
  for (size_t i = 0; i < n; i++) {
    if (i) strcat(out, " ");
    strcat(out, items[i]);
  }
  return out;
}

static char *c_bag(const tr_state *s) {
  tr_ctx *c = tr_state_ctx(s);
  size_t n = tr_present_count(s), i = 0;
  char **items = calloc(n + 1, sizeof *items);
  tr_term l;
  for (tr_occ o = tr_next_present(s, 0, &l); o; o = tr_next_present(s, o, &l), i++) {
    char buf[64];
    int len = snprintf(buf, sizeof buf, "(%s", tr_symbol_name(c, tr_term_symbol(c, l)));
    for (uint32_t j = 0; j < tr_term_arity(c, l); j++)
      len += snprintf(buf + len, sizeof buf - (size_t)len, " %lld", (long long)tr_term_code(c, tr_term_arg(c, l, j)));
    snprintf(buf + len, sizeof buf - (size_t)len, ")");
    items[i] = strdup(buf);
  }
  char *out = bag_text(items, n);
  for (size_t j = 0; j < n; j++) free(items[j]);
  free(items);
  return out;
}

/* Sets of stores, by bag. */
typedef struct {
  char **bag;
  tr_state **st;
  uint64_t *mask;
  size_t n, cap;
} storeset;
static bool storeset_has(const storeset *z, const char *bag, uint64_t mask) {
  for (size_t i = 0; i < z->n; i++)
    if (z->mask[i] == mask && strcmp(z->bag[i], bag) == 0) return true;
  return false;
}
static void storeset_add(storeset *z, char *bag, tr_state *st, uint64_t mask) {
  if (z->n == z->cap) {
    z->cap = z->cap ? 2 * z->cap : 16;
    z->bag = realloc(z->bag, z->cap * sizeof *z->bag);
    z->st = realloc(z->st, z->cap * sizeof *z->st);
    z->mask = realloc(z->mask, z->cap * sizeof *z->mask);
  }
  z->bag[z->n] = bag, z->st[z->n] = st, z->mask[z->n++] = mask;
}
static void storeset_free(storeset *z) {
  for (size_t i = 0; i < z->n; i++) free(z->bag[i]), tr_state_free(z->st[i]);
  free(z->bag), free(z->st), free(z->mask);
  memset(z, 0, sizeof *z);
}

/* Every store reached by trying each match once, in every order. */
static void explore(tr_state *s, const call *k, const matches *m, uint64_t mask, storeset *out,
                    storeset *seen, int fault, size_t *budget) {
  if (!*budget) return;
  (*budget)--;
  char *b = c_bag(s);
  if (storeset_has(seen, b, mask)) { free(b); return; }
  storeset_add(seen, strdup(b), NULL, mask);
  if (mask == (m->n == 64 ? ~0ULL : (1ULL << m->n) - 1)) {
    if (!storeset_has(out, b, 0)) storeset_add(out, b, tr_state_clone(s), 0);
    else free(b);
    return;
  }
  free(b);
  for (size_t i = 0; i < m->n; i++) {
    if (mask >> i & 1) continue;
    tr_state *t = tr_state_clone(s);
    fire_match(t, k, m->binds[i], fault);
    explore(t, k, m, mask | 1ULL << i, out, seen, fault, budget);
    tr_state_free(t);
  }
}

/* Parses "(final ID (item item ...))" from CeTTa's output. */
static char *cetta_bag(const char *line, int *id) {
  if (sscanf(line, "(final %d", id) != 1) return NULL;
  const char *p = strchr(line + 7, '(');
  if (!p) return NULL;
  p++;
  char **items = NULL;
  size_t n = 0, cap = 0;
  while (*p && *p != ')') {
    while (*p == ' ') p++;
    if (*p != '(') break;
    const char *start = p;
    int depth = 0;
    do {
      depth += *p == '(';
      depth -= *p == ')';
      p++;
    } while (depth && *p);
    if (n == cap) items = realloc(items, (cap = cap ? 2 * cap : 16) * sizeof *items);
    items[n++] = strndup(start, (size_t)(p - start));
  }
  char *out = bag_text(items, n);
  for (size_t j = 0; j < n; j++) free(items[j]);
  free(items);
  return out;
}

int main(int argc, char **argv) {
  if (argc < 4) {
    fprintf(stderr, "usage: %s CETTA SEED COUNT [FAULT [DIR]]\n", argv[0]);
    return 2;
  }
  const char *cetta = argv[1];
  uint64_t seed = strtoull(argv[2], NULL, 10);
  int count = atoi(argv[3]), fault = argc > 4 ? atoi(argv[4]) : 0;
  const char *dir = argc > 5 ? argv[5] : ".";
  char path[4096];
  snprintf(path, sizeof path, "%s/diff_transform_%llu.metta", dir, (unsigned long long)seed);
  FILE *out = fopen(path, "w");
  if (!out) { perror(path); return 2; }
  fputs("!(import! &self (library lib_transform))\n", out);
  storeset *finals = calloc((size_t)count, sizeof *finals);
  bool *skipped = calloc((size_t)count, sizeof *skipped);
  tr_ctx *c = tr_ctx_new();
  rng = seed * 2654435761ULL + 88172645463325252ULL;
  matches m = {0};
  for (int i = 0; i < count; i++) {
    program p;
    gen(&p);
    put_program(out, i, &p);
    tr_state *s = tr_state_new(c);
    tr_make mk[MAXFACT];
    for (int f = 0; f < p.nfact; f++) mk[f] = (tr_make){term_of(c, &p.fact[f], NULL), 0, 0};
    tr_firing init = {.makes = mk, .nmakes = (size_t)p.nfact};
    tr_fire(s, &init, NULL);
    storeset frontier = {0};
    storeset_add(&frontier, c_bag(s), s, 0);
    for (int k = 0; k < p.ncall && !skipped[i]; k++) {
      storeset next = {0};
      for (size_t f = 0; f < frontier.n && !skipped[i]; f++) {
        snapshot_matches(frontier.st[f], &p.calls[k], &m);
        if (m.n > MAXMATCH) { skipped[i] = true; break; }
        storeset seen = {0};
        size_t budget = 200000;
        explore(frontier.st[f], &p.calls[k], &m, 0, &next, &seen, fault, &budget);
        if (!budget) skipped[i] = true;
        storeset_free(&seen);
      }
      storeset_free(&frontier);
      frontier = next;
    }
    finals[i] = frontier;
  }
  free(m.binds);
  fclose(out);
  char cmd[8192];
  snprintf(cmd, sizeof cmd, "%s --lang petta %s 2>&1", cetta, path);
  FILE *in = popen(cmd, "r");
  if (!in) { perror("popen"); return 2; }
  char *line = NULL;
  size_t cap = 0;
  int seen = 0, exact = 0, among = 0, disagree = 0, skip = 0;
  while (getline(&line, &cap, in) > 0) {
    int id;
    char *bag = cetta_bag(line, &id);
    if (!bag) continue;
    seen++;
    if (id < 0 || id >= count) { free(bag); continue; }
    if (skipped[id]) { skip++; free(bag); continue; }
    if (storeset_has(&finals[id], bag, 0)) {
      if (finals[id].n == 1) exact++;
      else among++;
    } else {
      disagree++;
      if (disagree <= 3) {
        fprintf(stderr, "program %d (seed %llu):\n  cetta [%s]\n", id, (unsigned long long)seed, bag);
        for (size_t j = 0; j < finals[id].n && j < 4; j++) fprintf(stderr, "  ref   [%s]\n", finals[id].bag[j]);
      }
    }
    free(bag);
  }
  int status = pclose(in);
  free(line);
  printf("seed %llu fault %d: %d programs: %d exact (one possible store), %d among several, %d disagree, "
         "%d skipped (over %d matches), %d missing; firings admitted %zu, refused %zu; cetta status %d\n",
         (unsigned long long)seed, fault, count, exact, among, disagree, skip, MAXMATCH, count - seen,
         admitted, refused, status);
  for (int i = 0; i < count; i++) storeset_free(&finals[i]);
  free(finals);
  free(skipped);
  tr_ctx_free(c);
  return disagree || seen != count;
}
