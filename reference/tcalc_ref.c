/* tcalc_ref.c: one step of the transform calculus, written from the Lean definitions named in
 * tcalc_ref.h.  C11, no dependencies.
 *
 * Data structures and their costs (n = present occurrences, |t| = size of a term as a DAG):
 *   term table      hash-consed nodes; interning O(arity) expected; equality of terms without
 *                   variables or locals is equality of ids, O(1); each node records what kinds
 *                   occur below it and its largest variable, name and local, so a term without
 *                   them is checked, opened and resolved in O(1)
 *   locals          a firing's locals are slots of an environment that lives for one decision
 *                   (as in the WAM); local ids are relative to the firing, so trying a firing
 *                   creates no new terms, and a result keeps only the variables left unbound
 *   rebuilds        resolving through bindings and opening are memoized per call by node,
 *                   O(|t|), never exponential on shared subterms
 *   unification     bindings with a trail; a pair memo per call (each pair of nodes is unified
 *                   once) and an occurs check once per binding, memoized by node: O(|t|) per
 *                   binding, near-linear in practice; undo is O(bindings undone)
 *   occurrences     slots with a free list; an identity -> slot hash map, O(1) expected; one
 *                   list in the order of making and one list per label head, both doubly linked,
 *                   so taking, reading and making are O(1) per occurrence
 *   guards          absence and count read one head bucket (plus labels whose head is still a
 *                   variable), the standard index; a predicate query reads every occurrence
 *                   because its region is an arbitrary predicate
 *   disequations    each is watched by the free variables of its sides (as dif/2 is); a firing
 *                   re-checks only those watched by variables it binds, and the told ones
 *   symbols         an open-addressing table by name and arity, O(length of the name)
 * The term table is never collected: it grows with the distinct terms ever made.
 */
#include "tcalc_ref.h"

#include <ctype.h>
#include <stdlib.h>
#include <string.h>

/* ============================================================================================
 * Allocation.  Running out of memory is not a verdict: the process stops.
 * ========================================================================================== */

static void *xrealloc(void *p, size_t n) {
  void *q = realloc(p, n ? n : 1);
  if (!q) {
    fputs("tcalc_ref: out of memory\n", stderr);
    abort();
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

#define DUP(src, n) ((n) ? memcpy(xrealloc(NULL, (size_t)(n) * sizeof *(src)), (src), (size_t)(n) * sizeof *(src)) : NULL)

static uint64_t mix(uint64_t h, uint64_t x) {
  h ^= x + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
  return h * 0xff51afd7ed558ccdULL;
}

/* ============================================================================================
 * Terms.  A node is a kind, a value (the symbol of an APP, the code of a CODE, the index of a
 * NAME, VAR, LOCAL or FRESH), the arguments of an APP, and a summary of what occurs below it.
 * ========================================================================================== */

enum { HAS_VAR = 1, HAS_LOCAL = 2, HAS_FRESH = 4, OPEN = HAS_VAR | HAS_LOCAL };

typedef struct {
  uint8_t kind, flags;
  uint32_t nargs, args;                /* args: offset into argv */
  uint32_t maxvar, maxname, maxlocal;  /* 1 + the largest index below, 0 if none */
  uint64_t val, hash;
} node;

typedef struct {
  char *name;
  uint32_t arity;
} symbol;

typedef struct {
  uint64_t key;
  uint32_t gen;
} pairslot;

/* A work list, so that deep terms need no deep recursion; the context lends its buffers. */
typedef struct {
  tr_term *v;
  size_t n, cap;
} stack;

struct tr_ctx {
  node *nodes;
  size_t nnodes, capnodes;
  tr_term *argv;
  size_t nargv, capargv;
  tr_term *slots; /* hash-consing table: open addressing, 0 = empty, size a power of two */
  size_t nslots;
  symbol *syms;
  size_t nsyms, capsyms;
  uint32_t *symtab; /* symbol index + 1, by name and arity */
  size_t capsymtab;
  /* per-call memo tables, indexed by node and valid for the current generation */
  uint32_t *stamp, *seen; /* rebuild memo stamp; visit stamp (occurs check, variable walks) */
  tr_term *memo;
  size_t capmemo;
  uint32_t gen, seengen;
  pairslot *pairs; /* pairs of nodes already unified or compared in the current call */
  size_t npairs, cappairs;
  uint32_t pairgen;
  stack lent[3]; /* work-list buffers: walks, pairs, rebuilds */
};

static stack borrow(tr_ctx *c, int which) {
  stack p = c->lent[which];
  c->lent[which] = (stack){0};
  p.n = 0;
  return p;
}
static void give_back(tr_ctx *c, int which, stack p) {
  free(c->lent[which].v);
  c->lent[which] = p;
}

static const node *ND(const tr_ctx *c, tr_term t) { return &c->nodes[t]; }
static tr_term ARG(const tr_ctx *c, tr_term t, uint32_t i) { return c->argv[c->nodes[t].args + i]; }

static void rehash(tr_ctx *c) {
  size_t n = c->nslots ? 2 * c->nslots : 1024;
  tr_term *slots = xrealloc(NULL, n * sizeof *slots);
  memset(slots, 0, n * sizeof *slots);
  for (size_t t = 1; t < c->nnodes; t++) {
    size_t i = (size_t)c->nodes[t].hash & (n - 1);
    while (slots[i]) i = (i + 1) & (n - 1);
    slots[i] = (tr_term)t;
  }
  free(c->slots);
  c->slots = slots;
  c->nslots = n;
}

static void grow_memo(tr_ctx *c) {
  if (c->nnodes <= c->capmemo) return;
  size_t cap = c->capmemo ? c->capmemo : 1024;
  while (cap < c->nnodes) cap *= 2;
  c->stamp = xrealloc(c->stamp, cap * sizeof *c->stamp);
  c->seen = xrealloc(c->seen, cap * sizeof *c->seen);
  c->memo = xrealloc(c->memo, cap * sizeof *c->memo);
  memset(c->stamp + c->capmemo, 0, (cap - c->capmemo) * sizeof *c->stamp);
  memset(c->seen + c->capmemo, 0, (cap - c->capmemo) * sizeof *c->seen);
  c->capmemo = cap;
}

/* A new generation of the rebuild memo or of the visit stamps. */
static void next_gen(tr_ctx *c, uint32_t *gen, uint32_t *table) {
  if (++*gen == 0) {
    memset(table, 0, c->capmemo * sizeof *table);
    *gen = 1;
  }
}

static uint32_t umax(uint32_t a, uint32_t b) { return a > b ? a : b; }

/* `args` never points into c->argv. */
static tr_term intern(tr_ctx *c, tr_kind kind, uint64_t val, uint32_t nargs, const tr_term *args) {
  uint64_t h = mix(mix((uint64_t)kind, val), nargs);
  for (uint32_t i = 0; i < nargs; i++) h = mix(h, args[i]);
  if (2 * (c->nnodes + 1) >= c->nslots) rehash(c);
  size_t mask = c->nslots - 1, i = (size_t)h & mask;
  for (; c->slots[i]; i = (i + 1) & mask) {
    const node *n = &c->nodes[c->slots[i]];
    if (n->hash == h && n->kind == kind && n->val == val && n->nargs == nargs &&
        (nargs == 0 || memcmp(&c->argv[n->args], args, nargs * sizeof *args) == 0))
      return c->slots[i];
  }
  if (c->nnodes >= UINT32_MAX - 1 || c->nargv + nargs >= UINT32_MAX) {
    fputs("tcalc_ref: term table full\n", stderr);
    abort();
  }
  node nd = {(uint8_t)kind, 0, nargs, (uint32_t)c->nargv, 0, 0, 0, val, h};
  if (kind == TR_VAR) nd.flags = HAS_VAR, nd.maxvar = (uint32_t)val + 1;
  if (kind == TR_LOCAL) nd.flags = HAS_LOCAL, nd.maxlocal = (uint32_t)val + 1;
  if (kind == TR_FRESH) nd.flags = HAS_FRESH;
  if (kind == TR_NAME) nd.maxname = (uint32_t)val + 1;
  for (uint32_t k = 0; k < nargs; k++) {
    const node *a = &c->nodes[args[k]];
    nd.flags |= a->flags;
    nd.maxvar = umax(nd.maxvar, a->maxvar);
    nd.maxname = umax(nd.maxname, a->maxname);
    nd.maxlocal = umax(nd.maxlocal, a->maxlocal);
  }
  while (c->nargv + nargs > c->capargv) {
    c->capargv = c->capargv ? 2 * c->capargv : 1024;
    c->argv = xrealloc(c->argv, c->capargv * sizeof *c->argv);
  }
  if (nargs) memcpy(&c->argv[c->nargv], args, nargs * sizeof *args);
  c->nargv += nargs;
  GROW(c->nodes, c->nnodes, c->capnodes);
  tr_term t = (tr_term)c->nnodes++;
  c->nodes[t] = nd;
  c->slots[i] = t;
  grow_memo(c);
  return t;
}

tr_ctx *tr_ctx_new(void) {
  tr_ctx *c = xrealloc(NULL, sizeof *c);
  memset(c, 0, sizeof *c);
  GROW(c->nodes, c->nnodes, c->capnodes);
  c->nodes[0] = (node){0xff, 0, 0, 0, 0, 0, 0, 0, 0}; /* TR_NONE */
  c->nnodes = 1;
  rehash(c);
  grow_memo(c);
  return c;
}

void tr_ctx_free(tr_ctx *c) {
  if (!c) return;
  for (size_t i = 0; i < c->nsyms; i++) free(c->syms[i].name);
  free(c->syms);
  free(c->symtab);
  free(c->nodes);
  free(c->argv);
  free(c->slots);
  free(c->stamp);
  free(c->seen);
  free(c->memo);
  free(c->pairs);
  for (int i = 0; i < 3; i++) free(c->lent[i].v);
  free(c);
}

size_t tr_ctx_terms(const tr_ctx *c) { return c->nnodes - 1; }

static uint64_t symbol_hash(const char *name, uint32_t arity) {
  uint64_t h = arity;
  for (const unsigned char *p = (const unsigned char *)name; *p; p++) h = mix(h, *p);
  return h;
}

uint32_t tr_symbol(tr_ctx *c, const char *name, uint32_t arity) {
  if (2 * (c->nsyms + 1) > c->capsymtab) {
    size_t cap = c->capsymtab ? 2 * c->capsymtab : 64;
    uint32_t *tab = xrealloc(NULL, cap * sizeof *tab);
    memset(tab, 0, cap * sizeof *tab);
    for (size_t i = 0; i < c->nsyms; i++) {
      size_t j = (size_t)symbol_hash(c->syms[i].name, c->syms[i].arity) & (cap - 1);
      while (tab[j]) j = (j + 1) & (cap - 1);
      tab[j] = (uint32_t)i + 1;
    }
    free(c->symtab);
    c->symtab = tab;
    c->capsymtab = cap;
  }
  size_t j = (size_t)symbol_hash(name, arity) & (c->capsymtab - 1);
  for (; c->symtab[j]; j = (j + 1) & (c->capsymtab - 1)) {
    const symbol *s = &c->syms[c->symtab[j] - 1];
    if (s->arity == arity && strcmp(s->name, name) == 0) return c->symtab[j] - 1;
  }
  GROW(c->syms, c->nsyms, c->capsyms);
  size_t len = strlen(name) + 1;
  c->syms[c->nsyms] = (symbol){memcpy(xrealloc(NULL, len), name, len), arity};
  c->symtab[j] = (uint32_t)c->nsyms + 1;
  return (uint32_t)c->nsyms++;
}

const char *tr_symbol_name(const tr_ctx *c, uint32_t s) { return c->syms[s].name; }
uint32_t tr_symbol_arity(const tr_ctx *c, uint32_t s) { return c->syms[s].arity; }

tr_term tr_app(tr_ctx *c, uint32_t sym, const tr_term *args) {
  return intern(c, TR_APP, sym, c->syms[sym].arity, args);
}
tr_term tr_const(tr_ctx *c, const char *name) { return tr_app(c, tr_symbol(c, name, 0), NULL); }
tr_term tr_code(tr_ctx *c, int64_t v) { return intern(c, TR_CODE, (uint64_t)v, 0, NULL); }
tr_term tr_name(tr_ctx *c, uint32_t i) { return intern(c, TR_NAME, i, 0, NULL); }
tr_term tr_var(tr_ctx *c, uint32_t i) { return intern(c, TR_VAR, i, 0, NULL); }
tr_term tr_local(tr_ctx *c, uint32_t i) { return intern(c, TR_LOCAL, i, 0, NULL); }
tr_term tr_fresh(tr_ctx *c, uint32_t i) { return intern(c, TR_FRESH, i, 0, NULL); }

tr_kind tr_term_kind(const tr_ctx *c, tr_term t) { return (tr_kind)c->nodes[t].kind; }
uint32_t tr_term_symbol(const tr_ctx *c, tr_term t) { return (uint32_t)c->nodes[t].val; }
uint32_t tr_term_arity(const tr_ctx *c, tr_term t) { return c->nodes[t].nargs; }
tr_term tr_term_arg(const tr_ctx *c, tr_term t, uint32_t i) { return ARG(c, t, i); }
int64_t tr_term_code(const tr_ctx *c, tr_term t) { return (int64_t)c->nodes[t].val; }
uint32_t tr_term_index(const tr_ctx *c, tr_term t) { return (uint32_t)c->nodes[t].val; }

/* The pair memo: true when (a, b) is new in the current call. */
static void pairs_begin(tr_ctx *c) {
  if (++c->pairgen == 0) {
    memset(c->pairs, 0, c->cappairs * sizeof *c->pairs);
    c->pairgen = 1;
  }
  c->npairs = 0;
}
static bool pairs_add(tr_ctx *c, tr_term a, tr_term b) {
  if (2 * (c->npairs + 1) > c->cappairs) {
    size_t cap = c->cappairs ? 2 * c->cappairs : 256;
    pairslot *old = c->pairs, *nw = xrealloc(NULL, cap * sizeof *nw);
    memset(nw, 0, cap * sizeof *nw);
    for (size_t i = 0; i < c->cappairs; i++)
      if (old[i].gen == c->pairgen) {
        size_t j = (size_t)mix(0, old[i].key) & (cap - 1);
        while (nw[j].gen == c->pairgen) j = (j + 1) & (cap - 1);
        nw[j] = old[i];
      }
    free(old);
    c->pairs = nw;
    c->cappairs = cap;
  }
  uint64_t key = (uint64_t)a << 32 | b;
  size_t j = (size_t)mix(0, key) & (c->cappairs - 1);
  for (; c->pairs[j].gen == c->pairgen; j = (j + 1) & (c->cappairs - 1))
    if (c->pairs[j].key == key) return false;
  c->pairs[j] = (pairslot){key, c->pairgen};
  c->npairs++;
  return true;
}

/* An argument buffer: on the stack for small arities, on the heap otherwise. */
typedef struct {
  tr_term small[8];
  tr_term *v;
} argbuf;
static tr_term *argbuf_init(argbuf *b, uint32_t n) {
  b->v = n <= 8 ? b->small : xrealloc(NULL, n * sizeof *b->v);
  return b->v;
}
static void argbuf_done(argbuf *b) {
  if (b->v != b->small) free(b->v);
}

/* ============================================================================================
 * The test reader and the printer.
 * ========================================================================================== */

struct tr_scope {
  char **names;
  uint32_t n, cap;
};

tr_scope *tr_scope_new(void) {
  tr_scope *s = xrealloc(NULL, sizeof *s);
  memset(s, 0, sizeof *s);
  return s;
}
void tr_scope_free(tr_scope *s) {
  if (!s) return;
  for (uint32_t i = 0; i < s->n; i++) free(s->names[i]);
  free(s->names);
  free(s);
}
uint32_t tr_scope_size(const tr_scope *s) { return s->n; }

static uint32_t scope_local(tr_scope *s, const char *name, size_t len) {
  if (name)
    for (uint32_t i = 0; i < s->n; i++)
      if (s->names[i] && strlen(s->names[i]) == len && memcmp(s->names[i], name, len) == 0) return i;
  GROW(s->names, s->n, s->cap);
  s->names[s->n] = NULL;
  if (name) {
    s->names[s->n] = xrealloc(NULL, len + 1);
    memcpy(s->names[s->n], name, len);
    s->names[s->n][len] = 0;
  }
  return s->n++;
}

typedef struct {
  const char *p;
  bool bad;
  tr_ctx *c;
  tr_scope *sc;
} reader;

static void skip(reader *r) {
  while (isspace((unsigned char)*r->p)) r->p++;
}

static int64_t number(reader *r) {
  bool neg = *r->p == '-';
  if (neg) r->p++;
  if (!isdigit((unsigned char)*r->p)) r->bad = true;
  uint64_t v = 0;
  while (isdigit((unsigned char)*r->p)) v = v * 10 + (uint64_t)(*r->p++ - '0');
  return neg ? -(int64_t)v : (int64_t)v;
}

static tr_term read_term(reader *r) {
  skip(r);
  char ch = *r->p;
  if (ch == '-' || isdigit((unsigned char)ch)) return tr_code(r->c, number(r));
  if (ch == '$' || ch == '@' || ch == '#') {
    r->p++;
    int64_t i = number(r);
    if (i < 0 || i > (int64_t)UINT32_MAX) r->bad = true;
    return ch == '$' ? tr_var(r->c, (uint32_t)i) : ch == '@' ? tr_name(r->c, (uint32_t)i) : tr_fresh(r->c, (uint32_t)i);
  }
  const char *start = r->p;
  while (isalnum((unsigned char)*r->p) || *r->p == '_') r->p++;
  size_t len = (size_t)(r->p - start);
  if (!len) {
    r->bad = true;
    return TR_NONE;
  }
  if (len == 1 && *start == '_') return tr_local(r->c, scope_local(r->sc, NULL, 0));
  if (isupper((unsigned char)*start) || *start == '_') return tr_local(r->c, scope_local(r->sc, start, len));
  char *name = xrealloc(NULL, len + 1);
  memcpy(name, start, len);
  name[len] = 0;
  skip(r);
  tr_term *args = NULL, t = TR_NONE;
  uint32_t n = 0, cap = 0;
  if (*r->p == '(') {
    r->p++;
    for (;;) {
      tr_term a = read_term(r);
      GROW(args, n, cap);
      args[n++] = a;
      skip(r);
      if (*r->p == ',') {
        r->p++;
        continue;
      }
      if (*r->p == ')') r->p++;
      else r->bad = true;
      break;
    }
  }
  if (!r->bad) t = tr_app(r->c, tr_symbol(r->c, name, n), args);
  free(args);
  free(name);
  return t;
}

tr_term tr_read(tr_ctx *c, tr_scope *sc, const char *text) {
  reader r = {text, false, c, sc};
  tr_term t = read_term(&r);
  skip(&r);
  return (r.bad || *r.p) ? TR_NONE : t;
}

void tr_print(FILE *out, const tr_ctx *c, tr_term t) {
  const node *n = ND(c, t);
  switch ((tr_kind)n->kind) {
  case TR_CODE: fprintf(out, "%lld", (long long)(int64_t)n->val); return;
  case TR_NAME: fprintf(out, "@%llu", (unsigned long long)n->val); return;
  case TR_VAR: fprintf(out, "$%llu", (unsigned long long)n->val); return;
  case TR_LOCAL: fprintf(out, "L%llu", (unsigned long long)n->val); return;
  case TR_FRESH: fprintf(out, "#%llu", (unsigned long long)n->val); return;
  case TR_APP:
    fputs(c->syms[n->val].name, out);
    if (!n->nargs) return;
    fputc('(', out);
    for (uint32_t i = 0; i < n->nargs; i++) {
      if (i) fputc(',', out);
      tr_print(out, c, ARG(c, t, i));
    }
    fputc(')', out);
    return;
  }
  fputs("?", out);
}

/* ============================================================================================
 * Hash tables of 64-bit keys: the identity -> slot map of a state, the head index, and sets
 * for one decision.  Keys are never 0; TOMB marks a deleted entry.
 * ========================================================================================== */

#define TOMB UINT64_MAX

typedef struct {
  uint64_t *key;
  uint32_t *val;
  size_t cap, used; /* used counts live entries and tombstones */
} u64map;

static size_t u64map_find(const u64map *m, uint64_t k) {
  if (!m->cap) return SIZE_MAX;
  for (size_t j = (size_t)mix(1, k) & (m->cap - 1);; j = (j + 1) & (m->cap - 1)) {
    if (m->key[j] == k) return j;
    if (!m->key[j]) return SIZE_MAX;
  }
}

static void u64map_put(u64map *m, uint64_t k, uint32_t v) {
  if (2 * (m->used + 1) > m->cap) { /* rehash to four times the live entries: tombstones go */
    u64map old = *m;
    size_t live = 0;
    for (size_t i = 0; i < old.cap; i++) live += old.key[i] && old.key[i] != TOMB;
    m->cap = 64;
    while (4 * (live + 1) > m->cap) m->cap *= 2;
    m->key = xrealloc(NULL, m->cap * sizeof *m->key);
    m->val = xrealloc(NULL, m->cap * sizeof *m->val);
    memset(m->key, 0, m->cap * sizeof *m->key);
    m->used = 0;
    for (size_t i = 0; i < old.cap; i++)
      if (old.key[i] && old.key[i] != TOMB) u64map_put(m, old.key[i], old.val[i]);
    free(old.key);
    free(old.val);
  }
  size_t j = (size_t)mix(1, k) & (m->cap - 1);
  while (m->key[j] && m->key[j] != TOMB && m->key[j] != k) j = (j + 1) & (m->cap - 1);
  if (!m->key[j]) m->used++;
  m->key[j] = k;
  m->val[j] = v;
}

static void u64map_del(u64map *m, uint64_t k) {
  size_t j = u64map_find(m, k);
  if (j != SIZE_MAX) m->key[j] = TOMB;
}

static void u64map_free(u64map *m) {
  free(m->key);
  free(m->val);
}

static u64map u64map_clone(const u64map *m) {
  u64map c = *m;
  c.key = DUP(m->key, m->cap);
  c.val = DUP(m->val, m->cap);
  return c;
}

/* ============================================================================================
 * States.  The frame declares variables 0 .. nvars-1 (bind[v] != TR_NONE once a settlement has
 * instantiated v) and has minted names 0 .. nnames-1; its disequations are watched by their
 * free variables.  Present occurrences live in slots, linked in the order they were made and
 * in one list per label head.  `env` holds the locals of the firing being decided.
 * ========================================================================================== */

#define NIL UINT32_MAX
#define LOCAL_BIT 0x80000000u /* a trail entry for a local */

typedef struct {
  tr_occ id;
  tr_term label;
  uint32_t schema;       /* private variables of a stored schema; 0 for a shared row */
  uint32_t prev, next;   /* the order of making */
  uint32_t hprev, hnext; /* the head bucket */
  uint32_t bucket;
} slot;

typedef struct {
  uint32_t first, last, count;
} bucket;

typedef struct {
  tr_term left, right;
  bool live;
} diseq;

typedef struct {
  uint32_t diseq, next;
} watch;

struct tr_state {
  tr_ctx *ctx;
  tr_term *bind;     /* per variable */
  uint32_t *watched; /* per variable: first watch entry */
  uint32_t nvars, capbind;
  uint32_t nnames;
  tr_term *env; /* per local of the firing under decision */
  uint32_t capenv;
  diseq *ds;
  size_t nds, capds, live_ds;
  watch *ws;
  size_t nws, capws;
  slot *sl;
  size_t nsl, capsl;
  uint32_t freeslot, first, last;
  size_t count;
  u64map ids;   /* identity -> slot */
  u64map heads; /* head key -> bucket; bucket 0 holds labels whose head is open */
  bucket *bk;
  size_t nbk, capbk;
  tr_occ next_id;
  uint32_t *trail; /* variables and locals bound since the decision began */
  size_t ntrail, captrail;
  const tr_eq *told; /* the disequations told by the firing under decision */
  size_t ntold;
};

tr_state *tr_state_new(tr_ctx *c) {
  tr_state *s = xrealloc(NULL, sizeof *s);
  memset(s, 0, sizeof *s);
  s->ctx = c;
  s->next_id = 1;
  s->freeslot = s->first = s->last = NIL;
  GROW(s->bk, s->nbk, s->capbk);
  s->bk[s->nbk++] = (bucket){NIL, NIL, 0};
  return s;
}

tr_state *tr_state_clone(const tr_state *s) {
  tr_state *t = xrealloc(NULL, sizeof *t);
  *t = *s;
  t->bind = DUP(s->bind, s->capbind);
  t->watched = DUP(s->watched, s->capbind);
  t->env = NULL;
  t->capenv = 0;
  t->ds = DUP(s->ds, s->nds);
  t->capds = s->nds;
  t->ws = DUP(s->ws, s->nws);
  t->capws = s->nws;
  t->sl = DUP(s->sl, s->nsl);
  t->capsl = s->nsl;
  t->ids = u64map_clone(&s->ids);
  t->heads = u64map_clone(&s->heads);
  t->bk = DUP(s->bk, s->nbk);
  t->capbk = s->nbk;
  t->trail = NULL;
  t->ntrail = t->captrail = 0;
  return t;
}

void tr_state_free(tr_state *s) {
  if (!s) return;
  free(s->bind);
  free(s->watched);
  free(s->env);
  free(s->ds);
  free(s->ws);
  free(s->sl);
  u64map_free(&s->ids);
  u64map_free(&s->heads);
  free(s->bk);
  free(s->trail);
  free(s);
}

tr_ctx *tr_state_ctx(const tr_state *s) { return s->ctx; }
uint32_t tr_vars(const tr_state *s) { return s->nvars; }
uint32_t tr_names(const tr_state *s) { return s->nnames; }
size_t tr_present_count(const tr_state *s) { return s->count; }
size_t tr_apart_count(const tr_state *s) { return s->live_ds; }
bool tr_bound(const tr_state *s, uint32_t v) { return v < s->nvars && s->bind[v] != TR_NONE; }

bool tr_state_equal(const tr_state *a, const tr_state *b) {
  if (a->ctx != b->ctx || a->nvars != b->nvars || a->nnames != b->nnames || a->count != b->count ||
      a->live_ds != b->live_ds || a->next_id != b->next_id)
    return false;
  for (uint32_t v = 0; v < a->nvars; v++)
    if (a->bind[v] != b->bind[v]) return false;
  for (size_t i = 0, j = 0;; i++, j++) {
    while (i < a->nds && !a->ds[i].live) i++;
    while (j < b->nds && !b->ds[j].live) j++;
    if (i >= a->nds || j >= b->nds) {
      if (i < a->nds || j < b->nds) return false;
      break;
    }
    if (a->ds[i].left != b->ds[j].left || a->ds[i].right != b->ds[j].right) return false;
  }
  for (uint32_t i = a->first, j = b->first; i != NIL || j != NIL; i = a->sl[i].next, j = b->sl[j].next) {
    if (i == NIL || j == NIL) return false;
    if (a->sl[i].id != b->sl[j].id || a->sl[i].label != b->sl[j].label || a->sl[i].schema != b->sl[j].schema)
      return false;
  }
  return true;
}

static uint32_t find_slot(const tr_state *s, tr_occ id) {
  if (!id || id == TOMB) return NIL; /* never an identity */
  size_t j = u64map_find(&s->ids, id);
  return j == SIZE_MAX ? NIL : s->ids.val[j];
}

static uint32_t grow_to(uint32_t cap, uint64_t n) {
  if (n > UINT32_MAX) {
    fputs("tcalc_ref: too many variables\n", stderr);
    abort();
  }
  if (!cap) cap = 64;
  while (cap < n) cap = cap > UINT32_MAX / 2 ? UINT32_MAX : 2 * cap;
  return cap;
}

/* Room for variables 0 .. n-1; new variables are unbound and watch nothing. */
static void ensure_vars(tr_state *s, uint64_t n) {
  if (n <= s->capbind) return;
  uint32_t cap = grow_to(s->capbind, n);
  s->bind = xrealloc(s->bind, (size_t)cap * sizeof *s->bind);
  s->watched = xrealloc(s->watched, (size_t)cap * sizeof *s->watched);
  for (uint32_t v = s->capbind; v < cap; v++) s->bind[v] = TR_NONE, s->watched[v] = NIL;
  s->capbind = cap;
}

/* Room for locals 0 .. n-1, unbound. */
static void ensure_env(tr_state *s, uint64_t n) {
  if (n <= s->capenv) return;
  uint32_t cap = grow_to(s->capenv, n);
  s->env = xrealloc(s->env, (size_t)cap * sizeof *s->env);
  for (uint32_t v = s->capenv; v < cap; v++) s->env[v] = TR_NONE;
  s->capenv = cap;
}

/* ============================================================================================
 * Solutions: the theory.  The step asks the theory exactly three things, the Frames interface:
 *   unify     Solvable, with its principal answer: extend the bindings to a most general
 *             solution of a = b, or fail                        (Frames.Solvable, Principal)
 *   same      Entails of an equation: a = b at every solution    (Frames.Entails)
 *   possible  Solvable of an extension, separating the frame     (Disequality.solvable_iff)
 * The theory here is syntactic equality of first-order terms (Frames.ofSubstitution of the
 * first-order action, which is faithful: LawfulFirstOrder.firstOrder_faithful): a store is
 * solvable exactly when it unifies with the occurs check and its most general unifier separates
 * the frame's disequations (Disequality.solvable_iff_separates).  Another theory can replace
 * these three functions when its solutions have principal answers that are substitutions
 * (what the bindings record) and it equates only terms of one head (what the head index
 * assumes); the guards' decisions below then hold unchanged.  During a decision the firing's
 * locals are variables too, bound in `env`.
 * ========================================================================================== */

static tr_term binding(const tr_state *s, const node *n) {
  if (n->kind == TR_VAR) return n->val < s->capbind ? s->bind[n->val] : TR_NONE;
  if (n->kind == TR_LOCAL) return n->val < s->capenv ? s->env[n->val] : TR_NONE;
  return TR_NONE;
}

static tr_term deref(const tr_state *s, tr_term t) {
  for (tr_term b; (b = binding(s, ND(s->ctx, t))) != TR_NONE;) t = b;
  return t;
}

static bool is_var(const node *n) { return n->kind == TR_VAR || n->kind == TR_LOCAL; }

static void push(stack *p, tr_term a) {
  GROW(p->v, p->n, p->cap);
  p->v[p->n++] = a;
}
static void push2(stack *p, tr_term a, tr_term b) {
  push(p, a);
  push(p, b);
}

/* Does the unbound variable or local x occur in t?  Each node is visited once. */
static bool occurs(const tr_state *s, tr_term x, tr_term t) {
  tr_ctx *c = s->ctx;
  next_gen(c, &c->seengen, c->seen);
  stack p = borrow(c, 0);
  push(&p, t);
  bool found = false;
  while (!found && p.n) {
    tr_term u = deref(s, p.v[--p.n]);
    const node *n = ND(c, u);
    if (!(n->flags & OPEN) || c->seen[u] == c->seengen) continue;
    c->seen[u] = c->seengen;
    found = u == x;
    for (uint32_t i = 0; i < n->nargs; i++) push(&p, ARG(c, u, i));
  }
  give_back(c, 0, p);
  return found;
}

static void bind_node(tr_state *s, tr_term x, tr_term t) {
  const node *n = ND(s->ctx, x);
  GROW(s->trail, s->ntrail, s->captrail);
  if (n->kind == TR_VAR) {
    s->bind[n->val] = t;
    s->trail[s->ntrail++] = (uint32_t)n->val;
  } else {
    s->env[n->val] = t;
    s->trail[s->ntrail++] = (uint32_t)n->val | LOCAL_BIT;
  }
}

static void undo(tr_state *s, size_t mark) {
  while (s->ntrail > mark) {
    uint32_t e = s->trail[--s->ntrail];
    if (e & LOCAL_BIT) s->env[e & ~LOCAL_BIT] = TR_NONE;
    else s->bind[e] = TR_NONE;
  }
}

/* Of two unbound variables, which to bind: a local before a frame variable, then the later. */
static bool bind_first(const node *x, const node *y) {
  if (x->kind != y->kind) return x->kind == TR_LOCAL;
  return x->val > y->val;
}

/* Extends the bindings to a most general unifier of a = b, or fails (the caller undoes). */
static bool unify(tr_state *s, tr_term a, tr_term b) {
  tr_ctx *c = s->ctx;
  stack p = borrow(c, 1);
  push2(&p, a, b);
  pairs_begin(c);
  bool ok = true;
  while (ok && p.n) {
    tr_term y = deref(s, p.v[--p.n]), x = deref(s, p.v[--p.n]);
    if (x == y) continue;
    const node *nx = ND(c, x), *ny = ND(c, y);
    if (!((nx->flags | ny->flags) & OPEN)) ok = false; /* distinct terms without variables */
    else if (is_var(nx) && is_var(ny)) {
      if (bind_first(nx, ny)) bind_node(s, x, y);
      else bind_node(s, y, x);
    } else if (is_var(nx))
      ok = !occurs(s, x, y) && (bind_node(s, x, y), true);
    else if (is_var(ny))
      ok = !occurs(s, y, x) && (bind_node(s, y, x), true);
    else if (nx->kind == TR_APP && ny->kind == TR_APP && nx->val == ny->val) {
      if (pairs_add(c, x, y))
        for (uint32_t i = 0; i < nx->nargs; i++) push2(&p, ARG(c, x, i), ARG(c, y, i));
    } else
      ok = false; /* distinct symbols, codes or names */
  }
  give_back(c, 1, p);
  return ok;
}

/* Identical under the bindings: equal at every solution. */
static bool same(const tr_state *s, tr_term a, tr_term b) {
  tr_ctx *c = s->ctx;
  stack p = borrow(c, 1);
  push2(&p, a, b);
  pairs_begin(c);
  bool ok = true;
  while (ok && p.n) {
    tr_term y = deref(s, p.v[--p.n]), x = deref(s, p.v[--p.n]);
    if (x == y) continue;
    const node *nx = ND(c, x), *ny = ND(c, y);
    ok = nx->kind == TR_APP && ny->kind == TR_APP && nx->val == ny->val && ((nx->flags | ny->flags) & OPEN);
    if (ok && pairs_add(c, x, y))
      for (uint32_t i = 0; i < nx->nargs; i++) push2(&p, ARG(c, x, i), ARG(c, y, i));
  }
  give_back(c, 1, p);
  return ok;
}

/* Rebuilding a term: memoized by node, with an explicit stack, so shared subterms are rebuilt
 * once and deep terms need no deep recursion.  Three rebuilds:
 *   RESOLVE     the bindings applied: the term at the frame.  `env` reads the decision's locals
 *               (a stored schema's private locals are never read through it); `promote`, at a
 *               result, turns each local still unbound into a new variable of the frame.
 *   OPEN_FRESH  FRESH j written as the name base + j that the firing mints.
 *   SCHEMA      a stored schema's private LOCAL i < n written as the decision's local base + i. */
typedef enum { RESOLVE, OPEN_FRESH, SCHEMA } rebuild_mode;
typedef struct {
  rebuild_mode mode;
  bool env;
  uint32_t *promote; /* RESOLVE at a result: per local, the variable it becomes, or NIL */
  uint32_t *nvars;
  uint32_t base, n;
} rebuild;

static bool unchanged(const rebuild *rb, const node *n) {
  switch (rb->mode) {
  case RESOLVE: return !(n->flags & (rb->env ? OPEN : HAS_VAR));
  case OPEN_FRESH: return !(n->flags & HAS_FRESH);
  default: return !(n->flags & HAS_LOCAL);
  }
}

/* A node that is not an application: its result, or TR_NONE with *via a term whose result is
 * its result (a binding to follow). */
static tr_term leaf(tr_state *s, const rebuild *rb, tr_term t, tr_term *via) {
  tr_ctx *c = s->ctx;
  const node *n = ND(c, t);
  uint64_t kind = n->kind, val = n->val;
  *via = TR_NONE;
  if (rb->mode == OPEN_FRESH) return kind == TR_FRESH ? tr_name(c, rb->base + (uint32_t)val) : t;
  if (rb->mode == SCHEMA) return kind == TR_LOCAL && val < rb->n ? tr_local(c, rb->base + (uint32_t)val) : t;
  tr_term b = kind == TR_LOCAL && !rb->env ? TR_NONE : binding(s, n);
  if (b != TR_NONE) {
    *via = b;
    return TR_NONE;
  }
  if (kind != TR_LOCAL || !rb->promote) return t;
  if (rb->promote[val] == NIL) {
    rb->promote[val] = (*rb->nvars)++;
    ensure_vars(s, *rb->nvars);
  }
  return tr_var(c, rb->promote[val]);
}

static tr_term rebuild_term(tr_state *s, const rebuild *rb, tr_term root) {
  tr_ctx *c = s->ctx;
  if (unchanged(rb, ND(c, root))) return root;
  next_gen(c, &c->gen, c->stamp);
  stack p = borrow(c, 2);
  push(&p, root);
  while (p.n) {
    tr_term t = p.v[p.n - 1], r = t;
    if (c->stamp[t] == c->gen) {
      p.n--;
      continue;
    }
    uint32_t kind = ND(c, t)->kind, k = ND(c, t)->nargs, sym = (uint32_t)ND(c, t)->val;
    if (unchanged(rb, ND(c, t))) {
      /* the term itself */
    } else if (kind != TR_APP) {
      tr_term via;
      r = leaf(s, rb, t, &via);
      if (r == TR_NONE) {
        if (c->stamp[via] != c->gen && !unchanged(rb, ND(c, via))) {
          push(&p, via);
          continue;
        }
        r = c->stamp[via] == c->gen ? c->memo[via] : via;
      }
    } else {
      bool ready = true;
      for (uint32_t i = k; i-- > 0;) {
        tr_term a = ARG(c, t, i);
        if (c->stamp[a] != c->gen && !unchanged(rb, ND(c, a))) {
          push(&p, a);
          ready = false;
        }
      }
      if (!ready) continue;
      argbuf b;
      tr_term *args = argbuf_init(&b, k);
      bool changed = false;
      for (uint32_t i = 0; i < k; i++) {
        tr_term a = ARG(c, t, i);
        args[i] = c->stamp[a] == c->gen ? c->memo[a] : a;
        changed |= args[i] != a;
      }
      if (changed) r = tr_app(c, sym, args);
      argbuf_done(&b);
    }
    c->stamp[t] = c->gen;
    c->memo[t] = r;
    p.n--;
  }
  give_back(c, 2, p);
  return c->memo[root];
}

tr_term tr_resolve(const tr_state *s, tr_term t) {
  rebuild rb = {RESOLVE, false, NULL, NULL, 0, 0};
  return rebuild_term((tr_state *)s, &rb, t);
}

/* The term at the most general unifier of the decision under way. */
static tr_term resolve_in(tr_state *s, tr_term t) {
  rebuild rb = {RESOLVE, true, NULL, NULL, 0, 0};
  return rebuild_term(s, &rb, t);
}

/* Separation (Disequality.Separates) after the bindings since the decision began: the told
 * disequations, and those watched by a variable bound since then. */
static bool separated(const tr_state *s) {
  for (size_t i = 0; i < s->ntold; i++)
    if (same(s, s->told[i].left, s->told[i].right)) return false;
  for (size_t i = 0; i < s->ntrail; i++) {
    if (s->trail[i] & LOCAL_BIT) continue;
    for (uint32_t w = s->watched[s->trail[i]]; w != NIL; w = s->ws[w].next) {
      const diseq *d = &s->ds[s->ws[w].diseq];
      if (d->live && same(s, d->left, d->right)) return false;
    }
  }
  return true;
}

/* Is a = b at some solution that separates the frame?  Changes nothing. */
static bool possible(tr_state *s, tr_term a, tr_term b) {
  size_t mark = s->ntrail;
  bool ok = unify(s, a, b) && separated(s);
  undo(s, mark);
  return ok;
}

/* File disequation d at the frame: dropped when its sides are distinct without variables
 * (every solution separates it), otherwise watched by the free variables of its sides. */
static void file_diseq(tr_state *s, uint32_t d) {
  tr_ctx *c = s->ctx;
  tr_term l = tr_resolve(s, s->ds[d].left), r = tr_resolve(s, s->ds[d].right);
  if (!((ND(c, l)->flags | ND(c, r)->flags) & HAS_VAR)) {
    if (s->ds[d].live) s->live_ds--;
    s->ds[d].live = false;
    return;
  }
  next_gen(c, &c->seengen, c->seen);
  stack p = borrow(c, 0);
  push2(&p, l, r);
  while (p.n) {
    tr_term t = p.v[--p.n];
    const node *n = ND(c, t);
    if (!(n->flags & HAS_VAR) || c->seen[t] == c->seengen) continue;
    c->seen[t] = c->seengen;
    if (n->kind == TR_VAR) {
      GROW(s->ws, s->nws, s->capws);
      s->ws[s->nws] = (watch){d, s->watched[n->val]};
      s->watched[n->val] = (uint32_t)s->nws++;
    }
    for (uint32_t i = 0; i < n->nargs; i++) push(&p, ARG(c, t, i));
  }
  give_back(c, 0, p);
}

/* ============================================================================================
 * The present occurrences: slots, the order of making, and head buckets.
 * ========================================================================================== */

static uint64_t head_key(const tr_state *s, tr_term t) {
  const node *n = ND(s->ctx, deref(s, t));
  switch ((tr_kind)n->kind) {
  case TR_APP: return mix(11, n->val) | 1;
  case TR_CODE: return mix(13, n->val) | 1;
  case TR_NAME: return mix(17, n->val) | 1;
  default: return 0; /* an open head: a variable, or a schema's private variable */
  }
}

static uint32_t bucket_of(tr_state *s, uint64_t key, bool create) {
  if (!key) return 0;
  size_t j = u64map_find(&s->heads, key);
  if (j != SIZE_MAX) return s->heads.val[j];
  if (!create) return NIL;
  GROW(s->bk, s->nbk, s->capbk);
  s->bk[s->nbk] = (bucket){NIL, NIL, 0};
  u64map_put(&s->heads, key, (uint32_t)s->nbk);
  return (uint32_t)s->nbk++;
}

static void add_occ(tr_state *s, tr_occ id, tr_term label, uint32_t schema) {
  uint32_t i;
  if (s->freeslot != NIL) {
    i = s->freeslot;
    s->freeslot = s->sl[i].next;
  } else {
    GROW(s->sl, s->nsl, s->capsl);
    i = (uint32_t)s->nsl++;
  }
  uint32_t b = bucket_of(s, schema && ND(s->ctx, label)->kind != TR_APP ? 0 : head_key(s, label), true);
  s->sl[i] = (slot){id, label, schema, s->last, NIL, s->bk[b].last, NIL, b};
  if (s->last != NIL) s->sl[s->last].next = i;
  else s->first = i;
  s->last = i;
  if (s->bk[b].last != NIL) s->sl[s->bk[b].last].hnext = i;
  else s->bk[b].first = i;
  s->bk[b].last = i;
  s->bk[b].count++;
  s->count++;
  u64map_put(&s->ids, id, i);
}

static void remove_occ(tr_state *s, uint32_t i) {
  slot *o = &s->sl[i];
  bucket *b = &s->bk[o->bucket];
  if (o->prev != NIL) s->sl[o->prev].next = o->next;
  else s->first = o->next;
  if (o->next != NIL) s->sl[o->next].prev = o->prev;
  else s->last = o->prev;
  if (o->hprev != NIL) s->sl[o->hprev].hnext = o->hnext;
  else b->first = o->hnext;
  if (o->hnext != NIL) s->sl[o->hnext].hprev = o->hprev;
  else b->last = o->hprev;
  b->count--;
  s->count--;
  u64map_del(&s->ids, o->id);
  o->next = s->freeslot;
  s->freeslot = i;
}

/* A label at the frame; a stored schema is given as stored (its locals are its own). */
static tr_term label_at(const tr_state *s, uint32_t i) {
  return s->sl[i].schema ? s->sl[i].label : tr_resolve(s, s->sl[i].label);
}

tr_occ tr_next_present(const tr_state *s, tr_occ after, tr_term *label) {
  uint32_t i = after ? find_slot(s, after) : s->first;
  if (after && i != NIL) i = s->sl[i].next;
  if (i == NIL) return 0;
  if (label) *label = label_at(s, i);
  return s->sl[i].id;
}

/* The slots a pattern can match: its head bucket, then the open bucket; every slot when the
 * pattern's head is itself open.  `cursor` = NIL starts. */
static uint32_t next_candidate(const tr_state *s, tr_term pattern, uint32_t cursor) {
  uint64_t key = head_key(s, pattern);
  if (!key) return cursor == NIL ? s->first : s->sl[cursor].next;
  uint32_t b = bucket_of((tr_state *)s, key, false);
  uint32_t i;
  if (cursor == NIL) i = b == NIL ? NIL : s->bk[b].first;
  else i = s->sl[cursor].hnext;
  if (i == NIL && (cursor == NIL || s->sl[cursor].bucket != 0)) i = s->bk[0].first;
  return i;
}

tr_occ tr_next_candidate(const tr_state *s, tr_term pattern, tr_occ after, tr_term *label) {
  uint32_t cur = NIL;
  if (after) {
    cur = find_slot(s, after);
    if (cur == NIL) return 0;
  }
  uint32_t i = next_candidate(s, pattern, cur);
  if (i == NIL) return 0;
  if (label) *label = label_at(s, i);
  return s->sl[i].id;
}

bool tr_present(const tr_state *s, tr_occ id, tr_term *label) {
  uint32_t i = find_slot(s, id);
  if (i == NIL) return false;
  if (label) *label = label_at(s, i);
  return true;
}

/* ============================================================================================
 * The extension (EffectCore.extension, Helpers.extend).  A firing's terms live at its target
 * frame: the state's frame, the firing's locals and the names it mints.  A term that mentions a
 * variable not declared, a name not minted, or a local or fresh name the firing does not
 * declare is not a term of the target frame: the firing's shapes fail.  Every generative name
 * a caller supplies must therefore have been minted already.  Opening writes FRESH j as the
 * name it mints; locals stay locals until the result.
 * ========================================================================================== */

typedef struct {
  uint32_t locals;           /* LOCAL i, i < locals: the firing's locals */
  uint32_t base_name, fresh; /* FRESH j -> NAME(base_name + j), j < fresh */
  uint32_t keep_locals;      /* a stored schema: its LOCAL i < keep_locals are private */
} opening;

static tr_term open_term(tr_state *s, const opening *o, tr_term t, bool *ok) {
  if (t == TR_NONE || t >= s->ctx->nnodes) {
    *ok = false;
    return TR_NONE;
  }
  const node *n = ND(s->ctx, t);
  uint32_t locals = o->keep_locals ? o->keep_locals : o->locals;
  if (n->maxvar > s->nvars || n->maxname > s->nnames || n->maxlocal > locals ||
      ((n->flags & HAS_FRESH) && o->fresh == 0)) {
    *ok = false;
    return t;
  }
  if (!(n->flags & HAS_FRESH)) return t;
  rebuild rb = {OPEN_FRESH, false, NULL, NULL, o->base_name, 0};
  tr_term r = rebuild_term(s, &rb, t);
  /* a FRESH beyond the firing's own names is not a term of the target frame */
  if (ND(s->ctx, r)->maxname > o->base_name + o->fresh) *ok = false;
  return r;
}

/* A stored schema opened at a port's own scope: its private variables become the locals
 * base .. base+n-1 of the decision (ContextualStoredRows.prepared_read_store). */
static tr_term open_schema(tr_state *s, tr_term t, uint32_t n, uint32_t base) {
  rebuild rb = {SCHEMA, false, NULL, NULL, base, n};
  return rebuild_term(s, &rb, t);
}

/* ============================================================================================
 * Guards at every solution (Frames.Entails; Disequality.entails_iff).
 *
 * Let theta be the most general unifier of the information; it separates the frame (the firing
 * is prepared), so theta is itself a solution, and every solution factors through it.  A
 * present occurrence o and a pattern p are
 *   DEFINITE   when theta(p) and theta(label o) are identical: equal at every solution;
 *   IMPOSSIBLE when the information with p = label o has no solution separating the frame:
 *              they differ at every solution;
 *   POSSIBLE   otherwise: equal at the solution mgu(information, p = label o), which separates
 *              the frame, and different at the solution theta.
 * Count p n holds at every solution iff no occurrence is POSSIBLE and n occurrences are
 * DEFINITE: at theta the count is #DEFINITE, and at the solution that makes a POSSIBLE one
 * equal the count is larger.  Absence is count 0.  An ask a = b holds at every solution iff
 * theta(a) and theta(b) are identical (theta is a solution).  Only the pattern's head bucket
 * and the open bucket can hold a DEFINITE or POSSIBLE occurrence.
 * ========================================================================================== */

typedef enum { DEFINITE, IMPOSSIBLE, POSSIBLE, UNDETERMINED } match_class;

struct tr_view {
  tr_state *s;
  opening o;
  uint32_t scratch; /* first local free for scratch scopes */
};

/* Whether a guard pattern reads a stored schema is left open by the definition
 * (ContextualActivatedStep requires empty checks): a schema row that could match leaves the
 * guard without a verdict. */
static match_class classify(tr_view *v, tr_term pattern, const slot *o) {
  tr_state *s = v->s;
  if (o->schema) {
    ensure_env(s, (uint64_t)v->scratch + o->schema);
    tr_term opened = open_schema(s, o->label, o->schema, v->scratch);
    return possible(s, pattern, opened) ? UNDETERMINED : IMPOSSIBLE;
  }
  if (same(s, pattern, o->label)) return DEFINITE;
  return possible(s, pattern, o->label) ? POSSIBLE : IMPOSSIBLE;
}

/* 1 holds at every solution, 0 fails at some solution, -1 no verdict. */
static int count_entailed(tr_view *v, tr_term pattern, size_t number) {
  size_t definite = 0;
  bool undetermined = false;
  for (uint32_t i = next_candidate(v->s, pattern, NIL); i != NIL; i = next_candidate(v->s, pattern, i)) {
    match_class m = classify(v, pattern, &v->s->sl[i]);
    if (m == POSSIBLE) return 0;
    definite += m == DEFINITE;
    undetermined |= m == UNDETERMINED;
  }
  if (undetermined) return -1;
  return definite == number;
}

static tr_term view_label(tr_view *v, uint32_t i) {
  return v->s->sl[i].schema ? v->s->sl[i].label : resolve_in(v->s, v->s->sl[i].label);
}

static int query_entailed(tr_view *v, const tr_guard *g) {
  tr_state *s = v->s;
  u64map seen = {0};
  int out = 1;
  for (size_t j = 0; j < g->nseen; j++) {
    if (!g->seen[j] || g->seen[j] == TOMB) out = 0; /* never present */
    else u64map_put(&seen, g->seen[j], 0);
  }
  size_t inside = 0;
  for (uint32_t i = s->first; i != NIL && out; i = s->sl[i].next) {
    tr_member m = g->region(v, view_label(v, i), g->env);
    if (m == TR_DEPENDS) out = 0; /* the region differs between two solutions */
    else if (m == TR_IN) {
      if (u64map_find(&seen, s->sl[i].id) == SIZE_MAX) out = 0;
      inside++;
    }
  }
  size_t distinct = 0;
  for (size_t j = 0; j < seen.cap; j++) distinct += seen.key[j] && seen.key[j] != TOMB;
  u64map_free(&seen);
  return out && distinct == inside; /* the region holds exactly the occurrences seen */
}

static int guard_entailed(tr_view *v, const tr_guard *g, tr_term a, tr_term b) {
  switch (g->kind) {
  case TR_G_EQUAL: return same(v->s, a, b);
  case TR_G_ABSENT: return count_entailed(v, a, 0);
  case TR_G_COUNT: return count_entailed(v, a, g->number);
  case TR_G_QUERY: return g->region ? query_entailed(v, g) : 0;
  case TR_G_HOST: return g->entailed ? g->entailed(v, g->env) : 0;
  }
  return 0;
}

tr_ctx *tr_view_ctx(const tr_view *v) { return v->s->ctx; }

static tr_term view_open(tr_view *v, tr_term t, bool *ok) {
  *ok = true;
  return open_term(v->s, &v->o, t, ok);
}

tr_term tr_view_resolve(tr_view *v, tr_term t) {
  bool ok;
  tr_term r = view_open(v, t, &ok);
  return ok ? resolve_in(v->s, r) : TR_NONE;
}

bool tr_view_ground(tr_view *v, tr_term t) {
  tr_term r = tr_view_resolve(v, t);
  return r != TR_NONE && !(ND(v->s->ctx, r)->flags & OPEN);
}

bool tr_view_same(tr_view *v, tr_term a, tr_term b) {
  bool oka, okb;
  tr_term x = view_open(v, a, &oka), y = view_open(v, b, &okb);
  return oka && okb && same(v->s, x, y);
}

bool tr_view_possible(tr_view *v, tr_term a, tr_term b) {
  bool oka, okb;
  tr_term x = view_open(v, a, &oka), y = view_open(v, b, &okb);
  return oka && okb && possible(v->s, x, y);
}

bool tr_view_code(tr_view *v, tr_term t, int64_t *value) {
  tr_term r = tr_view_resolve(v, t);
  if (r == TR_NONE || ND(v->s->ctx, r)->kind != TR_CODE) return false;
  *value = (int64_t)ND(v->s->ctx, r)->val;
  return true;
}

tr_occ tr_view_next_present(tr_view *v, tr_occ after, tr_term *label) {
  tr_state *s = v->s;
  uint32_t i = after ? find_slot(s, after) : s->first;
  if (after && i != NIL) i = s->sl[i].next;
  if (i == NIL) return 0;
  if (label) *label = view_label(v, i);
  return s->sl[i].id;
}

/* ============================================================================================
 * Admission (Step.Standard.admits_iff) and the result (Step.result).
 *
 *   Shapes    the terms of the firing are terms of its target frame; takes are distinct; the
 *             identities it makes are distinct (AnnotatedRuns.firstOrder.Shapes); the told
 *             disequations with the frame's form a frame (Disequality.Firing.formed).
 *   Fits      what it takes and reads is present, nothing is both taken and read, what it makes
 *             is fresh (OccurrenceCommits.Enabled of Selection.commit).
 *   Solvable  the information -- the old knowledge carried along the extension (identities, see
 *             tcalc_ref.h), take pattern = label, read pattern = label, the tells -- has a
 *             solution separating every disequation (Disequality.solvable_iff).
 *   Entails   every guard holds at every such solution (Frames.Entails).
 * The result fires the selection (OccurrenceCommits.fire), keeps the extended frame settled along
 * the most general unifier with the disequations carried along it (Disequality.image), and its
 * knowledge is the information applied along the settlement.  The settlement is written into
 * the result: what it makes, the bindings it adds and the disequations it tells are resolved,
 * and each local left unbound becomes a new variable of the frame.
 * ========================================================================================== */

static tr_verdict refuse(tr_result *r, tr_reason why, size_t guard) {
  r->verdict = TR_REFUSED;
  r->reason = why;
  r->guard = guard;
  return TR_REFUSED;
}

static tr_verdict decide(tr_state *s, const tr_firing *f, tr_result *r, bool commit) {
  size_t nuse = f->ntakes + f->nreads;
  size_t nterms = 2 * nuse + f->nmakes + 2 * f->ntells + 2 * f->nguards;
  tr_term *block = xrealloc(NULL, (nterms + 1) * sizeof *block);
  memset(block, 0, (nterms + 1) * sizeof *block);
  uint32_t *at = xrealloc(NULL, (nuse + 1) * sizeof *at);
  tr_eq *apart = xrealloc(NULL, (f->napart + 1) * sizeof *apart);
  uint32_t *promote = NULL;
  tr_term *pat = block, *lab = pat + nuse, *made = lab + nuse, *tells = made + f->nmakes;
  tr_term *ga = tells + 2 * f->ntells, *gb = ga + f->nguards;
  u64map ids = {0};
  r->verdict = TR_REFUSED;
  r->reason = TR_OK;
  r->guard = 0;
  tr_verdict out = TR_REFUSED;
  bool ok = (uint64_t)s->nnames + f->fresh <= UINT32_MAX && f->locals < LOCAL_BIT;
  opening o = {f->locals, s->nnames, f->fresh, 0};
  uint64_t top = f->locals; /* locals of the decision: the firing's, then the ports' scopes */

  /* ---- Shapes ---- */
  for (size_t i = 0; ok && i < f->ntakes; i++) {
    if (!f->takes[i].occ || u64map_find(&ids, f->takes[i].occ) != SIZE_MAX) ok = false; /* one take consumes one copy */
    else u64map_put(&ids, f->takes[i].occ, 1);
  }
  u64map_free(&ids);
  ids = (u64map){0};
  for (size_t i = 0; ok && i < f->nmakes; i++) {
    tr_occ id = f->makes[i].id;
    if (id == TOMB || (id && u64map_find(&ids, id) != SIZE_MAX)) ok = false;
    else if (id) u64map_put(&ids, id, 1);
    opening om = o;
    om.keep_locals = f->makes[i].schema_locals;
    made[i] = open_term(s, &om, f->makes[i].label, &ok);
  }
  u64map_free(&ids);
  ids = (u64map){0};
  for (size_t i = 0; ok && i < nuse; i++)
    pat[i] = open_term(s, &o, i < f->ntakes ? f->takes[i].pattern : f->reads[i - f->ntakes].pattern, &ok);
  for (size_t i = 0; ok && i < f->ntells; i++) {
    tells[2 * i] = open_term(s, &o, f->tells[i].left, &ok);
    tells[2 * i + 1] = open_term(s, &o, f->tells[i].right, &ok);
  }
  for (size_t i = 0; ok && i < f->nguards; i++) {
    const tr_guard *g = &f->guards[i];
    if (g->kind == TR_G_EQUAL || g->kind == TR_G_ABSENT || g->kind == TR_G_COUNT) ga[i] = open_term(s, &o, g->a, &ok);
    if (g->kind == TR_G_EQUAL) gb[i] = open_term(s, &o, g->b, &ok);
  }
  for (size_t i = 0; ok && i < f->napart; i++) {
    apart[i].left = open_term(s, &o, f->apart[i].left, &ok);
    apart[i].right = open_term(s, &o, f->apart[i].right, &ok);
  }
  if (ok) {
    ensure_env(s, top);
    for (size_t i = 0; ok && i < f->napart; i++) ok = !same(s, apart[i].left, apart[i].right);
  }
  if (!ok) {
    refuse(r, TR_SHAPES, 0);
    goto done;
  }

  /* ---- Fits ---- */
  for (size_t i = 0; ok && i < nuse; i++) {
    tr_occ id = i < f->ntakes ? f->takes[i].occ : f->reads[i - f->ntakes].occ;
    at[i] = find_slot(s, id);
    if (at[i] == NIL) ok = false;
    else if (i < f->ntakes) u64map_put(&ids, id, 1);
    else if (u64map_find(&ids, id) != SIZE_MAX) ok = false; /* Enabled.apart */
  }
  for (size_t i = 0; ok && i < f->nmakes; i++)
    if (f->makes[i].id && find_slot(s, f->makes[i].id) != NIL) ok = false; /* Enabled.fresh */
  if (!ok) {
    refuse(r, TR_FITS, 0);
    goto done;
  }

  /* ---- the extension: each schema port opens its schema at a scope of its own ---- */
  for (size_t i = 0; ok && i < nuse; i++) {
    const slot *sl = &s->sl[at[i]];
    lab[i] = sl->label;
    if (sl->schema) {
      if (top + sl->schema > LOCAL_BIT) ok = false;
      else {
        ensure_env(s, top + sl->schema);
        lab[i] = open_schema(s, sl->label, sl->schema, (uint32_t)top);
        top += sl->schema;
      }
    }
  }
  if (!ok) {
    refuse(r, TR_SHAPES, 0);
    goto done;
  }

  /* ---- Solvable: unify the information, then separate every disequation ---- */
  s->told = apart;
  s->ntold = f->napart;
  for (size_t i = 0; ok && i < nuse; i++) ok = unify(s, pat[i], lab[i]);
  for (size_t i = 0; ok && i < f->ntells; i++) ok = unify(s, tells[2 * i], tells[2 * i + 1]);
  if (!ok || !separated(s)) {
    refuse(r, TR_UNSOLVABLE, 0);
    goto done;
  }

  /* ---- Entails: every guard at every solution ---- */
  tr_view v = {s, o, (uint32_t)top};
  bool undetermined = false;
  for (size_t i = 0; i < f->nguards; i++) {
    int e = guard_entailed(&v, &f->guards[i], ga[i], gb[i]);
    if (e == 0) {
      refuse(r, TR_GUARD, i);
      goto done;
    }
    undetermined |= e < 0;
  }
  if (undetermined) {
    r->verdict = out = TR_NO_VERDICT;
    goto done;
  }
  r->verdict = out = TR_ADMITTED;
  r->first_name = s->nnames;
  if (!commit) goto done;

  /* ---- the result: write the settlement in, then fire ---- */
  promote = xrealloc(NULL, (top + 1) * sizeof *promote);
  for (uint64_t i = 0; i <= top; i++) promote[i] = NIL;
  uint32_t nvars = s->nvars;
  rebuild inst = {RESOLVE, true, promote, &nvars, 0, 0}, kept = {RESOLVE, false, NULL, NULL, 0, 0};
  for (size_t i = 0; i < s->ntrail; i++) /* bindings of frame variables, without locals */
    if (!(s->trail[i] & LOCAL_BIT)) {
      tr_term b = rebuild_term(s, &inst, s->bind[s->trail[i]]); /* may grow s->bind */
      s->bind[s->trail[i]] = b;
    }
  for (size_t i = 0; i < f->nmakes; i++)
    made[i] = rebuild_term(s, f->makes[i].schema_locals ? &kept : &inst, made[i]);
  for (size_t i = 0; i < f->napart; i++) {
    apart[i].left = rebuild_term(s, &inst, apart[i].left);
    apart[i].right = rebuild_term(s, &inst, apart[i].right);
  }
  if (r->locals)
    for (uint32_t i = 0; i < f->locals; i++) r->locals[i] = rebuild_term(s, &inst, tr_local(s->ctx, i));
  size_t keep = 0; /* the frame variables bound by this firing stay bound; its locals go */
  for (size_t i = 0; i < s->ntrail; i++) {
    uint32_t e = s->trail[i];
    if (e & LOCAL_BIT) s->env[e & ~LOCAL_BIT] = TR_NONE;
    else s->trail[keep++] = e;
  }
  s->ntrail = keep;
  s->nvars = nvars;
  s->nnames += f->fresh;
  s->told = NULL;
  s->ntold = 0;
  for (size_t i = 0; i < f->ntakes; i++) remove_occ(s, at[i]);
  for (size_t i = 0; i < f->nmakes; i++) {
    tr_occ id = f->makes[i].id ? f->makes[i].id : s->next_id;
    if (id >= s->next_id) s->next_id = id + 1;
    add_occ(s, id, made[i], f->makes[i].schema_locals);
    if (r->made) r->made[i] = id;
  }
  for (size_t i = 0; i < f->napart; i++) { /* told disequations join the frame */
    GROW(s->ds, s->nds, s->capds);
    s->ds[s->nds] = (diseq){apart[i].left, apart[i].right, true};
    s->live_ds++;
    file_diseq(s, (uint32_t)s->nds++);
  }
  for (size_t i = 0; i < s->ntrail; i++) { /* re-file what the bound variables watched */
    uint32_t var = s->trail[i], w = s->watched[var];
    s->watched[var] = NIL;
    for (; w != NIL; w = s->ws[w].next)
      if (s->ds[s->ws[w].diseq].live) file_diseq(s, s->ws[w].diseq);
  }
  s->ntrail = 0; /* the bindings stay */
  goto cleanup;

done:
  undo(s, 0);
  s->told = NULL;
  s->ntold = 0;
cleanup:
  u64map_free(&ids);
  free(block);
  free(at);
  free(apart);
  free(promote);
  return out;
}

tr_verdict tr_admits(tr_state *s, const tr_firing *f, tr_result *r) {
  tr_result scratch = {0};
  return decide(s, f, r ? r : &scratch, false);
}

tr_verdict tr_fire(tr_state *s, const tr_firing *f, tr_result *r) {
  tr_result scratch = {0};
  return decide(s, f, r ? r : &scratch, true);
}

size_t tr_run(tr_state *s, const tr_firing *firings, size_t n) {
  size_t i = 0;
  while (i < n && tr_fire(s, &firings[i], NULL) == TR_ADMITTED) i++;
  return i;
}
