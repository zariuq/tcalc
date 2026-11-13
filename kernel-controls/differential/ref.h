/* A naive reference for one firing of the transform step over ground stores.

   Written from the statement of the step in tcalc.h ("take occurrences, keep (read) occurrences,
   tell equations and disequations, check that absent/count queries hold, check the hole sorts,
   mint a fresh name if asked, make the result"), not from the kernel's code. No hashing, no
   sharing, no fast paths: terms are trees, the store is an array, matching is brute force.

   Fragment: first-order sorted terms without binders; every fact is ground. A candidate whose
   tell or disequation would leave a hole unbound is reported as RV_OUT (outside the fragment). */
#pragma once
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { RK_APP = 1, RK_NAME, RK_HOLE };
#define R_MAXAR 5
#define R_MAXH 8
#define R_MAXFACTS 512

typedef struct RT { uint8_t kind, sort, n; int16_t head; uint64_t id; const struct RT *a[R_MAXAR]; } RT;
typedef struct { uint8_t sort, arity, asort[R_MAXAR]; } RCon;
typedef struct { const RT *t; uint8_t space; } RPat;
typedef struct { const RT *t; uint8_t space; uint32_t n; } RCount;
typedef struct {
  int nholes; uint8_t hsort[R_MAXH];
  int ntake, nkeep, nabsent, ncount, ntell, nneq, nmake, fresh;   /* fresh: hole index or -1 */
  RPat take[4], keep[8], absent[4], make[5];
  RCount count[4];
  const RT *tell[4][2], *neq[4][2];
} RRule;
typedef struct { const RT *t; uint8_t space; bool alive; int key_step, key_k; uint32_t kocc; } RFact;
typedef struct { RFact f[R_MAXFACTS]; int n; uint64_t next_name; } RStore;
typedef enum { RV_REFUSE = 0, RV_ACCEPT = 1, RV_OUT = 2 } RVerdict;

static RCon r_con[32]; static int r_ncon;
static bool r_theory_has_query;                                /* some rule of the theory has an absent or count query */
static RT *r_arena; static size_t r_na, r_cap;

static RT *r_new(void) {
  if (r_na >= r_cap) { fprintf(stderr, "reference arena exhausted\n"); exit(3); }
  RT *t = &r_arena[r_na++]; memset(t, 0, sizeof *t); return t;
}
static const RT *r_app(int head, const RT *const *a) {
  RT *t = r_new(); t->kind = RK_APP; t->head = (int16_t)head; t->sort = r_con[head].sort; t->n = r_con[head].arity;
  for (int i = 0; i < t->n; i++) t->a[i] = a[i];
  return t;
}
static const RT *r_name(int sort, uint64_t id) { RT *t = r_new(); t->kind = RK_NAME; t->sort = (uint8_t)sort; t->id = id; return t; }
static const RT *r_hole(int idx, int sort) { RT *t = r_new(); t->kind = RK_HOLE; t->sort = (uint8_t)sort; t->head = (int16_t)idx; return t; }

static const RT *r_walk(const RT *t, const RT *const *B) {
  while (t->kind == RK_HOLE && B[t->head]) t = B[t->head];
  return t;
}
static bool r_occurs(int h, const RT *t, const RT *const *B) {
  t = r_walk(t, B);
  if (t->kind == RK_HOLE) return t->head == h;
  for (int i = 0; i < t->n; i++) if (r_occurs(h, t->a[i], B)) return true;
  return false;
}
/* First-order unification; a hole takes only a term of its own sort. Binds into B. */
static bool r_unify(const RT *a, const RT *b, const RT **B) {
  a = r_walk(a, B); b = r_walk(b, B);
  if (a->kind == RK_HOLE && b->kind == RK_HOLE && a->head == b->head) return true;
  if (a->kind == RK_HOLE) {
    if (a->sort != b->sort || r_occurs(a->head, b, B)) return false;
    B[a->head] = b; return true;
  }
  if (b->kind == RK_HOLE) {
    if (a->sort != b->sort || r_occurs(b->head, a, B)) return false;
    B[b->head] = a; return true;
  }
  if (a->kind != b->kind) return false;
  if (a->kind == RK_NAME) return a->sort == b->sort && a->id == b->id;
  if (a->head != b->head) return false;
  for (int i = 0; i < a->n; i++) if (!r_unify(a->a[i], b->a[i], B)) return false;
  return true;
}
static bool r_ground(const RT *t, const RT *const *B) {
  t = r_walk(t, B);
  if (t->kind == RK_HOLE) return false;
  for (int i = 0; i < t->n; i++) if (!r_ground(t->a[i], B)) return false;
  return true;
}
static const RT *r_subst(const RT *t, const RT *const *B) {
  t = r_walk(t, B);
  if (t->kind != RK_APP) return t;
  const RT *a[R_MAXAR];
  for (int i = 0; i < t->n; i++) a[i] = r_subst(t->a[i], B);
  return r_app(t->head, a);
}
static bool r_equal(const RT *a, const RT *b) {              /* ground terms */
  if (a->kind != b->kind || a->sort != b->sort) return false;
  if (a->kind == RK_NAME) return a->id == b->id;
  if (a->kind == RK_HOLE) return a->head == b->head;
  if (a->head != b->head) return false;
  for (int i = 0; i < a->n; i++) if (!r_equal(a->a[i], b->a[i])) return false;
  return true;
}
static uint64_t r_max_name(const RT *t) {                    /* 1 + the largest name id below t, or 0 */
  if (t->kind == RK_NAME) return t->id + 1;
  uint64_t m = 0;
  for (int i = 0; i < t->n; i++) { uint64_t c = r_max_name(t->a[i]); if (c > m) m = c; }
  return m;
}
/* How many live facts in the space unify with the pattern (its unbound holes existential)? */
static uint32_t r_count(const RStore *st, const RT *pat, int space, const RT *const *B, int nholes) {
  uint32_t hits = 0;
  for (int i = 0; i < st->n; i++) {
    if (!st->f[i].alive || st->f[i].space != space) continue;
    const RT *B2[R_MAXH];
    for (int h = 0; h < nholes; h++) B2[h] = B[h];
    if (r_unify(pat, st->f[i].t, B2)) hits++;
  }
  return hits;
}

/* One candidate firing. take/keep: indices into st->f, or -1 for "no such occurrence".
   in: NULL, or nholes entries (NULL = hole not given). With apply, an accepted firing is
   carried out and made[] receives the indices of the facts it made. */
static RVerdict r_fire(RStore *st, const RRule *r, const int *take, const int *keep,
                       const RT *const *in, bool apply, int step, int *made) {
  const RT *B[R_MAXH];
  /* Names are minted before they are used: a given value mentions only minted names, whatever the rule
     (a name used early and minted later can witness facts no run derives once facts are consumed). */
  bool schematic = !r->ntake && !r->nabsent && !r->ncount && !r->ntell && !r->nneq && r->fresh < 0 && r->nmake == 1;
  for (int h = 0; h < r->nholes; h++) {
    B[h] = in ? in[h] : NULL;
    if (!B[h]) continue;
    if (B[h]->sort != r->hsort[h]) return RV_REFUSE;                    /* a hole holds a term of its sort */
    if (r_max_name(B[h]) > st->next_name) return RV_REFUSE;             /* names must already be minted */
  }
  if (r->fresh >= 0 && B[r->fresh]) return RV_REFUSE;                   /* the fresh hole is not the caller's */
  for (int i = 0; i < r->ntake; i++) {
    if (take[i] < 0 || !st->f[take[i]].alive) return RV_REFUSE;
    for (int j = 0; j < i; j++) if (take[j] == take[i]) return RV_REFUSE;   /* one occurrence, one take */
    if (st->f[take[i]].space != r->take[i].space) return RV_REFUSE;
    if (!r_unify(r->take[i].t, st->f[take[i]].t, B)) return RV_REFUSE;
  }
  for (int i = 0; i < r->nkeep; i++) {
    if (keep[i] < 0 || !st->f[keep[i]].alive) return RV_REFUSE;
    for (int j = 0; j < r->ntake; j++) if (take[j] == keep[i]) return RV_REFUSE;   /* taken, so not also read */
    if (st->f[keep[i]].space != r->keep[i].space) return RV_REFUSE;
    if (!r_unify(r->keep[i].t, st->f[keep[i]].t, B)) return RV_REFUSE;
  }
  for (int i = 0; i < r->ntell; i++)
    if (!r_unify(r->tell[i][0], r->tell[i][1], B)) return RV_REFUSE;
  for (int i = 0; i < r->ntell; i++)
    if (!r_ground(r->tell[i][0], B) || !r_ground(r->tell[i][1], B)) return RV_OUT;
  for (int i = 0; i < r->nneq; i++) {
    if (!r_ground(r->neq[i][0], B) || !r_ground(r->neq[i][1], B)) return RV_OUT;
    if (r_equal(r_subst(r->neq[i][0], B), r_subst(r->neq[i][1], B))) return RV_REFUSE;
  }
  for (int i = 0; i < r->nabsent; i++)
    if (r_count(st, r->absent[i].t, r->absent[i].space, B, r->nholes) != 0) return RV_REFUSE;
  for (int i = 0; i < r->ncount; i++)
    if (r_count(st, r->count[i].t, r->count[i].space, B, r->nholes) != r->count[i].n) return RV_REFUSE;
  if (!schematic)                                                       /* only schematic facts may mention */
    for (int h = 0; h < r->nholes; h++)                                 /* names not yet minted */
      if (B[h] && r_ground(B[h], B) && r_max_name(r_subst(B[h], B)) > st->next_name) return RV_REFUSE;
  uint64_t next = st->next_name;
  if (r->fresh >= 0) B[r->fresh] = r_name(r->hsort[r->fresh], next++);
  const RT *out[5];
  for (int m = 0; m < r->nmake; m++) {
    if (!r_ground(r->make[m].t, B)) return RV_REFUSE;                   /* a made fact has no unbound hole */
    out[m] = r_subst(r->make[m].t, B);
  }
  if (!apply) return RV_ACCEPT;
  if (st->n + r->nmake > R_MAXFACTS) { fprintf(stderr, "reference store full\n"); exit(3); }
  st->next_name = next;
  for (int i = 0; i < r->ntake; i++) st->f[take[i]].alive = false;
  for (int m = 0; m < r->nmake; m++) {
    if (made) made[m] = st->n;
    st->f[st->n++] = (RFact){ out[m], r->make[m].space, true, step, m, 0 };
  }
  return RV_ACCEPT;
}

static int r_show(const RT *t, char *buf, int cap) {            /* the same text the driver prints for kernel terms */
  int n = 0;
  if (t->kind == RK_NAME) return snprintf(buf, (size_t)cap, "n%d#%llu", t->sort, (unsigned long long)t->id);
  if (t->kind == RK_HOLE) return snprintf(buf, (size_t)cap, "?%d", t->head);
  n += snprintf(buf + n, (size_t)(cap - n), "c%d", t->head);
  if (t->n) {
    n += snprintf(buf + n, (size_t)(cap - n), "(");
    for (int i = 0; i < t->n && n < cap - 8; i++) { if (i) buf[n++] = ','; n += r_show(t->a[i], buf + n, cap - n); }
    n += snprintf(buf + n, (size_t)(cap - n), ")");
  }
  return n;
}
