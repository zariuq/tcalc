/* bl.c: the binder layer (see bl.h).  The rules are built once from the binding signature; the
 * functions below only choose a rule and the facts it reads, fire it, and remember the fact. */
#include "bl.h"

#include <stdlib.h>
#include <string.h>

int bl_fault = 0;

static void *bl_xrealloc(void *p, size_t n) {
  void *q = realloc(p, n ? n : 1);
  if (!q) {
    fputs("bl: out of memory\n", stderr);
    exit(2);
  }
  return q;
}

/* A memo: 64-bit key -> (occurrence, known).  Open addressing, keys never 0. */
typedef struct {
  uint64_t key;
  tr_occ occ;
} mslot;
typedef struct {
  mslot *v;
  size_t cap, n;
} memo_t;

static uint64_t mhash(uint64_t k) {
  k ^= k >> 33;
  k *= 0xff51afd7ed558ccdULL;
  k ^= k >> 33;
  return k;
}
static bool memo_get(const memo_t *m, uint64_t key, tr_occ *occ) {
  if (!m->cap) return false;
  for (size_t j = mhash(key) & (m->cap - 1);; j = (j + 1) & (m->cap - 1)) {
    if (!m->v[j].key) return false;
    if (m->v[j].key == key) {
      *occ = m->v[j].occ;
      return true;
    }
  }
}
static void memo_put(memo_t *m, uint64_t key, tr_occ occ) {
  if (2 * (m->n + 1) > m->cap) {
    size_t cap = m->cap ? 2 * m->cap : 1024;
    mslot *nv = bl_xrealloc(NULL, cap * sizeof *nv);
    memset(nv, 0, cap * sizeof *nv);
    for (size_t i = 0; i < m->cap; i++)
      if (m->v[i].key) {
        size_t j = mhash(m->v[i].key) & (cap - 1);
        while (nv[j].key) j = (j + 1) & (cap - 1);
        nv[j] = m->v[i];
      }
    free(m->v);
    m->v = nv;
    m->cap = cap;
  }
  size_t j = mhash(key) & (m->cap - 1);
  while (m->v[j].key && m->v[j].key != key) j = (j + 1) & (m->cap - 1);
  if (!m->v[j].key) m->n++;
  m->v[j] = (mslot){key, occ};
}

typedef struct {
  uint32_t sym, arity, nterm;
  uint8_t *binders;
  rk_rule ev;
  rk_rule *men; /* per argument (term arguments only) */
} con_t;

struct bl {
  rk_engine *e;
  tr_ctx *c;
  con_t *con;
  size_t ncon;
  uint32_t *con_of_sym; /* symbol -> constructor + 1 */
  size_t capcos;
  uint32_t s_var, s_z, s_s, s_ev, s_men, s_id, s_sh, s_bot, s_shk, s_lf, s_cs;
  tr_term *nats;
  size_t nnats;
  rk_rule r_idall, r_cs0, r_csS, r_lf0, r_lfS, r_sh, r_shk0, r_shkS, r_mvar;
  memo_t mev, mmen;
  uint32_t *fb; /* per term id: free bound + 1, 0 unknown */
  uint32_t *natv; /* per term id: numeral value + 1, 0 unknown */
  size_t capterm;
  tr_term *vals; /* parameter scratch */
  size_t capvals;
};

static tr_term L(bl *b, uint32_t i) { return tr_local(b->c, i); }
static tr_term A1(bl *b, uint32_t f, tr_term x) { return tr_app(b->c, f, &x); }
static tr_term A2(bl *b, uint32_t f, tr_term x, tr_term y) {
  tr_term a[2] = {x, y};
  return tr_app(b->c, f, a);
}
static tr_term A3(bl *b, uint32_t f, tr_term x, tr_term y, tr_term z) {
  tr_term a[3] = {x, y, z};
  return tr_app(b->c, f, a);
}
static tr_term K0(bl *b, uint32_t f) { return tr_app(b->c, f, NULL); }

static void grow_terms(bl *b) {
  size_t n = tr_ctx_terms(b->c) + 2;
  if (n <= b->capterm) return;
  size_t cap = b->capterm ? b->capterm : 1024;
  while (cap < n) cap *= 2;
  b->fb = bl_xrealloc(b->fb, cap * sizeof *b->fb);
  b->natv = bl_xrealloc(b->natv, cap * sizeof *b->natv);
  memset(b->fb + b->capterm, 0, (cap - b->capterm) * sizeof *b->fb);
  memset(b->natv + b->capterm, 0, (cap - b->capterm) * sizeof *b->natv);
  b->capterm = cap;
}

uint32_t bl_symbol(const bl *b, size_t con) { return b->con[con].sym; }

tr_term bl_nat(bl *b, uint32_t n) {
  if (n >= b->nnats) {
    size_t cap = b->nnats ? b->nnats : 64;
    while (cap <= n) cap *= 2;
    b->nats = bl_xrealloc(b->nats, cap * sizeof *b->nats);
    for (size_t i = b->nnats; i < cap; i++) b->nats[i] = i ? A1(b, b->s_s, b->nats[i - 1]) : K0(b, b->s_z);
    b->nnats = cap;
  }
  return b->nats[n];
}

bool bl_nat_value(const bl *b, tr_term t, uint32_t *n) {
  bl *m = (bl *)b;
  uint32_t k = 0;
  tr_term u = t;
  for (;;) {
    grow_terms(m);
    if (u < m->capterm && m->natv[u]) {
      k += m->natv[u] - 1;
      break;
    }
    if (tr_term_kind(b->c, u) != TR_APP) return false;
    uint32_t f = tr_term_symbol(b->c, u);
    if (f == b->s_z) break;
    if (f != b->s_s) return false;
    k++;
    u = tr_term_arg(b->c, u, 0);
  }
  grow_terms(m);
  if (t < m->capterm) m->natv[t] = k + 1;
  *n = k;
  return true;
}

tr_term bl_var(bl *b, uint32_t n) { return A1(b, b->s_var, bl_nat(b, n)); }
bool bl_var_index(const bl *b, tr_term t, uint32_t *n) {
  if (tr_term_kind(b->c, t) != TR_APP || tr_term_symbol(b->c, t) != b->s_var) return false;
  return bl_nat_value(b, tr_term_arg(b->c, t, 0), n);
}

tr_term bl_id(bl *b) { return K0(b, b->s_id); }
tr_term bl_sh(bl *b) { return K0(b, b->s_sh); }
tr_term bl_bot(bl *b) { return K0(b, b->s_bot); }
tr_term bl_shk(bl *b, uint32_t k) { return A1(b, b->s_shk, bl_nat(b, k)); }
tr_term bl_lf(bl *b, tr_term s) { return A1(b, b->s_lf, s); }
tr_term bl_cs(bl *b, tr_term u, tr_term s) { return A2(b, b->s_cs, u, s); }
tr_term bl_ev_fact(bl *b, tr_term t, tr_term s, tr_term r) { return A3(b, b->s_ev, t, s, r); }
tr_term bl_mentions_fact(bl *b, tr_term t, tr_term k) { return A2(b, b->s_men, t, k); }

tr_term bl_rho(bl *b, uint32_t depth, const uint32_t *ys, uint32_t arity) {
  tr_term s = bl_shk(b, bl_fault == 5 ? depth : arity);
  for (uint32_t i = depth; i-- > 0;) {
    tr_term e = bl_bot(b);
    for (uint32_t j = 0; j < arity; j++)
      if (ys[j] == i) e = bl_var(b, bl_fault == 6 ? j : arity - 1 - j);
    s = bl_cs(b, e, s);
  }
  return s;
}

static tr_term lift(bl *b, tr_term s, uint32_t k) {
  while (k--) s = bl_lf(b, s);
  return s;
}

bl *bl_new(rk_engine *e, const bl_con *cons, size_t ncons) {
  bl *b = bl_xrealloc(NULL, sizeof *b);
  memset(b, 0, sizeof *b);
  b->e = e;
  b->c = e->ctx;
  tr_ctx *c = b->c;
  b->s_var = tr_symbol(c, "var", 1), b->s_z = tr_symbol(c, "z", 0), b->s_s = tr_symbol(c, "s", 1);
  b->s_ev = tr_symbol(c, "ev", 3), b->s_men = tr_symbol(c, "mentions", 2);
  b->s_id = tr_symbol(c, "id", 0), b->s_sh = tr_symbol(c, "sh", 0), b->s_bot = tr_symbol(c, "bot", 0);
  b->s_shk = tr_symbol(c, "shk", 1), b->s_lf = tr_symbol(c, "lf", 1), b->s_cs = tr_symbol(c, "cs", 2);
  b->ncon = ncons;
  b->con = bl_xrealloc(NULL, (ncons + 1) * sizeof *b->con);
  memset(b->con, 0, (ncons + 1) * sizeof *b->con);
  for (size_t k = 0; k < ncons; k++) {
    con_t *f = &b->con[k];
    uint32_t n = cons[k].arity;
    f->sym = tr_symbol(c, cons[k].name, n);
    f->arity = n;
    f->binders = bl_xrealloc(NULL, n + 1);
    for (uint32_t i = 0; i < n; i++) {
      f->binders[i] = cons[k].binders ? cons[k].binders[i] : 0;
      if (f->binders[i] != BL_DATA) f->nterm++;
    }
    if (f->sym >= b->capcos) {
      size_t cap = b->capcos ? b->capcos : 64;
      while (cap <= f->sym) cap *= 2;
      b->con_of_sym = bl_xrealloc(b->con_of_sym, cap * sizeof *b->con_of_sym);
      memset(b->con_of_sym + b->capcos, 0, (cap - b->capcos) * sizeof *b->con_of_sym);
      b->capcos = cap;
    }
    b->con_of_sym[f->sym] = (uint32_t)k + 1;
    /* ev: X_i = L(i), Y_i = L(n + i), S = L(2n) */
    tr_term *xs = bl_xrealloc(NULL, (n + 1) * sizeof *xs), *ys = bl_xrealloc(NULL, (n + 1) * sizeof *ys);
    rk_init(&f->ev, cons[k].name, 2 * n + 1);
    tr_term S = L(b, 2 * n);
    for (uint32_t i = 0; i < n; i++) {
      xs[i] = L(b, i);
      if (f->binders[i] == BL_DATA) {
        ys[i] = xs[i];
        rk_param(&f->ev, i);
        continue;
      }
      ys[i] = L(b, n + i);
      uint32_t lifts = f->binders[i];
      if (bl_fault == 4 && lifts) lifts--;
      rk_read(&f->ev, A3(b, b->s_ev, xs[i], lift(b, S, lifts), ys[i]));
    }
    if (!f->nterm) rk_param(&f->ev, 2 * n);
    rk_make(&f->ev, A3(b, b->s_ev, tr_app(c, f->sym, xs), S, tr_app(c, f->sym, ys)));
    /* mentions, per term argument: X_j = L(j), K = L(n) */
    f->men = bl_xrealloc(NULL, (n + 1) * sizeof *f->men);
    for (uint32_t i = 0; i < n; i++) {
      if (f->binders[i] == BL_DATA) continue;
      rk_rule *r = &f->men[i];
      rk_init(r, "mentions", n + 1);
      tr_term K = L(b, n);
      uint32_t up = bl_fault == 7 ? 0 : f->binders[i];
      for (uint32_t u = 0; u < up; u++) K = A1(b, b->s_s, K);
      rk_read(r, A2(b, b->s_men, xs[i], K));
      rk_make(r, A2(b, b->s_men, tr_app(c, f->sym, xs), L(b, n)));
      for (uint32_t j = 0; j < n; j++)
        if (j != i) rk_param(r, j);
    }
    free(xs);
    free(ys);
  }
  tr_term V0 = A1(b, b->s_var, K0(b, b->s_z));
  /* ev(T, id, T) */
  rk_init(&b->r_idall, "t[id] = t", 1);
  rk_make(&b->r_idall, A3(b, b->s_ev, L(b, 0), bl_id(b), L(b, 0)));
  rk_param(&b->r_idall, 0);
  /* var(0)[cs(U, S)] = U */
  rk_init(&b->r_cs0, "var(0)[u.s] = u", 2);
  rk_make(&b->r_cs0, A3(b, b->s_ev, V0, A2(b, b->s_cs, L(b, 0), L(b, 1)), L(b, 0)));
  rk_param(&b->r_cs0, 0);
  rk_param(&b->r_cs0, 1);
  /* var(n+1)[cs(U, S)] = var(n)[S]: N 0, U 1, S 2, R 3 */
  rk_init(&b->r_csS, "var(n+1)[u.s] = var(n)[s]", 4);
  rk_read(&b->r_csS, A3(b, b->s_ev, A1(b, b->s_var, L(b, 0)), L(b, 2), L(b, 3)));
  rk_make(&b->r_csS, A3(b, b->s_ev, A1(b, b->s_var, A1(b, b->s_s, L(b, 0))), A2(b, b->s_cs, L(b, 1), L(b, 2)),
                        bl_fault == 2 ? A1(b, b->s_var, L(b, 0)) : L(b, 3)));
  rk_param(&b->r_csS, 1);
  /* var(0)[lf(S)] = var(0) */
  rk_init(&b->r_lf0, "var(0)[lift s] = var(0)", 1);
  rk_make(&b->r_lf0, A3(b, b->s_ev, V0, A1(b, b->s_lf, L(b, 0)), V0));
  rk_param(&b->r_lf0, 0);
  /* var(n+1)[lf(S)] = (var(n)[S])[sh]: N 0, S 1, M 2, R 3 */
  rk_init(&b->r_lfS, "var(n+1)[lift s] = var(n)[s][shift]", 4);
  rk_read(&b->r_lfS, A3(b, b->s_ev, A1(b, b->s_var, L(b, 0)), L(b, 1), L(b, 2)));
  if (bl_fault != 1) rk_read(&b->r_lfS, A3(b, b->s_ev, L(b, 2), bl_sh(b), L(b, 3)));
  rk_make(&b->r_lfS, A3(b, b->s_ev, A1(b, b->s_var, A1(b, b->s_s, L(b, 0))), A1(b, b->s_lf, L(b, 1)),
                        bl_fault == 1 ? L(b, 2) : L(b, 3)));
  /* var(n)[sh] = var(n+1) */
  rk_init(&b->r_sh, "var(n)[shift] = var(n+1)", 1);
  rk_make(&b->r_sh, A3(b, b->s_ev, A1(b, b->s_var, L(b, 0)), bl_sh(b),
                       A1(b, b->s_var, bl_fault == 3 ? L(b, 0) : A1(b, b->s_s, L(b, 0)))));
  rk_param(&b->r_sh, 0);
  /* var(n)[shk(0)] = var(n) */
  rk_init(&b->r_shk0, "var(n)[shift^0] = var(n)", 1);
  rk_make(&b->r_shk0, A3(b, b->s_ev, A1(b, b->s_var, L(b, 0)), A1(b, b->s_shk, K0(b, b->s_z)), A1(b, b->s_var, L(b, 0))));
  rk_param(&b->r_shk0, 0);
  /* var(n)[shk(k+1)] = var(m+1) when var(n)[shk(k)] = var(m): N 0, K 1, M 2 */
  rk_init(&b->r_shkS, "var(n)[shift^(k+1)] = var(m+1)", 3);
  rk_read(&b->r_shkS, A3(b, b->s_ev, A1(b, b->s_var, L(b, 0)), A1(b, b->s_shk, L(b, 1)), A1(b, b->s_var, L(b, 2))));
  rk_make(&b->r_shkS, A3(b, b->s_ev, A1(b, b->s_var, L(b, 0)), A1(b, b->s_shk, A1(b, b->s_s, L(b, 1))),
                         A1(b, b->s_var, A1(b, b->s_s, L(b, 2)))));
  /* mentions(var(k), k) */
  rk_init(&b->r_mvar, "mentions(var(k), k)", 1);
  rk_make(&b->r_mvar, A2(b, b->s_men, A1(b, b->s_var, L(b, 0)), L(b, 0)));
  rk_param(&b->r_mvar, 0);
  return b;
}

void bl_free(bl *b) {
  if (!b) return;
  for (size_t k = 0; k < b->ncon; k++) {
    rk_free(&b->con[k].ev);
    for (uint32_t i = 0; i < b->con[k].arity; i++)
      if (b->con[k].binders[i] != BL_DATA) rk_free(&b->con[k].men[i]);
    free(b->con[k].men);
    free(b->con[k].binders);
  }
  free(b->con);
  free(b->con_of_sym);
  free(b->nats);
  rk_rule *rs[] = {&b->r_idall, &b->r_cs0, &b->r_csS, &b->r_lf0, &b->r_lfS, &b->r_sh, &b->r_shk0, &b->r_shkS, &b->r_mvar};
  for (size_t i = 0; i < sizeof rs / sizeof *rs; i++) rk_free(rs[i]);
  free(b->mev.v);
  free(b->mmen.v);
  free(b->fb);
  free(b->natv);
  free(b->vals);
  free(b);
}

static const con_t *con_of(const bl *b, tr_term t) {
  if (tr_term_kind(b->c, t) != TR_APP) return NULL;
  uint32_t f = tr_term_symbol(b->c, t);
  if (f >= b->capcos || !b->con_of_sym[f]) return NULL;
  return &b->con[b->con_of_sym[f] - 1];
}

static tr_occ fire(bl *b, const rk_rule *r, const tr_occ *occs, const tr_term *vals) {
  return rk_fire(b->e, r, occs, vals, NULL, NULL);
}

uint32_t bl_free_bound(bl *b, tr_term t) {
  grow_terms(b);
  if (t < b->capterm && b->fb[t]) return b->fb[t] - 1;
  uint32_t n = 0, v;
  if (bl_var_index(b, t, &v)) n = v + 1;
  else {
    const con_t *f = con_of(b, t);
    if (f)
      for (uint32_t i = 0; i < f->arity; i++) {
        if (f->binders[i] == BL_DATA) continue;
        uint32_t a = bl_free_bound(b, tr_term_arg(b->c, t, i));
        if (a > f->binders[i] && a - f->binders[i] > n) n = a - f->binders[i];
      }
  }
  grow_terms(b);
  b->fb[t] = n + 1;
  return n;
}

tr_occ bl_ev(bl *b, tr_term t, tr_term s, tr_term *r) {
  uint64_t key = (uint64_t)t << 32 | s;
  tr_occ o = 0;
  if (memo_get(&b->mev, key, &o)) {
    if (o && r) *r = rk_arg(b->e, o, 2);
    return o;
  }
  tr_ctx *c = b->c;
  uint32_t n;
  if (s == bl_id(b)) {
    o = fire(b, &b->r_idall, NULL, &t);
  } else if (bl_var_index(b, t, &n)) {
    uint32_t sk = tr_term_kind(c, s) == TR_APP ? tr_term_symbol(c, s) : UINT32_MAX;
    if (sk == b->s_cs) {
      tr_term u = tr_term_arg(c, s, 0), s2 = tr_term_arg(c, s, 1);
      if (n == 0) {
        if (u != bl_bot(b)) {
          tr_term v[2] = {u, s2};
          o = fire(b, &b->r_cs0, NULL, v);
        }
      } else {
        tr_occ o1 = bl_ev(b, bl_var(b, n - 1), s2, NULL);
        if (o1) o = fire(b, &b->r_csS, &o1, &u);
      }
    } else if (sk == b->s_lf) {
      tr_term s2 = tr_term_arg(c, s, 0), m;
      if (n == 0) o = fire(b, &b->r_lf0, NULL, &s2);
      else {
        tr_occ os[2];
        os[0] = bl_ev(b, bl_var(b, n - 1), s2, &m);
        if (os[0]) {
          if (bl_fault == 1) o = fire(b, &b->r_lfS, os, NULL);
          else if ((os[1] = bl_ev(b, m, bl_sh(b), NULL))) o = fire(b, &b->r_lfS, os, NULL);
        }
      }
    } else if (sk == b->s_sh) {
      tr_term k = bl_nat(b, n);
      o = fire(b, &b->r_sh, NULL, &k);
    } else if (sk == b->s_shk) {
      uint32_t k;
      if (bl_nat_value(b, tr_term_arg(c, s, 0), &k)) {
        tr_term nn = bl_nat(b, n);
        if (k == 0) o = fire(b, &b->r_shk0, NULL, &nn);
        else {
          tr_occ o1 = bl_ev(b, t, bl_shk(b, k - 1), NULL);
          if (o1) o = fire(b, &b->r_shkS, &o1, NULL);
        }
      }
    }
  } else {
    const con_t *f = con_of(b, t);
    if (f) {
      tr_occ occs[16], *op = f->nterm <= 16 ? occs : bl_xrealloc(NULL, f->nterm * sizeof *op);
      size_t no = 0, nv = 0;
      bool ok = true;
      for (uint32_t i = 0; ok && i < f->arity; i++) {
        if (f->binders[i] == BL_DATA) continue;
        op[no] = bl_ev(b, tr_term_arg(c, t, i), lift(b, s, f->binders[i]), NULL);
        ok = op[no++] != 0;
      }
      if (ok) { /* the parameters, filled after the recursion (which reuses the scratch) */
        if (f->arity + 1 > b->capvals) b->capvals = f->arity + 1, b->vals = bl_xrealloc(b->vals, b->capvals * sizeof *b->vals);
        for (uint32_t i = 0; i < f->arity; i++)
          if (f->binders[i] == BL_DATA) b->vals[nv++] = tr_term_arg(c, t, i);
        if (!f->nterm) b->vals[nv++] = s;
        o = fire(b, &f->ev, op, b->vals);
      }
      if (op != occs) free(op);
    }
  }
  /* The fact made is the one asked for, or the rules are wrong: never remember another fact. */
  if (o && (rk_arg(b->e, o, 0) != t || rk_arg(b->e, o, 1) != s)) o = 0;
  memo_put(&b->mev, key, o);
  if (o && r) *r = rk_arg(b->e, o, 2);
  return o;
}

tr_occ bl_mentions(bl *b, tr_term t, uint32_t k) {
  if (bl_free_bound(b, t) <= k) return 0;
  uint64_t key = (uint64_t)t << 32 | k;
  tr_occ o = 0;
  if (memo_get(&b->mmen, key, &o)) return o;
  uint32_t n;
  if (bl_var_index(b, t, &n)) {
    if (n == k) {
      tr_term kk = bl_nat(b, k);
      o = fire(b, &b->r_mvar, NULL, &kk);
    }
  } else {
    const con_t *f = con_of(b, t);
    for (uint32_t i = 0; f && !o && i < f->arity; i++) {
      if (f->binders[i] == BL_DATA) continue;
      tr_occ o1 = bl_mentions(b, tr_term_arg(b->c, t, i), k + f->binders[i]);
      if (!o1) continue;
      if (f->arity + 1 > b->capvals) b->capvals = f->arity + 1, b->vals = bl_xrealloc(b->vals, b->capvals * sizeof *b->vals);
      size_t nv = 0;
      for (uint32_t j = 0; j < f->arity; j++)
        if (j != i) b->vals[nv++] = tr_term_arg(b->c, t, j);
      o = fire(b, &f->men[i], &o1, b->vals);
    }
  }
  if (o && (rk_arg(b->e, o, 0) != t || rk_arg(b->e, o, 1) != bl_nat(b, k))) o = 0;
  memo_put(&b->mmen, key, o);
  return o;
}

uint64_t bl_facts_made(const bl *b) { return b->e->fired; }

size_t bl_rules(bl *b, rk_rule **out, size_t cap) {
  size_t n = 0;
#define PUT(r) ((n < cap ? (out[n] = (r)) : NULL), n++)
  for (size_t k = 0; k < b->ncon; k++) {
    PUT(&b->con[k].ev);
    for (uint32_t i = 0; i < b->con[k].arity; i++)
      if (b->con[k].binders[i] != BL_DATA) PUT(&b->con[k].men[i]);
  }
  PUT(&b->r_idall), PUT(&b->r_cs0), PUT(&b->r_csS), PUT(&b->r_lf0), PUT(&b->r_lfS);
  PUT(&b->r_sh), PUT(&b->r_shk0), PUT(&b->r_shkS), PUT(&b->r_mvar);
#undef PUT
  return n;
}
