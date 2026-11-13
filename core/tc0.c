/* tc0: the tier-0 step over hash-consed flat facts.  See tc0.h for the contract. */
#include "tc0.h"
#include <stdlib.h>
#include <string.h>

typedef struct { uint8_t kind, arity, ground; uint16_t con; uint32_t args; uint64_t id; } Node;

static Node *N;      static uint32_t nn, ncap;       /* node 0 is "no term" */
static Term *P;      static uint32_t np, pcap;       /* argument pool */
static uint32_t *H;  static uint32_t hcap;           /* hash-consing table of node indices, 0 = empty */
static uint8_t con_arity[1u << 16]; static int ncon;
static bool has_gen; static uint64_t last_gen;       /* generative names minted so far: ids 0..last_gen */
static bool sealed;

typedef struct { uint8_t i, j, i0, j0; Term c; } Guard;   /* premise i, argument j equals (i0, j0), or c */
typedef struct {
  uint8_t nkeep, mar, ng; int8_t fresh; uint16_t mcon, kcon[TC0_KEEPS];
  int8_t bi[TC0_HOLES], bj[TC0_HOLES];               /* where a hole is first matched, or -1 */
  uint8_t kind[TC0_HOLES]; uint32_t used;             /* hole kinds; holes the conclusion or a premise uses */
  Guard g[TC0_KEEPS * TC0_ARITY];
  int8_t mh[TC0_ARITY]; Term mc[TC0_ARITY];           /* conclusion: hole index, or the constant term */
} Rule0;
static Rule0 *R; static int nr, rcap;

static Term *S; static uint64_t nslot, max_slots;     /* the store; S[s] == 0: never written */
static Term dflt;                                     /* the fact of an unwritten slot */

static uint64_t mix(uint64_t h, uint64_t v) {
  h ^= v + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
  return h * 0xff51afd7ed558ccdull;
}
static uint64_t hash_of(uint8_t kind, uint16_t con, int ar, const Term *a, uint64_t id) {
  uint64_t h = mix(mix(kind, con), id);
  for (int j = 0; j < ar; j++) h = mix(h, a[j]);
  return h ^ (h >> 31);
}
static bool same(const Node *x, uint8_t kind, uint16_t con, int ar, const Term *a, uint64_t id) {
  if (x->kind != kind || x->con != con || x->arity != ar || x->id != id) return false;
  return ar == 0 || memcmp(&P[x->args], a, (size_t)ar * sizeof *a) == 0;
}

/* Make room for k more nodes and m more arguments, so that the next k interns cannot fail.
   On failure nothing changes. */
static bool reserve(uint32_t k, uint32_t m) {
  if (nn > UINT32_MAX / 4 - k || np > UINT32_MAX / 4 - m) return false;
  if (nn + k > ncap) {
    uint32_t c = ncap * 2; while (c < nn + k) c *= 2;
    Node *t = realloc(N, (size_t)c * sizeof *t); if (!t) return false;
    N = t; ncap = c;
  }
  if (np + m > pcap) {
    uint32_t c = pcap * 2; while (c < np + m) c *= 2;
    Term *t = realloc(P, (size_t)c * sizeof *t); if (!t) return false;
    P = t; pcap = c;
  }
  if ((uint64_t)(nn + k) * 2 > hcap) {                /* load at most one half */
    uint32_t c = hcap * 2; while ((uint64_t)(nn + k) * 2 > c) c *= 2;
    uint32_t *t = calloc(c, sizeof *t); if (!t) return false;
    for (uint32_t i = 0; i < hcap; i++)
      if (H[i]) {
        const Node *x = &N[H[i]];
        uint32_t p = (uint32_t)hash_of(x->kind, x->con, x->arity, &P[x->args], x->id) & (c - 1);
        while (t[p]) p = (p + 1) & (c - 1);
        t[p] = H[i];
      }
    free(H); H = t; hcap = c;
  }
  return true;
}

static Term intern(uint8_t kind, uint16_t con, int ar, const Term *a, uint64_t id) {
  if (!reserve(1, (uint32_t)ar)) return 0;
  uint32_t p = (uint32_t)hash_of(kind, con, ar, a, id) & (hcap - 1);
  for (; H[p]; p = (p + 1) & (hcap - 1))
    if (same(&N[H[p]], kind, con, ar, a, id)) return H[p];
  uint8_t ground = kind == TC0_K_GEN || kind == TC0_K_CODE;
  if (kind == TC0_K_APP) { ground = 1; for (int j = 0; j < ar; j++) ground &= N[a[j]].ground; }
  N[nn] = (Node){ kind, (uint8_t)ar, ground, con, np, id };
  if (ar) memcpy(&P[np], a, (size_t)ar * sizeof *a);
  np += (uint32_t)ar;
  H[p] = nn;
  return nn++;
}

static bool is_term(Term t) { return t > 0 && t < nn; }
static bool is_atom(Term t) { return is_term(t) && (N[t].kind == TC0_K_GEN || N[t].kind == TC0_K_CODE); }

bool tc0_init(uint64_t slots) {
  free(N); free(P); free(H); free(R); free(S);
  ncap = 1024; pcap = 4096; hcap = 4096; rcap = 16;
  N = calloc(ncap, sizeof *N); P = calloc(pcap, sizeof *P); H = calloc(hcap, sizeof *H);
  R = calloc((size_t)rcap, sizeof *R); S = NULL;
  nn = 1; np = 0; ncon = 0; nr = 0; nslot = 0; max_slots = slots; dflt = 0;
  has_gen = false; last_gen = 0; sealed = false;
  return N && P && H && R;
}

int tc0_con(int arity) {
  if (sealed || arity < 0 || arity > TC0_ARITY || ncon >= (int)(sizeof con_arity)) return -1;
  con_arity[ncon] = (uint8_t)arity;
  return ncon++;
}

Term tc0_mint(void) {
  if (has_gen && last_gen == UINT64_MAX) return 0;
  if (!reserve(1, 0)) return 0;                       /* the name is counted only if its node exists */
  uint64_t id = has_gen ? last_gen + 1 : 0;
  has_gen = true; last_gen = id;
  return intern(TC0_K_GEN, 0, 0, NULL, id);
}
Term tc0_gen(uint64_t id) { return has_gen && id <= last_gen ? intern(TC0_K_GEN, 0, 0, NULL, id) : 0; }
Term tc0_code(uint64_t n) { return intern(TC0_K_CODE, 0, 0, NULL, n); }
Term tc0_hole(int i) { return i >= 0 && i < TC0_HOLES ? intern(TC0_K_HOLE, 0, 0, NULL, (uint64_t)i) : 0; }
Term tc0_app(int con, const Term *args) {
  if (con < 0 || con >= ncon) return 0;
  int ar = con_arity[con];
  for (int j = 0; j < ar; j++) if (!is_term(args[j])) return 0;
  return intern(TC0_K_APP, (uint16_t)con, ar, args, 0);
}
uint64_t tc0_last_gen(void) { return last_gen; }
int tc0_kind(Term t) { return is_term(t) ? N[t].kind : 0; }
uint64_t tc0_id(Term t) { return is_atom(t) ? N[t].id : 0; }
const Term *tc0_args(Term t, int *con, int *arity) {
  if (!is_term(t) || N[t].kind != TC0_K_APP) return NULL;
  if (con) *con = N[t].con;
  if (arity) *arity = N[t].arity;
  return &P[N[t].args];
}

/* A flat pattern: an application whose arguments are holes or atoms. */
static bool flat(Term t) {
  if (!is_term(t) || N[t].kind != TC0_K_APP) return false;
  for (int j = 0; j < N[t].arity; j++) {
    Term a = P[N[t].args + (uint32_t)j];
    if (N[a].kind != TC0_K_HOLE && !is_atom(a)) return false;
  }
  return true;
}

int tc0_rule(int nkeep, const Term *keep, Term make, int fresh, const uint8_t *hole_kind) {
  if (sealed || nkeep < 0 || nkeep > TC0_KEEPS || (nkeep && !keep) || !flat(make) || fresh < -1 || fresh >= TC0_HOLES) return -1;
  Rule0 k; memset(&k, 0, sizeof k);
  memset(k.bi, -1, sizeof k.bi); memset(k.bj, -1, sizeof k.bj);
  k.nkeep = (uint8_t)nkeep; k.fresh = (int8_t)fresh;
  for (int i = 0; i < nkeep; i++) {
    if (!flat(keep[i])) return -1;
    k.kcon[i] = N[keep[i]].con;
    for (int j = 0; j < N[keep[i]].arity; j++) {
      Term a = P[N[keep[i]].args + (uint32_t)j];
      Guard g = { (uint8_t)i, (uint8_t)j, 0, 0, 0 };
      if (N[a].kind == TC0_K_HOLE) {
        int h = (int)N[a].id;
        if (h == fresh) return -1;                     /* a fresh name cannot occur in a premise */
        k.used |= 1u << h;
        if (k.bi[h] < 0) { k.bi[h] = (int8_t)i; k.bj[h] = (int8_t)j; continue; }
        g.i0 = (uint8_t)k.bi[h]; g.j0 = (uint8_t)k.bj[h];
      } else g.c = a;
      k.g[k.ng++] = g;
    }
  }
  k.mcon = N[make].con; k.mar = N[make].arity;
  for (int j = 0; j < k.mar; j++) {
    Term a = P[N[make].args + (uint32_t)j];
    if (N[a].kind == TC0_K_HOLE) { k.mh[j] = (int8_t)N[a].id; k.used |= 1u << N[a].id; }
    else { k.mh[j] = -1; k.mc[j] = a; }
  }
  for (int h = 0; h < TC0_HOLES; h++) k.kind[h] = hole_kind ? hole_kind[h] : TC0_ANY;
  if (fresh >= 0 && !(k.used >> fresh & 1)) return -1;  /* a fresh name the conclusion does not use */
  if (nr == rcap) {
    Rule0 *t = realloc(R, (size_t)rcap * 2 * sizeof *t); if (!t) return -1;
    R = t; rcap *= 2;
  }
  R[nr] = k;
  return nr++;
}

void tc0_seal(void) { sealed = true; }
Term tc0_slot(uint64_t s) { return s < nslot && S[s] ? S[s] : dflt; }

static bool slot_room(uint64_t s) {
  if (s >= max_slots) return false;
  if (s < nslot) return true;
  uint64_t c = nslot ? nslot : 1024;
  while (c <= s) c *= 2;
  if (c > max_slots) c = max_slots;
  Term *t = realloc(S, (size_t)c * sizeof *t); if (!t) return false;
  memset(t + nslot, 0, (size_t)(c - nslot) * sizeof *t);
  S = t; nslot = c;
  return true;
}

bool tc0_put(uint64_t s, Term fact) {
  if (!is_term(fact) || N[fact].kind != TC0_K_APP || !N[fact].ground || !slot_room(s)) return false;
  S[s] = fact;
  return true;
}

/* The values of a rule's holes for the given premises and inputs, without minting.  False if the
   rule does not apply. */
static bool match(const Rule0 *k, const uint64_t *keep, const Term *in, Term *val) {
  const Term *a[TC0_KEEPS];
  if (k->nkeep && !keep) return false;
  for (int i = 0; i < k->nkeep; i++) {
    Term f = tc0_slot(keep[i]);
    if (!f || N[f].kind != TC0_K_APP || N[f].con != k->kcon[i]) return false;
    a[i] = &P[N[f].args];
  }
  for (int g = 0; g < k->ng; g++) {
    const Guard *q = &k->g[g];
    if (a[q->i][q->j] != (q->c ? q->c : a[q->i0][q->j0])) return false;
  }
  for (int h = 0; h < TC0_HOLES; h++) {
    if (!(k->used >> h & 1) || h == k->fresh) continue;
    if (k->bi[h] >= 0) val[h] = a[k->bi[h]][k->bj[h]];
    else if (in && is_term(in[h]) && N[in[h]].ground) val[h] = in[h];
    else return false;
    if (k->kind[h] == TC0_GEN_ONLY && N[val[h]].kind != TC0_K_GEN) return false;
  }
  return true;
}

bool tc0_fire(int r, const uint64_t *keep, const Term *in, uint64_t dest) {
  if (r < 0 || r >= nr) return false;
  const Rule0 *k = &R[r];
  Term val[TC0_HOLES] = { 0 };
  if (!match(k, keep, in, val)) return false;
  if (k->fresh >= 0 && has_gen && last_gen == UINT64_MAX) return false;
  if (!slot_room(dest) || !reserve(2, k->mar)) return false;  /* from here on nothing can fail */
  if (k->fresh >= 0) val[k->fresh] = tc0_mint();
  Term b[TC0_ARITY];
  for (int j = 0; j < k->mar; j++) b[j] = k->mh[j] >= 0 ? val[k->mh[j]] : k->mc[j];
  S[dest] = intern(TC0_K_APP, k->mcon, k->mar, b, 0);
  return true;
}

bool tc0_default(int r, const Term *in) {
  if (sealed || r < 0 || r >= nr || R[r].nkeep || R[r].fresh >= 0) return false;
  Term val[TC0_HOLES] = { 0 }, b[TC0_ARITY];
  const Rule0 *k = &R[r];
  if (!match(k, NULL, in, val)) return false;
  for (int j = 0; j < k->mar; j++) b[j] = k->mh[j] >= 0 ? val[k->mh[j]] : k->mc[j];
  Term f = intern(TC0_K_APP, k->mcon, k->mar, b, 0);
  if (!f) return false;
  dflt = f;
  return true;
}
