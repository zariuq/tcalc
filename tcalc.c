#include "tcalc.h"
#include "compiled/ordinary_flat_adapter.h"
#include <stdlib.h>
#include <string.h>
#ifdef __AVX2__
#include <immintrin.h>
#endif

/* ---- terms: hash-consed n-ary nodes; args live in one word arena ---- */
enum { F_META = 1, F_BV = 2, F_NAME = 4, F_PLAIN = 8, F_BIRTH = 16 };   /* F_BIRTH: made (or built over a node made) in a tc_birth scope, not hash-consed */
typedef struct {
  uint8_t kind, bound, flags, sort;
  uint8_t arity, pad; uint16_t cep; /* cep: context epoch */
  uint32_t head, args;
  uint64_t bm, vm;                  /* bm: bound variables it may mention; vm: holes */
} Node;
typedef struct {
  uint8_t sort, arity, ndum, isdef; Term t0;
  uint32_t abound; Term body;
  uint64_t retdeps, h0;
  uint8_t asort[TC_ARGS];
} Con;
typedef struct { uint32_t adeps[TC_ARGS]; uint8_t dsort[TC_VARS]; } ConDef;
typedef struct { uint8_t i, j, i0, j0; } Guard;
typedef struct { uint64_t avoid; uint16_t sort; uint8_t bound; } Hole;   /* a rule hole: sort, bound flag, and the holes it must avoid */
typedef struct {
  uint32_t ro; int n; uint32_t h0, kcode, mcode; /* the rule, at RP + ro; holes: HK[h0 .. h0+n) */
  Term make; uint32_t fl;                        /* flat rules: their layout, FL[fl] */
  uint8_t nkeep, mspace, fibre; bool pure, flat, mflat, prepped, fprepped, ks_zero;
  uint64_t implied, mimplied;       /* holes whose sort kept/make pattern formation guarantees */
  uint64_t bounds, pad;             /* the bound holes */
  uint64_t inputs, outs;            /* declared (or, for a derived rule, derived) input holes; operation outputs */
  int16_t mks[5];                   /* each make's static space, -1 if a hole names it, -2 for a dynamic space */
  uint8_t nmk;
  bool fns, derived, range_ok, barred, dynmake;   /* dynmake: some make's space is computed at firing */
} RuleK;
typedef struct {                    /* a flat rule: premise tags, field guards, and where the result's fields come from */
  uint32_t ktag[TC_HYPS], mhead; uint16_t msort, mar, nguard, nconst;
  Guard guard[32]; uint8_t mi[TC_ARGS], mj[TC_ARGS]; Term mc[32];
  uint32_t packed_guard[32], packed_make[TC_ARGS];
  bool ordinary;
} Flat;
typedef struct __attribute__((aligned(64))) {
  uint8_t perm[16];
  uint32_t mperm[4];
  uint32_t ktag[4], mtag;
  uint8_t ok, single_tag, pad[10];
} Flat4;

static Node *N; static Term *A, *H; static uint64_t *vval, *Nid, *Nmax, upair[1024];
static uint32_t *vis, *Nhslot, vgen, ugen[1024], ug, nn, ncap, na, acap, hmask; static Occ *Nocc;
static Con *C; static ConDef *CD; static int ncon; static uint8_t sorts[256]; static int nsort;
static RuleK *R; static int nr; static Hole *HK; static uint32_t nhk, hkcap; static Flat *FL; static uint32_t nfl, flcap; static uint8_t *RP; static size_t nrp, rpcap;
static Flat4 FF[64];
#ifdef TC_ORDINARY_FLAT_TEST_HOOKS
uint64_t tc_test_ordinary_flat_leaf_calls;
uint64_t tc_test_ordinary_flat_leaf_fired;
uint64_t tc_test_ordinary_flat_refusals;
uint64_t tc_test_ordinary_flat_slow_calls;
#endif
#define RULE(k) ((const Rule *)(RP + (k)->ro))
#define HOLE(k, h) HK[(k)->h0 + (uint32_t)(h)]
static uint32_t * code; static uint32_t ncode;
static Term *Wt, *Wtag, *Warg, *Wrow, *Wsp; static Occ *Wnext, *Wprev, Wlive[256]; static uint8_t *Ws, *Wa, *Wmark, space_has_flat[256]; static uint32_t nw, wcap;
static Term *bind, *trail, qmeta[TC_VARS]; static uint16_t *Msort, *msort_prev; static uint32_t *msort_who, nmeta, ntrail;
/* The tables outlive tc_init. Each keeps its allocation (cap*: elements) and tc_init clears it only over
   the extent the previous state may have written, which leaves every table all zero, as calloc would,
   at the cost of what the last run used rather than of the table's size. Extents: the counters, with
   the high-water marks of what release and prep_rule rolled back, of capacity grown during the run, and
   of the slots slot mode fills above the board;
   H's slots scatter, so every slot written is logged (Hlog) and cleared, or the whole table when more
   were written than the log holds; the meta tables are small and cleared whole. Nid, Nmax and Nocc are made on first use in a run, as before: between runs their
   storage waits, cleared, as spare*. */
static size_t capN, capA, capH, capVis, capNhs, capVval, capNid, capNmax, capNocc, capC, capCD, capR, capCode,
              capWt, capWtag, capWarg, capWrow, capWsp, capWnext, capWprev, capWs, capWa, capWmark,
              capBind, capTrail, capMsort, capMsortPrev, capMsortWho;
static uint32_t nodes_hw, args_hw, code_hw, w_hw;
#define TC_HLOG (1u << 16)
static uint32_t Hlog[TC_HLOG], nhlog; static bool hlog_over;
static inline void hlog(uint32_t i) { if (nhlog < TC_HLOG) Hlog[nhlog++] = i; else hlog_over = true; }
static uint64_t *spareNid, *spareNmax; static Occ *spareNocc;
/* Keeps table p for n elements: cleared over its first d when it holds n, otherwise made afresh. */
#define TC_KEEP(p, cap, d, n) do { \
    if ((p) && (cap) >= (size_t)(n)) memset((p), 0, ((size_t)(d) < (cap) ? (size_t)(d) : (cap)) * sizeof *(p)); \
    else { free(p); (p) = calloc((size_t)(n), sizeof *(p)); (cap) = (p) ? (size_t)(n) : 0; } \
  } while (0)
/* A lazily made table at the end of a run: cleared over its first d and kept as the spare. */
#define TC_SPARE(live, spare, cap, d) do { \
    if (live) { memset((live), 0, ((size_t)(d) < (cap) ? (size_t)(d) : (cap)) * sizeof *(live)); \
                free(spare); (spare) = (live); (live) = NULL; } \
  } while (0)
/* Makes a lazily made table for n elements: the spare when it holds n, otherwise afresh. */
#define TC_TAKE(live, spare, cap, n) \
  ((spare) && (cap) >= (size_t)(n) ? ((live) = (spare), (spare) = NULL, true) \
   : (free(spare), (spare) = NULL, (cap) = ((live) = calloc((size_t)(n), sizeof *(live))) ? (size_t)(n) : 0, (live) != NULL))
static Term NE[65536][2], ncache[4096]; static int nne; static uint16_t ncache_sort;
static uint64_t next_name, nsteps; static uint16_t cepoch; static uint32_t tmark, tamark; static bool tscope, bscope, lok, slot_mode, wt_dirty, has_widecon, flat4_board; static bool sealed, has_take, has_query, protect[256];
static uint16_t space_sort_id; static Term space_terms[256]; static int handle_con_id; static Occ last_extra_occ[4];
static int q_quote_con, q_act_con, q_lam_con, q_app_con, rho_quote_con, rho_drop_con; static bool rho_allow_drop;
static int cn; static uint16_t csort[TC_VARS]; static uint8_t cbound[TC_VARS];
static uint64_t cbm[TC_VARS], cdeps[TC_VARS]; static Term cvar[TC_VARS], ecvar[TC_VARS];
static uint16_t bv_sort[64]; static unsigned bv_idx[64]; static int nbv;
static const RuleK *cur_k;
enum { CAP_CON = 16384, CAP_RULE = 65536, CAP_CODE = 1u << 20, CAP_META = 1u << 14, CAP_FN = 256 };
/* The sealed function registry (tc_fn) and the evidence spaces (tc_publishers): fixed by the seal. */
typedef struct { char name[TC_FN_NAME]; uint8_t kind, nin, nout; TcFn fn; uint8_t sha[32]; } FnEntry;
static FnEntry FNR[CAP_FN]; static int nfn;
static bool pubset[256], has_pubset; static int *pubs[256]; static uint32_t npub[256], cpub[256];

static Term mk(uint8_t k, uint32_t head, uint16_t s, uint8_t bound, uint64_t id, int ar, const Term *a);
static inline bool has_meta(Term t) { return (N[t].flags & F_META) != 0; }
static inline bool has_bv(Term t) { return (N[t].flags & F_BV) != 0; }
/* A located pattern node (tc_at_space / tc_at_birth): rule syntax, never a fact or an argument. */
static inline bool at_node_any(Term t) { return N[t].kind == K_APP && N[t].head >= 0xFFFFFFFEu; }
/* Names are minted before they are used: every name in a posted fact, a tell, a rule, a lemma or a hole
   value lies below the counter (ids with top bits 01 count as minted), so a fresh name is new to the
   whole state, pure rules included. */
static inline bool name_ok(Term t) { return !(N[t].flags & F_NAME) || Nmax[t] <= next_name; }

#ifdef TC_INIT_VERIFY
#include <stdio.h>
/* -DTC_INIT_VERIFY: tc_init checks that every table it keeps is all zero over its whole allocation. */
static void zero_or_die(const void *p, size_t bytes, const char *what) {
  static const unsigned char zero[4096];
  const unsigned char *b = p;
  for (size_t i = 0; p && i < bytes; i += sizeof zero) {
    size_t n = bytes - i < sizeof zero ? bytes - i : sizeof zero;
    if (memcmp(b + i, zero, n)) { fprintf(stderr, "tc_init: %s not cleared (within bytes %zu..%zu)\n", what, i, i + n); abort(); }
  }
}
#define TC_VERIFY(p, cap) zero_or_die((p), (cap) * sizeof *(p), #p)
static void init_verify(void) {
  TC_VERIFY(N, capN); TC_VERIFY(vis, capVis); TC_VERIFY(Nhslot, capNhs); TC_VERIFY(vval, capVval);
  TC_VERIFY(spareNid, capNid); TC_VERIFY(spareNmax, capNmax); TC_VERIFY(spareNocc, capNocc);
  TC_VERIFY(A, capA); TC_VERIFY(H, capH); TC_VERIFY(C, capC); TC_VERIFY(CD, capCD); TC_VERIFY(R, capR); TC_VERIFY(code, capCode);
  TC_VERIFY(Wt, capWt); TC_VERIFY(Wtag, capWtag); TC_VERIFY(Warg, capWarg); TC_VERIFY(Wrow, capWrow); TC_VERIFY(Wsp, capWsp);
  TC_VERIFY(Wnext, capWnext); TC_VERIFY(Wprev, capWprev); TC_VERIFY(Ws, capWs); TC_VERIFY(Wa, capWa); TC_VERIFY(Wmark, capWmark);
  TC_VERIFY(bind, capBind); TC_VERIFY(trail, capTrail); TC_VERIFY(Msort, capMsort); TC_VERIFY(msort_prev, capMsortPrev);
  TC_VERIFY(msort_who, capMsortWho);
}
#endif
bool tc_init(uint32_t nodes, uint32_t occs) {
  if (nodes > (1u << 28) || occs > (1u << 28)) return false;
  if (nodes < 256) nodes = 256;
  if (occs < 2) occs = 2;
  free(HK); HK = NULL; nhk = hkcap = 0; free(FL); FL = NULL; nfl = flcap = 0; free(RP); RP = NULL; nrp = rpcap = 0;
  /* the extents the previous state wrote: below which each table is cleared (or made afresh) */
  size_t dn = nn > nodes_hw ? nn : nodes_hw, da = na > args_hw ? na : args_hw, dc = ncode > code_hw ? ncode : code_hw;
  size_t dh = H && hlog_over ? (size_t)hmask + 1 : 0, dw = nw > w_hw ? nw : w_hw;
  if (H && !hlog_over) for (uint32_t i = 0; i < nhlog; i++) H[Hlog[i]] = 0;
  nhlog = 0; hlog_over = false;
  uint32_t hsize = 1;
  while (hsize < 4 * nodes) hsize <<= 1;
  TC_KEEP(N, capN, dn, nodes); TC_KEEP(vis, capVis, dn, nodes); TC_KEEP(Nhslot, capNhs, dn, nodes); TC_KEEP(vval, capVval, dn, nodes);
  TC_SPARE(Nid, spareNid, capNid, dn); TC_SPARE(Nmax, spareNmax, capNmax, dn); TC_SPARE(Nocc, spareNocc, capNocc, dn);
  TC_KEEP(A, capA, da, (size_t)nodes * 4); TC_KEEP(H, capH, dh, hsize);
  TC_KEEP(C, capC, ncon, CAP_CON); TC_KEEP(CD, capCD, ncon, CAP_CON); TC_KEEP(R, capR, nr, CAP_RULE); TC_KEEP(code, capCode, dc, CAP_CODE);
  TC_KEEP(Wt, capWt, dw, occs); TC_KEEP(Wtag, capWtag, dw, occs); TC_KEEP(Warg, capWarg, dw, occs); TC_KEEP(Wrow, capWrow, dw * 4, (size_t)occs * 4);
  TC_KEEP(Wsp, capWsp, dw, occs); TC_KEEP(Wnext, capWnext, dw, occs); TC_KEEP(Wprev, capWprev, dw, occs);
  TC_KEEP(Ws, capWs, dw, occs); TC_KEEP(Wa, capWa, dw, occs); TC_KEEP(Wmark, capWmark, dw, occs);
  TC_KEEP(bind, capBind, CAP_META, CAP_META); TC_KEEP(trail, capTrail, CAP_META, CAP_META);
  TC_KEEP(Msort, capMsort, CAP_META, CAP_META); TC_KEEP(msort_prev, capMsortPrev, CAP_META, CAP_META); TC_KEEP(msort_who, capMsortWho, CAP_META, CAP_META);
  if (!(N && A && H && vis && Nhslot && vval && C && CD && R && code && Wt && Wtag && Warg && Wrow && Wsp && Wnext && Wprev && Ws && Wa && Wmark && bind && trail && Msort && msort_prev && msort_who)) return false;
#ifdef TC_INIT_VERIFY
  init_verify();
#endif
  hmask = hsize - 1; ncap = nodes; acap = nodes * 4; wcap = occs; nodes_hw = args_hw = code_hw = w_hw = 0;
  vgen = 0; ug = 1; nn = 1; na = 0; ncon = 0; nsort = 1; nr = 0; ncode = 0; nw = 1; nmeta = 0; ntrail = 0; nne = 0;
  cepoch = 1;
  tscope = false; bscope = false; lok = false; slot_mode = false; wt_dirty = false; has_widecon = false; flat4_board = false; ncache_sort = 0xFFFFu;
  next_name = 0; nsteps = 0; sealed = false; has_take = false; has_query = false; cn = 0; nbv = 0; memset(Wlive, 0, sizeof Wlive); memset(space_has_flat, 0, sizeof space_has_flat); cur_k = NULL;
  space_sort_id = 0; handle_con_id = -1; q_quote_con = q_act_con = q_lam_con = q_app_con = -1; rho_quote_con = rho_drop_con = -1; rho_allow_drop = false;
  memset(space_terms, 0, sizeof space_terms); memset(last_extra_occ, 0, sizeof last_extra_occ);
  memset(protect, 0, sizeof protect); memset(ncache, 0, sizeof ncache); memset(ugen, 0, sizeof ugen); memset(sorts, 0, sizeof sorts); memset(ecvar, 0, sizeof ecvar); memset(FF, 0, sizeof FF);
  nfn = 0; memset(FNR, 0, sizeof FNR); has_pubset = false; memset(pubset, 0, sizeof pubset);
  for (int s = 0; s < 256; s++) { free(pubs[s]); pubs[s] = NULL; npub[s] = cpub[s] = 0; }
  for (int h = 0; h < TC_VARS; h++) qmeta[h] = mk(K_META, (CAP_META - TC_VARS) + (uint32_t)h, TC_ANY, 0, 0, 0, NULL);
  return true;
}

static inline uint64_t hash(uint8_t k, uint32_t head, uint16_t s, uint64_t id, int ar, const Term *a) {
  uint64_t h = ((uint64_t)head << 24 | (uint64_t)s << 8 | k) * 0x9E3779B97F4A7C15u ^ id * 0xBF58476D1CE4E5B9u;
  for (int i = 0; i < ar; i++) h = (h ^ a[i]) * 0xD6E8FEB86659FD93u;
  return h ^ (h >> 32);
}

static __attribute__((noinline)) bool grow(uint32_t args) { /* double the node arena; rehash oldest first when the table fills */
  uint32_t nc = nn >= ncap ? 2 * ncap : ncap, ac = acap;
  while (na + args > ac) ac *= 2;
  if (nc > (1u << 28) || ac > (1u << 30)) return false;
  if (ac > acap) {
    if (ac > capA) { Term *a2 = realloc(A, ac * sizeof *A); if (!a2) return false; A = a2; capA = ac; }
    acap = ac;
    if (ac > args_hw) args_hw = ac;                       /* new space: cleared whole at the next tc_init */
  }
  if (nc <= ncap) return true;
  if (nc > nodes_hw) nodes_hw = nc;
  if (nc > capN) { Node *n2 = realloc(N, nc * sizeof *N); if (!n2) return false; N = n2; capN = nc; }
  if (nc > capVval) { uint64_t *w2 = realloc(vval, nc * sizeof *vval); if (!w2) return false; vval = w2; capVval = nc; }
  if (Nid) {
    if (nc > capNid) { uint64_t *id2 = realloc(Nid, nc * sizeof *Nid); if (!id2) return false; Nid = id2; capNid = nc; }
    if (nc > capNmax) { uint64_t *mx2 = realloc(Nmax, nc * sizeof *Nmax); if (!mx2) return false; Nmax = mx2; capNmax = nc; }
  }
  if (nc > capVis) { uint32_t *v2 = realloc(vis, nc * sizeof *vis); if (!v2) return false; vis = v2; capVis = nc; }
  if (nc > capNhs) { uint32_t *hs2 = realloc(Nhslot, nc * sizeof *Nhslot); if (!hs2) return false; Nhslot = hs2; capNhs = nc; }
  if (Nocc) {
    if (nc > capNocc) { Occ *oc2 = realloc(Nocc, nc * sizeof *Nocc); if (!oc2) return false; Nocc = oc2; capNocc = nc; }
    memset(Nocc + ncap, 0, (nc - ncap) * sizeof *Nocc);
  }
  memset(vis + ncap, 0, (nc - ncap) * sizeof *vis);
  if (4 * (uint64_t)nc <= (uint64_t)hmask + 1) { ncap = nc; return true; }   /* load at most a quarter */
  uint32_t m = 2 * (hmask + 1); Term *h2 = calloc(m, sizeof *h2);
  if (!h2) return false;                                  /* capacity stays: the table keeps its load bound */
  ncap = nc;
  free(H); H = h2; hmask = m - 1; capH = m;
  for (Term t = 1; t < nn; t++) if (Nhslot[t] != UINT32_MAX) {
    Node *x = &N[t];
    uint64_t id = x->kind == K_VAR ? x->bm : x->kind == K_NAME ? Nid[t] : 0;
    uint32_t i = (uint32_t)hash(x->kind, x->head, x->sort, id, x->arity, &A[x->args]) & hmask;
    while (H[i]) i = (i + 1) & hmask;
    H[i] = t; Nhslot[t] = i; hlog(i);
  }
  return true;
}

static Term mk(uint8_t k, uint32_t head, uint16_t s, uint8_t bound, uint64_t id, int ar, const Term *a) {
  uint32_t i = 0;
  if (!bscope) {
    i = (uint32_t)hash(k, head, s, id, ar, a) & hmask;
    for (Term t; (t = H[i]); i = (i + 1) & hmask) {
      Node *x = &N[t];
      if (x->head != head || x->kind != k || x->arity != ar || x->sort != s || x->bound != bound) continue;
      if (k == K_VAR ? x->bm != id : k == K_NAME && Nid[t] != id) continue;
      const Term *b = &A[x->args]; int j = 0;
      while (j < ar && b[j] == a[j]) j++;
      if (j < ar) continue;
      if (x->vm && x->cep != cepoch && k == K_APP) {         /* an older term met again: refresh its scope verdict */
        bool scoped = true;
        for (j = 0; j < ar; j++) scoped &= !N[a[j]].vm || N[a[j]].cep == cepoch;
        if (scoped) x->cep = cepoch;
      }
      return t;
    }
  }
  if (nn >= ncap || na + ar > acap) {                     /* grow, then intern again: a may point into A */
    Term c[TC_ARGS];
    if (ar > TC_ARGS) return 0;
    for (int j = 0; j < ar; j++) c[j] = a[j];
    return grow((uint32_t)ar) ? mk(k, head, s, bound, id, ar, ar ? c : NULL) : 0;
  }
  Term t = nn++;
  uint8_t fl = (k == K_META ? F_META : k == K_BV ? F_BV : k == K_NAME ? F_NAME : 0) | (bscope ? F_BIRTH : 0);
  uint64_t bm = k == K_BV ? 1ull << head : k == K_VAR ? id : 0;
  uint64_t vm = k == K_VAR ? 1ull << head : 0;
  uint32_t a0 = na; na += (uint32_t)ar;
  bool scoped = true;                                     /* well-scoped in the current context, if its children are */
  for (int j = 0; j < ar; j++) {
    Term cj = a[j];
    A[a0 + (uint32_t)j] = cj;
    const Node *y = &N[cj];
    bm |= y->bm; vm |= y->vm; fl |= y->flags;
    scoped &= !y->vm || y->cep == cepoch;
  }
  N[t] = (Node){ k, bound, fl, (uint8_t)s, (uint8_t)ar, 0, k == K_APP && scoped ? cepoch : 0, head, a0, bm, vm };
  if (bscope) { Nhslot[t] = UINT32_MAX; return t; }
  Nhslot[t] = i;
  if (__builtin_expect((fl & F_NAME) != 0, 0)) {
    Nid[t] = k == K_NAME ? id : 0;
    /* minted names are below the counter; 01-prefixed ids and the words of a word sort are literals */
    uint64_t mx = k == K_NAME ? ((id >> 62) == 1 || (sorts[(uint8_t)s] & SORT_WORD) ? 0 : (id == UINT64_MAX ? id : id + 1)) : 0;
    for (int j = 0; j < ar; j++) if ((N[a[j]].flags & F_NAME) && Nmax[a[j]] > mx) mx = Nmax[a[j]];
    Nmax[t] = mx;
  }
  hlog(i);
  return H[i] = t;
}

static const Term *argv(Term t) { return &A[N[t].args]; }
static bool is_bvar(Term t) { return (N[t].kind == K_VAR && N[t].bound) || N[t].kind == K_BV; }
uint16_t tc_sort_of(Term t) { return t < nn ? N[t].sort : 0; }
uint64_t tc_name_id(Term t) { return t < nn && N[t].kind == K_NAME ? Nid[t] : 0; }
uint64_t tc_steps(void) { return nsteps; }
void tc_node(Term t, uint8_t *k, uint32_t *head, int *ar, const Term **a) {
  if (t >= nn) t = 0;
  *k = N[t].kind; *head = N[t].head; *ar = N[t].arity; *a = argv(t);
}
/* The name tables, made when the run's first name is (from the spare when it holds the arena). */
static bool names_on(void) { return TC_TAKE(Nid, spareNid, capNid, ncap) && TC_TAKE(Nmax, spareNmax, capNmax, ncap); }
static __attribute__((noinline)) Term tc_name_slow(uint16_t s, uint64_t id) {
  if (s >= (uint16_t)nsort) return 0;
  if (!Nid && !names_on()) return 0;
  Term c = id < 4096 ? ncache[id] : 0;
  if (c && c < nn && N[c].kind == K_NAME && Nid[c] == id && N[c].sort == s) {
    if (!tscope && ncache_sort == s && id < next_name) N[c].flags |= F_PLAIN;
    return c;
  }
  Term t = mk(K_NAME, 0, s, 0, id, 0, NULL);
  if (id < 4096 && t && !tscope) {
    if (ncache_sort == 0xFFFFu) ncache_sort = s;
    if (ncache_sort == s) { ncache[id] = t; if (id < next_name) N[t].flags |= F_PLAIN; }
  }
  return t;
}
Term tc_name(uint16_t s, uint64_t id) {
  if (__builtin_expect(!tscope && s == ncache_sort && id < 4096 && ncache[id] != 0, 1)) return ncache[id];
  return tc_name_slow(s, id);
}
Term tc_bv(uint16_t s, unsigned i) {
  if (s >= (uint16_t)nsort || (sorts[s] & (SORT_STRICT | SORT_WORD))) return 0;
  int bit = -1;
  for (int j = 0; j < nbv; j++) if (bv_sort[j] == s && bv_idx[j] == i) { bit = j; break; }
  if (bit < 0) {
    if (nbv >= 64) return 0;
    bit = nbv++; bv_sort[bit] = s; bv_idx[bit] = i;
  }
  return mk(K_BV, (uint32_t)bit, s, 1, 0, 0, NULL);
}
Term tc_meta(void) { tscope = bscope = false; return nmeta < CAP_META - TC_VARS ? mk(K_META, nmeta++, TC_ANY, 0, 0, 0, NULL) : 0; }
uint64_t tc_fresh_name(void) { return next_name >= UINT64_MAX - 1 ? UINT64_MAX : next_name++; }
uint64_t tc_next_name(void) { return next_name; }
static void prep_flat(RuleK *k);
static bool rule_bars(const RuleK *k, int rid);
void tc_protect(uint8_t s) {
  protect[s] = true; if (!s) flat4_board = false;
  if (sealed) for (int i = 0; i < nr; i++) if (!R[i].barred && rule_bars(&R[i], i)) R[i].barred = true;   /* protection after the seal */
}
void tc_seal(void) {
  sealed = true;
  for (int i = 0; i < nr; i++) {
    if (!R[i].fprepped) prep_flat(&R[i]);
    R[i].barred = rule_bars(&R[i], i);                    /* range restriction and evidence spaces, rechecked */
  }
  flat4_board = slot_mode && !has_take && !protect[0] && ncon == 1 && C[0].arity == 4 &&
                ncache_sort < (uint16_t)nsort &&
                C[0].asort[0] == ncache_sort && C[0].asort[1] == ncache_sort &&
                C[0].asort[2] == ncache_sort && C[0].asort[3] == ncache_sort;
  if (flat4_board) space_has_flat[0] = true;              /* tc_flat_put writes rows of space 0 in place */
}

int tc_sort(uint8_t flags) { if (nsort >= 256) return -1; sorts[nsort] = flags; return nsort++; }

static bool binders_ok(int n, const Binder *b, uint64_t *bits) {   /* deps: earlier bound positions */
  if (n < 0 || (n > 0 && !b)) return false;
  uint64_t bound = 0, next = 1;
  for (int i = 0; i < n; i++) {
    if (b[i].sort >= nsort || (b[i].deps & ~bound)) return false;
    if (b[i].bound) {
      if ((sorts[b[i].sort] & (SORT_STRICT | SORT_WORD)) || !next) return false;
      bound |= 1ull << i; if (bits) bits[i] = next; next <<= 1;
    } else if (bits) {
      bits[i] = 0;
      for (int j = 0; j < i; j++) if (b[i].deps >> j & 1) bits[i] |= bits[j];
    }
  }
  return true;
}

int tc_con(uint16_t s, uint64_t retdeps, int ar, const Binder *a) {
  uint64_t bound = 0;
  if (ncon >= CAP_CON || ar < 0 || ar > TC_ARGS || s >= nsort || (sorts[s] & (SORT_PURE | SORT_WORD)) || !binders_ok(ar, a, NULL)) return -1;
  for (int i = 0; i < ar; i++) if (a[i].bound) bound |= 1ull << i;
  if (retdeps & ~bound) return -1;
  uint64_t h0 = ((uint64_t)(uint32_t)ncon << 24 | (uint64_t)s << 8 | K_APP) * 0x9E3779B97F4A7C15u;
  C[ncon] = (Con){ .sort = (uint8_t)s, .arity = (uint8_t)ar, .abound = (uint32_t)bound, .retdeps = retdeps, .h0 = h0 };
  if (ar > 4) has_widecon = true;
  for (int i = 0; i < ar; i++) C[ncon].asort[i] = (uint8_t)a[i].sort;
  if (bound) for (int i = 0; i < ar; i++) CD[ncon].adeps[i] = (uint32_t)a[i].deps;
  return ncon++;
}

bool tc_ctx(int n, const Binder *v) {                    /* all or nothing */
  uint64_t bits[TC_VARS]; Term vars[TC_VARS];
  tscope = bscope = false; lok = false;
  if (n < 0 || n > TC_VARS || !binders_ok(n, v, bits)) return false;
  bool bump = false;
  for (int i = 0; i < n; i++) {
    if (!(vars[i] = mk(K_VAR, (uint32_t)i, v[i].sort, v[i].bound, bits[i], 0, NULL))) return false;
    bump |= ecvar[i] && ecvar[i] != vars[i];
  }
  if (bump) {
    if (!++cepoch) { for (uint32_t i = 0; i < nn; i++) N[i].cep = 0; cepoch = 1; }
    memset(ecvar, 0, sizeof ecvar);
  }
  for (int i = 0; i < n; i++) {
    csort[i] = v[i].sort; cbound[i] = v[i].bound; cdeps[i] = v[i].deps; cbm[i] = bits[i];
    cvar[i] = ecvar[i] = vars[i]; N[vars[i]].cep = cepoch;
  }
  cn = n;
  return true;
}
bool tc_ctx_push(Binder v) {                             /* one more variable; earlier terms stay well-scoped */
  uint64_t bound = 0, bits = 0; int nbd = 0;
  for (int i = 0; i < cn; i++) if (cbound[i]) { bound |= 1ull << i; nbd++; }
  if (cn >= TC_VARS || v.sort >= nsort || (v.deps & ~bound)) return false;
  if (v.bound) { if ((sorts[v.sort] & (SORT_STRICT | SORT_WORD)) || nbd >= 64) return false; bits = 1ull << nbd; }
  else for (int j = 0; j < cn; j++) if (v.deps >> j & 1) bits |= cbm[j];
  Term x = mk(K_VAR, (uint32_t)cn, v.sort, v.bound, bits, 0, NULL);
  if (!x) return false;
  if (ecvar[cn] && ecvar[cn] != x) {
    if (!++cepoch) { for (uint32_t i = 0; i < nn; i++) N[i].cep = 0; cepoch = 1; }
    memset(ecvar, 0, sizeof ecvar);
    for (int i = 0; i < cn; i++) { ecvar[i] = cvar[i]; N[cvar[i]].cep = cepoch; }
  }
  csort[cn] = v.sort; cbound[cn] = v.bound; cdeps[cn] = v.deps; cbm[cn] = bits;
  cvar[cn] = ecvar[cn] = x; cn++; N[x].cep = cepoch;
  return true;
}
Term tc_v(int i) { return i >= 0 && i < cn ? cvar[i] : 0; }

/* Constrain an unknown's sort on the trail (a sort-only entry: trail[] = UINT32_MAX), so that the
   undo of a refused firing removes the constraint with the bindings. */
static bool msort_set(uint32_t mh, uint16_t s) {
  if (Msort[mh] == s) return true;
  if (ntrail >= CAP_META) return false;
  msort_who[ntrail] = mh; msort_prev[ntrail] = Msort[mh]; trail[ntrail++] = UINT32_MAX;
  Msort[mh] = s;
  return true;
}
static __attribute__((noinline)) Term app_intern(int con, const Term *a) {
  Con *c = &C[con];
  int ar = c->arity;
  if (!ar) {
    Term t = c->t0;
    if (t && t < nn && N[t].kind == K_APP && N[t].head == (uint32_t)con && !N[t].arity) return t;
    return c->t0 = mk(K_APP, (uint32_t)con, c->sort, 0, 0, 0, NULL);
  }
  if (!a) return 0;
  uint16_t cs = c->sort;
  uint64_t h = c->h0;
  for (int k = 0; k < ar; k++) h = (h ^ a[k]) * 0xD6E8FEB86659FD93u;
  uint32_t slot = (uint32_t)(h ^ (h >> 32)) & hmask;
  Term hit = 0;
  for (Term t; (t = H[slot]); slot = (slot + 1) & hmask) {
    Node *x = &N[t];
    if (x->head != (uint32_t)con || x->kind != K_APP) continue;
    const Term *b = &A[x->args]; int j = 0;
    while (j < ar && b[j] == a[j]) j++;
    if (j < ar) continue;
    if (__builtin_expect((x->flags & F_META) != 0, 0)) { hit = t; break; }
    if (__builtin_expect(x->vm && x->cep != cepoch, 0)) {
      bool sc = true;
      for (j = 0; j < ar; j++) sc &= !N[a[j]].vm || N[a[j]].cep == cepoch;
      if (sc) x->cep = cepoch;
    }
    return t;
  }
  uint32_t ab = c->abound;
  uint64_t bm = 0, vm = 0;
  uint8_t fl = 0;
  bool scoped = true, has_m = false;
  for (int i = 0; i < ar; i++) {
    Term x = a[i];
    if (!x || x >= nn) return 0;
    const Node *nx = &N[x];
    if (__builtin_expect(nx->head >= 0xFFFFFFFEu && nx->kind == K_APP, 0)) return 0;   /* located nodes are not arguments */
    if (__builtin_expect(nx->sort != c->asort[i], 0)) {
      if (nx->kind == K_META && !(ab >> i & 1)) { has_m = true; goto step; }
      return 0;
    }
    if ((ab >> i & 1) && !((nx->kind == K_VAR && nx->bound) || nx->kind == K_BV)) return 0;
  step:
    bm |= nx->bm; vm |= nx->vm; fl |= nx->flags;
    scoped &= !nx->vm || nx->cep == cepoch;
  }
  if (__builtin_expect(has_m, 0)) {
    for (int i = 0; i < ar; i++) if (N[a[i]].kind == K_META) {
      uint32_t mh = N[a[i]].head;
      if (mh >= CAP_META - TC_VARS) continue;
      uint16_t s = c->asort[i];
      if (Msort[mh] != TC_ANY && Msort[mh] != s) return 0;
      Term x = a[i]; while (N[x].kind == K_META && bind[N[x].head]) x = bind[N[x].head];
      uint16_t ws = N[x].kind == K_META ? Msort[N[x].head] : N[x].sort;
      if (ws != TC_ANY && ws != s) return 0;
      if (!msort_set(mh, s)) return 0;
      if (N[x].kind == K_META && N[x].head < CAP_META - TC_VARS && !msort_set(N[x].head, s)) return 0;
    }
  }
  if (hit) {
    if (vm && scoped && N[hit].cep != cepoch) N[hit].cep = cepoch;
    return hit;
  }
  if (__builtin_expect(nn >= ncap || na + ar > acap, 0))
    return mk(K_APP, (uint32_t)con, cs, 0, 0, ar, a);
  Term t = nn++;
  uint32_t a0 = na; na += (uint32_t)ar;
  for (int j = 0; j < ar; j++) A[a0 + (uint32_t)j] = a[j];
  N[t] = (Node){ K_APP, 0, fl, (uint8_t)cs, (uint8_t)ar, 0, scoped ? cepoch : 0, (uint32_t)con, a0, bm, vm };
  Nhslot[t] = slot;
  if (__builtin_expect((fl & F_NAME) != 0, 0)) {
    Nid[t] = 0;
    uint64_t mx = 0;
    for (int j = 0; j < ar; j++) if ((N[a[j]].flags & F_NAME) && Nmax[a[j]] > mx) mx = Nmax[a[j]];
    Nmax[t] = mx;
  }
  hlog(slot);
  return H[slot] = t;
}

Term tc_app(int con, const Term *a) {
  if ((unsigned)con >= (unsigned)ncon) return 0;
  if (!bscope) return app_intern(con, a);
  Con *c = &C[con];
  int ar = c->arity;
  if (ar && !a) return 0;
  uint32_t ab = c->abound;
  uint64_t bm = 0, vm = 0;
  uint8_t fl = F_BIRTH;
  bool scoped = true;
  for (int i = 0; i < ar; i++) {
    Term x = a[i];
    if (!x || x >= nn) return 0;
    const Node *nx = &N[x];
    if (__builtin_expect(nx->head >= 0xFFFFFFFEu && nx->kind == K_APP, 0)) return 0;   /* located nodes are not arguments */
    if (__builtin_expect(nx->sort != c->asort[i], 0)) return 0;
    if ((ab >> i & 1) && !((nx->kind == K_VAR && nx->bound) || nx->kind == K_BV)) return 0;
    bm |= nx->bm; vm |= nx->vm; fl |= nx->flags;
    scoped &= !nx->vm || nx->cep == cepoch;
  }
  if (__builtin_expect(nn >= ncap || na + ar > acap, 0))
    return mk(K_APP, (uint32_t)con, c->sort, 0, 0, ar, a);
  Term t = nn++;
  uint32_t a0 = na; na += (uint32_t)ar;
  for (int j = 0; j < ar; j++) A[a0 + (uint32_t)j] = a[j];
  N[t] = (Node){ K_APP, 0, fl, c->sort, (uint8_t)ar, 0, scoped ? cepoch : 0, (uint32_t)con, a0, bm, vm };
  Nhslot[t] = UINT32_MAX;
  return t;
}

/* ---- unknowns: bindings with a trail ---- */
static uint32_t next_vgen(void) { if (++vgen) return vgen; memset(vis, 0, nn * sizeof *vis); return vgen = 1; }
static Term walk(Term t) { while (N[t].kind == K_META && bind[N[t].head]) t = bind[N[t].head]; return t; }
/* The hash-consed node for a term built in a tc_birth scope (identity again means equality).
   Hash-consing is on while it runs; nodes without F_BIRTH are returned as they are. */
static Term canon_rec(Term t, uint32_t g, int d) {
  if (!t || t >= nn || d > 4096) return 0;
  if (!(N[t].flags & F_BIRTH)) return t;
  if (vis[t] == g) return (Term)vval[t];
  Node x = N[t];                                          /* copied: mk may move N and A */
  if (x.arity > TC_ARGS) return 0;
  Term b[TC_ARGS];
  for (int i = 0; i < x.arity; i++) if (!(b[i] = canon_rec(A[x.args + (uint32_t)i], g, d + 1))) return 0;
  uint64_t id = x.kind == K_VAR ? x.bm : x.kind == K_NAME ? Nid[t] : 0;
  Term r = mk(x.kind, x.head, x.sort, x.bound, id, x.arity, x.arity ? b : NULL);
  if (r) { vis[t] = g; vval[t] = r; }
  return r;
}
static Term canon(Term t) {
  if (!t || t >= nn || !(N[t].flags & F_BIRTH)) return t;
  bool bs = bscope; bscope = false;
  uint32_t g = next_vgen();
  Term r = canon_rec(t, g, 0);
  bscope = bs;
  return r;
}
static Term norm_rec(Term t, uint32_t g, int d) {
  if (d > 4096) return 0;
  t = walk(t);
  if (!has_meta(t) || N[t].kind != K_APP) return t;
  if (vis[t] == g) return (Term)vval[t];
  Term b[TC_ARGS];
  for (int i = 0; i < N[t].arity; i++) if (!(b[i] = norm_rec(argv(t)[i], g, d + 1))) return 0;
  Term r = tc_app((int)N[t].head, b);
  vis[t] = g; vval[t] = r; return r;
}
static Term norm(Term t) { return norm_rec(t, next_vgen(), 0); }
Term tc_deref(Term t) { return t && t < nn ? norm(t) : 0; }
static bool occ_rec(Term m, Term t, uint32_t g, int d) {
  if (d > 4096) return true;
  t = walk(t);
  if (t == m) return true;
  if (!has_meta(t) || vis[t] == g) return false;
  vis[t] = g;
  for (int i = 0; i < N[t].arity; i++) if (occ_rec(m, argv(t)[i], g, d + 1)) return true;
  return false;
}
static bool occurs(Term m, Term t) { return occ_rec(m, t, next_vgen(), 0); }
static bool ucache(uint64_t key, bool set) {
  uint32_t i = (uint32_t)((key * 0x9E3779B97F4A7C15ull) >> 54);
  if (!set) return ugen[i] == ug && upair[i] == key;
  ugen[i] = ug; upair[i] = key; return true;
}
static bool unify_rec(Term u, Term v, int d) {
  if (d > 4096) return false;
  u = walk(u); v = walk(v);
  if (u == v) return true;
  if (N[v].kind == K_META && (N[u].kind != K_META || N[u].head < N[v].head)) { Term s = u; u = v; v = s; }
  if (N[u].kind == K_META) {
    if (occurs(u, v) || ntrail >= CAP_META) return false;
    uint16_t su = Msort[N[u].head], sv = N[v].kind == K_META ? Msort[N[v].head] : N[v].sort;
    if (su != TC_ANY && sv != TC_ANY && su != sv) return false;
    uint32_t hv = N[v].kind == K_META ? N[v].head : 0;
    msort_who[ntrail] = hv; msort_prev[ntrail] = Msort[hv];
    if (N[v].kind == K_META && Msort[hv] == TC_ANY && su != TC_ANY && hv < CAP_META - TC_VARS) Msort[hv] = su;
    bind[N[u].head] = v; trail[ntrail++] = N[u].head; tscope = bscope = false; return true;   /* K may now hold transient terms */
  }
  if (N[u].kind != K_APP || N[v].kind != K_APP || N[u].head != N[v].head) return false;
  uint64_t key = ((uint64_t)u << 32) | v;
  if (ucache(key, false)) return true;
  for (int i = 0; i < N[u].arity; i++) if (!unify_rec(argv(u)[i], argv(v)[i], d + 1)) return false;
  return ucache(key, true);
}
static bool unify(Term u, Term v) { return unify_rec(u, v, 0); }
static void undo(uint32_t mark) {
  if (ntrail > mark) ug++;
  if (!ug) { memset(ugen, 0, sizeof ugen); ug = 1; }
  while (ntrail > mark) { --ntrail; Msort[msort_who[ntrail]] = msort_prev[ntrail]; if (trail[ntrail] != UINT32_MAX) bind[trail[ntrail]] = 0; }
}
static bool diseqs_ok(void) {
  for (int i = 0; i < nne; i++) { Term a = norm(NE[i][0]), b = norm(NE[i][1]); if (!a || !b || a == b) return false; }
  return true;
}
bool tc_tell(Term u, Term v) {
  tscope = bscope = false;
  if (!u || !v || u >= nn || v >= nn || N[u].vm || N[v].vm || !name_ok(u) || !name_ok(v) || at_node_any(u) || at_node_any(v)) return false;
  if (!(u = canon(u)) || !(v = canon(v))) return false;   /* K holds hash-consed terms only */
  uint32_t m = ntrail;
  if (u && v && u < nn && v < nn && unify(u, v) && diseqs_ok()) return true;
  undo(m); return false;
}
bool tc_tell_neq(Term u, Term v) {
  tscope = bscope = false;
  if (!u || !v || u >= nn || v >= nn || N[u].vm || N[v].vm || !name_ok(u) || !name_ok(v) || at_node_any(u) || at_node_any(v) || nne >= 65536) return false;
  if (!(u = canon(u)) || !(v = canon(v))) return false;   /* K holds hash-consed terms only */
  Term na = norm(u), nb = norm(v);
  if (!na || !nb || na == nb) return false;
  if (!has_meta(na) && !has_meta(nb)) return true;
  NE[nne][0] = u; NE[nne][1] = v; nne++;
  if (diseqs_ok()) return true;
  nne--; return false;
}

/* ---- rules: premises compiled to preorder bytecode ---- */
enum { OP_APP = 1u << 28, OP_HOLE = 2u << 28, OP_SAME = 3u << 28, OP_FLAT = 4u << 28, OP_CON = 5u << 28, OP_MASK = 15u << 28 };
static bool emit(Term p, uint32_t lim, const RuleK *k, uint64_t *imp) {
  if (ncode >= lim) return false;
  if (N[p].kind == K_VAR) { code[ncode++] = OP_HOLE | N[p].head; return true; }
  if (!bscope && !N[p].vm) return p < (1u << 28) && (code[ncode++] = OP_SAME | p, true);
  if (N[p].kind == K_APP && N[p].arity == 0) { code[ncode++] = OP_CON | N[p].head; return true; }
  if (N[p].kind != K_APP) return p < (1u << 28) && (code[ncode++] = OP_SAME | p, true);
  bool flat = true;                                       /* FLAT: an application of leaves, matched in place */
  const Con *c = &C[N[p].head]; const Term *pa = argv(p); int ar = N[p].arity;
  for (int i = 0; i < ar; i++) {
    Term a = pa[i];
    if (N[a].kind == K_VAR) {
      int h = (int)N[a].head;
      if ((HOLE(k, h).sort == TC_ANY || c->asort[i] == HOLE(k, h).sort) && (!HOLE(k, h).bound || (c->abound >> i & 1))) *imp |= 1ull << h;
    } else flat &= (!bscope && !N[a].vm) || (N[a].kind == K_APP && N[a].arity == 0) || N[a].kind != K_APP;
  }
  code[ncode++] = (flat ? OP_FLAT : OP_APP) | ((uint32_t)ar << 20) | N[p].head;
  for (int i = 0; i < ar; i++) if (!emit(pa[i], lim, k, imp)) return false;
  return true;
}
static inline bool leaf(uint32_t op, Term x, Term *S, bool exact) {
  if ((op & OP_MASK) == OP_HOLE) {
    Term *s = &S[op & 0xFFFFFu];
    if (*s == x) return true;
    if (!*s) { *s = x; return true; }
    return !exact && has_meta(*s) && unify(*s, x);
  }
  if ((op & OP_MASK) == OP_CON) return N[x].kind == K_APP && N[x].head == (op & 0xFFFFFu);
  return x == (op & 0xFFFFFFFu);
}
static Term run_st[512];
static bool run_ovf;                                       /* the last run_stack stopped at its 512-term cap */
static bool run_stack(uint32_t pc, int sp, Term *S, bool exact) {   /* run_st[0..sp) has no unknowns */
  run_ovf = false;
  while (sp) {
    Term x = run_st[--sp]; uint32_t op = code[pc++];
    switch (op & OP_MASK) {
      case OP_SAME: case OP_HOLE: case OP_CON: if (!leaf(op, x, S, exact)) return false; break;
      case OP_FLAT: {
        if (N[x].kind != K_APP || N[x].head != (op & 0xFFFFFu)) return false;
        const Term *a = argv(x); int ar = (int)((op >> 20) & 0xFFu);
        for (int i = 0; i < ar; i++) if (!leaf(code[pc++], a[i], S, exact)) return false;
        break;
      }
      default: {
        int ar = (int)((op >> 20) & 0xFFu);
        if (N[x].kind != K_APP || N[x].head != (op & 0xFFFFFu)) return false;
        if (sp + ar > 512) { run_ovf = true; return false; }   /* not a mismatch: the caller matches another way */
        const Term *a = argv(x);
        for (int i = ar - 1; i >= 0; i--) run_st[sp++] = a[i];
      }
    }
  }
  return true;
}
/* Instantiate a template. Closed instantiation keeps formation (holes hold terms of their
   sorts), so it builds directly; open instantiation (unbound holes become unknowns) rechecks. */
static Term inst_rec(Term p, Term *S, bool open, uint32_t g, int d) {
  if (!p || d > 4096) return 0;
  if (!N[p].vm) return p;
  if (N[p].kind == K_VAR) { Term *s = &S[N[p].head]; if (!*s && open) *s = tc_meta(); return *s; }
  if (vis[p] == g) return (Term)vval[p];
  Term b[TC_ARGS];
  for (int i = 0; i < N[p].arity; i++) if (!(b[i] = inst_rec(argv(p)[i], S, open, g, d + 1))) return 0;
  Term r = open ? tc_app((int)N[p].head, b) : mk(K_APP, N[p].head, N[p].sort, 0, 0, N[p].arity, b);
  vis[p] = g; vval[p] = r; return r;
}
static Term inst(Term p, Term *S, bool open) { return inst_rec(p, S, open, next_vgen(), 0); }
static bool umatch_rec(Term p, Term t, Term *S, int d) {  /* two-way, for terms with unknowns */
  if (d > 4096) return false;
  t = walk(t);
  if (N[p].kind == K_VAR) { Term *s = &S[N[p].head]; if (!*s) { *s = t; return true; } return unify(*s, t); }
  if (!N[p].vm || N[t].kind == K_META) { Term q = inst(p, S, true); return q && unify(q, t); }
  if (N[t].kind != K_APP || N[t].head != N[p].head) return false;
  uint64_t key = (1ull << 63) | ((uint64_t)p << 32) | t;
  if (ucache(key, false)) return true;
  for (int i = 0; i < N[p].arity; i++) if (!umatch_rec(argv(p)[i], argv(t)[i], S, d + 1)) return false;
  return ucache(key, true);
}
static bool umatch(Term p, Term t, Term *S) {
  if (!++ug) { memset(ugen, 0, sizeof ugen); ug = 1; }
  return umatch_rec(p, t, S, 0);
}

static bool ctx_rec(Term t, int d) {                   /* every hole below t is the current context's variable */
  if (!t || t >= nn || d > 4096) return false;
  if (!N[t].vm || N[t].cep == cepoch) return true;
  if (N[t].kind == K_VAR) return N[t].head < (uint32_t)cn && t == cvar[N[t].head];
  for (int i = 0; i < N[t].arity; i++) if (!ctx_rec(argv(t)[i], d + 1)) return false;
  N[t].cep = cepoch; return true;
}
static inline bool ctx_ok(Term t) { return t && t < nn && (!N[t].vm || N[t].cep == cepoch || ctx_rec(t, 0)); }

enum { HEAD_AT_SPACE = 0xFFFFFFFEu, HEAD_AT_BIRTH = 0xFFFFFFFFu };
static inline bool is_at_node(Term t) {
  return t && t < nn && N[t].kind == K_APP && N[t].arity == 2 && N[t].head >= HEAD_AT_SPACE;
}
static inline void unpack_pat(Term pt, Term *t_out, Term *sp_out, uint8_t *mark_out) {
  if (is_at_node(pt)) {
    *sp_out = argv(pt)[0];
    *t_out  = argv(pt)[1];
    *mark_out = N[pt].head == HEAD_AT_BIRTH ? 1 : 0;
  } else {
    *sp_out = 0;
    *t_out  = pt;
    *mark_out = 0;
  }
}
Term tc_at_space(Term space, Term t) {
  if (!space || space >= nn || !t || t >= nn || is_at_node(space) || is_at_node(t)) return 0;
  return mk(K_APP, HEAD_AT_SPACE, N[t].sort, 0, 0, 2, (Term[2]){ space, t });
}
Term tc_at_birth(Term space, Term t) {
  if (!space || space >= nn || !t || t >= nn || is_at_node(space) || is_at_node(t)) return 0;
  return mk(K_APP, HEAD_AT_BIRTH, N[t].sort, 0, 0, 2, (Term[2]){ space, t });
}
static bool pats_ok(const Pat *p, int n, uint64_t ctx) {
  for (int i = 0; i < n; i++)
    if (!p[i].t || p[i].t >= nn || !ctx_ok(p[i].t) || (N[p[i].t].vm & ~ctx) || has_bv(p[i].t) || !name_ok(p[i].t)) return false;
  return true;
}
static uint64_t mask(int n) { return n >= 64 ? ~0ull : (1ull << n) - 1; }

static bool linear_pat(Term p, uint64_t *seen, int d) {
  if (d > 4096) return false;
  if (!N[p].vm) return true;
  if (*seen & N[p].vm) return false;
  if (N[p].kind == K_VAR) { *seen |= N[p].vm; return true; }
  for (int i = 0; i < N[p].arity; i++) if (!linear_pat(argv(p)[i], seen, d + 1)) return false;
  return true;
}

/* ---- transient terms: made since tc_transient(), released when the next rule is installed ----
   Hash-consing is stack-disciplined and topologically ordered (children < parent): a kept prefix
   stays in place, and any kept nodes after the first dead node slide down in a single pass. */
void tc_transient(void) { tscope = true; bscope = false; tmark = nn; tamark = na; }
void tc_birth(void) { tscope = true; bscope = true; tmark = nn; tamark = na; }
static bool mark_rec(Term t, uint32_t g, int d) {
  if (t < tmark || (t < nn && vis[t] == g)) return true;
  if (t >= nn || d > 4096) return false;
  for (int i = 0; i < N[t].arity; i++) if (!mark_rec(argv(t)[i], g, d + 1)) return false;
  vis[t] = g; return true;
}
static void release(Term *const *ts, int n) {   /* ts: the installed patterns, rewritten in place */
  if (!tscope) return;
  bool bs = bscope;
  tscope = bscope = false;
  uint32_t g = n ? next_vgen() : 0;
  for (int i = 0; i < n; i++) if (!mark_rec(*ts[i], g, 0)) return;
  if (n) while (tmark < nn && vis[tmark] == g) { tamark += N[tmark].arity; tmark++; }
  if (!bs) for (Term t = tmark; t < nn; t++) {
    if (Nhslot[t] != UINT32_MAX) H[Nhslot[t]] = 0;
    if (N[t].kind == K_NAME && Nid && Nid[t] < 4096 && ncache[Nid[t]] >= tmark) ncache[Nid[t]] = 0;
  }
  uint32_t end = nn;
  if (nn > nodes_hw) nodes_hw = nn;                      /* written: cleared at the next tc_init */
  if (na > args_hw) args_hw = na;
  nn = tmark; na = tamark;
  if (!++ug) { memset(ugen, 0, sizeof ugen); ug = 1; }     /* the unify cache is keyed by term ids */
  for (Term t = tmark; n && t < end; t++) if (vis[t] == g) {   /* slide kept nodes down, children first */
    Node x = N[t]; Term nt = nn++;
    uint32_t a0 = na; na += x.arity;
    for (int j = 0; j < x.arity; j++) { Term c = A[x.args + (uint32_t)j]; A[a0 + (uint32_t)j] = c < tmark ? c : (Term)vval[c]; }
    uint64_t id = x.kind == K_VAR ? x.bm : (x.flags & F_NAME) && x.kind == K_NAME ? Nid[t] : 0;
    x.args = a0; N[nt] = x; vval[t] = nt;
    if (bs) {
      Nhslot[nt] = UINT32_MAX;
    } else {
      uint32_t i = (uint32_t)hash(x.kind, x.head, x.sort, id, x.arity, &A[a0]) & hmask;
      while (H[i]) i = (i + 1) & hmask;
      H[i] = nt; Nhslot[nt] = i; hlog(i);
    }
    if (__builtin_expect((x.flags & F_NAME) != 0, 0)) {
      Nid[nt] = id;
      uint64_t mx = x.kind == K_NAME ? ((id >> 62) == 1 || (sorts[x.sort] & SORT_WORD) ? 0 : (id == UINT64_MAX ? id : id + 1)) : 0;
      for (int j = 0; j < x.arity; j++) { Term cj = A[a0 + (uint32_t)j]; if ((N[cj].flags & F_NAME) && Nmax[cj] > mx) mx = Nmax[cj]; }
      Nmax[nt] = mx;
    }
  }
  for (int i = 0; i < n; i++) if (*ts[i] >= tmark) *ts[i] = (Term)vval[*ts[i]];
  for (int i = 0; i < 256; i++) if (space_terms[i] >= tmark) space_terms[i] = vis[space_terms[i]] == g ? (Term)vval[space_terms[i]] : 0;
  for (int i = 0; i < TC_VARS; i++) if (ecvar[i] >= tmark) ecvar[i] = 0;
  for (int i = 0; i < cn; i++) if (cvar[i] >= tmark) { cn = i; break; }   /* variables pushed since the mark go too */
}

static int static_space_of(Term sp);
static bool is_pub(int s, int rid) {
  for (uint32_t i = 0; i < npub[s]; i++) if (pubs[s][i] == rid) return true;
  return false;
}
/* A rule is barred once sealed if a make of it lands, statically, in a protected space without range
   restriction or in an evidence space it does not produce: no firing of it may commit. */
static bool rule_bars(const RuleK *k, int rid) {
  for (int m = 0; m < k->nmk; m++) {
    int s = k->mks[m];
    if (s >= 0 && ((protect[s] && !k->range_ok) || (pubset[s] && !is_pub(s, rid)))) return true;
  }
  return false;
}
/* The same at commit, for the spaces a firing computed (makes located at a hole). */
static bool publish_ok(const RuleK *k, int rid, int nmake, const bool *has_sp, const uint8_t *mark,
                       const Term *sp, const uint8_t *raw) {
  for (int m = 0; m < nmake; m++) {
    int s = (has_sp[m] || mark[m]) ? static_space_of(sp[m]) : (int)raw[m];
    if (s >= 0 && ((protect[s] && !k->range_ok) || (pubset[s] && !is_pub(s, rid)))) return false;
  }
  return true;
}

/* derived: a lemma's rule (tc_lemma_end); it calls no function and its inputs are derived. */
static int add_rule(const Rule *r, int n, bool derived) {
  RuleK *k = &R[nr];
  uint64_t ctx = mask(n);
  Pat tells[24] = {0}; int nt = 0;
  if (nhk + (uint32_t)n > hkcap) {
    uint32_t m = hkcap ? hkcap : 4096; while (m < nhk + (uint32_t)n) m *= 2;
    Hole *g = realloc(HK, m * sizeof *g); if (!g) return -1;
    HK = g; hkcap = m;
  }
  if ((slot_mode && (r->nabsent || r->ncount || r->ntake)) ||   /* slot mode: no queries, no takes (tc_unset) */
      nr >= CAP_RULE || n > cn || r->ntake > 4 || r->nkeep > TC_HYPS || r->nabsent > 4 || r->ncount > 4 || r->ntell > 4 || r->nneq > 4 || r->nmake_extra > 4
      || r->nop > TC_FN_USES || r->nguard > TC_FN_USES || (derived && (r->nop || r->nguard))) return -1;
  for (int i = 0; i < r->ntell; i++) { tells[nt++] = (Pat){ r->tell[i][0], 0 }; tells[nt++] = (Pat){ r->tell[i][1], 0 }; }
  for (int i = 0; i < r->nneq; i++) { tells[nt++] = (Pat){ r->neq[i][0], 0 }; tells[nt++] = (Pat){ r->neq[i][1], 0 }; }
  for (int i = 0; i < r->ncount; i++) tells[nt++] = (Pat){ r->count[i].t, r->count[i].space };
  if (!pats_ok(r->take, r->ntake, ctx) || !pats_ok(r->keep, r->nkeep, ctx) || !pats_ok(r->absent, r->nabsent, ctx)
      || !pats_ok(&r->make, 1, ctx) || !pats_ok(r->make_extra, r->nmake_extra, ctx) || !pats_ok(tells, nt, ctx)
      || (r->fresh >= 0 && (r->fresh >= n || cbound[r->fresh] || (sorts[csort[r->fresh]] & SORT_WORD)))) return -1;
  /* Sealed functions: an operation reads holes its take/keep patterns bind or earlier operations
     compute; a guard reads bound holes and any operation's outputs; every such hole has a word sort.
     An output occurs in no premise pattern, is not fresh, not an input, and is computed once. */
  uint64_t bmask = 0, pmask = 0, made = N[r->make.t].vm, outs = 0;
  for (int i = 0; i < r->ntake; i++) bmask |= N[r->take[i].t].vm;
  for (int i = 0; i < r->nkeep; i++) bmask |= N[r->keep[i].t].vm;
  for (int i = 0; i < r->nabsent; i++) pmask |= N[r->absent[i].t].vm;
  for (int i = 0; i < nt; i++) pmask |= N[tells[i].t].vm;  /* tells, disequations and counts */
  for (int i = 0; i < r->nmake_extra; i++) made |= N[r->make_extra[i].t].vm;
  for (int i = 0; i < r->nop; i++) {
    const TcOpUse *u = &r->op[i];
    if (u->fn < 0 || u->fn >= nfn || FNR[u->fn].kind != TC_FN_OP) return -1;
    uint64_t mine = 0;
    for (int j = 0; j < FNR[u->fn].nin; j++) {
      int h = u->in[j];
      if (h >= n || !(sorts[csort[h]] & SORT_WORD) || !((bmask | outs) >> h & 1)) return -1;
    }
    for (int j = 0; j < FNR[u->fn].nout; j++) {
      int h = u->out[j];
      if (h >= n || !(sorts[csort[h]] & SORT_WORD) || ((bmask | pmask | outs | mine | r->inputs) >> h & 1) || h == r->fresh) return -1;
      mine |= 1ull << h;
    }
    outs |= mine;
  }
  for (int i = 0; i < r->nguard; i++) {
    const TcGuardUse *u = &r->guard[i];
    if (u->fn < 0 || u->fn >= nfn || FNR[u->fn].kind != TC_FN_GUARD) return -1;
    for (int j = 0; j < FNR[u->fn].nin; j++) {
      int h = u->in[j];
      if (h >= n || !(sorts[csort[h]] & SORT_WORD) || !((bmask | outs) >> h & 1)) return -1;
    }
  }
  /* Range restriction: every made hole is bound by a take/keep pattern, computed, fresh, or an input. */
  uint64_t fbit = r->fresh >= 0 ? 1ull << r->fresh : 0;
  uint64_t inputs = derived ? made & ~bmask & ctx : r->inputs;
  if (!derived && ((inputs & ~ctx) || (inputs & (outs | fbit)))) return -1;
  bool range_ok = !(made & ~(bmask | outs | fbit | inputs)), dynmake = false;
  int16_t mks[5]; uint8_t nmk = (uint8_t)(1 + r->nmake_extra);
  for (int m = 0; m < nmk; m++) {
    const Pat *mp = m ? &r->make_extra[m - 1] : &r->make;
    Term pt, psp; uint8_t pmk; unpack_pat(mp->t, &pt, &psp, &pmk);
    if (!psp) mks[m] = mp->space;
    else if (N[psp].vm || has_meta(psp)) { mks[m] = -1; dynmake = true; }
    else { int s = static_space_of(psp); mks[m] = (int16_t)(s >= 0 ? s : -2); }
    if (mks[m] >= 0 && protect[mks[m]] && !range_ok) return -1;     /* made holes the rule cannot account for */
    if (derived && mks[m] >= 0 && pubset[mks[m]]) return -1;          /* a derived rule produces no evidence */
  }
  for (int i = 0; i < r->nkeep; i++) if (r->fresh >= 0 && (N[r->keep[i].t].vm >> r->fresh & 1)) return -1;
  for (int i = 0; r->fresh >= 0 && i < nt; i++) if (N[tells[i].t].vm >> r->fresh & 1) return -1;
  for (int i = 0; r->fresh >= 0 && i < r->ntake; i++) if (N[r->take[i].t].vm >> r->fresh & 1) return -1;
  for (int i = 0; r->fresh >= 0 && i < r->nabsent; i++) if (N[r->absent[i].t].vm >> r->fresh & 1) return -1;
  bool meta_pat = has_meta(r->make.t), ks_zero = true;
  bool dyn_space = is_at_node(r->make.t) || r->nmake_extra > 0 || r->birth_law != 0;
  bool dyn_loc = is_at_node(r->make.t) || r->birth_law != 0;
  for (int i = 0; i < r->nmake_extra; i++) dyn_loc |= is_at_node(r->make_extra[i].t);
  for (int i = 0; i < r->nkeep; i++) {
    meta_pat |= has_meta(r->keep[i].t);
    ks_zero &= !r->keep[i].space && !is_at_node(r->keep[i].t);
    dyn_space |= is_at_node(r->keep[i].t);
    dyn_loc |= is_at_node(r->keep[i].t);
  }
  for (int i = 0; i < r->ntake; i++) { dyn_space |= is_at_node(r->take[i].t); dyn_loc |= is_at_node(r->take[i].t); }
  for (int i = 0; i < r->nabsent; i++) { dyn_space |= is_at_node(r->absent[i].t); dyn_loc |= is_at_node(r->absent[i].t); }
  for (int i = 0; i < r->ncount; i++) { dyn_space |= is_at_node(r->count[i].t); dyn_loc |= is_at_node(r->count[i].t); }
  if (slot_mode && dyn_loc) return -1;                     /* slot mode: no located premises (tc_unset) */
  size_t rsz = (offsetof(Rule, keep) + r->nkeep * sizeof(Pat) + 7) & ~(size_t)7;
  if (nrp + rsz > rpcap) {
    size_t m = rpcap ? 2 * rpcap : 1u << 16; while (m < nrp + rsz) m *= 2;
    uint8_t *g = realloc(RP, m); if (!g) return -1;
    RP = g; rpcap = m;
  }
  bool fns = r->nop || r->nguard;
  bool pure = !meta_pat && !dyn_space && !r->ntake && !r->nabsent && !r->ncount && !r->ntell && !r->nneq && r->fresh < 0 && !fns;
  *k = (RuleK){ .ro = (uint32_t)nrp, .n = n, .h0 = nhk, .make = r->make.t, .nkeep = r->nkeep, .mspace = r->make.space,
                .fibre = (uint8_t)((pure ? FIBRE_PURE : 0) | (fns ? FIBRE_FN : 0)), .pure = pure, .ks_zero = ks_zero,
                .inputs = inputs, .outs = outs, .nmk = nmk, .fns = fns, .derived = derived, .range_ok = range_ok,
                .dynmake = dynmake };
  memcpy(k->mks, mks, sizeof mks);
  for (int h = 0; h < n; h++) {
    HOLE(k, h) = (Hole){ 0, csort[h], cbound[h] }; if (cbound[h]) k->bounds |= 1ull << h;
    for (int j = 0; cbound[h] && j < n; j++)            /* a bound hole avoids every hole not depending on it */
      if (j != h && !(cbm[j] & cbm[h])) HOLE(k, h).avoid |= 1ull << j;
  }
  if (r->ntake || r->ncount || dyn_loc) has_take = true;
  if (r->nabsent || r->ncount) has_query = true;
  memcpy(RP + nrp, r, rsz < sizeof *r ? rsz : sizeof *r);
  ((Rule *)(RP + nrp))->inputs = inputs;                  /* a derived rule's derived inputs, as stored */
  nrp += rsz;
  nhk += (uint32_t)n;
  k->barred = sealed && rule_bars(k, nr);                 /* a lemma installed after the seal */
  return nr++;
}
static void prep_rule(RuleK *k) {
  k->prepped = true;
  const Rule *r = RULE(k);
  uint32_t s = ncode, lim = s + 4096 < CAP_CODE ? s + 4096 : CAP_CODE;
  bool ok = k->pure;
  uint64_t imp = 0;
  for (int i = 0; ok && i < k->nkeep; i++) ok = emit(r->keep[i].t, lim, k, &imp);
  if (ncode > code_hw) code_hw = ncode;                  /* written, even when rolled back */
  k->kcode = ok ? s : (ncode = s, UINT32_MAX);
  k->implied = ok ? imp : 0;
  uint32_t ms = ncode, mlim = ms + 4096 < CAP_CODE ? ms + 4096 : CAP_CODE;
  uint64_t mimp = k->implied;
  bool mok = ok && emit(k->make, mlim, k, &mimp);
  if (ncode > code_hw) code_hw = ncode;
  k->mcode = mok ? ms : (ncode = ms, UINT32_MAX);
  k->mimplied = k->mcode != UINT32_MAX ? mimp : k->implied;
}
static void prep_flat(RuleK *k) {
  if (!k->prepped) prep_rule(k);
  k->fprepped = true;
  const Rule *r = RULE(k);
  if (k->nkeep == 0 && !r->ntake && !r->nabsent && !r->ncount && !r->ntell && !r->nneq && !k->bounds
      && !r->nmake_extra && !r->birth_law && !is_at_node(k->make)       /* the make-only path writes one plain fact */
      && !k->fns                                                        /* and computes nothing */
      && !has_meta(k->make) && N[k->make].kind == K_APP) {
    bool mf = true;
    for (int j = 0; mf && j < N[k->make].arity; j++) {
      Term a = argv(k->make)[j];
      mf = !N[a].vm || N[a].kind == K_VAR;
    }
    k->mflat = mf;
  }
  if (!k->pure) return;
  bool gnd = k->nkeep > 0 && !(k->implied & k->bounds) && !(N[k->make].vm & ~k->implied), lin = gnd;
  uint64_t lseen = 0;
  for (int i = 0; i < k->nkeep; i++) {
    gnd &= !(N[r->keep[i].t].vm & ~k->implied);
    lin &= gnd && linear_pat(r->keep[i].t, &lseen, 0);
  }
  if (gnd) k->fibre |= FIBRE_GROUND;
  if (lin) k->fibre |= FIBRE_LINEAR;
  if (gnd && N[k->make].kind == K_APP) {
    int8_t fi[TC_VARS], fj[TC_VARS]; memset(fi, -1, sizeof fi);
    Flat f = { 0 }, *q = &f;
    q->ordinary = true;
    bool ok = true;
    for (int i = 0; ok && i < k->nkeep; i++) {
      Term p = r->keep[i].t;
      if (N[p].kind != K_APP || (N[p].vm & ~k->implied)) { ok = false; break; }
      q->ktag[i] = (N[p].head << 9) | ((uint32_t)r->keep[i].space << 1) | 1u;
      for (int j = 0; j < N[p].arity; j++) {
        Term a = argv(p)[j];
        if (!N[a].vm) {
          if (q->nguard >= 32 || q->nconst >= 32) { ok = false; break; }
          q->mc[q->nconst] = a;
          q->guard[q->nguard++] = (Guard){ (uint8_t)i, (uint8_t)j, k->nkeep, (uint8_t)q->nconst++ };
        } else if (N[a].kind == K_VAR) {
          int h = (int)N[a].head;
          if (fi[h] < 0) { fi[h] = (int8_t)i; fj[h] = (int8_t)j; }
          else if (q->nguard < 32) q->guard[q->nguard++] = (Guard){ (uint8_t)i, (uint8_t)j, (uint8_t)fi[h], (uint8_t)fj[h] };
          else { ok = false; break; }
        } else { ok = false; break; }
      }
    }
    Term m = k->make; q->mhead = N[m].head; q->msort = N[m].sort; q->mar = N[m].arity;
    for (int j = 0; ok && j < q->mar; j++) {
      Term a = argv(m)[j];
      if (!N[a].vm && q->nconst < 32) { q->mc[q->nconst] = a; q->mi[j] = k->nkeep; q->mj[j] = (uint8_t)q->nconst++; }
      else if (N[a].kind == K_VAR && fi[N[a].head] >= 0) { q->mi[j] = (uint8_t)fi[N[a].head]; q->mj[j] = (uint8_t)fj[N[a].head]; }
      else ok = false;
    }
    q->ordinary &= q->mar <= 4;
    for (int i = 0; i < k->nkeep; i++)
      q->ordinary &= N[r->keep[i].t].arity <= 4;
    for (int g = 0; g < q->nguard; g++) {
      Guard e = q->guard[g];
      q->packed_guard[g] = (uint32_t)e.i | (uint32_t)e.j << 8 |
                           (uint32_t)e.i0 << 16 | (uint32_t)e.j0 << 24;
      bool left = e.i < k->nkeep ? e.j < N[r->keep[e.i].t].arity
                                 : e.i == k->nkeep && e.j < q->nconst;
      bool right = e.i0 < k->nkeep ? e.j0 < N[r->keep[e.i0].t].arity
                                   : e.i0 == k->nkeep && e.j0 < q->nconst;
      q->ordinary &= left && right;
    }
    for (int j = 0; j < q->mar; j++) {
      q->packed_make[j] = (uint32_t)q->mi[j] | (uint32_t)q->mj[j] << 8;
      bool valid = q->mi[j] < k->nkeep
        ? q->mj[j] < N[r->keep[q->mi[j]].t].arity
        : q->mi[j] == k->nkeep && q->mj[j] < q->nconst;
      q->ordinary &= valid;
    }
    if (ok && nfl >= flcap) {
      uint32_t cap = flcap ? 2 * flcap : 256; Flat *g = realloc(FL, cap * sizeof *g);
      if (g) { FL = g; flcap = cap; } else ok = false;
    }
    if (ok) {
      int rid = (int)(k - R);
      bool ar4 = rid >= 0 && rid < 64 && q->nconst == 0 && k->nkeep == 4 && q->mar == 4;
      for (int i = 0; ar4 && i < 4; i++) if (N[r->keep[i].t].arity != 4) ar4 = false;
      if (ar4) {
        Flat4 *f4 = &FF[rid];
        for (int i = 0; i < 4; i++) f4->ktag[i] = q->ktag[i];
        f4->mtag = (q->mhead << 9) | ((uint32_t)k->mspace << 1) | 1u;
        f4->ok = 1;
        f4->single_tag = (slot_mode && !has_take && ncon == 1 && k->mspace == 0 &&
                          q->ktag[0] == Wtag[0] && q->ktag[1] == Wtag[0] &&
                          q->ktag[2] == Wtag[0] && q->ktag[3] == Wtag[0]);
        for (int i = 0; i < 4; i++) {
          Term p = r->keep[i].t;
          for (int j = 0; j < 4; j++) {
            int h = (int)N[argv(p)[j]].head;
            f4->perm[i * 4 + j] = (uint8_t)(fi[h] * 4 + fj[h]);
          }
        }
        for (int j = 0; j < 4; j++) f4->mperm[j] = (uint32_t)q->mi[j] * 4u + (uint32_t)q->mj[j];
      }
      FL[nfl] = f; k->fl = nfl++; k->flat = true; k->fibre |= FIBRE_FLAT;
    }
  }
}
int tc_rule(const Rule *r) {
  if (sealed || !r || r->ntake > 4 || r->nkeep > TC_HYPS || r->nabsent > 4 || r->ncount > 4 || r->ntell > 4 || r->nneq > 4 || r->nmake_extra > 4
      || r->nop > TC_FN_USES || r->nguard > TC_FN_USES) { tscope = bscope = false; return -1; }
  bool birth = bscope;                                      /* a rule outlives its scope: its stored patterns are */
  bscope = false;                                           /* made hash-consed and kept by the release below */
  Rule c = *r; Term *ts[64]; int n = 0;                     /* every pattern, for release */
  for (int i = 0; i < c.ntake; i++) ts[n++] = &c.take[i].t;
  for (int i = 0; i < c.nkeep; i++) ts[n++] = &c.keep[i].t;
  for (int i = 0; i < c.nabsent; i++) ts[n++] = &c.absent[i].t;
  for (int i = 0; i < c.ncount; i++) ts[n++] = &c.count[i].t;
  for (int i = 0; i < c.ntell; i++) { ts[n++] = &c.tell[i][0]; ts[n++] = &c.tell[i][1]; }
  for (int i = 0; i < c.nneq; i++) { ts[n++] = &c.neq[i][0]; ts[n++] = &c.neq[i][1]; }
  ts[n++] = &c.make.t;
  for (int i = 0; i < c.nmake_extra; i++) ts[n++] = &c.make_extra[i].t;
  if (birth) for (int i = 0; i < n; i++) if (*ts[i] && *ts[i] < nn && !(*ts[i] = canon(*ts[i]))) { tscope = false; return -1; }
  release(ts, n);
  int rid = add_rule(&c, cn, false);
  if (birth && rid >= 0) { bscope = true; prep_rule(&R[rid]); bscope = false; }   /* structural bytecode, as before */
  return rid;
}
uint8_t tc_rule_fibre(int rid) {
  if (rid < 0 || rid >= nr) return 0;
  if (!R[rid].fprepped) prep_flat(&R[rid]);
  return R[rid].fibre;
}
int tc_rule_fns(int rid, int *out, int cap) {
  if (rid < 0 || rid >= nr) return -1;
  const Rule *r = RULE(&R[rid]);
  int n = 0;
  for (int i = 0; i < r->nop; i++, n++) if (out && n < cap) out[n] = r->op[i].fn;
  for (int i = 0; i < r->nguard; i++, n++) if (out && n < cap) out[n] = r->guard[i].fn;
  return n;
}
bool tc_rule_barred(int rid) { return rid >= 0 && rid < nr && R[rid].barred; }

/* ---- sealed functions and evidence spaces ---- */
int tc_fn(const char *name, uint8_t kind, uint8_t nin, uint8_t nout, TcFn fn, const uint8_t sha[32]) {
  if (sealed || nfn >= CAP_FN || !name || !fn || !sha || nin > TC_FN_IN) return -1;
  size_t len = 0;
  while (len < TC_FN_NAME && name[len]) len++;
  if (!len || len >= TC_FN_NAME) return -1;
  if (kind == TC_FN_GUARD ? nout != 0 : kind == TC_FN_OP ? (nout < 1 || nout > TC_FN_OUT) : true) return -1;
  FnEntry *e = &FNR[nfn];
  memcpy(e->name, name, len + 1); e->kind = kind; e->nin = nin; e->nout = nout; e->fn = fn;
  memcpy(e->sha, sha, 32);
  return nfn++;
}
int tc_fn_count(void) { return nfn; }
bool tc_fn_info(int id, TcFnInfo *out) {
  if (id < 0 || id >= nfn || !out) return false;
  const FnEntry *e = &FNR[id];
  out->name = e->name; out->kind = e->kind; out->nin = e->nin; out->nout = e->nout; out->fn = e->fn;
  memcpy(out->contract_sha256, e->sha, 32);
  return true;
}
bool tc_publishers(uint8_t s, const int *rules, int n) {
  if (sealed || slot_mode || !protect[s] || n < 0 || (n > 0 && !rules)) return false;
  for (int i = 0; i < n; i++) {
    int id = rules[i];
    if (id < 0 || id >= nr) return false;
    const RuleK *k = &R[id];
    bool makes = k->dynmake;
    for (int m = 0; m < k->nmk; m++) makes |= k->mks[m] == s;
    if (k->derived || !k->range_ok || k->inputs || !makes) return false;   /* a producer makes nothing chosen by its caller */
  }
  if (npub[s] + (uint32_t)n > cpub[s]) {
    uint32_t c = cpub[s] ? cpub[s] : 16; while (c < npub[s] + (uint32_t)n) c *= 2;
    int *g = realloc(pubs[s], c * sizeof *g); if (!g) return false;
    pubs[s] = g; cpub[s] = c;
  }
  for (int i = 0; i < n; i++) if (!is_pub(s, rules[i])) pubs[s][npub[s]++] = rules[i];
  pubset[s] = has_pubset = true;
  return true;
}
int tc_space_publishers(uint8_t s, int *out, int cap) {
  if (!pubset[s]) return -1;
  for (uint32_t i = 0; out && i < npub[s] && (int)i < cap; i++) out[i] = pubs[s][i];
  return (int)npub[s];
}
/* The words of a function's inputs: each a name of the hole's word sort (a canonical word), nothing else. */
static inline bool fn_word(const RuleK *k, const Term *S, int h, uint64_t *w) {
  Term v = S[h];
  if (!v || v >= nn) return false;
  v = walk(v);
  if (N[v].kind != K_NAME || N[v].sort != HOLE(k, h).sort || !Nid) return false;
  *w = Nid[v];
  return true;
}
/* The kernel's call into a registered function. A native image is proved under its entry facts (the
   HOL/s2n contracts' cb_entry; tisa/native_alu): in and out 8-byte aligned; in[0..15], out[0..7] and
   the return word at canonical user-space addresses whose ranges do not wrap; out[0..7] apart from
   in[0..15], from the function's code and from the return word. Here in and out are this frame's
   uint64_t arrays, so they are aligned and apart from each other and from the code, and the return word
   the call pushes lies below this frame; that is the compiler's to keep, not proved. A debug build
   (-DTC_DEBUG_CALLS) checks what C can see: the alignment and the non-overlap of in, out and the
   first 34 code bytes (a control, not a proof of the call site). */
#ifdef TC_DEBUG_CALLS
#include <assert.h>
static void call_checks(const uint64_t *in, const uint64_t *out, TcFn fn) {
  uintptr_t i = (uintptr_t)in, o = (uintptr_t)out, c = (uintptr_t)fn;
  assert(i % 8 == 0 && o % 8 == 0);
  assert(o + 8 * TC_FN_OUT <= i || i + 8 * TC_FN_IN <= o);
  assert(o + 8 * TC_FN_OUT <= c || c + 34 <= o);
}
#define CALL_CHECKS(in, out, fn) call_checks(in, out, fn)
#else
#define CALL_CHECKS(in, out, fn) ((void)0)
#endif
/* Operations in declaration order: inputs read, outputs bound to the words they compute. */
static bool run_ops(const RuleK *k, const Rule *r, Term *S) {
  for (int i = 0; i < r->nop; i++) {
    const TcOpUse *u = &r->op[i]; const FnEntry *e = &FNR[u->fn];
    uint64_t in[TC_FN_IN] = { 0 }, out[TC_FN_OUT] = { 0 };
    for (int j = 0; j < e->nin; j++) if (!fn_word(k, S, u->in[j], &in[j])) return false;
    CALL_CHECKS(in, out, e->fn);
    if (!e->fn(in, out)) return false;                    /* no value */
    for (int j = 0; j < e->nout; j++) {
      Term t = tc_name(HOLE(k, u->out[j]).sort, out[j]);  /* a word of the output's word sort */
      if (!t) return false;
      S[u->out[j]] = t;
    }
  }
  return true;
}
static bool run_guards(const RuleK *k, const Rule *r, const Term *S) {
  for (int i = 0; i < r->nguard; i++) {
    const TcGuardUse *u = &r->guard[i]; const FnEntry *e = &FNR[u->fn];
    uint64_t in[TC_FN_IN] = { 0 }, scratch[TC_FN_OUT] = { 0 };
    for (int j = 0; j < e->nin; j++) if (!fn_word(k, S, u->in[j], &in[j])) return false;
    CALL_CHECKS(in, scratch, e->fn);
    if (!e->fn(in, scratch)) return false;
  }
  return true;
}

/* Sorts, binders and separation, for the holes that are bound.
   given: holes the caller supplied; the others came from matching well-formed premises. */
static bool holes_ok(const RuleK *k, Term *S, uint64_t given, bool clean) {
  Term U[TC_VARS];
  for (int h = 0; h < k->n; h++) {
    if (!(U[h] = S[h])) continue;
    Term t = U[h] = walk(S[h]);
    if (N[t].vm) return false;
    if ((k->implied >> h & 1) && !(given >> h & 1) && clean) continue;
    if (HOLE(k, h).sort != TC_ANY && N[t].sort != HOLE(k, h).sort) return false;
    if (HOLE(k, h).bound && !is_bvar(t)) return false;
  }
  for (uint64_t m = k->bounds; m; m &= m - 1) {
    int h = __builtin_ctzll(m);
    for (uint64_t a = U[h] ? HOLE(k, h).avoid : 0; a; a &= a - 1) {
      int j = __builtin_ctzll(a);
      if (U[j] && (has_meta(U[j]) || (N[U[h]].bm & N[U[j]].bm))) return false;
    }
  }
  return true;
}

/* ---- conversion: definitional unfolding, congruence, symmetry ---- */
static uint64_t fv_rec(Term t, uint32_t g, int depth) {
  if (depth > 4096) return ~0ull;
  if (N[t].kind != K_APP || !N[t].bm) return N[t].bm;
  if (vis[t] == g) return vval[t];
  const Con *c = &C[N[t].head]; const Term *a = argv(t);
  uint64_t acc = 0, bd[TC_ARGS];
  for (int i = 0; i < c->arity; i++) {
    if (c->abound >> i & 1) { bd[i] = N[a[i]].bm; if (c->retdeps >> i & 1) acc |= bd[i]; continue; }
    uint64_t d = fv_rec(a[i], g, depth + 1);
    uint32_t deps = c->abound ? CD[N[t].head].adeps[i] : 0;
    for (int j = 0; j < i; j++) if (deps >> j & 1) d &= ~bd[j];
    acc |= d;
  }
  vis[t] = g; return vval[t] = acc;
}
static uint64_t fv(Term t) { return fv_rec(t, next_vgen(), 0); }

int tc_def(uint16_t s, uint64_t retdeps, int ar, int nd, Term body) {
  if (ncon >= CAP_CON || ar + nd != cn || ar > TC_ARGS || ar < 0 || nd < 0 || s >= nsort || (sorts[s] & (SORT_PURE | SORT_WORD))
      || !body || body >= nn || at_node_any(body) || !ctx_ok(body) || (N[body].flags & (F_META | F_BV)) || (N[body].vm & ~mask(cn))
      || N[body].sort != s || !name_ok(body)) { tscope = bscope = false; return -1; }
  Binder a[TC_ARGS];
  uint64_t retbits = 0;
  for (int i = 0; i < ar; i++) {
    a[i] = (Binder){ csort[i], cbound[i], cdeps[i] };
    if (retdeps >> i & 1) { if (!cbound[i]) { tscope = bscope = false; return -1; } retbits |= cbm[i]; }
  }
  for (int i = ar; i < cn; i++) if (!cbound[i] || (sorts[csort[i]] & (SORT_STRICT | SORT_FREE))) { tscope = bscope = false; return -1; }
  if (fv(body) & ~retbits) { tscope = bscope = false; return -1; }               /* free variables, binders respected, are declared */
  tscope = bscope = false;
  if (!(body = canon(body))) return -1;                  /* the stored body outlives any birth scope */
  int id = tc_con(s, retdeps, ar, a);
  if (id < 0) return -1;
  for (int i = 0; i < nd; i++) CD[id].dsort[i] = (uint8_t)csort[ar + i];
  C[id].isdef = 1; C[id].body = body; C[id].ndum = (uint16_t)nd;
  return id;
}

static bool smatch(Term p, Term t, const Term *S, int d) {   /* t is p with its holes at S: holes by identity */
  if (d > 4096 || !t || t >= nn) return false;
  if (N[p].kind == K_VAR) return S[N[p].head] == t;
  if (N[p].kind != K_APP) return p == t;
  if (N[t].kind != K_APP || N[t].head != N[p].head || N[t].arity != N[p].arity) return false;
  for (int i = 0; i < N[p].arity; i++) if (!smatch(argv(p)[i], argv(t)[i], S, d + 1)) return false;
  return true;
}
static bool conv(const Conv *c, Term l, Term r, int depth) {   /* c proves l = r */
  if (!c || depth > 1000 || !l || !r || l >= nn || r >= nn) return false;
  switch (c->kind) {
    case CV_REFL:
      if (l == r) return true;
      if (rho_quote_con < 0 || rho_drop_con < 0) return false;
      {
        Term nl = tc_rho_norm_name(l), nr = tc_rho_norm_name(r);   /* 0: no normal form computed */
        return nl && nr && nl == nr;
      }
    case CV_SYM: return conv(c->kid, r, l, depth + 1);
    case CV_CONG: {
      int n = c->n;
      if (c->con < 0 || c->con >= ncon || n != C[c->con].arity || (n > 0 && !c->kid)) return false;
      if (N[l].kind != K_APP || N[r].kind != K_APP || N[l].head != (uint32_t)c->con || N[r].head != (uint32_t)c->con) return false;
      if (c->con == q_quote_con) return l == r;          /* inert quotation: no congruence inside quote */
      Term ls[TC_ARGS], rs[TC_ARGS];                      /* copied: a kid may make terms */
      for (int i = 0; i < n; i++) { ls[i] = argv(l)[i]; rs[i] = argv(r)[i]; }
      for (int i = 0; i < n; i++) if (!conv(&c->kid[i], ls[i], rs[i], depth + 1)) return false;
      return true;
    }
    case CV_UNFOLD: {                                     /* l = D(args); its body at args and dummies is c->t, or is made */
      if (c->con < 0 || c->con >= ncon || !C[c->con].isdef || !c->kid) return false;
      const Con *d = &C[c->con];
      if (N[l].kind != K_APP || N[l].head != (uint32_t)c->con || has_meta(l) || (d->ndum > 0 && !c->dummies)) return false;
      Term S[TC_VARS];
      for (int i = 0; i < d->arity; i++) {
        S[i] = argv(l)[i];
        if (c->args && c->args[i] != S[i]) return false;
      }
      for (int k = 0; k < d->ndum; k++) {                /* dummies: distinct bound variables, fresh for the args */
        Term x = S[d->arity + k] = c->dummies[k];
        if (!x || x >= nn || !is_bvar(x) || N[x].sort != CD[c->con].dsort[k]) return false;
        for (int i = 0; i < d->arity + k; i++) if (N[S[i]].bm & N[x].bm) return false;
      }
      Term e = c->t;
      if (e ? !smatch(d->body, e, S, 0) : !(e = inst(d->body, S, false))) return false;
      return conv(c->kid, e, r, depth + 1);
    }
  }
  return false;
}

/* ---- the board ---- */
static inline const Term *wargs(Occ o, uint32_t head) {
  return __builtin_expect(!has_widecon, 1) || C[head].arity <= 4 ? &Wrow[(size_t)o << 2] : &A[Warg[o]];
}
static __attribute__((noinline)) bool grow_w(uint32_t need) {
  uint32_t m = wcap ? wcap : 2;
  while (m <= need) {
    if (m > (1u << 27)) return false;
    m *= 2;
  }
  Term *a = realloc(Wt, m * sizeof *a), *d = realloc(Wtag, m * sizeof *d), *e = realloc(Warg, m * sizeof *e);
  Term *rw = realloc(Wrow, (size_t)m * 4 * sizeof *rw), *sp = realloc(Wsp, m * sizeof *sp);
  Occ *nx = realloc(Wnext, m * sizeof *nx), *pr = realloc(Wprev, m * sizeof *pr);
  uint8_t *b = realloc(Ws, m), *c = realloc(Wa, m), *mk_b = realloc(Wmark, m);
  if (a) Wt = a;
  if (d) Wtag = d;
  if (e) Warg = e;
  if (rw) Wrow = rw;
  if (sp) Wsp = sp;
  if (nx) Wnext = nx;
  if (pr) Wprev = pr;
  if (b) Ws = b;
  if (c) Wa = c;
  if (mk_b) Wmark = mk_b;
  if (!a || !d || !e || !rw || !sp || !nx || !pr || !b || !c || !mk_b) return false;
  memset(Wt + wcap, 0, (m - wcap) * sizeof *Wt);
  memset(Wtag + wcap, 0, (m - wcap) * sizeof *Wtag);
  memset(Warg + wcap, 0, (m - wcap) * sizeof *Warg);
  memset(Wsp + wcap, 0, (m - wcap) * sizeof *Wsp);
  memset(Wnext + wcap, 0, (m - wcap) * sizeof *Wnext);
  memset(Wprev + wcap, 0, (m - wcap) * sizeof *Wprev);
  memset(Ws + wcap, 0, m - wcap);
  memset(Wa + wcap, 0, m - wcap);
  memset(Wmark + wcap, 0, m - wcap);
  if (slot_mode) {
    uint32_t tag0 = Wtag[0];
    uint8_t s0 = Ws[0];
    Term r0 = Wrow[0], r1 = Wrow[1], r2 = Wrow[2], r3 = Wrow[3];
    for (uint32_t i = wcap; i < m; i++) {
      Term *ri = &Wrow[(size_t)i << 2];
      ri[0] = r0; ri[1] = r1; ri[2] = r2; ri[3] = r3;
      Wtag[i] = tag0; Ws[i] = s0; Wa[i] = 1;
    }
    if (m > w_hw) w_hw = m;                               /* written above the board: cleared at tc_init */
  } else {
    memset(Wrow + (size_t)wcap * 4, 0, (size_t)(m - wcap) * 4 * sizeof *Wrow);
  }
  wcap = m;
  capWt = capWtag = capWarg = capWsp = capWnext = capWprev = capWs = capWa = capWmark = m; capWrow = (size_t)m * 4;
  return true;
}
void tc_unset(Occ u) {
  /* A theory setting: not after the seal. Slot mode makes every unused slot a live copy of u, and the
     board's growth makes more: only a theory that cannot count or consume copies (no take, count or
     absent query, no located premise) can use it; slot-mode rows are not on the live lists either. */
  if (sealed || has_query || has_take || has_pubset || !u || u >= nw || !Wtag[u] || C[Wtag[u] >> 9].arity > 4) return;
  slot_mode = true;
  uint32_t tag0 = Wtag[0] = Wtag[u];
  uint8_t s0 = Ws[0] = Ws[u]; Wa[0] = 1;
  const Term *ru = wargs(u, tag0 >> 9);
  Term r0 = ru[0], r1 = ru[1], r2 = ru[2], r3 = ru[3];
  Wrow[0] = r0; Wrow[1] = r1; Wrow[2] = r2; Wrow[3] = r3;
  for (Occ o = 1; o < nw; o++) if (Wtag[o]) Wt[o] = 0;   /* row-backed facts re-read their rows: wt_dirty = false is then true */
  space_has_flat[s0] = true;
  Wt[u] = 0; wt_dirty = false;
  for (uint32_t i = nw; i < wcap; i++) {
    Term *ri = &Wrow[(size_t)i << 2];
    ri[0] = r0; ri[1] = r1; ri[2] = r2; ri[3] = r3;
    Wtag[i] = tag0; Ws[i] = s0; Wa[i] = 1;
  }
  nw = wcap;
}
static Occ post(uint8_t s, Term t) {
  tscope = bscope = false;
  if (N[t].flags & F_BIRTH) { if (!(t = canon(t))) return 0; }   /* the board holds hash-consed terms only */
  if (!Nocc && !TC_TAKE(Nocc, spareNocc, capNocc, ncap)) return 0;
  Occ o = Nocc[t];
  if (sealed && !has_take && o && o < nw && Wt[o] == t && Ws[o] == s && !Wsp[o] && !Wmark[o] && Wa[o]) return o;
  if (nw >= wcap && !grow_w(nw)) return 0;
  Occ at = nw;
  Nocc[t] = at; Wt[at] = t; Ws[at] = s; Wsp[at] = 0; Wmark[at] = 0; Wa[at] = 1; wt_dirty = true;
  Wtag[at] = !has_meta(t) && N[t].kind == K_APP ? (N[t].head << 9) | ((uint32_t)s << 1) | 1u : 0;
  Warg[at] = N[t].args;
  if (Wtag[at] && N[t].arity <= 4) {
    Term *rw = &Wrow[(size_t)at << 2]; const Term *a = &A[N[t].args];
    for (int j = 0; j < N[t].arity; j++) rw[j] = a[j];
  }
  Wprev[at] = 0; Wnext[at] = Wlive[s]; if (Wlive[s]) Wprev[Wlive[s]] = at; Wlive[s] = at;
  nw++;                                                   /* slot mode too: appends go one by one above the register table */
  return at;
}
uint16_t tc_space_sort(void) {
  if (!space_sort_id) {
    int s = tc_sort(0);
    if (s < 0) return 0;
    space_sort_id = (uint16_t)s;
  }
  return space_sort_id;
}
Term tc_space_term(uint8_t s) {
  uint16_t sp_sort = tc_space_sort();
  if (!sp_sort) return 0;
  Term c = space_terms[s];
  if (c && c < nn && N[c].kind == K_NAME && N[c].sort == sp_sort && Nid && Nid[c] == ((1ull << 62) | (uint64_t)s))
    return c;
  if (!Nid && !names_on()) return 0;
  bool old_ts = tscope, old_bs = bscope;
  tscope = bscope = false;
  Term t = mk(K_NAME, 0, sp_sort, 0, (1ull << 62) | (uint64_t)s, 0, NULL);
  tscope = old_ts; bscope = old_bs;
  if (t) { Nmax[t] = 0; space_terms[s] = t; }
  return t;
}
static int static_space_of(Term sp) {
  if (space_sort_id && sp && sp < nn && N[sp].kind == K_NAME && N[sp].sort == space_sort_id && Nid
      && (Nid[sp] & ~(uint64_t)0xFFu) == (1ull << 62))      /* exactly the ids tc_space_term makes */
    return (int)(Nid[sp] & 0xFFu);
  return -1;
}
static Occ post_at_internal(Term sp, Term t, uint8_t marker) {
  tscope = bscope = false;
  if (!sp) return 0;
  if ((N[sp].flags & F_BIRTH) && !(sp = canon(sp))) return 0;   /* the board holds hash-consed terms only */
  if ((N[t].flags & F_BIRTH) && !(t = canon(t))) return 0;
  int s_idx = static_space_of(sp);
  if (s_idx >= 0 && !marker) return post((uint8_t)s_idx, t);
  has_take = true;
  if (!Nocc && !TC_TAKE(Nocc, spareNocc, capNocc, ncap)) return 0;
  if (nw >= wcap && !grow_w(nw)) return 0;
  uint8_t s = s_idx >= 0 ? (uint8_t)s_idx : 255;
  Occ o = nw;
  Nocc[t] = o; Wt[o] = t; Ws[o] = s; Wsp[o] = sp; Wmark[o] = marker ? 1 : 0; Wa[o] = 1; wt_dirty = true;
  Wtag[o] = 0; Warg[o] = N[t].args;
  Wprev[o] = 0; Wnext[o] = Wlive[s]; if (Wlive[s]) Wprev[Wlive[s]] = o; Wlive[s] = o;
  nw++;                                                   /* slot mode too: appends go one by one above the register table */
  return o;
}
Occ tc_post(uint8_t s, Term t) {
  if (!t || t >= nn || N[t].vm || !name_ok(t) || at_node_any(t) || (protect[s] && sealed)) return 0;
  return post(s, t);
}
Occ tc_post_at(Term space, Term t, bool marker) {
  if (!space || space >= nn || N[space].vm || !name_ok(space) || !t || t >= nn || N[t].vm || !name_ok(t)
      || at_node_any(space) || at_node_any(t)) return 0;
  int s_idx = static_space_of(space);
  if (s_idx >= 0 && protect[s_idx] && sealed) return 0;
  if (marker && sealed) return 0;                         /* after the seal only a firing bears a space */
  return post_at_internal(space, t, marker ? 1 : 0);
}
Term tc_occ_space(Occ o) {
  if (!o || o >= nw || !Wa[o]) return 0;
  return Wsp[o] ? Wsp[o] : tc_space_term(Ws[o]);
}
bool tc_occ_marker(Occ o) { return o && o < nw && Wa[o] && Wmark[o] != 0; }
bool tc_space_born(Term space) {
  if (!space || space >= nn) return false;
  space = norm(space);
  int s_idx = static_space_of(space);
  int sp_lo = s_idx >= 0 ? s_idx : 255, sp_hi = sp_lo;
  for (int sp = sp_lo; sp <= sp_hi; sp++)
    for (Occ o = Wlive[sp]; o; o = Wnext[o])
      if (Wa[o] && Wmark[o] && norm(tc_occ_space(o)) == space) return true;
  return false;
}
bool tc_alive(Occ o) { return o && o < nw && Wa[o]; }
Term tc_term(Occ o) {
  if (o >= nw || !Wa[o]) return 0;
  if (!Wt[o] && Wtag[o]) {                                /* materializing writes the board: it ends a scope */
    tscope = bscope = false;
    Wt[o] = tc_app((int)(Wtag[o] >> 9), wargs(o, Wtag[o] >> 9)); wt_dirty = true;
  }
  return Wt[o];
}
const Term *tc_flat_args(Occ o, uint32_t ktag) {
  Occ u = o < nw ? o : 0;
  return __builtin_expect(ktag != 0 && Wtag[u] == ktag, 1) ? wargs(u, ktag >> 9) : NULL;
}
static __attribute__((noinline)) Occ flat_store_slow(Occ dest, uint32_t tag, const Term *b) {
  uint32_t head = tag >> 9;
  uint8_t s = (uint8_t)((tag >> 1) & 0xFFu);
  uint16_t sort = C[head].sort;
  int ar = C[head].arity;
  space_has_flat[s] = true;
  /* In place only into a row the board owns (arity <= 4: a wide fact's Warg is its term node's own
     argument array), and never over a fact of a protected space once sealed (that fact was not taken). */
  bool inplace_ok = ar <= 4 && !(sealed && protect[s]);
  if (inplace_ok && !has_take && dest && dest < nw && Wtag[dest] == tag) {
    Term *dst = &Wrow[(size_t)dest << 2];
    for (int j = 0; j < ar; j++) dst[j] = b[j];
    if (wt_dirty) Wt[dest] = 0;
    return dest;
  }
  if (inplace_ok && slot_mode && !has_take && dest >= nw) {
    if (!grow_w(dest)) return 0;
    nw = wcap;
    Term *dst = &Wrow[(size_t)dest << 2];
    for (int j = 0; j < ar; j++) dst[j] = b[j];
    Wtag[dest] = tag; Ws[dest] = s; Wa[dest] = 1;
    if (wt_dirty) Wt[dest] = 0;
    return dest;
  }
  if (__builtin_expect(nw >= wcap || (ar > 4 && na + (uint32_t)ar > acap), 0)) {
    Term out = mk(K_APP, head, sort, 0, 0, ar, b);
    return out ? post(s, out) : 0;
  }
  Occ o = nw++;
  if (ar <= 4) {
    Term *dst = &Wrow[(size_t)o << 2];
    for (int j = 0; j < ar; j++) dst[j] = b[j];
    Warg[o] = 0;
  } else {
    uint32_t a0 = na; na += (uint32_t)ar;
    for (int j = 0; j < ar; j++) A[a0 + (uint32_t)j] = b[j];
    Warg[o] = a0;
  }
  Wt[o] = 0; Wtag[o] = tag; Ws[o] = s; Wa[o] = 1;
  Wprev[o] = 0; Wnext[o] = Wlive[s]; if (Wlive[s]) Wprev[Wlive[s]] = o; Wlive[s] = o;
  return o;
}
static inline Occ flat_store(Occ dest, uint32_t tag, int ar, const Term *b) {
  uint8_t s = (uint8_t)((tag >> 1) & 0xFFu);
  if (__builtin_expect(!has_take && dest - 1u < nw - 1u && Wtag[dest] == tag && ar <= 4 && !(sealed && protect[s]), 1)) {
    Term *dst = &Wrow[(size_t)dest << 2];
    for (int j = 0; j < ar; j++) dst[j] = b[j];
    if (__builtin_expect(wt_dirty, 0)) Wt[dest] = 0;
    space_has_flat[s] = true;                             /* the row now holds a fact Nocc does not index */
    return dest;
  }
  return flat_store_slow(dest, tag, b);
}
Occ tc_flat_make(uint8_t s, uint32_t head, uint16_t sort, int ar, const Term *a) {
  if (head >= (uint32_t)ncon || C[head].sort != sort || C[head].arity != ar) return 0;
  return tc_post(s, tc_app((int)head, a));
}
/* A row written from outside a firing holds what tc_app would accept, ground and hash-consed. */
static inline bool flat_args_ok(int con, const Term *a) {
  const Con *c = &C[con];
  int ar = c->arity;
  if (ar && !a) return false;
  uint32_t lim = nn;
  for (int i = 0; i < ar; i++) {
    Term x = a[i];
    if (x - 1u >= lim - 1u) return false;                 /* 0, or no term */
    const Node *nx = &N[x];
    if (nx->sort != c->asort[i] || nx->vm || (nx->flags & (F_META | F_BIRTH))) return false;
    /* minted names only; a name marked plain was minted when it was marked (the counter only grows) */
    if (__builtin_expect((nx->flags & F_NAME) != 0, 0) && !(nx->kind == K_NAME && (nx->flags & F_PLAIN)) && Nmax[x] > next_name) return false;
    if (__builtin_expect(nx->kind == K_APP && nx->head >= 0xFFFFFFFEu, 0)) return false;   /* located node */
  }
  if (__builtin_expect(c->abound != 0, 0))
    for (int i = 0; i < ar; i++) if ((c->abound >> i & 1) && !is_bvar(a[i])) return false;
  return true;
}
static __attribute__((noinline)) Occ tc_flat_put_slow(Occ dest, uint8_t s, int con, const Term *a) {
  if ((unsigned)con >= (unsigned)ncon || (protect[s] && sealed) || !flat_args_ok(con, a)) return 0;
  const Con *c = &C[con];
  int ar = c->arity;
  for (int i = 0; i < ar; i++) {
    Term x = a[i];
    if (!tscope && !has_meta(x) && c->asort[i] == ncache_sort) N[x].flags |= F_PLAIN;
  }
  return flat_store(dest, ((uint32_t)con << 9) | ((uint32_t)s << 1) | 1u, ar, a);
}
Occ tc_flat_put(Occ dest, uint8_t s, int con, const Term *a) {
  if (__builtin_expect(flat4_board && !s && !con && dest - 1u < nw - 1u, 1)) {
    Term x0 = a[0], x1 = a[1], x2 = a[2], x3 = a[3];
    uint32_t lim = nn;
    if (__builtin_expect(x0 < lim && x1 < lim && x2 < lim && x3 < lim &&
        ((N[x0].flags & N[x1].flags & N[x2].flags & N[x3].flags & F_PLAIN) != 0), 1)) {
      Term *dst = &Wrow[(size_t)dest << 2];
      dst[0] = x0; dst[1] = x1; dst[2] = x2; dst[3] = x3;
      if (__builtin_expect(wt_dirty, 0)) Wt[dest] = 0;
      return dest;
    }
  }
  return tc_flat_put_slow(dest, s, con, a);
}
Occ tc_flat_out(Occ dest, uint8_t s, int con, const Term *a) {
  if ((unsigned)con >= (unsigned)ncon || (protect[s] && sealed) || !flat_args_ok(con, a)) return 0;
  return flat_store(dest, ((uint32_t)con << 9) | ((uint32_t)s << 1) | 1u, C[con].arity, a);
}
static __attribute__((noinline)) Occ tc_flat_fire_slow(int rid, const Occ *keep, const Term *in, Occ dest) {
#ifdef TC_ORDINARY_FLAT_TEST_HOOKS
  tc_test_ordinary_flat_slow_calls++;
#endif
  if ((unsigned)rid >= (unsigned)nr) return 0;
  RuleK *k = &R[rid];
  if (__builtin_expect(!k->fprepped, 0)) prep_flat(k);
  if (sealed && k->barred) return 0;                      /* no commit where the rule may not make */
  if (__builtin_expect(!in && k->flat && keep != NULL, 1)) {
    const Flat *q = &FL[k->fl];
    int nk = k->nkeep, ng = q->nguard, ar = q->mar;
    const Term *pa[TC_HYPS + 1];
    pa[nk] = q->mc;
    for (int i = 0; i < nk; i++) {
      Occ o = keep[i];
      if (slot_mode) {
        Occ u = o < nw ? o : 0;
        if (__builtin_expect(Wtag[u] != q->ktag[i], 0)) return 0;
        pa[i] = wargs(u, q->ktag[i] >> 9);
      } else {
        if (__builtin_expect(!o || o >= nw || Wtag[o] != q->ktag[i], 0)) return 0;
        pa[i] = wargs(o, q->ktag[i] >> 9);
      }
    }
    for (int g = 0; g < ng; g++) {
      Guard e = q->guard[g];
      if (pa[e.i][e.j] != pa[e.i0][e.j0]) return 0;
    }
    Term b[TC_ARGS];
    for (int j = 0; j < ar; j++) b[j] = pa[q->mi[j]][q->mj[j]];
    return flat_store(dest, (q->mhead << 9) | ((uint32_t)k->mspace << 1) | 1u, ar, b);
  }
  if (__builtin_expect(!keep && k->mflat && in != NULL, 1)) {
    const Rule *r = RULE(k);
    Term m = k->make;
    uint64_t req = N[m].vm & ~(r->fresh >= 0 ? (1ull << r->fresh) : 0ull);
    if (r->fresh >= 0 && in[r->fresh]) return 0;
    for (int h = 0; h < k->n; h++) {
      Term t = in[h];
      if (!t) { if (req >> h & 1) return 0; continue; }
      if (t >= nn || N[t].vm || has_meta(t) || (N[t].flags & F_BIRTH) || at_node_any(t)) goto full;   /* the full path checks these */
      if (HOLE(k, h).sort != TC_ANY && N[t].sort != HOLE(k, h).sort) return 0;
      if (!name_ok(t)) return 0;                          /* pure rules too: names are minted before use */
    }
    Term ft = 0;
    uint64_t nmark = next_name;
    if (r->fresh >= 0) {
      if (next_name >= UINT64_MAX - 1 || !(ft = tc_name(HOLE(k, r->fresh).sort, next_name))) return 0;
      next_name++;
    }
    int ar = N[m].arity;
    const Term *ma = argv(m);
    Term b[TC_ARGS];
    for (int j = 0; j < ar; j++) {
      Term a = ma[j];
      b[j] = !N[a].vm ? a : ((int)N[a].head == r->fresh ? ft : in[N[a].head]);
    }
    Occ o = flat_store(dest, (N[m].head << 9) | ((uint32_t)k->mspace << 1) | 1u, ar, b);
    if (!o) next_name = nmark;
    else if (ft && !tscope && ncache_sort == HOLE(k, r->fresh).sort) N[ft].flags |= F_PLAIN;
    return o;
  }
full:;
  uint32_t nw0 = nw;
  Occ o = tc_fire(rid, NULL, keep, in);
  if (!o || !dest || !Wtag[o]) return o;                  /* no destination: the firing's own occurrence */
  uint32_t head = Wtag[o] >> 9;
  const Term *src = wargs(o, head);
  Term b[TC_ARGS];
  for (int j = 0; j < C[head].arity; j++) b[j] = src[j];
  Occ d = flat_store(dest, Wtag[o], C[head].arity, b);
  if (d && d != o && o >= nw0) { Wa[o] = 0; Wtag[o] = 0; } /* one firing, one fact: it lives at d */
  return d ? d : o;
}
static OrdinaryFlatWorkspace ordinary_flat_workspace;

/* The runtime is single-threaded and makes no callbacks while this workspace is live. */
static uint64_t tc_flat_fire_ordinary(int rid, const Occ *keep, const Term *in,
                                      Occ dest, Occ *out) {
  *out = 0;
  if (in || !keep || (unsigned)rid >= (unsigned)nr) return ORDINARY_FLAT_UNSUPPORTED;
  RuleK *k = &R[rid];
  if (!k->fprepped) prep_flat(k);
  if (!k->flat || !FL[k->fl].ordinary) return ORDINARY_FLAT_UNSUPPORTED;
  if (sealed && k->barred) return ORDINARY_FLAT_REFUSED;  /* no commit where the rule may not make */
  const Flat *q = &FL[k->fl];
  const Term *pa[TC_HYPS];
  for (int i = 0; i < k->nkeep; i++) {
    Occ o = keep[i];
    if (slot_mode) {
      Occ u = o < nw ? o : 0;
      if (Wtag[u] != q->ktag[i]) {
#ifdef TC_ORDINARY_FLAT_TEST_HOOKS
        tc_test_ordinary_flat_refusals++;
#endif
        return ORDINARY_FLAT_REFUSED;
      }
      pa[i] = wargs(u, q->ktag[i] >> 9);
    } else {
      if (!o || o >= nw || Wtag[o] != q->ktag[i]) {
#ifdef TC_ORDINARY_FLAT_TEST_HOOKS
        tc_test_ordinary_flat_refusals++;
#endif
        return ORDINARY_FLAT_REFUSED;
      }
      pa[i] = wargs(o, q->ktag[i] >> 9);
    }
  }
  OrdinaryFlatWorkspace *ws = &ordinary_flat_workspace;
  uint32_t premise_offsets[TC_HYPS];
  for (int i = 0; i < k->nkeep; i++)
    premise_offsets[i] = (uint32_t)(pa[i] - Wrow);
#ifdef TC_ORDINARY_FLAT_TEST_HOOKS
  tc_test_ordinary_flat_leaf_calls++;
#endif
  uint64_t status = ordinary_flat_adapter(
    (cesta_read_u32_span){Wrow, 4 * (size_t)nw},
    (cesta_read_u32_span){premise_offsets, (size_t)k->nkeep},
    (cesta_read_u32_span){q->mc, q->nconst},
    (cesta_read_u32_span){q->packed_guard, q->nguard},
    (cesta_read_u32_span){q->packed_make, q->mar},
    (cesta_write_u32_span){ws->fields, 4 * (size_t)k->nkeep + q->nconst},
    (cesta_write_u32_span){ws->rows, (size_t)k->nkeep + 1},
    (cesta_write_u32_span){ws->dest, q->mar},
    (cesta_write_u32_span){ws->scratch, q->mar});
  if (status == ORDINARY_FLAT_REFUSED) {
#ifdef TC_ORDINARY_FLAT_TEST_HOOKS
    tc_test_ordinary_flat_refusals++;
#endif
    return status;
  }
  if (status != ORDINARY_FLAT_FIRED) return ORDINARY_FLAT_UNSUPPORTED;
  Term b[TC_ARGS];
  for (int j = 0; j < q->mar; j++) b[j] = ordinary_flat_workspace.dest[j];
  *out = flat_store(dest, (q->mhead << 9) | ((uint32_t)k->mspace << 1) | 1u,
                    q->mar, b);
#ifdef TC_ORDINARY_FLAT_TEST_HOOKS
  tc_test_ordinary_flat_leaf_fired++;
#endif
  return ORDINARY_FLAT_FIRED;
}

Occ tc_flat_fire(int rid, const Occ *keep, const Term *in, Occ dest) {
  tscope = bscope = false;                                /* a firing writes the board: it ends a scope */
  memset(last_extra_occ, 0, sizeof last_extra_occ);       /* extras are this firing's, or none */
  if (!in && keep) {
    Occ out;
    uint64_t status = tc_flat_fire_ordinary(rid, keep, in, dest, &out);
    if (status != ORDINARY_FLAT_UNSUPPORTED) return out;
  }
#ifdef __AVX512F__
  if (__builtin_expect((unsigned)rid < 64 && FF[rid].single_tag && !in && keep != NULL && !has_take && !(sealed && protect[0])
                       && !R[rid].barred, 1)) {
    const Flat4 *q = &FF[rid];
    uint32_t lim = nw;
    if (__builtin_expect(dest - 1u >= lim - 1u, 0)) return tc_flat_fire_slow(rid, keep, in, dest);
    Occ o0 = keep[0], o1 = keep[1], o2 = keep[2], o3 = keep[3];
    o0 = o0 < lim ? o0 : 0;
    o1 = o1 < lim ? o1 : 0;
    o2 = o2 < lim ? o2 : 0;
    o3 = o3 < lim ? o3 : 0;
    const Term *w = Wrow;
    __m128i x0 = _mm_loadu_si128((const __m128i *)&w[(size_t)o0 << 2]);
    __m128i x1 = _mm_loadu_si128((const __m128i *)&w[(size_t)o1 << 2]);
    __m128i x2 = _mm_loadu_si128((const __m128i *)&w[(size_t)o2 << 2]);
    __m128i x3 = _mm_loadu_si128((const __m128i *)&w[(size_t)o3 << 2]);
    __m256i y0 = _mm256_inserti128_si256(_mm256_castsi128_si256(x0), x1, 1);
    __m256i y1 = _mm256_inserti128_si256(_mm256_castsi128_si256(x2), x3, 1);
    __m512i z = _mm512_inserti64x4(_mm512_castsi256_si512(y0), y1, 1);
    __m512i perm = _mm512_cvtepu8_epi32(_mm_load_si128((const __m128i *)q->perm));
    if (_mm512_cmpneq_epi32_mask(z, _mm512_permutexvar_epi32(perm, z))) return 0;
    __m512i mperm = _mm512_zextsi128_si512(_mm_load_si128((const __m128i *)q->mperm));
    __m128i out = _mm512_castsi512_si128(_mm512_permutexvar_epi32(mperm, z));
    _mm_storeu_si128((__m128i *)&w[(size_t)dest << 2], out);
    if (__builtin_expect(wt_dirty, 0)) Wt[dest] = 0;
    return dest;
  }
#endif
  return tc_flat_fire_slow(rid, keep, in, dest);
}

static bool in_term_set(Term t, const Term *set, int n) {
  if (!t) return false;
  t = norm(t);
  for (int i = 0; i < n; i++) if (norm(set[i]) == t) return true;
  return false;
}
void tc_set_handle_con(int con) {                     /* a theory setting: not after the seal */
  if (sealed || (con >= 0 && (con >= ncon || C[con].arity < 1))) return;
  handle_con_id = con;
}
static void collect_handles(Term t, Term *out, int *nr_sp, int cap, bool *changed, int d) {
  if (!t || t >= nn || d > 256) return;
  if (handle_con_id >= 0) {
    if (N[t].kind == K_APP && (int)N[t].head == handle_con_id && N[t].arity >= 1) {
      Term h = norm(argv(t)[0]);
      if (h && !in_term_set(h, out, *nr_sp) && *nr_sp < cap) { out[(*nr_sp)++] = h; *changed = true; }
    }
    if (N[t].kind == K_APP) for (int i = 0; i < N[t].arity; i++) collect_handles(argv(t)[i], out, nr_sp, cap, changed, d + 1);
  } else {
    if (space_sort_id && N[t].sort == space_sort_id) {
      Term h = norm(t);
      if (h && !in_term_set(h, out, *nr_sp) && *nr_sp < cap) { out[(*nr_sp)++] = h; *changed = true; }
    }
    if (N[t].kind == K_APP) for (int i = 0; i < N[t].arity; i++) collect_handles(argv(t)[i], out, nr_sp, cap, changed, d + 1);
  }
}
int tc_reach(const Term *seeds, int nseed, Term *out, int cap) {
  if (!out || cap <= 0) return 0;
  int nr_sp = 0;
  if (!seeds) nseed = 0;
  for (int i = 0; i < nseed; i++) {
    Term s = seeds[i] && seeds[i] < nn ? norm(seeds[i]) : 0;   /* an id that is no term seeds nothing */
    if (!s) continue;
    if (handle_con_id >= 0 && N[s].kind == K_APP && (int)N[s].head == handle_con_id) {
      bool dummy = false;
      collect_handles(s, out, &nr_sp, cap, &dummy, 0);
    } else if (!in_term_set(s, out, nr_sp) && nr_sp < cap) {
      out[nr_sp++] = s;
    }
  }
  bool changed = true;
  while (changed) {
    changed = false;
    for (int sp = 0; sp < 256; sp++) {
      for (Occ o = Wlive[sp]; o; o = Wnext[o]) if (Wa[o] && !Wmark[o]) {
        Term osp = tc_occ_space(o);
        if (!in_term_set(osp, out, nr_sp)) continue;
        collect_handles(norm(tc_term(o)), out, &nr_sp, cap, &changed, 0);
      }
    }
  }
  return nr_sp;
}
Occ tc_last_extra(int idx) { return (idx >= 0 && idx < 4) ? last_extra_occ[idx] : 0; }

static bool count_ok_at(Term pat, uint8_t space, Term space_term, uint32_t want, const Term *S, int n,
                        const Term *reach_set, int nreach, bool enforce_reach) {
  const RuleK *rk = cur_k;
  if (enforce_reach) {
    if (space_term) {
      Term sp_b = inst(space_term, (Term *)S, false);
      if (!sp_b || N[sp_b].vm) return false;
      sp_b = norm(sp_b);
      if (!sp_b || has_meta(sp_b) || !in_term_set(sp_b, reach_set, nreach)) return false;
    } else if (!in_term_set(tc_space_term(space), reach_set, nreach)) return false;
  }
  uint32_t m_local = CAP_META - TC_VARS, hits = 0;
  Term E[TC_VARS];
  for (int h = 0; h < n; h++) E[h] = S[h] ? S[h] : qmeta[h];
  Term p = inst(pat, E, false);
  if (!p) return false;
  Term sp_p = space_term ? inst(space_term, E, false) : 0;
  if (space_term && !sp_p) return false;
  if (!space_term && !nmeta && !has_meta(p) && !space_has_flat[space] && Nocc && !Nocc[p])
    return want == 0;
  uint64_t vm_mask = N[pat].vm | (space_term ? N[space_term].vm : 0);
  int sp_lo = space_term ? 0 : space, sp_hi = space_term ? 255 : space;
  for (int sp = sp_lo; sp <= sp_hi; sp++) {
    for (Occ o = Wlive[sp], nxt; o; o = nxt) {
      nxt = Wnext[o];
      if (!Wa[o]) {
        if (Wprev[o]) Wnext[Wprev[o]] = Wnext[o]; else Wlive[sp] = Wnext[o];
        if (Wnext[o]) Wprev[Wnext[o]] = Wprev[o];
      }
      if (!Wa[o] || Wmark[o]) continue;
      if (!space_term && (Ws[o] != space || (Wsp[o] && Wsp[o] != tc_space_term(space)))) continue;
      uint32_t m = ntrail;
      bool hit = (!space_term || unify(sp_p, tc_occ_space(o))) && unify(p, tc_term(o)) && diseqs_ok(), amb = false;
      for (uint32_t k = m; hit && k < ntrail; k++) amb |= trail[k] < m_local;
      if (hit && !amb && rk && vm_mask) {
        Term Q[TC_VARS] = {0};
        for (int h = 0; h < n; h++) if (S[h] || (vm_mask >> h & 1)) {
          Term t = Q[h] = norm(E[h]);
          uint16_t ts = N[t].kind == K_META ? Msort[N[t].head] : N[t].sort;
          if (HOLE(rk, h).sort != TC_ANY && ts != HOLE(rk, h).sort) { if (ts == TC_ANY) amb = true; else hit = false; }
          if (rk->bounds && has_meta(t)) amb = true;
        }
        if (hit && !amb && rk->bounds && !holes_ok(rk, Q, vm_mask, false)) hit = false;
      }
      undo(m);
      if (amb || (hit && ++hits > want)) return false;
    }
  }
  return hits == want;
}

static Occ fire_ex(int rid, const Occ *take, const Occ *keep, const Term *in,
                   const Term *reach_seeds, int nseed, bool enforce_reach) {
  tscope = bscope = false;                                /* a firing writes the board: it ends a scope */
  memset(last_extra_occ, 0, sizeof last_extra_occ);       /* extras are this firing's, or none */
  if (rid < 0 || rid >= nr) return 0;
  nsteps++;
  RuleK *k = &R[rid];
  if (__builtin_expect(!k->fprepped, 0)) prep_flat(k);
  if (sealed && k->barred) return 0;                      /* no commit where the rule may not make */
  const Rule *r = RULE(k);
  if (!enforce_reach && !in && !take && k->flat && keep) {
    const Flat *q = &FL[k->fl];
    const Term *pa[TC_HYPS + 1]; pa[k->nkeep] = q->mc;
    for (int i = 0; i < k->nkeep; i++) {
      Occ o = keep[i];
      if (!o || o >= nw || Wtag[o] != q->ktag[i]) {
        if (o && o < nw && Wa[o] && has_meta(tc_term(o))) goto slow;
        return 0;
      }
      pa[i] = wargs(o, q->ktag[i] >> 9);
    }
    for (int g = 0; g < q->nguard; g++) {
      Guard e = q->guard[g];
      if (pa[e.i][e.j] != pa[e.i0][e.j0]) return 0;
    }
    Term b[TC_ARGS];
    for (int j = 0; j < q->mar; j++) b[j] = pa[q->mi[j]][q->mj[j]];
    Term out = mk(K_APP, q->mhead, q->msort, 0, 0, q->mar, b);
    return out ? post(k->mspace, out) : 0;
  }
slow:;
  Term S[TC_VARS]; uint64_t given = 0;
  uint32_t mmark = nmeta;
  uint32_t mark = ntrail; int nemark = nne; uint64_t nmark = next_name;
  Term reach_set[512]; int nreach = 0;
  if (enforce_reach) nreach = tc_reach(reach_seeds, nseed, reach_set, 512);
  ug++;
  if (!ug) { memset(ugen, 0, sizeof ugen); ug = 1; }
  for (int h = 0; h < k->n; h++) {
    S[h] = in ? in[h] : 0;
    if (S[h] && (S[h] >= nn || N[S[h]].vm || at_node_any(S[h]) || !name_ok(S[h]))) return 0;   /* minted before use */
    if (S[h] && !(S[h] = canon(S[h]))) return 0;          /* identity is equality from here on */
    if (S[h]) given |= 1ull << h;
  }
  if (r->fresh >= 0 && S[r->fresh]) return 0;
  if (given & k->outs) return 0;                          /* computed words are the kernel's to bind */
  for (int i = 0; i < r->ntake; i++) {
    if (!take || !tc_alive(take[i]) || Wmark[take[i]]) goto fail;  /* Births.keeps: never take a marker */
    for (int j = 0; j < i; j++) if (take[j] == take[i]) goto fail;
    Term osp = tc_occ_space(take[i]), pt, psp; uint8_t pmk;
    unpack_pat(r->take[i].t, &pt, &psp, &pmk);
    if (enforce_reach && !in_term_set(osp, reach_set, nreach)) goto fail;
    if (psp) {
      if (!umatch(psp, osp, S)) goto fail;
    } else if (Ws[take[i]] != r->take[i].space || (Wsp[take[i]] && osp != tc_space_term(r->take[i].space))) goto fail;
    if (!umatch(pt, tc_term(take[i]), S)) goto fail;
  }
  bool can_run = k->kcode != UINT32_MAX;
  for (int i = 0; i < k->nkeep; i++) {
    if (!keep || !tc_alive(keep[i]) || Wmark[keep[i]]) goto fail;
    for (int j = 0; j < r->ntake; j++) if (take[j] == keep[i]) goto fail;
    Term osp = tc_occ_space(keep[i]), pt, psp; uint8_t pmk;
    unpack_pat(r->keep[i].t, &pt, &psp, &pmk);
    if (enforce_reach && !in_term_set(osp, reach_set, nreach)) goto fail;
    if (psp) {
      if (!umatch(psp, osp, S)) goto fail;
      can_run = false;
    } else if (Ws[keep[i]] != r->keep[i].space || (Wsp[keep[i]] && osp != tc_space_term(r->keep[i].space))) goto fail;
    can_run &= !has_meta(tc_term(keep[i]));
  }
  if (can_run) {
    int sp = 0;
    for (int i = k->nkeep - 1; i >= 0; i--) run_st[sp++] = tc_term(keep[i]);
    if (!run_stack(k->kcode, sp, S, false)) {
      if (!run_ovf) goto fail;
      can_run = false;                                    /* past the matcher's stack: match by unification */
    }
  }
  if (!can_run) {
    for (int i = 0; i < k->nkeep; i++) {
      Term pt, psp; uint8_t pmk; unpack_pat(r->keep[i].t, &pt, &psp, &pmk);
      if (!umatch(pt, tc_term(keep[i]), S)) goto fail;
    }
  }
  for (int i = 0; i < r->ntell; i++) {
    Term a = inst(r->tell[i][0], S, true), b = inst(r->tell[i][1], S, true);
    if (!a || !b || !unify(a, b)) goto fail;
  }
  for (int i = 0; i < r->nneq; i++) {
    Term a = inst(r->neq[i][0], S, true), b = inst(r->neq[i][1], S, true);
    if (!a || !b) goto fail;
    Term na = norm(a), nb = norm(b);
    if (!na || !nb || na == nb) goto fail;
    if (!has_meta(na) && !has_meta(nb)) continue;
    if (nne >= 65536) goto fail;
    NE[nne][0] = a; NE[nne][1] = b; nne++;
  }
  bool clean = !r->ntake && !r->ntell && !r->nneq;
  if (!k->pure) clean = false;
  for (int i = 0; clean && i < k->nkeep; i++) clean = !has_meta(tc_term(keep[i]));
  for (int h = 0; clean && h < k->n; h++) clean = !S[h] || !has_meta(S[h]);
  for (int h = 0; !clean && h < k->n; h++) if (S[h] && has_meta(S[h]) && !(S[h] = norm(S[h]))) goto fail;
  if ((nne && !diseqs_ok()) || !holes_ok(k, S, given, clean)) goto fail;
  if (k->fns && !run_ops(k, r, S)) goto fail;             /* sealed operations, in order, after matching */
  cur_k = k;
  for (int i = 0; i < r->nabsent; i++) {
    Term pt, psp; uint8_t pmk; unpack_pat(r->absent[i].t, &pt, &psp, &pmk);
    if (!count_ok_at(pt, r->absent[i].space, psp, 0, S, k->n, reach_set, nreach, enforce_reach)) goto fail;
  }
  for (int i = 0; i < r->ncount; i++) {
    Term pt, psp; uint8_t pmk; unpack_pat(r->count[i].t, &pt, &psp, &pmk);
    if (!count_ok_at(pt, r->count[i].space, psp, r->count[i].n, S, k->n, reach_set, nreach, enforce_reach)) goto fail;
  }
  if (k->fns && !run_guards(k, r, S)) goto fail;          /* sealed guards, after the operations and queries */
  if (!k->pure) {
    for (int h = 0; h < k->n; h++) if (S[h] && !name_ok(S[h])) goto fail;
  }
  if (r->fresh >= 0) {                                /* EXTEND: a new name, defined from existing ones */
    for (int h = 0; h < k->n; h++) if (S[h] && has_meta(S[h])) goto fail;
    if (next_name >= UINT64_MAX - 1 || !(S[r->fresh] = tc_name(HOLE(k, r->fresh).sort, next_name))) goto fail;
    next_name++;
  }
  int nmake = 1 + r->nmake_extra;
  Term m_out[5], m_sp[5]; uint8_t m_raw_s[5], m_mark[5]; bool m_has_sp[5];
  for (int m = 0; m < nmake; m++) {
    const Pat *mp = (m == 0) ? &r->make : &r->make_extra[m - 1];
    Term pt, psp; uint8_t pmk; unpack_pat(mp->t, &pt, &psp, &pmk);
    Term out_t = inst(pt, S, false);
    if (!out_t || N[out_t].vm || (!clean && has_meta(out_t) && !(out_t = norm(out_t)))) goto fail;
    m_out[m] = out_t; m_raw_s[m] = mp->space; m_mark[m] = pmk; m_has_sp[m] = psp != 0;
    if (psp) {
      Term sp_t = inst(psp, S, false);
      if (!sp_t || N[sp_t].vm || (!clean && has_meta(sp_t) && !(sp_t = norm(sp_t)))) goto fail;
      m_sp[m] = sp_t;
    } else {
      m_sp[m] = (r->birth_law || enforce_reach || pmk) ? tc_space_term(mp->space) : 0;
    }
  }
  if (r->birth_law) {
    /* Births.fresh & Births.single */
    for (int m = 0; m < nmake; m++) if (m_mark[m]) {
      if (tc_space_born(m_sp[m])) goto fail;
      for (int m2 = m + 1; m2 < nmake; m2++) if (m_mark[m2] && m_sp[m] == m_sp[m2]) goto fail;
    }
    /* Births.located: every take, keep, and make lies in born(present) or a newly born space of this firing */
    for (int i = 0; i < r->ntake; i++) {
      Term sp = norm(tc_occ_space(take[i]));
      bool loc = tc_space_born(sp);
      for (int m = 0; !loc && m < nmake; m++) if (m_mark[m] && m_sp[m] == sp) loc = true;
      if (!loc) goto fail;
    }
    for (int i = 0; i < k->nkeep; i++) {
      Term sp = norm(tc_occ_space(keep[i]));
      bool loc = tc_space_born(sp);
      for (int m = 0; !loc && m < nmake; m++) if (m_mark[m] && m_sp[m] == sp) loc = true;
      if (!loc) goto fail;
    }
    for (int j = 0; j < nmake; j++) {
      Term sp = m_sp[j];
      bool loc = tc_space_born(sp);
      for (int m = 0; !loc && m < nmake; m++) if (m_mark[m] && m_sp[m] == sp) loc = true;
      if (!loc) goto fail;
    }
  }
  if (enforce_reach) {
    for (int j = 0; j < nmake; j++) {
      bool ok_r = in_term_set(m_sp[j], reach_set, nreach);
      for (int m = 0; !ok_r && m < nmake; m++) if (m_mark[m] && m_sp[m] == m_sp[j]) ok_r = true;
      if (!ok_r) goto fail;
    }
  }
  if (sealed && k->dynmake && !publish_ok(k, rid, nmake, m_has_sp, m_mark, m_sp, m_raw_s)) goto fail;   /* computed spaces */
  uint32_t nw0 = nw;                                      /* occurrences from nw0 on are this firing's own */
  Occ o = (m_has_sp[0] || m_mark[0]) ? post_at_internal(m_sp[0], m_out[0], m_mark[0]) : post(m_raw_s[0], m_out[0]);
  if (!o) goto fail;
  memset(last_extra_occ, 0, sizeof last_extra_occ);
  for (int m = 1; m < nmake; m++) {
    Occ oe = (m_has_sp[m] || m_mark[m]) ? post_at_internal(m_sp[m], m_out[m], m_mark[m]) : post(m_raw_s[m], m_out[m]);
    if (!oe) {                                            /* undo only what this firing appended (a set store may */
      if (o >= nw0) { Wa[o] = 0; Wtag[o] = 0; }           /* have answered a make with an older occurrence) */
      for (int j = 1; j < m; j++) if (last_extra_occ[j - 1] >= nw0) { Wa[last_extra_occ[j - 1]] = 0; Wtag[last_extra_occ[j - 1]] = 0; }
      goto fail;
    }
    last_extra_occ[m - 1] = oe;
  }
  for (int i = 0; i < r->ntake; i++) { Wa[take[i]] = 0; Wtag[take[i]] = 0; }
  return o;
fail:
  undo(mark); nne = nemark; next_name = nmark; nmeta = mmark;
  return 0;
}

Occ tc_fire(int rid, const Occ *take, const Occ *keep, const Term *in) {
  return fire_ex(rid, take, keep, in, NULL, 0, false);
}
Occ tc_fire_reach(int rid, const Occ *take, const Occ *keep, const Term *in,
                  const Term *seeds, int nseed) {
  return fire_ex(rid, take, keep, in, seeds, nseed, true);
}
/* ---- search under reach ----
   tc_search_reach proposes; tc_fire_reach admits. Every firing the search performs is one call of
   tc_fire_reach on a complete selection, made from the state the search was entered in, so the search
   admits nothing that tc_fire_reach would not admit on that selection.

   A selection is built one position at a time, the takes in order and then the keeps in order. A
   candidate is skipped at a position when the firing would refuse every selection that extends the
   positions chosen so far with it:
     - it is dead, a birth marker, outside the reach, or one of the takes chosen so far (for a keep: one
       of the takes): the tests fire_ex makes first for that position;
     - a pattern with a static space has its candidates on that space's live list only;
     - its space does not match the position's space pattern, or its term does not match the position's
       pattern, under the bindings of the earlier positions. The matcher is umatch, which fire_ex
       applies to the same patterns and occurrences. For the takes these are fire_ex's own first
       operations in its own order. For the keeps fire_ex matches every space before any term and may
       match ground terms with the compiled matcher; here a keep's term is unified as soon as its
       position is reached, which refuses no selection whose equations have a solution.
   The chosen positions are matched from the entry state each time and undone (sr_prefix), so no binding
   of the search is in force when tc_fire_reach runs.

   Candidates are walked on the live lists in the lists' own order: spaces 0..255, newest first, the
   order of the selections is the order the exhaustive enumeration had. Walking the lists while firings
   are attempted is safe: an occurrence slot is never reused, a refused firing kills only what it
   appended (at the head of a list), and only dead occurrences are unlinked, so the successor link of a
   live cursor stays valid. The number of candidates is not bounded.

   Not changed: the reach is computed into 512 terms, as fire_ex computes its own, and a space past that
   bound is treated as out of reach by both. */
typedef struct {
  int rid; const RuleK *k; const Rule *r;
  const Term *seeds; int nseed;
  const Term *reach; int nreach;
  uint32_t mark, mmark;                                   /* the trail and the unknowns at entry */
  Occ take[4], keep[TC_HYPS];
} SrSearch;
/* Positions 0..upto-1 of the selection, matched from the entry state: the takes in order (space, then
   term), then the keeps' spaces in order, then the keeps' terms in order. False at the first refusal.
   The caller undoes the trail. */
static bool sr_prefix(const SrSearch *c, int upto, Term *S) {
  const Rule *r = c->r;
  int nt = upto < r->ntake ? upto : r->ntake, nk = upto - nt;
  for (int h = 0; h < c->k->n; h++) S[h] = 0;
  for (int i = 0; i < nt; i++) {
    Occ o = c->take[i];
    Term osp = tc_occ_space(o), pt, psp; uint8_t pmk;
    unpack_pat(r->take[i].t, &pt, &psp, &pmk);
    if (psp) {
      if (!umatch(psp, osp, S)) return false;
    } else if (Ws[o] != r->take[i].space || (Wsp[o] && osp != tc_space_term(r->take[i].space))) return false;
    if (!umatch(pt, tc_term(o), S)) return false;
  }
  for (int i = 0; i < nk; i++) {
    Occ o = c->keep[i];
    Term osp = tc_occ_space(o), pt, psp; uint8_t pmk;
    unpack_pat(r->keep[i].t, &pt, &psp, &pmk);
    if (psp) {
      if (!umatch(psp, osp, S)) return false;
    } else if (Ws[o] != r->keep[i].space || (Wsp[o] && osp != tc_space_term(r->keep[i].space))) return false;
  }
  for (int i = 0; i < nk; i++) {
    Term pt, psp; uint8_t pmk;
    unpack_pat(r->keep[i].t, &pt, &psp, &pmk);
    if (!umatch(pt, tc_term(c->keep[i]), S)) return false;
  }
  return true;
}
static Occ sr_rec(SrSearch *c, int idx) {
  const Rule *r = c->r;
  int nkeep = c->k->nkeep;
  if (idx == r->ntake + nkeep)
    return tc_fire_reach(c->rid, r->ntake ? c->take : NULL, nkeep ? c->keep : NULL, NULL, c->seeds, c->nseed);
  bool is_take = idx < r->ntake;
  int j = is_take ? idx : idx - r->ntake;
  const Pat *p = is_take ? &r->take[j] : &r->keep[j];
  Term pt, psp; uint8_t pmk;
  unpack_pat(p->t, &pt, &psp, &pmk);
  int sp_lo = psp ? 0 : p->space, sp_hi = psp ? 255 : p->space;
  int ntaken = is_take ? j : r->ntake;
  for (int sp = sp_lo; sp <= sp_hi; sp++)
    for (Occ o = Wlive[sp]; o; o = Wnext[o]) {
      if (!Wa[o] || Wmark[o] || !in_term_set(tc_occ_space(o), c->reach, c->nreach)) continue;
      bool dup = false;
      for (int t = 0; t < ntaken; t++) if (c->take[t] == o) { dup = true; break; }
      if (dup) continue;
      if (is_take) c->take[j] = o; else c->keep[j] = o;
      Term S[TC_VARS];
      bool ok = sr_prefix(c, idx + 1, S);
      undo(c->mark); nmeta = c->mmark;
      if (!ok) continue;
      Occ got = sr_rec(c, idx + 1);
      if (got) return got;
    }
  return 0;
}
Occ tc_search_reach(int rid, const Term *seeds, int nseed) {
  if (rid < 0 || rid >= nr) return 0;
  tscope = bscope = false;                                /* a search may write the board: it ends a scope */
  memset(last_extra_occ, 0, sizeof last_extra_occ);       /* extras are a firing's of this search, or none */
  RuleK *k = &R[rid];
  Term reach_set[512];
  SrSearch c = { .rid = rid, .k = k, .r = RULE(k), .seeds = seeds, .nseed = nseed, .reach = reach_set };
  c.nreach = tc_reach(seeds, nseed, reach_set, 512);
  c.mark = ntrail; c.mmark = nmeta;
  return sr_rec(&c, 0);
}

/* A conversion, an active step or a rho step rewrites one occurrence into an equal term. In a store
   with multiplicity (some rule takes or counts, or a located fact exists: has_take) it replaces the
   source, as a firing that takes it would; in a set store it adds the equal fact. */
static Occ rewrite_occ(Occ p, Term t) {
  Occ o = Wsp[p] ? post_at_internal(Wsp[p], t, Wmark[p]) : post(Ws[p], t);
  if (o && o != p && has_take) { Wa[p] = 0; Wtag[p] = 0; }
  return o;
}
/* An occurrence of an evidence space: after the seal only its producers write there, so no
   conversion, active step or rho step rewrites it. */
static bool occ_in_evidence(Occ p) {
  if (!p || p >= nw) return false;
  int s = Wsp[p] ? static_space_of(Wsp[p]) : (int)Ws[p];
  return s >= 0 && pubset[s];
}
Occ tc_convert(Occ p, const Conv *c, Term target) {
  tscope = bscope = false;                                /* a conversion writes the board: it ends a scope */
  nsteps++;
  if (sealed && occ_in_evidence(p)) return 0;
  if (target && target < nn && (at_node_any(target) || !(target = canon(target)))) return 0;
  Term pt = tc_term(p);
  if (!tc_alive(p) || !pt || !target || target >= nn || N[target].vm || !name_ok(target)
      || has_meta(pt) || has_meta(target) || !(conv(c, pt, target, 0) || conv(c, target, pt, 0))) return 0;
  return rewrite_occ(p, target);
}

/* ---- SHARE: a proof script checked once in its context, then one rule ---- */
static inline bool lemma_term(Term t, uint64_t ctx) {
  return ctx_ok(t) && !(N[t].flags & (F_META | F_BV)) && !(N[t].vm & ~ctx);
}
/* A lemma is checked step by step as its proof arrives: tc_lemma opens it over the first nb
   variables of the context, each step is checked against earlier ones and the hypotheses, and
   tc_lemma_end installs the conclusion of one of them as a rule. */
static Term *lres, lhyp[TC_HYPS]; static uint8_t *lsp; static uint32_t nlres, lcap, lmark;
static int lnb, nlhyp; static uint8_t lspace;
bool tc_lemma(int nb, uint8_t space) {
  lok = nb >= 0 && nb <= cn; lnb = nb; lspace = space; nlres = 0; nlhyp = 0; lmark = ntrail;
  return lok;
}
bool tc_lemma_hyp(Term h) {                               /* hypothesis k is referred to as -1-k */
  if (!lok || nlhyp >= TC_HYPS || !lemma_term(h, mask(lnb)) || !(sorts[N[h].sort] & SORT_PROVABLE)) return lok = false;
  lhyp[nlhyp++] = h;
  return true;
}
Term tc_lemma_term(int ref) { return !lok ? 0 : ref >= 0 ? (ref < (int)nlres ? lres[ref] : 0) : (-1 - ref < nlhyp ? lhyp[-1 - ref] : 0); }
static bool lemma_step(const Step *s) {
  static Term S[TC_VARS];
  uint64_t ctx = mask(cn);
  nsteps++;
  Term out; uint8_t space;
  if (__builtin_expect(s->kind == ST_CONV, 0)) {
    int q = s->prem[0];
    if (q >= (int)nlres || q < -nlhyp) return false;
    Term pt = q >= 0 ? lres[q] : lhyp[-1 - q];
    space = q >= 0 ? lsp[q] : lspace;
    if (!lemma_term(s->target, ctx) || !name_ok(s->target)
        || !(conv(s->conv, pt, s->target, 0) || conv(s->conv, s->target, pt, 0))) return false;
    out = s->target;
  } else {
    if ((unsigned)s->rule >= (unsigned)nr) return false;
    RuleK *k = &R[s->rule];
    if (!k->pure) return false;
    if (__builtin_expect(!k->prepped, 0)) prep_rule(k);
    if (s->inst) for (int h = 0; h < k->n; h++) S[h] = s->inst[h];
    else for (int h = 0; h < k->n; h++) S[h] = 0;
    int np = k->nkeep, sp = 0;
    if (s->target) {
      if (!lemma_term(s->target, ctx) || !name_ok(s->target)) return false;
      run_st[sp++] = s->target;
    }
    if (__builtin_expect(k->ks_zero, 1)) {
      for (int j = np - 1; j >= 0; j--) {
        int q = s->prem[j];
        if (q >= (int)nlres || q < -nlhyp || (q >= 0 ? lsp[q] : lspace)) return false;
        run_st[sp++] = q >= 0 ? lres[q] : lhyp[-1 - q];
      }
    } else {
      const Rule *r = RULE(k);
      for (int j = np - 1; j >= 0; j--) {
        int q = s->prem[j];
        if (q >= (int)nlres || q < -nlhyp || (q >= 0 ? lsp[q] : lspace) != r->keep[j].space) return false;
        run_st[sp++] = q >= 0 ? lres[q] : lhyp[-1 - q];
      }
    }
    uint64_t rem = mask(k->n) & ~(s->target ? k->mimplied : k->implied);
    bool by_unify = k->mcode == UINT32_MAX;
    if (__builtin_expect(!by_unify, 1)) {
      Term saved[TC_HYPS + 1];                            /* run_stack consumes run_st */
      for (int i = 0; i < sp; i++) saved[i] = run_st[i];
      if (!run_stack(k->kcode, sp, S, true)) {
        if (!run_ovf) return false;
        for (int i = 0; i < sp; i++) run_st[i] = saved[i];   /* past the matcher's stack: match by unification */
        for (int h = 0; h < k->n; h++) S[h] = s->inst ? s->inst[h] : 0;
        by_unify = true;
      }
    }
    if (by_unify) {
      rem = mask(k->n);
      for (int h = 0; h < k->n; h++) if (S[h] && (!lemma_term(S[h], ctx) || !name_ok(S[h]) || at_node_any(S[h]))) return false;
      const Rule *r = RULE(k);
      for (int j = 0; j < np; j++) if (!umatch(r->keep[j].t, run_st[sp - 1 - j], S)) return false;
      if (s->target && !umatch(k->make, s->target, S)) return false;
    }
    if (__builtin_expect(rem != 0, 0)) {
      for (uint64_t m = rem; m; m &= m - 1) {
        int h = __builtin_ctzll(m);
        Term t = S[h];
        if (!t) continue;
        if (!lemma_term(t, ctx) || !name_ok(t) || at_node_any(t) || (HOLE(k, h).sort != TC_ANY && N[t].sort != HOLE(k, h).sort) || (HOLE(k, h).bound && !is_bvar(t))) return false;
      }
    }
    if (k->bounds) {
      for (uint64_t m = k->bounds; m; m &= m - 1) {
        int h = __builtin_ctzll(m);
        for (uint64_t a = S[h] ? HOLE(k, h).avoid : 0; a; a &= a - 1) {
          int j = __builtin_ctzll(a);
          if (S[j] && (N[S[h]].bm & N[S[j]].bm)) return false;
        }
      }
    }
    if (s->target) out = s->target;
    else if (!(out = inst(k->make, S, false)) || (N[out].vm & ~ctx) || has_meta(out)) return false;
    space = k->mspace;
  }
  if (nlres >= lcap) {
    uint32_t m = lcap ? 2 * lcap : 1024;
    Term *a = realloc(lres, m * sizeof *a); if (!a) return false; lres = a;
    uint8_t *b = realloc(lsp, m); if (!b) return false; lsp = b;
    lcap = m;
  }
  lres[nlres] = out; lsp[nlres++] = space;
  return true;
}
int tc_lemma_step(const Step *s) {                        /* the new step's index, or -1 */
  if (!lok || !s || !lemma_step(s)) { lok = false; undo(lmark); return -1; }
  return (int)nlres - 1;
}
int tc_lemma_end(int ref) {                               /* install the conclusion of ref as a rule */
  Term concl = tc_lemma_term(ref);                        /* 0 unless ref names a step or hypothesis */
  uint8_t space = !concl ? 0 : ref >= 0 ? lsp[ref] : lspace;
  bool ok = lok && concl && space == lspace && lemma_term(concl, mask(lnb)) && (sorts[N[concl].sort] & SORT_PROVABLE)
            && !pubset[lspace];                           /* a derived rule produces no evidence */
  for (int i = lnb; ok && i < cn; i++) ok = cbound[i] && !(sorts[csort[i]] & (SORT_STRICT | SORT_FREE));   /* dummies */
  lok = false;
  if (!ok) { tscope = bscope = false; return -1; }
  Rule L = { .nkeep = (uint8_t)nlhyp, .make = { concl, lspace }, .fresh = -1 };
  bool birth = bscope;                                      /* the installed rule outlives the scope: its patterns */
  bscope = false;                                           /* are made hash-consed and kept by the release below */
  Term *ts[TC_HYPS + 1] = { [0] = &L.make.t };
  for (int i = 0; i < nlhyp; i++) { L.keep[i] = (Pat){ lhyp[i], lspace }; ts[i + 1] = &L.keep[i].t; }
  if (birth) for (int i = 0; i < nlhyp + 1; i++) if (!(*ts[i] = canon(*ts[i]))) { tscope = false; return -1; }
  release(ts, nlhyp + 1);
  int rid = add_rule(&L, lnb, true);
  if (birth && rid >= 0) { bscope = true; prep_rule(&R[rid]); bscope = false; }   /* structural bytecode, as before */
  return rid;
}
int tc_promote(int nb, uint8_t space, int nhyp, const Term *hyps, Term concl, const Step *st, int ns) {
  if (nhyp < 0 || nhyp > TC_HYPS || ns <= 0 || (nhyp > 0 && !hyps) || !st || !tc_lemma(nb, space)) return -1;
  for (int i = 0; i < nhyp; i++) if (!tc_lemma_hyp(hyps[i])) return -1;
  for (int i = 0; i < ns; i++) if (tc_lemma_step(&st[i]) < 0) return -1;
  if (tc_lemma_term(ns - 1) != concl) { lok = false; return -1; }
  return tc_lemma_end(ns - 1);
}

/* ---- Row 6: ProgramReflection & ProgramBindersQuoted ---- */
static bool con_arity_is(int con, int ar) { return con >= 0 && con < ncon && C[con].arity == ar; }
void tc_set_quote_con(int quote_con, int activate_con, int lam_con, int app_con) {
  /* a theory setting: not after the seal; each constructor has the arity the steps below read */
  if (sealed || !con_arity_is(quote_con, 1) || !con_arity_is(activate_con, 1) || !con_arity_is(lam_con, 2) || !con_arity_is(app_con, 2)) return;
  q_quote_con = quote_con; q_act_con = activate_con; q_lam_con = lam_con; q_app_con = app_con;
}
static bool active_deep;                                  /* the last step search stopped short: depth or capture */
static Term subst_bv(Term body, Term bv, Term val, int d) {
  if (!body || body >= nn || d > 4096) return 0;
  if (body == bv) return val;
  if (N[body].kind != K_APP) return body;
  if ((int)N[body].head == q_lam_con && N[body].arity == 2 && argv(body)[0] == bv) return body;
  if ((int)N[body].head == q_lam_con && N[body].arity == 2 && (N[argv(body)[0]].bm & N[val].bm)
      && (N[argv(body)[1]].bm & N[bv].bm)) { active_deep = true; return 0; }   /* would capture: no renaming here, so no step */
  Term b[TC_ARGS]; bool chg = false;
  int ar = N[body].arity;
  for (int i = 0; i < ar; i++) {
    Term ai = argv(body)[i];
    if ((int)N[body].head == q_lam_con && i == 0) b[i] = ai;
    else {
      b[i] = subst_bv(ai, bv, val, d + 1);
      if (!b[i]) return 0;
      chg |= (b[i] != ai);
    }
  }
  return chg ? tc_app((int)N[body].head, b) : body;
}
static Term active_step_rec(Term t, int d) {
  if (!t || t >= nn) return 0;
  if (d > 4096) { active_deep = true; return 0; }        /* bounded like every other recursion here */
  t = norm(t);
  if (!t || N[t].kind != K_APP || (int)N[t].head == q_quote_con) return 0;  /* quote is inert */
  int hd = (int)N[t].head, ar = N[t].arity;
  if (hd == q_app_con && ar == 2) {
    Term f = argv(t)[0], a = argv(t)[1];
    if (N[f].kind == K_APP && (int)N[f].head == q_lam_con && N[f].arity == 2)
      return subst_bv(argv(f)[1], argv(f)[0], a, 0);
    Term sf = active_step_rec(f, d + 1);
    if (sf) return tc_app(q_app_con, (Term[2]){ sf, a });
    Term sa = active_step_rec(a, d + 1);
    if (sa) return tc_app(q_app_con, (Term[2]){ f, sa });
    return 0;
  }
  if (hd == q_act_con && ar == 1) {
    Term c = argv(t)[0];
    if (N[c].kind == K_APP && (int)N[c].head == q_quote_con && N[c].arity == 1)
      return argv(c)[0];                                                     /* one layer of quotation removed */
    Term sc = active_step_rec(c, d + 1);
    if (sc) return tc_app(q_act_con, &sc);
    return 0;
  }
  if (hd == q_lam_con && ar == 2) {
    Term x = argv(t)[0], body = argv(t)[1];
    Term sb = active_step_rec(body, d + 1);
    if (sb) return tc_app(q_lam_con, (Term[2]){ x, sb });
    return 0;
  }
  return 0;
}
Term tc_active_step(Term t) { active_deep = false; return active_step_rec(t, 0); }
Term tc_active_norm(Term t, int max_steps) {
  if (!t || t >= nn || max_steps < 0) return 0;
  t = norm(t);
  for (int i = 0; i < max_steps; i++) {
    Term nxt = tc_active_step(t);
    if (!nxt) return active_deep ? 0 : t;                 /* too deep to search is not a normal form */
    t = nxt;
  }
  return tc_active_step(t) || active_deep ? 0 : t;
}
Occ tc_active_step_occ(Occ o) {
  if (!tc_alive(o) || (sealed && occ_in_evidence(o))) return 0;
  Term nxt = tc_active_step(tc_term(o));
  if (!nxt) return 0;
  nsteps++;
  return rewrite_occ(o, nxt);
}

/* ---- Row 7: RhoContinuation & ContextualCommunicationReflection ---- */
void tc_set_rho_con(int quote_con, int drop_con, bool allow_proc_drop) {
  /* a theory setting: not after the seal; quote : Proc -> Name and drop : Name -> Proc, so the law
     quote(drop(n)) = n relates two terms of the Name sort only */
  if (sealed || !con_arity_is(quote_con, 1) || !con_arity_is(drop_con, 1) || quote_con == drop_con
      || C[quote_con].asort[0] != C[drop_con].sort || C[drop_con].asort[0] != C[quote_con].sort
      || C[quote_con].sort == C[drop_con].sort) return;
  rho_quote_con = quote_con; rho_drop_con = drop_con; rho_allow_drop = allow_proc_drop;
}
static Term rho_norm_rec(Term t, int d) {
  if (!t || t >= nn || d > 4096) return 0;
  t = norm(t);
  if (!t || N[t].kind != K_APP) return t;
  int hd = (int)N[t].head, ar = N[t].arity;
  Term b[TC_ARGS];
  for (int i = 0; i < ar; i++) {
    b[i] = rho_norm_rec(argv(t)[i], d + 1);
    if (!b[i]) return 0;
  }
  if (hd == rho_quote_con && ar == 1 && N[b[0]].kind == K_APP && (int)N[b[0]].head == rho_drop_con && N[b[0]].arity == 1)
    return argv(b[0])[0];                                                    /* Name-sort law: quote(drop(n)) = n */
  return tc_app(hd, ar ? b : NULL);
}
Term tc_rho_norm_name(Term t) { return rho_norm_rec(t, 0); }
Occ tc_rho_step_occ(Occ o) {
  if (!rho_allow_drop || !tc_alive(o) || (sealed && occ_in_evidence(o))) return 0;
  Term t = norm(tc_term(o));
  if (!t || N[t].kind != K_APP || (int)N[t].head != rho_drop_con || N[t].arity != 1) return 0;
  Term inner = argv(t)[0];
  if (N[inner].kind != K_APP || (int)N[inner].head != rho_quote_con || N[inner].arity != 1) return 0;
  Term proc = argv(inner)[0];
  nsteps++;
  return rewrite_occ(o, proc);
}
Term tc_rho_comm(Term ch_out, Term ch_in, Term payload_proc,
                 Term cont_pat, int var_name, int var_proc) {
  if (rho_quote_con < 0 || !ch_out || !ch_in || !payload_proc || !cont_pat) return 0;
  Term no = tc_rho_norm_name(ch_out), ni = tc_rho_norm_name(ch_in);
  if (!no || !ni || no != ni) return 0;
  Term q_pay = tc_app(rho_quote_con, &payload_proc);
  if (!q_pay) return 0;
  Term S[TC_VARS] = {0};
  if (var_name >= 0 && var_name < TC_VARS) S[var_name] = q_pay;
  if (var_proc >= 0 && var_proc < TC_VARS) S[var_proc] = payload_proc;
  return inst(cont_pat, S, false);
}

/* ---- Modular Prepared-Step & Cursor Interface (CeTTa <-> tcalc Bridge) ---- */
int tc_rule_count(void) { return nr; }
bool tc_rule_arity(int rule, uint8_t *out_ntake, uint8_t *out_nkeep, uint8_t *out_nholes) {
  if (rule < 0 || rule >= nr) return false;
  RuleK *k = &R[rule];
  const Rule *r = RULE(k);
  if (out_ntake)  *out_ntake  = r->ntake;
  if (out_nkeep)  *out_nkeep  = k->nkeep;
  if (out_nholes) *out_nholes = (uint8_t)k->n;
  return true;
}

int tc_eval_prepared_ex(const TcPreparedStep *step,
                        bool check_absent, bool check_count,
                        bool check_birth, bool check_reach,
                        bool do_commit,
                        Term out_make_terms[5], Term out_make_spaces[5],
                        uint8_t out_make_marks[5], uint8_t *out_nmake,
                        Occ *out_occ) {
  if (out_nmake) *out_nmake = 0;
  if (out_occ) *out_occ = 0;
  tscope = bscope = false;                                /* evaluation makes terms the board may keep: it ends a scope */
  if (do_commit) memset(last_extra_occ, 0, sizeof last_extra_occ);   /* extras are this firing's, or none */
  if (!step || step->rule < 0 || step->rule >= nr) return TC_PREP_BAD_RULE;
  RuleK *k = &R[step->rule];
  if (__builtin_expect(!k->fprepped, 0)) prep_flat(k);
  if (sealed && k->barred) return TC_PREP_PUBLISH_GUARD;  /* no firing of it commits after the seal */
  const Rule *r = RULE(k);
  const Occ *take = step->take;
  const Occ *keep = step->keep;
  const Term *in  = step->inst;

  /* 1. Enabled(present(s), selection(f)): live resources & no double-take */
  for (int i = 0; i < r->ntake; i++) {
    if (!take || !tc_alive(take[i]) || Wmark[take[i]]) return TC_PREP_ABSENT_RESOURCE;
    for (int j = 0; j < i; j++) if (take[j] == take[i]) return TC_PREP_DOUBLE_TAKE;
  }
  for (int i = 0; i < k->nkeep; i++) {
    if (!keep || !tc_alive(keep[i]) || Wmark[keep[i]]) return TC_PREP_ABSENT_RESOURCE;
    for (int j = 0; j < r->ntake; j++) if (take[j] == keep[i]) return TC_PREP_DOUBLE_TAKE;
  }

  /* 2. Shapes(f) & Solvable(information(f)): premise matching, tell/neq, and prepared result */
  Term S[TC_VARS]; uint64_t given = 0;
  uint32_t mmark = nmeta;
  uint32_t mark = ntrail; int nemark = nne; uint64_t nmark = next_name;
  int rc = TC_PREP_SHAPE_UNIFY;
  ug++;
  if (!ug) { memset(ugen, 0, sizeof ugen); ug = 1; }
  for (int h = 0; h < k->n; h++) {
    S[h] = in ? in[h] : 0;
    if (S[h] && (S[h] >= nn || N[S[h]].vm || at_node_any(S[h]) || !name_ok(S[h]))) goto fail;   /* minted before use */
    if (S[h] && !(S[h] = canon(S[h]))) goto fail;         /* identity is equality from here on */
    if (S[h]) given |= 1ull << h;
  }
  if (r->fresh >= 0 && S[r->fresh]) goto fail;
  if (given & k->outs) goto fail;                         /* computed words are the kernel's to bind */
  for (int i = 0; i < r->ntake; i++) {
    Term osp = tc_occ_space(take[i]), pt, psp; uint8_t pmk;
    unpack_pat(r->take[i].t, &pt, &psp, &pmk);
    if (psp) {
      if (!umatch(psp, osp, S)) goto fail;
    } else if (Ws[take[i]] != r->take[i].space || (Wsp[take[i]] && osp != tc_space_term(r->take[i].space))) goto fail;
    if (!umatch(pt, tc_term(take[i]), S)) goto fail;
  }
  for (int i = 0; i < k->nkeep; i++) {
    Term osp = tc_occ_space(keep[i]), pt, psp; uint8_t pmk;
    unpack_pat(r->keep[i].t, &pt, &psp, &pmk);
    if (psp) {
      if (!umatch(psp, osp, S)) goto fail;
    } else if (Ws[keep[i]] != r->keep[i].space || (Wsp[keep[i]] && osp != tc_space_term(r->keep[i].space))) goto fail;
    if (!umatch(pt, tc_term(keep[i]), S)) goto fail;
  }
  for (int i = 0; i < r->ntell; i++) {
    Term a = inst(r->tell[i][0], S, true), b = inst(r->tell[i][1], S, true);
    if (!a || !b || !unify(a, b)) goto fail;
  }
  for (int i = 0; i < r->nneq; i++) {
    Term a = inst(r->neq[i][0], S, true), b = inst(r->neq[i][1], S, true);
    if (!a || !b) goto fail;
    Term na = norm(a), nb = norm(b);
    if (!na || !nb || na == nb) goto fail;
    if (!has_meta(na) && !has_meta(nb)) continue;
    if (nne >= 65536) goto fail;
    NE[nne][0] = a; NE[nne][1] = b; nne++;
  }
  bool clean = !r->ntake && !r->ntell && !r->nneq && k->pure;
  for (int i = 0; clean && i < k->nkeep; i++) clean = !has_meta(tc_term(keep[i]));
  for (int h = 0; clean && h < k->n; h++) clean = !S[h] || !has_meta(S[h]);
  for (int h = 0; !clean && h < k->n; h++) if (S[h] && has_meta(S[h]) && !(S[h] = norm(S[h]))) goto fail;
  if ((nne && !diseqs_ok()) || !holes_ok(k, S, given, clean)) goto fail;
  if (!k->pure) {
    for (int h = 0; h < k->n; h++) if (S[h] && !name_ok(S[h])) goto fail;
  }
  if (k->fns && !run_ops(k, r, S)) { rc = TC_PREP_FN_GUARD; goto fail; }   /* sealed operations, after matching */
  if (r->fresh >= 0) {
    for (int h = 0; h < k->n; h++) if (S[h] && has_meta(S[h])) goto fail;
    if (next_name >= UINT64_MAX - 1 || !(S[r->fresh] = tc_name(HOLE(k, r->fresh).sort, next_name))) goto fail;
    next_name++;
  }
  int nmake = 1 + r->nmake_extra;
  Term m_out[5], m_sp[5]; uint8_t m_raw_s[5], m_mark[5]; bool m_has_sp[5];
  for (int m = 0; m < nmake; m++) {
    const Pat *mp = (m == 0) ? &r->make : &r->make_extra[m - 1];
    Term pt, psp; uint8_t pmk; unpack_pat(mp->t, &pt, &psp, &pmk);
    Term out_t = inst(pt, S, false);
    if (!out_t || N[out_t].vm || (!clean && has_meta(out_t) && !(out_t = norm(out_t)))) goto fail;
    m_out[m] = out_t; m_raw_s[m] = mp->space; m_mark[m] = pmk; m_has_sp[m] = psp != 0;
    if (psp) {
      Term sp_t = inst(psp, S, false);
      if (!sp_t || N[sp_t].vm || (!clean && has_meta(sp_t) && !(sp_t = norm(sp_t)))) goto fail;
      m_sp[m] = sp_t;
    } else {
      m_sp[m] = tc_space_term(mp->space);
    }
    if (out_make_terms) out_make_terms[m] = m_out[m];
    if (out_make_spaces) out_make_spaces[m] = m_sp[m];
    if (out_make_marks) out_make_marks[m] = m_mark[m];
  }
  if (out_nmake) *out_nmake = (uint8_t)nmake;

  /* A commit into a protected space of a sealed theory is a firing of the theory: the guards its
     rule declares are part of the rule, not of the caller's profile. */
  if (do_commit && sealed) {
    bool into_protected = false;
    for (int m = 0; m < nmake; m++) {
      int si = (m_has_sp[m] || m_mark[m]) ? static_space_of(m_sp[m]) : (int)m_raw_s[m];
      if (si >= 0 && protect[si]) into_protected = true;
    }
    if (into_protected) check_absent = check_count = check_birth = true;
  }

  /* 3. Admission guards (evaluated only as requested by the admission profile) */
  Term reach_set[512]; int nreach = 0;
  if (check_reach) {
    nreach = tc_reach(step->seeds, step->nseeds, reach_set, 512);
    for (int i = 0; i < r->ntake; i++) {
      if (!in_term_set(tc_occ_space(take[i]), reach_set, nreach)) { rc = TC_PREP_REACH_GUARD; goto fail; }
    }
    for (int i = 0; i < k->nkeep; i++) {
      if (!in_term_set(tc_occ_space(keep[i]), reach_set, nreach)) { rc = TC_PREP_REACH_GUARD; goto fail; }
    }
    for (int j = 0; j < nmake; j++) {
      bool ok_r = in_term_set(m_sp[j], reach_set, nreach);
      for (int m = 0; !ok_r && m < nmake; m++) if (m_mark[m] && m_sp[m] == m_sp[j]) ok_r = true;
      if (!ok_r) { rc = TC_PREP_REACH_GUARD; goto fail; }
    }
  }
  cur_k = k;
  if (check_absent) {
    for (int i = 0; i < r->nabsent; i++) {
      Term pt, psp; uint8_t pmk; unpack_pat(r->absent[i].t, &pt, &psp, &pmk);
      if (!count_ok_at(pt, r->absent[i].space, psp, 0, S, k->n, check_reach ? reach_set : NULL, nreach, check_reach)) {
        rc = TC_PREP_ABSENT_GUARD; goto fail;
      }
    }
  }
  if (check_count) {
    for (int i = 0; i < r->ncount; i++) {
      Term pt, psp; uint8_t pmk; unpack_pat(r->count[i].t, &pt, &psp, &pmk);
      if (!count_ok_at(pt, r->count[i].space, psp, r->count[i].n, S, k->n, check_reach ? reach_set : NULL, nreach, check_reach)) {
        rc = TC_PREP_COUNT_GUARD; goto fail;
      }
    }
  }
  if (check_birth && r->birth_law) {
    for (int m = 0; m < nmake; m++) if (m_mark[m]) {
      if (tc_space_born(m_sp[m])) { rc = TC_PREP_BIRTH_GUARD; goto fail; }
      for (int m2 = m + 1; m2 < nmake; m2++) if (m_mark[m2] && m_sp[m] == m_sp[m2]) { rc = TC_PREP_BIRTH_GUARD; goto fail; }
    }
    for (int i = 0; i < r->ntake; i++) {
      Term sp = norm(tc_occ_space(take[i]));
      bool loc = tc_space_born(sp);
      for (int m = 0; !loc && m < nmake; m++) if (m_mark[m] && m_sp[m] == sp) loc = true;
      if (!loc) { rc = TC_PREP_BIRTH_GUARD; goto fail; }
    }
    for (int i = 0; i < k->nkeep; i++) {
      Term sp = norm(tc_occ_space(keep[i]));
      bool loc = tc_space_born(sp);
      for (int m = 0; !loc && m < nmake; m++) if (m_mark[m] && m_sp[m] == sp) loc = true;
      if (!loc) { rc = TC_PREP_BIRTH_GUARD; goto fail; }
    }
    for (int j = 0; j < nmake; j++) {
      Term sp = m_sp[j];
      bool loc = tc_space_born(sp);
      for (int m = 0; !loc && m < nmake; m++) if (m_mark[m] && m_sp[m] == sp) loc = true;
      if (!loc) { rc = TC_PREP_BIRTH_GUARD; goto fail; }
    }
  }
  /* The rule's sealed guards and where it may publish: part of the rule in every variant. */
  if (k->fns && !run_guards(k, r, S)) { rc = TC_PREP_FN_GUARD; goto fail; }
  if (sealed && k->dynmake && !publish_ok(k, step->rule, nmake, m_has_sp, m_mark, m_sp, m_raw_s)) {
    rc = TC_PREP_PUBLISH_GUARD; goto fail;
  }

  if (!do_commit) {
    undo(mark); nne = nemark; next_name = nmark; nmeta = mmark;
    return TC_PREP_OK;
  }

  nsteps++;
  Occ o = 0;
  uint32_t nw0 = nw;                                      /* occurrences from nw0 on are this firing's own */
  if (step->dest && nmake == 1 && !step->take && step->nseeds <= 0 &&
      !m_has_sp[0] && !m_mark[0]) {
    uint64_t status = tc_flat_fire_ordinary(step->rule, keep, step->inst, step->dest, &o);
    if (status == ORDINARY_FLAT_FIRED && !o) goto fail;   /* admitted above: a declining leaf is not a refusal */
    if (status != ORDINARY_FLAT_FIRED) o = 0;
    /* `dest` means what it means for tc_commit_prepared and tc_flat_fire: a flat rule's fact is written
       at dest (in place where that is allowed, else appended), also when the leaf declines */
    if (!o && k->flat && N[m_out[0]].kind == K_APP && !has_meta(m_out[0]) && !at_node_any(m_out[0])) {
      Term b[TC_ARGS]; int ar = N[m_out[0]].arity;
      for (int j = 0; j < ar; j++) b[j] = argv(m_out[0])[j];
      if (!(o = flat_store(step->dest, (N[m_out[0]].head << 9) | ((uint32_t)m_raw_s[0] << 1) | 1u, ar, b))) goto fail;
    }
  }
  if (!o)
    o = (m_has_sp[0] || m_mark[0]) ? post_at_internal(m_sp[0], m_out[0], m_mark[0])
                                  : post(m_raw_s[0], m_out[0]);
  if (!o) goto fail;
  memset(last_extra_occ, 0, sizeof last_extra_occ);
  for (int m = 1; m < nmake; m++) {
    Occ oe = (m_has_sp[m] || m_mark[m]) ? post_at_internal(m_sp[m], m_out[m], m_mark[m]) : post(m_raw_s[m], m_out[m]);
    if (!oe) {                                            /* undo only what this firing appended */
      if (o >= nw0) { Wa[o] = 0; Wtag[o] = 0; }
      for (int j = 1; j < m; j++) if (last_extra_occ[j - 1] >= nw0) { Wa[last_extra_occ[j - 1]] = 0; Wtag[last_extra_occ[j - 1]] = 0; }
      goto fail;
    }
    last_extra_occ[m - 1] = oe;
  }
  for (int i = 0; i < r->ntake; i++) { Wa[take[i]] = 0; Wtag[take[i]] = 0; }
  if (out_occ) *out_occ = o;
  return TC_PREP_OK;

fail:
  undo(mark); nne = nemark; next_name = nmark; nmeta = mmark;
  return rc;
}

bool tc_cursor_next_raw(const TcCandidateCursor *cursor, TcPreparedStep *out) {
  return cursor && cursor->next && out && cursor->next(cursor->ctx, out);
}

#ifndef TC_USE_CESTA_EXPORT
bool tc_commit_prepared(const TcPreparedStep *step, TcAdmissionReceipt *receipt) {
  if (receipt) memset(receipt, 0, sizeof(*receipt));
  if (!step || step->rule < 0 || step->rule >= nr) return false;
  Occ out = 0;
  if (step->dest && (tc_rule_fibre(step->rule) & FIBRE_FLAT) && !step->take && step->nseeds <= 0) {
    out = tc_flat_fire(step->rule, step->keep, step->inst, step->dest);
  } else if (step->nseeds > 0) {
    out = tc_fire_reach(step->rule, step->take, step->keep, step->inst, step->seeds, step->nseeds);
  } else {
    out = tc_fire(step->rule, step->take, step->keep, step->inst);
  }
  if (!out) return false;
  if (receipt) {
    receipt->admitted = true;
    receipt->rule = step->rule;
    receipt->out = out;
    receipt->out_term = tc_term(out);
    for (int i = 0; i < 4; i++) {
      if (last_extra_occ[i]) {
        receipt->extra[receipt->nextra++] = last_extra_occ[i];
      }
    }
  }
  return true;
}

int tc_step_cursor(TcCandidateCursor *cursor, TcAdmissionReceipt *receipt) {
  if (receipt) memset(receipt, 0, sizeof(*receipt));
  if (!cursor || !cursor->next) return -1;
  TcPreparedStep cand;
  while (cursor->next(cursor->ctx, &cand)) {
    if (tc_commit_prepared(&cand, receipt)) return 1;
  }
  return 0;
}
#endif

#include "tisa/tc_theory_inspect.h"

int tc_inspect_sort_count(void) {
  return nsort;
}

uint8_t tc_inspect_sort_flags(int sort_id) {
  return (sort_id >= 0 && sort_id < nsort) ? sorts[sort_id] : 0;
}

bool tc_inspect_space_protected(uint8_t space) {
  return protect[space];
}

int tc_inspect_con_count(void) {
  return ncon;
}

bool tc_inspect_con(int con_id, TcInspectCon *out) {
  if (!out || con_id < 0 || con_id >= ncon) return false;
  memset(out, 0, sizeof(*out));
  const Con *c = &C[con_id];
  out->con_id  = con_id;
  out->sort    = c->sort;
  out->arity   = c->arity;
  out->ndum    = c->ndum;
  out->isdef   = c->isdef;
  out->abound  = c->abound;
  out->retdeps = c->retdeps;
  for (int i = 0; i < c->arity && i < TC_ARGS; i++) {
    out->asort[i] = c->asort[i];
  }
  return true;
}

bool tc_inspect_rule(int rule_id, TcInspectRule *out, TcInspectFlat *out_flat) {
  if (!out || rule_id < 0 || rule_id >= nr) return false;
  memset(out, 0, sizeof(*out));
  if (out_flat) memset(out_flat, 0, sizeof(*out_flat));
  RuleK *k = &R[rule_id];
  if (!k->fprepped) prep_flat(k);
  const Rule *r = RULE(k);
  out->rule_id   = rule_id;
  out->nvars     = k->n;
  out->nkeep     = k->nkeep;
  out->mspace    = k->mspace;
  out->fibre     = k->fibre;
  out->pure      = k->pure;
  out->flat      = k->flat;
  out->mflat     = k->mflat;
  out->implied   = k->implied;
  out->mimplied  = k->mimplied;
  out->bounds    = k->bounds;
  memset(&out->decl_rule, 0, sizeof(out->decl_rule));
  /* Copy the header + stored nkeep premises from RP + k->ro */
  size_t r_bytes = offsetof(Rule, keep) + (size_t)r->nkeep * sizeof(Pat);
  memcpy(&out->decl_rule, r, r_bytes);
  for (int h = 0; h < k->n && h < TC_VARS; h++) {
    Hole hl = HOLE(k, h);
    out->holes[h].sort  = hl.sort;
    out->holes[h].bound = hl.bound;
    out->holes[h].avoid = hl.avoid;
  }
  if (k->flat && out_flat && k->fl < nfl) {
    const Flat *fl = &FL[k->fl];
    out_flat->fl_index = k->fl;
    out_flat->ordinary = fl->ordinary;
    for (int i = 0; i < k->nkeep && i < TC_HYPS; i++) {
      out_flat->ktag[i] = fl->ktag[i];
    }
    out_flat->mhead  = fl->mhead;
    out_flat->msort  = fl->msort;
    out_flat->mar    = fl->mar;
    out_flat->nguard = fl->nguard;
    out_flat->nconst = fl->nconst;
    for (int g = 0; g < fl->nguard && g < 32; g++) {
      out_flat->guard[g].i  = fl->guard[g].i;
      out_flat->guard[g].j  = fl->guard[g].j;
      out_flat->guard[g].i0 = fl->guard[g].i0;
      out_flat->guard[g].j0 = fl->guard[g].j0;
      out_flat->packed_guard[g] = fl->packed_guard[g];
    }
    for (int j = 0; j < fl->mar && j < TC_ARGS; j++) {
      out_flat->mi[j] = fl->mi[j];
      out_flat->mj[j] = fl->mj[j];
      out_flat->packed_make[j] = fl->packed_make[j];
    }
    for (int c = 0; c < fl->nconst && c < 32; c++) {
      out_flat->mc[c] = fl->mc[c];
    }
  }
  return true;
}
