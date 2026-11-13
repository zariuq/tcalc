/* Random differential: the tcalc kernel against the naive reference in ref.h.

   usage: diff_main FIRST_SEED COUNT [options]
     --future P      probability that a caller-supplied hole value mentions a name not yet minted
     --no-flatfire   never call tc_flat_fire
     --flat-only-flat  call tc_flat_fire only on rules the kernel tags FIBRE_FLAT
     --no-dry        never use the dry-run entry point
     --verbose       print every shrunk failure in full
     --replay SEED   run one scenario and print it step by step
   Each scenario: a random theory variant, 2..6 random rules, random initial facts in spaces 0..3,
   protection and sealing, then up to 40 steps. After every step the verdict, the store (as a
   multiset of space:term, or as a set when no rule takes or counts and the store is sealed), and the
   name counter are compared. A disagreement ends the scenario; it is shrunk and classified. */
#include "ref.h"
#include "tcalc.h"

/* ---- randomness ---- */
static uint64_t rng_s;
static uint64_t rnd(void) { rng_s ^= rng_s >> 12; rng_s ^= rng_s << 25; rng_s ^= rng_s >> 27; return rng_s * 0x2545F4914F6CDD1Dull; }
static int rint_(int n) { return n <= 0 ? 0 : (int)(rnd() % (uint64_t)n); }
static bool chance(double p) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0) < p; }

/* ---- the theory, built in both worlds ---- */
enum { S_D = 1, S_N = 2, S_T = 3 };
static const RCon THEORY[12] = {
  { S_D, 0, { 0 } }, { S_D, 0, { 0 } }, { S_D, 1, { S_D } }, { S_D, 2, { S_D, S_D } }, { S_D, 1, { S_N } },
  { S_T, 1, { S_D } }, { S_T, 2, { S_D, S_D } }, { S_T, 1, { S_D } }, { S_T, 2, { S_N, S_D } }, { S_T, 0, { 0 } },
  { S_T, 4, { S_D, S_D, S_D, S_D } }, { S_T, 5, { S_D, S_D, S_D, S_D, S_D } },
};
static int kcon[32];
static bool theory_init(bool wide) {
  if (!tc_init(1u << 12, 1u << 8)) return false;
  int d = tc_sort(0), n = tc_sort(0), t = tc_sort(SORT_PROVABLE);
  if (d != S_D || n != S_N || t != S_T) return false;
  r_ncon = wide ? 12 : 11;
  for (int i = 0; i < r_ncon; i++) {
    r_con[i] = THEORY[i];
    Binder b[R_MAXAR];
    for (int j = 0; j < THEORY[i].arity; j++) b[j] = (Binder){ THEORY[i].asort[j], 0, 0 };
    kcon[i] = tc_con(THEORY[i].sort, 0, THEORY[i].arity, b);
    if (kcon[i] != i) return false;
  }
  return true;
}
static Term k_of(const RT *t) {
  if (t->kind == RK_NAME) return tc_name(t->sort, t->id);
  if (t->kind == RK_HOLE) return tc_v(t->head);
  Term a[R_MAXAR];
  for (int i = 0; i < t->n; i++) if (!(a[i] = k_of(t->a[i]))) return 0;
  return tc_app(kcon[t->head], t->n ? a : NULL);
}
static int k_show(Term t, char *buf, int cap) {
  uint8_t kind; uint32_t head; int ar; const Term *args;
  tc_node(t, &kind, &head, &ar, &args);
  if (kind == K_NAME) return snprintf(buf, (size_t)cap, "n%d#%llu", tc_sort_of(t), (unsigned long long)tc_name_id(t));
  if (kind != K_APP) return snprintf(buf, (size_t)cap, "<kind%d:%u>", kind, head);
  int n = snprintf(buf, (size_t)cap, "c%u", head);
  if (ar) {
    n += snprintf(buf + n, (size_t)(cap - n), "(");
    for (int i = 0; i < ar && n < cap - 8; i++) { if (i) buf[n++] = ','; n += k_show(args[i], buf + n, cap - n); }
    n += snprintf(buf + n, (size_t)(cap - n), ")");
  }
  return n;
}

/* ---- generators ---- */
static const RT *gen_ground(int sort, int depth, uint64_t nnames) {
  if (sort == S_N) return r_name(S_N, (uint64_t)rint_((int)nnames));
  const RT *a[R_MAXAR];
  if (sort == S_D) {
    int c = depth <= 0 ? rint_(2) : rint_(5);
    for (int i = 0; i < THEORY[c].arity; i++) a[i] = gen_ground(THEORY[c].asort[i], depth - 1, nnames);
    return r_app(c, a);
  }
  int c = 5 + rint_(r_ncon - 5);
  for (int i = 0; i < THEORY[c].arity; i++) a[i] = gen_ground(THEORY[c].asort[i], depth - 1, nnames);
  return r_app(c, a);
}
static int pick_hole(const RRule *r, int sort, uint32_t allowed) {
  int c[R_MAXH], n = 0;
  for (int h = 0; h < r->nholes; h++) if (r->hsort[h] == sort && (allowed >> h & 1)) c[n++] = h;
  return n ? c[rint_(n)] : -1;
}
static const RT *gen_pat(int sort, int depth, const RRule *r, uint32_t allowed, uint64_t nnames) {
  int h = pick_hole(r, sort, allowed);
  if (h >= 0 && chance(depth <= 0 ? 0.75 : 0.4)) return r_hole(h, sort);
  if (sort == S_N) return r_name(S_N, (uint64_t)rint_((int)nnames));
  const RT *a[R_MAXAR];
  int c = sort == S_D ? (depth <= 0 ? rint_(2) : rint_(5)) : 5 + rint_(r_ncon - 5);
  for (int i = 0; i < THEORY[c].arity; i++) a[i] = gen_pat(THEORY[c].asort[i], depth - 1, r, allowed, nnames);
  return r_app(c, a);
}
static const RT *gen_fact_pat(const RRule *r, uint32_t allowed, int depth, uint64_t nnames) {
  int h = pick_hole(r, S_T, allowed);
  if (h >= 0 && chance(0.08)) return r_hole(h, S_T);
  const RT *a[R_MAXAR];
  int c = 5 + rint_(r_ncon - 5);
  for (int i = 0; i < THEORY[c].arity; i++) a[i] = gen_pat(THEORY[c].asort[i], depth - 1, r, allowed, nnames);
  return r_app(c, a);
}
static uint32_t holes_of(const RT *t) {
  if (t->kind == RK_HOLE) return 1u << t->head;
  uint32_t m = 0;
  for (int i = 0; i < t->n; i++) m |= holes_of(t->a[i]);
  return m;
}
static void gen_rule(RRule *r, bool allow_take, uint64_t nnames) {
  memset(r, 0, sizeof *r);
  r->nholes = 1 + rint_(5);
  for (int h = 0; h < r->nholes; h++) { int x = rint_(100); r->hsort[h] = x < 60 ? S_D : x < 85 ? S_N : S_T; }
  r->fresh = -1;
  int home = rint_(4);
#define SPACE() (uint8_t)(chance(0.7) ? home : rint_(4))
  uint32_t all = (1u << r->nholes) - 1;
  if (chance(0.35)) {                                  /* shallow keep-only rules: the flat fibre */
    r->nkeep = 1 + rint_(3);
    uint32_t seen = 0;
    for (int i = 0; i < r->nkeep; i++) { r->keep[i] = (RPat){ gen_fact_pat(r, all, 1, nnames), SPACE() }; seen |= holes_of(r->keep[i].t); }
    r->nmake = 1;
    r->make[0] = (RPat){ gen_fact_pat(r, chance(0.9) ? seen : all, 1, nnames), SPACE() };
    return;
  }
  if (chance(0.25)) {
    int c[R_MAXH], n = 0;
    for (int h = 0; h < r->nholes; h++) if (r->hsort[h] != S_T) c[n++] = h;
    if (n) r->fresh = c[rint_(n)];
  }
  uint32_t nf = r->fresh >= 0 ? all & ~(1u << r->fresh) : all;
  if (allow_take) { int x = rint_(10); r->ntake = x < 4 ? 0 : x < 8 ? 1 : 2; }
  r->nkeep = rint_(3);
  r->nabsent = chance(0.3);
  r->ncount = allow_take && chance(0.25);
  r->ntell = chance(0.2);
  r->nneq = chance(0.2);
  r->nmake = 1 + (chance(0.3) ? 1 + rint_(2) : 0);
  uint32_t seen = 0;
  for (int i = 0; i < r->ntake; i++) { r->take[i] = (RPat){ gen_fact_pat(r, nf, 1 + rint_(2), nnames), SPACE() }; seen |= holes_of(r->take[i].t); }
  for (int i = 0; i < r->nkeep; i++) { r->keep[i] = (RPat){ gen_fact_pat(r, nf, 1 + rint_(2), nnames), SPACE() }; seen |= holes_of(r->keep[i].t); }
  uint32_t guard_holes = chance(0.8) && seen ? seen : nf;      /* mostly holes the premises bind */
  for (int i = 0; i < r->ntell; i++) {
    int s = chance(0.7) ? S_D : S_N;
    r->tell[i][0] = gen_pat(s, 1, r, guard_holes, nnames); r->tell[i][1] = gen_pat(s, 1, r, guard_holes, nnames);
  }
  for (int i = 0; i < r->nneq; i++) {
    int s = chance(0.7) ? S_D : S_N;
    r->neq[i][0] = gen_pat(s, 1, r, seen ? seen : nf, nnames); r->neq[i][1] = gen_pat(s, 1, r, seen ? seen : nf, nnames);
  }
  for (int i = 0; i < r->nabsent; i++) r->absent[i] = (RPat){ gen_fact_pat(r, nf, 1 + rint_(2), nnames), SPACE() };
  for (int i = 0; i < r->ncount; i++) r->count[i] = (RCount){ gen_fact_pat(r, nf, 1 + rint_(2), nnames), SPACE(), (uint32_t)rint_(3) };
  for (int m = 0; m < r->nmake; m++) r->make[m] = (RPat){ gen_fact_pat(r, chance(0.85) && (seen || r->fresh >= 0) ? (seen | (all & ~nf)) : all, 1 + rint_(2), nnames), SPACE() };
#undef SPACE
}

/* ---- scenarios ---- */
enum { V_FIRE, V_COMMIT, V_EVAL, V_FLAT, V_DRY, NVARIANT };
static const char *VNAME[NVARIANT] = { "tc_fire", "tc_commit_prepared", "tc_eval_prepared_ex", "tc_flat_fire", "dry-run+tc_fire" };
enum { ST_FIRE, ST_POST, ST_FRESH };
#define KEY_BOGUS (-9)
typedef struct {
  int kind, rule, variant;
  int tk_step[4], tk_k[4], kp_step[8], kp_k[8];
  bool has_in, take_nonnull, in_zero;
  const RT *in[R_MAXH];
  const RT *post_t; int post_space;
} DStep;
typedef struct {
  uint64_t seed; bool wide, sealed, persistent, prot[4];
  int premint, nrules, nfacts, nsteps;
  RRule rules[8]; RPat facts[24]; DStep steps[64];
} Scenario;
enum { F_NONE, F_VERDICT, F_STORE, F_NAME, F_SETUP, F_POST, F_RECEIPT, F_DRY };
static const char *FNAME[] = { "none", "verdict", "store", "name-counter", "setup", "post", "receipt", "dry-run-changed-state" };
typedef struct { int kind, step, variant, rule; bool kacc, racc; char note[256]; } Fail;

static double opt_future = 0.0; static bool opt_noflat, opt_flat_only_flat, opt_nodry, opt_verbose, opt_trace, opt_no_open_tells, opt_fine;
static RStore st; static int krule[8]; static Occ maxocc; static bool set_mode;
static unsigned long n_steps, n_fire, n_acc, n_ref, n_out, n_receipt_soft, n_variant[NVARIANT], n_variant_acc[NVARIANT];
static unsigned long cov_acc[12], cov_ref[12];
static const char *COV[12] = { "take", "keep", "tell", "neq", "absent", "count", "fresh", "extra-make", "flat-rule", "sealed", "set-store", "hole-values" };

static int find_key(int step, int k) {
  if (step == KEY_BOGUS) return -1;
  for (int i = 0; i < st.n; i++) if (st.f[i].key_step == step && st.f[i].key_k == k) return i;
  return -1;
}
static int cmp_str(const void *a, const void *b) { return strcmp((const char *)a, (const char *)b); }
#define SLEN 192
static char ks[1024][SLEN], rs[1024][SLEN];
static bool stores_agree(char *note, int cap) {
  int nk = 0, nrf = 0;
  Term sp[4];
  for (int s = 0; s < 4; s++) sp[s] = tc_space_term((uint8_t)s);
  for (Occ o = 1; o <= maxocc + 64 && nk < 1024; o++) if (tc_alive(o)) {
    Term osp = tc_occ_space(o); int s = -1;
    for (int j = 0; j < 4; j++) if (osp == sp[j]) s = j;
    int n = snprintf(ks[nk], SLEN, "s%d%s:", s, tc_occ_marker(o) ? "!" : "");
    k_show(tc_term(o), ks[nk] + n, SLEN - n); nk++;
  }
  for (int i = 0; i < st.n && nrf < 1024; i++) if (st.f[i].alive) {
    int n = snprintf(rs[nrf], SLEN, "s%d:", st.f[i].space);
    r_show(st.f[i].t, rs[nrf] + n, SLEN - n); nrf++;
  }
  qsort(ks, (size_t)nk, SLEN, cmp_str); qsort(rs, (size_t)nrf, SLEN, cmp_str);
  if (set_mode) {
    int u = 0; for (int i = 0; i < nk; i++) if (!u || strcmp(ks[u - 1], ks[i])) { if (u != i) memcpy(ks[u], ks[i], SLEN); u++; } nk = u;
    u = 0; for (int i = 0; i < nrf; i++) if (!u || strcmp(rs[u - 1], rs[i])) { if (u != i) memcpy(rs[u], rs[i], SLEN); u++; } nrf = u;
  }
  int i = 0, j = 0;
  while (i < nk && j < nrf) {
    int c = strcmp(ks[i], rs[j]);
    if (c == 0) { i++; j++; continue; }
    if (c < 0) { snprintf(note, (size_t)cap, "kernel has %s, reference does not (kernel %d facts, reference %d)", ks[i], nk, nrf); return false; }
    snprintf(note, (size_t)cap, "reference has %s, kernel does not (kernel %d facts, reference %d)", rs[j], nk, nrf); return false;
  }
  if (i < nk) { snprintf(note, (size_t)cap, "kernel has %s, reference does not (kernel %d facts, reference %d)", ks[i], nk, nrf); return false; }
  if (j < nrf) { snprintf(note, (size_t)cap, "reference has %s, kernel does not (kernel %d facts, reference %d)", rs[j], nk, nrf); return false; }
  return true;
}
static void note_occ(Occ o) { if (o > maxocc && o < (1u << 24)) maxocc = o; }

static bool install_rule(const RRule *r, int *rid) {
  Binder b[R_MAXH];
  for (int h = 0; h < r->nholes; h++) b[h] = (Binder){ r->hsort[h], 0, 0 };
  if (!tc_ctx(r->nholes, b)) return false;
  Rule k; memset(&k, 0, sizeof k);
  k.ntake = (uint8_t)r->ntake; k.nkeep = (uint8_t)r->nkeep; k.nabsent = (uint8_t)r->nabsent; k.ncount = (uint8_t)r->ncount;
  k.ntell = (uint8_t)r->ntell; k.nneq = (uint8_t)r->nneq; k.nmake_extra = (uint8_t)(r->nmake - 1); k.fresh = (int8_t)r->fresh;
  for (int i = 0; i < r->ntake; i++) k.take[i] = (Pat){ k_of(r->take[i].t), r->take[i].space };
  for (int i = 0; i < r->nkeep; i++) k.keep[i] = (Pat){ k_of(r->keep[i].t), r->keep[i].space };
  for (int i = 0; i < r->nabsent; i++) k.absent[i] = (Pat){ k_of(r->absent[i].t), r->absent[i].space };
  for (int i = 0; i < r->ncount; i++) k.count[i] = (Count){ k_of(r->count[i].t), r->count[i].space, r->count[i].n };
  for (int i = 0; i < r->ntell; i++) { k.tell[i][0] = k_of(r->tell[i][0]); k.tell[i][1] = k_of(r->tell[i][1]); }
  for (int i = 0; i < r->nneq; i++) { k.neq[i][0] = k_of(r->neq[i][0]); k.neq[i][1] = k_of(r->neq[i][1]); }
  k.make = (Pat){ k_of(r->make[0].t), r->make[0].space };
  for (int m = 1; m < r->nmake; m++) k.make_extra[m - 1] = (Pat){ k_of(r->make[m].t), r->make[m].space };
  uint64_t bound = r->fresh >= 0 ? 1ull << r->fresh : 0, made = 0;   /* the caller supplies the other made holes */
  for (int i = 0; i < r->ntake; i++) bound |= holes_of(r->take[i].t);
  for (int i = 0; i < r->nkeep; i++) bound |= holes_of(r->keep[i].t);
  for (int m = 0; m < r->nmake; m++) made |= holes_of(r->make[m].t);
  k.inputs = made & ~bound;
  *rid = tc_rule(&k);
  return *rid >= 0;
}

static void gen_fire_step(Scenario *sc, DStep *s) {
  memset(s, 0, sizeof *s);
  s->kind = ST_FIRE; s->rule = rint_(sc->nrules);
  const RRule *r = &sc->rules[s->rule];
  const RT *B[R_MAXH]; bool guided = false;
  int pick_t[4], pick_k[8];
  if (chance(0.75)) for (int attempt = 0; attempt < 30 && !guided; attempt++) {
    memset(B, 0, sizeof B);
    bool ok = true;
    for (int i = 0; ok && i < r->ntake + r->nkeep; i++) {
      const RPat *p = i < r->ntake ? &r->take[i] : &r->keep[i - r->ntake];
      int cand[R_MAXFACTS], n = 0;
      for (int f = 0; f < st.n; f++) if (st.f[f].alive && st.f[f].space == p->space) {
        bool used = false;
        for (int j = 0; j < (i < r->ntake ? i : r->ntake); j++) used |= pick_t[j] == f;
        if (used) continue;
        const RT *B2[R_MAXH]; memcpy(B2, B, sizeof B2);
        if (r_unify(p->t, st.f[f].t, B2)) cand[n++] = f;
      }
      if (!n) { ok = false; break; }
      int f = cand[rint_(n)];
      r_unify(p->t, st.f[f].t, B);
      if (i < r->ntake) pick_t[i] = f; else pick_k[i - r->ntake] = f;
    }
    guided = ok;
  }
  for (int i = 0; i < r->ntake + r->nkeep; i++) {
    int *ks_ = i < r->ntake ? &s->tk_step[i] : &s->kp_step[i - r->ntake], *kk = i < r->ntake ? &s->tk_k[i] : &s->kp_k[i - r->ntake];
    int f = -1;
    if (guided && chance(0.97)) f = i < r->ntake ? pick_t[i] : pick_k[i - r->ntake];
    else if (st.n && chance(0.85)) f = rint_(st.n);            /* any fact ever made: live, dead, any space */
    if (f >= 0) { *ks_ = st.f[f].key_step; *kk = st.f[f].key_k; }
    else { *ks_ = KEY_BOGUS; *kk = chance(0.5) ? 0 : 9000 + rint_(100000); }
  }
  if (!guided) memset(B, 0, sizeof B);
  if (chance(0.55)) {
    s->has_in = true;
    for (int h = 0; h < r->nholes; h++) {
      const RT *v = B[h] && r_ground(B[h], B) ? r_subst(B[h], B) : NULL;
      double give = v ? 0.4 : 0.8;
      if (h == r->fresh) give = 0.04;
      if (!chance(give)) continue;
      if (v && chance(0.85)) s->in[h] = v;
      else {
        int sort = chance(0.93) ? r->hsort[h] : 1 + rint_(3);
        s->in[h] = gen_ground(sort, 1 + rint_(2), st.next_name);
        if (opt_future > 0 && chance(opt_future)) s->in[h] = r_name(r->hsort[h] == S_T ? S_N : r->hsort[h], st.next_name + (uint64_t)rint_(2));
      }
    }
  } else s->in_zero = chance(0.25);
  s->take_nonnull = chance(0.3);
  for (;;) {
    s->variant = rint_(NVARIANT);
    if (s->variant == V_FLAT && (r->ntake > 0 || opt_noflat)) continue;
    if (s->variant == V_DRY && opt_nodry) continue;
    break;
  }
}

static bool exec_step(Scenario *sc, int i, Fail *fail) {
  DStep *s = &sc->steps[i];
  n_steps++;
  if (s->kind == ST_FRESH) {
    uint64_t k = tc_fresh_name();
    if (k != st.next_name) { *fail = (Fail){ F_NAME, i, 0, -1, 0, 0, "" }; snprintf(fail->note, sizeof fail->note, "tc_fresh_name gave %llu, reference %llu", (unsigned long long)k, (unsigned long long)st.next_name); return false; }
    st.next_name++;
    return true;
  }
  if (s->kind == ST_POST) {
    Term t = k_of(s->post_t);
    Occ o = t ? tc_post((uint8_t)s->post_space, t) : 0;
    bool expect = !(sc->sealed && sc->prot[s->post_space]) && r_max_name(s->post_t) <= st.next_name;
    if ((o != 0) != expect) { *fail = (Fail){ F_POST, i, 0, -1, o != 0, expect, "" }; snprintf(fail->note, sizeof fail->note, "tc_post into space %d (protected %d, sealed %d)", s->post_space, sc->prot[s->post_space], sc->sealed); return false; }
    if (o) { note_occ(o); st.f[st.n++] = (RFact){ s->post_t, (uint8_t)s->post_space, true, i, 0, o }; }
    if (!stores_agree(fail->note, sizeof fail->note)) { fail->kind = F_STORE; fail->step = i; fail->variant = 0; fail->rule = -1; return false; }
    return true;
  }
  const RRule *r = &sc->rules[s->rule];
  int ti[4], ki[8]; Occ tk[4] = { 0 }, kk[8] = { 0 };
  for (int j = 0; j < r->ntake; j++) { ti[j] = find_key(s->tk_step[j], s->tk_k[j]); tk[j] = ti[j] >= 0 ? st.f[ti[j]].kocc : s->tk_step[j] == KEY_BOGUS ? (Occ)s->tk_k[j] : 0x00FFFFFFu; }
  for (int j = 0; j < r->nkeep; j++) { ki[j] = find_key(s->kp_step[j], s->kp_k[j]); kk[j] = ki[j] >= 0 ? st.f[ki[j]].kocc : s->kp_step[j] == KEY_BOGUS ? (Occ)s->kp_k[j] : 0x00FFFFFFu; }
  RVerdict rv = r_fire(&st, r, ti, ki, s->has_in ? s->in : NULL, false, i, NULL);
  if (rv == RV_OUT) { n_out++; return true; }
  n_fire++;
  Term kin[R_MAXH] = { 0 };
  if (s->has_in) for (int h = 0; h < r->nholes; h++) if (s->in[h] && !(kin[h] = k_of(s->in[h]))) { *fail = (Fail){ F_SETUP, i, s->variant, s->rule, 0, 0, "could not build a hole value" }; return false; }
  const Occ *ptake = r->ntake || s->take_nonnull ? tk : NULL;
  const Occ *pkeep = r->nkeep ? kk : NULL;
  const Term *pin = s->has_in || s->in_zero ? kin : NULL;
  int rid = krule[s->rule];
  int variant = s->variant;
  /* --flat-only-flat: tc_flat_fire only where it runs its own flat code (flat rule, premises, no hole values) */
  if (variant == V_FLAT && opt_flat_only_flat && !((tc_rule_fibre(rid) & FIBRE_FLAT) && !pin && pkeep)) variant = V_FIRE;
  if (opt_no_open_tells && (r->ntell || r->nneq)) {       /* skip candidates whose tell or disequation meets an unbound hole */
    const RT *B0[R_MAXH]; bool open = false, matched = true;
    for (int h = 0; h < r->nholes; h++) B0[h] = s->has_in ? s->in[h] : NULL;
    for (int j = 0; matched && j < r->ntake; j++) matched = ti[j] >= 0 && r_unify(r->take[j].t, st.f[ti[j]].t, B0);
    for (int j = 0; matched && j < r->nkeep; j++) matched = ki[j] >= 0 && r_unify(r->keep[j].t, st.f[ki[j]].t, B0);
    for (int j = 0; j < r->ntell; j++) open |= !r_ground(r->tell[j][0], B0) || !r_ground(r->tell[j][1], B0);
    for (int j = 0; j < r->nneq; j++) open |= !r_ground(r->neq[j][0], B0) || !r_ground(r->neq[j][1], B0);
    if (open) { n_out++; n_fire--; return true; }
  }
  n_variant[variant]++;
  uint64_t name_before = tc_next_name();
  Occ o = 0; bool kacc = false; TcAdmissionReceipt rc; memset(&rc, 0, sizeof rc);
  TcPreparedStep ps = { .rule = rid, .take = ptake, .keep = pkeep, .inst = pin, .dest = 0, .nseeds = 0, .seeds = NULL };
  if (variant == V_DRY) {
    Term mt[5], ms[5]; uint8_t mm[5], nm = 0; Occ oo = 0;
    int v = tc_eval_prepared_ex(&ps, true, true, true, false, false, mt, ms, mm, &nm, &oo);
    if ((v == TC_PREP_OK) != (rv == RV_ACCEPT)) { *fail = (Fail){ F_VERDICT, i, variant, s->rule, v == TC_PREP_OK, rv == RV_ACCEPT, "dry run verdict" }; return false; }
    char note[256];
    if (!stores_agree(note, sizeof note) || tc_next_name() != name_before) { *fail = (Fail){ F_DRY, i, variant, s->rule, v == TC_PREP_OK, rv == RV_ACCEPT, "" }; snprintf(fail->note, sizeof fail->note, "%s", note); return false; }
    o = tc_fire(rid, ptake, pkeep, pin); kacc = o != 0;
  } else if (variant == V_FIRE) { o = tc_fire(rid, ptake, pkeep, pin); kacc = o != 0; }
  else if (variant == V_COMMIT) { kacc = tc_commit_prepared(&ps, &rc); o = rc.out; }
  else if (variant == V_EVAL) {
    Term mt[5], ms[5]; uint8_t mm[5], nm = 0;
    int v = tc_eval_prepared_ex(&ps, true, true, true, false, true, mt, ms, mm, &nm, &o);
    kacc = v == TC_PREP_OK && o;
  } else { o = tc_flat_fire(rid, pkeep, pin, 0); kacc = o != 0; }
  if (kacc != (rv == RV_ACCEPT)) { *fail = (Fail){ F_VERDICT, i, variant, s->rule, kacc, rv == RV_ACCEPT, "" }; return false; }
  {
    unsigned long *c = kacc ? cov_acc : cov_ref;
    c[0] += r->ntake > 0; c[1] += r->nkeep > 0; c[2] += r->ntell > 0; c[3] += r->nneq > 0; c[4] += r->nabsent > 0;
    c[5] += r->ncount > 0; c[6] += r->fresh >= 0; c[7] += r->nmake > 1; c[8] += (tc_rule_fibre(rid) & FIBRE_FLAT) != 0;
    c[9] += sc->sealed; c[10] += set_mode; c[11] += s->has_in;
  }
  if (kacc) {
    n_acc++; n_variant_acc[variant]++;
    int made[5];
    r_fire(&st, r, ti, ki, s->has_in ? s->in : NULL, true, i, made);
    st.f[made[0]].kocc = o; note_occ(o);
    for (int m = 1; m < r->nmake; m++) { Occ e = tc_last_extra(m - 1); st.f[made[m]].kocc = e; note_occ(e); }
    if (variant == V_COMMIT && rc.nextra != r->nmake - 1) n_receipt_soft++;
  } else n_ref++;
  if (!stores_agree(fail->note, sizeof fail->note)) { fail->kind = F_STORE; fail->step = i; fail->variant = variant; fail->rule = s->rule; fail->kacc = kacc; fail->racc = rv == RV_ACCEPT; return false; }
  if (tc_next_name() != st.next_name) { *fail = (Fail){ F_NAME, i, variant, s->rule, kacc, rv == RV_ACCEPT, "" }; snprintf(fail->note, sizeof fail->note, "kernel next name %llu, reference %llu", (unsigned long long)tc_next_name(), (unsigned long long)st.next_name); return false; }
  return true;
}

static void show_pat(const char *label, const RT *t, int space) { char b[256]; r_show(t, b, sizeof b); printf(" %s %s@%d", label, b, space); }
static void show_rule(int idx, const RRule *r) {
  printf("    rule %d: holes", idx);
  for (int h = 0; h < r->nholes; h++) printf(" ?%d:%s", h, r->hsort[h] == S_D ? "D" : r->hsort[h] == S_N ? "N" : "T");
  if (r->fresh >= 0) printf(" fresh ?%d", r->fresh);
  printf(" |");
  for (int i = 0; i < r->ntake; i++) show_pat("take", r->take[i].t, r->take[i].space);
  for (int i = 0; i < r->nkeep; i++) show_pat("keep", r->keep[i].t, r->keep[i].space);
  for (int i = 0; i < r->ntell; i++) { char a[128], b[128]; r_show(r->tell[i][0], a, sizeof a); r_show(r->tell[i][1], b, sizeof b); printf(" tell %s = %s", a, b); }
  for (int i = 0; i < r->nneq; i++) { char a[128], b[128]; r_show(r->neq[i][0], a, sizeof a); r_show(r->neq[i][1], b, sizeof b); printf(" neq %s != %s", a, b); }
  for (int i = 0; i < r->nabsent; i++) show_pat("absent", r->absent[i].t, r->absent[i].space);
  for (int i = 0; i < r->ncount; i++) { show_pat("count", r->count[i].t, r->count[i].space); printf(" = %u", r->count[i].n); }
  for (int m = 0; m < r->nmake; m++) show_pat("make", r->make[m].t, r->make[m].space);
  printf("\n");
}
static void show_step(const Scenario *sc, int i) {
  const DStep *s = &sc->steps[i];
  if (s->kind == ST_FRESH) { printf("    step %d: tc_fresh_name()\n", i); return; }
  if (s->kind == ST_POST) { char b[256]; r_show(s->post_t, b, sizeof b); printf("    step %d: tc_post(%d, %s)\n", i, s->post_space, b); return; }
  const RRule *r = &sc->rules[s->rule];
  printf("    step %d: %s rule %d", i, VNAME[s->variant], s->rule);
  for (int j = 0; j < r->ntake; j++) printf(" take[%d]=fact(%d,%d)", j, s->tk_step[j], s->tk_k[j]);
  for (int j = 0; j < r->nkeep; j++) printf(" keep[%d]=fact(%d,%d)", j, s->kp_step[j], s->kp_k[j]);
  if (s->has_in) for (int h = 0; h < r->nholes; h++) if (s->in[h]) { char b[256]; r_show(s->in[h], b, sizeof b); printf(" ?%d:=%s", h, b); }
  if (!s->has_in && s->in_zero) printf(" (hole array of zeros)");
  if (!r->ntake && s->take_nonnull) printf(" (take array non-NULL)");
  printf("\n");
}
static void show_scenario(const Scenario *sc, const bool *skip_step, const bool *skip_fact, int upto) {
  printf("  scenario seed %llu: wide=%d sealed=%d persistent=%d protected spaces:", (unsigned long long)sc->seed, sc->wide, sc->sealed, sc->persistent);
  for (int s = 0; s < 4; s++) if (sc->prot[s]) printf(" %d", s);
  printf("; %d names minted first\n", sc->premint);
  bool used[8] = { 0 };
  for (int i = 0; i <= upto && i < sc->nsteps; i++) if (!skip_step[i] && sc->steps[i].kind == ST_FIRE) used[sc->steps[i].rule] = true;
  for (int k = 0; k < sc->nrules; k++) if (used[k]) show_rule(k, &sc->rules[k]);
  for (int f = 0; f < sc->nfacts; f++) if (!skip_fact[f]) { char b[256]; r_show(sc->facts[f].t, b, sizeof b); printf("    fact(-1,%d): %s@%d\n", f, b, sc->facts[f].space); }
  for (int i = 0; i <= upto && i < sc->nsteps; i++) if (!skip_step[i]) show_step(sc, i);
}

/* Run a scenario. generate: draw the steps as it goes; otherwise replay the recorded ones. */
static Fail run_scenario(Scenario *sc, bool generate, const bool *skip_step, const bool *skip_fact, int upto) {
  Fail fail = { 0 };
  size_t mark = r_na;
  if (!theory_init(sc->wide)) { fail.kind = F_SETUP; snprintf(fail.note, sizeof fail.note, "theory"); return fail; }
  memset(&st, 0, sizeof st); maxocc = 0;
  for (int i = 0; i < sc->premint; i++) { tc_fresh_name(); st.next_name++; }
  bool has_take = false;
  r_theory_has_query = false;
  for (int k = 0; k < sc->nrules; k++) r_theory_has_query |= sc->rules[k].nabsent || sc->rules[k].ncount;
  for (int k = 0; k < sc->nrules; k++) {
    if (!install_rule(&sc->rules[k], &krule[k])) { fail.kind = F_SETUP; fail.rule = k; snprintf(fail.note, sizeof fail.note, "tc_rule refused rule %d", k); r_na = mark; return fail; }
    has_take |= sc->rules[k].ntake || sc->rules[k].ncount;
  }
  set_mode = sc->sealed && !has_take;
  for (int f = 0; f < sc->nfacts; f++) if (!skip_fact || !skip_fact[f]) {
    Term t = k_of(sc->facts[f].t);
    Occ o = t ? tc_post(sc->facts[f].space, t) : 0;
    if (!o) { fail.kind = F_SETUP; snprintf(fail.note, sizeof fail.note, "initial fact %d refused", f); r_na = mark; return fail; }
    note_occ(o);
    st.f[st.n++] = (RFact){ sc->facts[f].t, sc->facts[f].space, true, -1, f, o };
  }
  for (int s = 0; s < 4; s++) if (sc->prot[s]) tc_protect((uint8_t)s);
  if (sc->sealed) tc_seal();
  if (!stores_agree(fail.note, sizeof fail.note)) { fail.kind = F_STORE; fail.step = -1; r_na = mark; return fail; }
  for (int i = 0; i < sc->nsteps && (upto < 0 || i <= upto); i++) {
    if (generate) {
      DStep *s = &sc->steps[i];
      int x = rint_(100);
      if (x < 86 || st.n == 0) gen_fire_step(sc, s);
      else if (x < 95) { memset(s, 0, sizeof *s); s->kind = ST_POST; s->post_space = rint_(4); s->post_t = gen_ground(chance(0.9) ? S_T : S_D, 2, st.next_name); }
      else { memset(s, 0, sizeof *s); s->kind = ST_FRESH; }
      mark = r_na;                                       /* generated terms belong to the scenario */
    } else if (skip_step && skip_step[i]) continue;
    if (opt_trace) show_step(sc, i);
    if (!exec_step(sc, i, &fail)) { if (!fail.kind) fail.kind = F_SETUP; fail.step = i; break; }
    if (st.n > R_MAXFACTS - 16) { sc->nsteps = i + 1; break; }
  }
  if (!generate) r_na = mark;
  return fail;
}
static void gen_scenario(Scenario *sc, uint64_t seed) {
  memset(sc, 0, sizeof *sc);
  sc->seed = seed; rng_s = seed * 0x9E3779B97F4A7C15ull + 0x1234567ull; for (int i = 0; i < 8; i++) rnd();
  sc->wide = chance(0.4); sc->sealed = chance(0.85); sc->persistent = chance(0.3);
  for (int s = 0; s < 4; s++) sc->prot[s] = chance(0.4);
  sc->premint = 1 + rint_(4);
  r_ncon = sc->wide ? 12 : 11;
  for (int i = 0; i < 12; i++) r_con[i] = THEORY[i];
  sc->nrules = 2 + rint_(5);
  for (int k = 0; k < sc->nrules; k++) gen_rule(&sc->rules[k], !sc->persistent, (uint64_t)sc->premint);
  sc->nfacts = 4 + rint_(14);
  for (int f = 0; f < sc->nfacts; f++) {
    sc->facts[f] = (RPat){ gen_ground(chance(0.95) ? S_T : S_D, 1 + rint_(2), (uint64_t)sc->premint), (uint8_t)rint_(4) };
    const RRule *r = &sc->rules[rint_(sc->nrules)];
    int np = r->ntake + r->nkeep + r->nabsent + r->ncount;
    if (!np || !chance(0.65)) continue;                  /* otherwise: an instance of some rule's premise or guard pattern */
    int p = rint_(np);
    RPat pat = p < r->ntake ? r->take[p] : p < r->ntake + r->nkeep ? r->keep[p - r->ntake]
             : p < r->ntake + r->nkeep + r->nabsent ? r->absent[p - r->ntake - r->nkeep]
             : (RPat){ r->count[p - r->ntake - r->nkeep - r->nabsent].t, r->count[p - r->ntake - r->nkeep - r->nabsent].space };
    const RT *B[R_MAXH];
    for (int h = 0; h < r->nholes; h++) B[h] = gen_ground(r->hsort[h], rint_(2), (uint64_t)sc->premint);
    sc->facts[f] = (RPat){ r_subst(pat.t, B), pat.space };
  }
  sc->nsteps = 40;
}
static bool same_failure(const Fail *a, const Fail *b) {
  return a->kind == b->kind && a->step == b->step && a->kacc == b->kacc && a->racc == b->racc && a->variant == b->variant;
}
static void shrink(Scenario *sc, Fail *fail, bool *skip_step, bool *skip_fact) {
  memset(skip_step, 0, 64); memset(skip_fact, 0, 24);
  for (int pass = 0; pass < 2; pass++) {
    for (int j = fail->step - 1; j >= 0; j--) {
      if (skip_step[j]) continue;
      skip_step[j] = true;
      Fail f2 = run_scenario(sc, false, skip_step, skip_fact, fail->step);
      if (!same_failure(fail, &f2)) skip_step[j] = false; else *fail = f2;
    }
    for (int f = sc->nfacts - 1; f >= 0; f--) {
      if (skip_fact[f]) continue;
      skip_fact[f] = true;
      Fail f2 = run_scenario(sc, false, skip_step, skip_fact, fail->step);
      if (!same_failure(fail, &f2)) skip_fact[f] = false; else *fail = f2;
    }
  }
}
static void feature_string(const Scenario *sc, const Fail *f, char *buf, int cap) {
  if (f->rule < 0 || f->kind == F_SETUP) { snprintf(buf, (size_t)cap, "%s", FNAME[f->kind]); return; }
  const RRule *r = &sc->rules[f->rule];
  uint8_t fib = tc_rule_fibre(krule[f->rule]);
  if (!opt_fine) {
    snprintf(buf, (size_t)cap, "%s via %s kernel=%s reference=%s | rule:%s%s%s | %s",
             FNAME[f->kind], VNAME[f->variant], f->kacc ? "accept" : "refuse", f->racc ? "accept" : "refuse",
             r->nmake > 1 ? " extra-make" : "", (r->ntell || r->nneq) ? " tell/neq" : "",
             (fib & FIBRE_FLAT) ? " [flat]" : (fib & FIBRE_PURE) ? " [pure]" : " [general]", set_mode ? "set-store" : "multiset-store");
    return;
  }
  snprintf(buf, (size_t)cap, "%s via %s kernel=%s reference=%s | rule:%s%s%s%s%s%s%s%s%s | %s",
           FNAME[f->kind], VNAME[f->variant], f->kacc ? "accept" : "refuse", f->racc ? "accept" : "refuse",
           r->ntake ? " take" : "", r->nkeep ? " keep" : "", r->ntell ? " tell" : "", r->nneq ? " neq" : "",
           r->nabsent ? " absent" : "", r->ncount ? " count" : "", r->fresh >= 0 ? " fresh" : "", r->nmake > 1 ? " extra-make" : "",
           (fib & FIBRE_FLAT) ? " [flat]" : (fib & FIBRE_PURE) ? " [pure]" : "", set_mode ? "set-store" : "multiset-store");
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s FIRST_SEED COUNT [--future P] [--no-flatfire] [--flat-only-flat] [--no-dry] [--verbose] [--replay]\n", argv[0]); return 2; }
  uint64_t first = strtoull(argv[1], NULL, 10), count = strtoull(argv[2], NULL, 10);
  bool replay = false;
  for (int i = 3; i < argc; i++) {
    if (!strcmp(argv[i], "--future") && i + 1 < argc) opt_future = atof(argv[++i]);
    else if (!strcmp(argv[i], "--no-flatfire")) opt_noflat = true;
    else if (!strcmp(argv[i], "--flat-only-flat")) opt_flat_only_flat = true;
    else if (!strcmp(argv[i], "--no-open-tells")) opt_no_open_tells = true;
    else if (!strcmp(argv[i], "--fine")) opt_fine = true;
    else if (!strcmp(argv[i], "--no-dry")) opt_nodry = true;
    else if (!strcmp(argv[i], "--verbose")) opt_verbose = true;
    else if (!strcmp(argv[i], "--replay")) replay = true;
    else { fprintf(stderr, "unknown option %s\n", argv[i]); return 2; }
  }
  r_cap = 1u << 22; r_arena = malloc(r_cap * sizeof *r_arena);
  if (!r_arena) return 3;
  static Scenario sc; static char classes[64][400]; static unsigned long class_n[64]; static uint64_t class_seed[64]; int nclass = 0;
  unsigned long nfail = 0, nsetup = 0;
  for (uint64_t seed = first; seed < first + count; seed++) {
    r_na = 0;
    gen_scenario(&sc, seed);
    opt_trace = false;
    Fail fail = run_scenario(&sc, true, NULL, NULL, -1);
    if (replay) {
      bool z1[64] = { 0 }, z2[24] = { 0 };
      show_scenario(&sc, z1, z2, fail.kind ? fail.step : sc.nsteps - 1);
      printf("  result: %s %s\n", FNAME[fail.kind], fail.note);
    }
    if (!fail.kind) continue;
    if (fail.kind == F_SETUP) { nsetup++; if (opt_verbose) printf("setup failure seed %llu: %s\n", (unsigned long long)seed, fail.note); continue; }
    nfail++;
    static bool skip_step[64], skip_fact[24];
    shrink(&sc, &fail, skip_step, skip_fact);
    Fail again = run_scenario(&sc, false, skip_step, skip_fact, fail.step);
    char key[400]; feature_string(&sc, &again, key, sizeof key);
    int c = 0;
    while (c < nclass && strcmp(classes[c], key)) c++;
    if (c == nclass && nclass < 64) { snprintf(classes[nclass], 400, "%s", key); class_seed[nclass] = seed; nclass++; }
    if (c < 64) class_n[c]++;
    if (opt_verbose || class_n[c] == 1) {
      printf("DISAGREEMENT class [%s] seed %llu, step %d: %s\n", key, (unsigned long long)seed, again.step, again.note);
      show_scenario(&sc, skip_step, skip_fact, again.step);
    }
  }
  printf("\nsummary: seeds %llu..%llu; steps %lu; firings compared %lu (kernel and reference both accept %lu, both refuse %lu); outside the fragment %lu\n",
         (unsigned long long)first, (unsigned long long)(first + count - 1), n_steps, n_fire, n_acc, n_ref, n_out);
  for (int v = 0; v < NVARIANT; v++) printf("  entry %-22s %lu firings, %lu accepted\n", VNAME[v], n_variant[v], n_variant_acc[v]);
  printf("  coverage (firings whose rule or candidate has the feature; accepted / refused):");
  for (int c = 0; c < 12; c++) printf(" %s %lu/%lu;", COV[c], cov_acc[c], cov_ref[c]);
  printf("\n  scenarios ended by a disagreement: %lu; setup failures: %lu; receipts with a wrong extra count: %lu\n", nfail, nsetup, n_receipt_soft);
  for (int c = 0; c < nclass; c++) printf("  class %2d: %6lu x [%s] first seed %llu\n", c, class_n[c], classes[c], (unsigned long long)class_seed[c]);
  return nfail ? 1 : 0;
}
