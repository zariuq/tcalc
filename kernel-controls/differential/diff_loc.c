/* Random differential for located premises, dynamic spaces, births and reach: the tcalc kernel
   against a naive reference written from the statements of Rows 3-5 in tcalc.h and the Lean names
   (Births.fresh, Births.single, Births.located, NamedSpacesReach), not from the kernel's code.

   usage: diff_loc FIRST_SEED COUNT [--verbose]

   Reference semantics (one firing):
   - a fact lives in a space; a space is a term of the space sort: static space i is the reserved
     name (2^62 | i), a dynamic space any other name of that sort; a fact is a birth marker or not;
   - takes and keeps: live, not markers, distinct, keeps not taken; a premise names a static space or
     a located space pattern (unified with the fact's space);
   - absent and count: live non-marker facts in the space (located: unified) that unify with the
     instantiated pattern, unbound holes existential; exactly n (absent: 0);
   - every hole value names only minted names (located rules are never schematic); a fresh hole is
     minted; makes must be ground, located makes go to their (ground) space, at_birth makes post markers;
   - birth law: a marker's space is not already born and is marked once per firing; every take, keep
     and make space is born (a live marker) or born by this firing;
   - reach (seeded entries): the reach set is the seeds plus every space-sort subterm of a live
     non-marker fact in a space already in the set, to a fixed point; takes, keeps, query spaces and
     makes must be in it (a make may also go to a space this firing bears).
   The store is compared as a multiset of (space, marker, term) after every step. */
#include "ref.h"
#include "tcalc.h"

static uint64_t rng_s;
static uint64_t rnd(void) { rng_s ^= rng_s >> 12; rng_s ^= rng_s << 25; rng_s ^= rng_s >> 27; return rng_s * 0x2545F4914F6CDD1Dull; }
static int rint_(int n) { return n <= 0 ? 0 : (int)(rnd() % (uint64_t)n); }
static bool chance(double p) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0) < p; }

enum { S_D = 1, S_N = 2, S_T = 3, S_SP = 4 };
#define STATIC_ID(i) ((1ull << 62) | (uint64_t)(i))
static const RCon THEORY[14] = {
  { S_D, 0, { 0 } }, { S_D, 0, { 0 } }, { S_D, 1, { S_D } }, { S_D, 2, { S_D, S_D } }, { S_D, 1, { S_N } },
  { S_T, 1, { S_D } }, { S_T, 2, { S_D, S_D } }, { S_T, 1, { S_D } }, { S_T, 2, { S_N, S_D } }, { S_T, 0, { 0 } },
  { S_T, 4, { S_D, S_D, S_D, S_D } }, { S_T, 5, { S_D, S_D, S_D, S_D, S_D } },
  { S_T, 1, { S_SP } }, { S_T, 2, { S_SP, S_D } },            /* handles: facts that mention spaces */
};
#define NCON 14

/* ---- reference ---- */
typedef struct { const RT *t, *sp; int space; bool mark; } LP;      /* sp: located space pattern, else static `space` */
typedef struct {
  int nholes; uint8_t hsort[R_MAXH]; int fresh; bool birth;
  int ntake, nkeep, nabsent, ncount, nmake;
  LP take[2], keep[3], absent[1], count[1], make[3]; uint32_t cnt[1];
} LRule;
typedef struct { const RT *t, *sp; bool mark, alive; int key_step, key_k; Occ kocc; } LFact;
#define LMAX 400
static struct { LFact f[LMAX]; int n; uint64_t next_name; } st;

static const RT *static_sp(int i) { return r_name(S_SP, STATIC_ID(i)); }
static uint64_t l_max_name(const RT *t) {                   /* reserved ids (2^62 | i) count as minted */
  if (t->kind == RK_NAME) return (t->id >> 62) == 1 ? 0 : t->id + 1;
  uint64_t m = 0;
  for (int i = 0; i < t->n; i++) { uint64_t c = l_max_name(t->a[i]); if (c > m) m = c; }
  return m;
}
static bool born(const RT *sp, const RT *const *newly, int nnew) {
  for (int i = 0; i < st.n; i++) if (st.f[i].alive && st.f[i].mark && r_equal(st.f[i].sp, sp)) return true;
  for (int i = 0; i < nnew; i++) if (r_equal(newly[i], sp)) return true;
  return false;
}
static void collect(const RT *t, const RT **set, int *n) {
  if (t->sort == S_SP) { for (int i = 0; i < *n; i++) if (r_equal(set[i], t)) goto kids; if (*n < 512) set[(*n)++] = t; }
kids:
  for (int i = 0; i < t->n; i++) collect(t->a[i], set, n);
}
static int reach_set(const RT *const *seeds, int nseed, const RT **set) {
  int n = 0;
  for (int i = 0; i < nseed; i++) { bool dup = false; for (int j = 0; j < n; j++) dup |= r_equal(set[j], seeds[i]); if (!dup) set[n++] = seeds[i]; }
  for (bool changed = true; changed;) {
    changed = false;
    for (int f = 0; f < st.n; f++) {
      if (!st.f[f].alive || st.f[f].mark) continue;
      bool in = false; for (int j = 0; j < n; j++) in |= r_equal(set[j], st.f[f].sp);
      if (!in) continue;
      int before = n; collect(st.f[f].t, set, &n); changed |= n != before;
    }
  }
  return n;
}
static bool in_set(const RT *t, const RT *const *set, int n) { for (int i = 0; i < n; i++) if (r_equal(set[i], t)) return true; return false; }
static bool match_space(const LP *p, const RT *sp, const RT **B) {
  return p->sp ? r_unify(p->sp, sp, B) : r_equal(sp, static_sp(p->space));
}
static uint32_t lcount(const LP *p, const RT *const *B, int nh, bool reach, const RT *const *rs, int nrs, bool *refuse) {
  if (reach) {
    const RT *sp = p->sp ? (r_ground(p->sp, B) ? r_subst(p->sp, B) : NULL) : static_sp(p->space);
    if (!sp || !in_set(sp, rs, nrs)) { *refuse = true; return 0; }
  }
  uint32_t hits = 0;
  for (int i = 0; i < st.n; i++) {
    if (!st.f[i].alive || st.f[i].mark) continue;
    const RT *B2[R_MAXH]; for (int h = 0; h < nh; h++) B2[h] = B[h];
    if (match_space(p, st.f[i].sp, B2) && r_unify(p->t, st.f[i].t, B2)) hits++;
  }
  return hits;
}
static bool schematic(const LRule *r) {
  if (r->ntake || r->nabsent || r->ncount || r->fresh >= 0 || r->nmake != 1 || r->birth) return false;
  for (int i = 0; i < r->nkeep; i++) if (r->keep[i].sp) return false;
  return !r->make[0].sp && !r->make[0].mark;
}
static RVerdict l_fire(const LRule *r, const int *take, const int *keep, const RT *const *in,
                       const RT *const *seeds, int nseed, bool reach, bool apply, int step, int *made) {
  const RT *B[R_MAXH];
  const RT *rs[512]; int nrs = reach ? reach_set(seeds, nseed, rs) : 0;
  for (int h = 0; h < r->nholes; h++) {
    B[h] = in ? in[h] : NULL;
    if (B[h] && B[h]->sort != r->hsort[h]) return RV_REFUSE;
  }
  if (r->fresh >= 0 && B[r->fresh]) return RV_REFUSE;
  for (int i = 0; i < r->ntake; i++) {
    if (take[i] < 0 || !st.f[take[i]].alive || st.f[take[i]].mark) return RV_REFUSE;
    for (int j = 0; j < i; j++) if (take[j] == take[i]) return RV_REFUSE;
    if (reach && !in_set(st.f[take[i]].sp, rs, nrs)) return RV_REFUSE;
    if (!match_space(&r->take[i], st.f[take[i]].sp, B) || !r_unify(r->take[i].t, st.f[take[i]].t, B)) return RV_REFUSE;
  }
  for (int i = 0; i < r->nkeep; i++) {
    if (keep[i] < 0 || !st.f[keep[i]].alive || st.f[keep[i]].mark) return RV_REFUSE;
    for (int j = 0; j < r->ntake; j++) if (take[j] == keep[i]) return RV_REFUSE;
    if (reach && !in_set(st.f[keep[i]].sp, rs, nrs)) return RV_REFUSE;
    if (!match_space(&r->keep[i], st.f[keep[i]].sp, B) || !r_unify(r->keep[i].t, st.f[keep[i]].t, B)) return RV_REFUSE;
  }
  bool refuse = false;
  for (int i = 0; i < r->nabsent; i++) if (lcount(&r->absent[i], B, r->nholes, reach, rs, nrs, &refuse) != 0 || refuse) return RV_REFUSE;
  for (int i = 0; i < r->ncount; i++) if (lcount(&r->count[i], B, r->nholes, reach, rs, nrs, &refuse) != r->cnt[i] || refuse) return RV_REFUSE;
  if (!schematic(r))
    for (int h = 0; h < r->nholes; h++) if (B[h] && r_ground(B[h], B) && l_max_name(r_subst(B[h], B)) > st.next_name) return RV_REFUSE;
  uint64_t next = st.next_name;
  if (r->fresh >= 0) B[r->fresh] = r_name(r->hsort[r->fresh], next++);
  const RT *out[3], *osp[3], *newly[3]; int nnew = 0;
  for (int m = 0; m < r->nmake; m++) {
    if (!r_ground(r->make[m].t, B)) return RV_REFUSE;
    out[m] = r_subst(r->make[m].t, B);
    if (r->make[m].sp) { if (!r_ground(r->make[m].sp, B)) return RV_REFUSE; osp[m] = r_subst(r->make[m].sp, B); }
    else osp[m] = static_sp(r->make[m].space);
    if (r->make[m].mark) newly[nnew++] = osp[m];
  }
  if (r->birth) {
    for (int m = 0; m < r->nmake; m++) if (r->make[m].mark) {
      if (born(osp[m], NULL, 0)) return RV_REFUSE;                               /* Births.fresh */
      for (int m2 = m + 1; m2 < r->nmake; m2++) if (r->make[m2].mark && r_equal(osp[m], osp[m2])) return RV_REFUSE;   /* Births.single */
    }
    for (int i = 0; i < r->ntake; i++) if (!born(st.f[take[i]].sp, newly, nnew)) return RV_REFUSE;   /* Births.located */
    for (int i = 0; i < r->nkeep; i++) if (!born(st.f[keep[i]].sp, newly, nnew)) return RV_REFUSE;
    for (int m = 0; m < r->nmake; m++) if (!born(osp[m], newly, nnew)) return RV_REFUSE;
  }
  if (reach) for (int m = 0; m < r->nmake; m++) if (!in_set(osp[m], rs, nrs) && !in_set(osp[m], newly, nnew)) return RV_REFUSE;
  if (!apply) return RV_ACCEPT;
  if (st.n + r->nmake > LMAX) { fprintf(stderr, "reference store full\n"); exit(3); }
  st.next_name = next;
  for (int i = 0; i < r->ntake; i++) st.f[take[i]].alive = false;
  for (int m = 0; m < r->nmake; m++) { made[m] = st.n; st.f[st.n++] = (LFact){ out[m], osp[m], r->make[m].mark, true, step, m, 0 }; }
  return RV_ACCEPT;
}

/* ---- kernel side ---- */
static Term k_of(const RT *t) {
  if (t->kind == RK_NAME) return tc_name(t->sort, t->id);
  if (t->kind == RK_HOLE) return tc_v(t->head);
  Term a[R_MAXAR];
  for (int i = 0; i < t->n; i++) if (!(a[i] = k_of(t->a[i]))) return 0;
  return tc_app(t->head, t->n ? a : NULL);
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
static Term pat_of(const LP *p) {
  Term t = k_of(p->t);
  if (!t || !p->sp) return t;
  Term sp = k_of(p->sp);
  return sp ? (p->mark ? tc_at_birth(sp, t) : tc_at_space(sp, t)) : 0;
}

/* ---- generators ---- */
static int npremint;
static const RT *gen_space(void) { return chance(0.5) ? static_sp(rint_(4)) : r_name(S_SP, (uint64_t)rint_(npremint)); }
static const RT *gen_ground(int sort, int depth) {
  if (sort == S_N) return r_name(S_N, (uint64_t)rint_(npremint));
  if (sort == S_SP) return gen_space();
  const RT *a[R_MAXAR];
  int c = sort == S_D ? (depth <= 0 ? rint_(2) : rint_(5)) : 5 + rint_(NCON - 5);
  for (int i = 0; i < THEORY[c].arity; i++) a[i] = gen_ground(THEORY[c].asort[i], depth - 1);
  return r_app(c, a);
}
static int pick_hole(const LRule *r, int sort, uint32_t allowed) {
  int c[R_MAXH], n = 0;
  for (int h = 0; h < r->nholes; h++) if (r->hsort[h] == sort && (allowed >> h & 1)) c[n++] = h;
  return n ? c[rint_(n)] : -1;
}
static const RT *gen_pat(int sort, int depth, const LRule *r, uint32_t allowed) {
  int h = pick_hole(r, sort, allowed);
  if (h >= 0 && chance(depth <= 0 ? 0.75 : 0.45)) return r_hole(h, sort);
  if (sort == S_N) return r_name(S_N, (uint64_t)rint_(npremint));
  if (sort == S_SP) return gen_space();
  const RT *a[R_MAXAR];
  int c = sort == S_D ? (depth <= 0 ? rint_(2) : rint_(5)) : 5 + rint_(NCON - 5);
  for (int i = 0; i < THEORY[c].arity; i++) a[i] = gen_pat(THEORY[c].asort[i], depth - 1, r, allowed);
  return r_app(c, a);
}
static uint32_t holes_of(const RT *t) {
  if (t->kind == RK_HOLE) return 1u << t->head;
  uint32_t m = 0; for (int i = 0; i < t->n; i++) m |= holes_of(t->a[i]); return m;
}
/* The holes of a (located) pattern. */
static uint64_t lp_holes(const LP *p) { return holes_of(p->t) | (p->sp ? holes_of(p->sp) : 0u); }
static void gen_lp(LP *p, const LRule *r, uint32_t allowed, int home, double located) {
  p->t = gen_pat(S_T, 1 + rint_(2), r, allowed);
  p->mark = false; p->space = chance(0.7) ? home : rint_(4);
  p->sp = NULL;
  if (chance(located)) { int h = pick_hole(r, S_SP, allowed); p->sp = h >= 0 && chance(0.7) ? r_hole(h, S_SP) : gen_space(); }
}
static void gen_rule(LRule *r, bool allow_take) {
  memset(r, 0, sizeof *r);
  r->nholes = 1 + rint_(5);
  for (int h = 0; h < r->nholes; h++) { int x = rint_(100); r->hsort[h] = x < 45 ? S_D : x < 80 ? S_SP : x < 90 ? S_N : S_T; }
  r->fresh = -1;
  if (chance(0.3)) { int c[R_MAXH], n = 0; for (int h = 0; h < r->nholes; h++) if (r->hsort[h] != S_T) c[n++] = h; if (n) r->fresh = c[rint_(n)]; }
  uint32_t all = (1u << r->nholes) - 1, nf = r->fresh >= 0 ? all & ~(1u << r->fresh) : all;
  int home = rint_(4);
  r->ntake = allow_take ? rint_(3) : 0; r->nkeep = rint_(3);
  r->nabsent = chance(0.3); r->ncount = allow_take && chance(0.25);
  r->nmake = 1 + rint_(3);
  r->birth = chance(0.35);
  uint32_t seen = 0;
  for (int i = 0; i < r->ntake; i++) { gen_lp(&r->take[i], r, nf, home, 0.5); seen |= holes_of(r->take[i].t) | (r->take[i].sp ? holes_of(r->take[i].sp) : 0); }
  for (int i = 0; i < r->nkeep; i++) { gen_lp(&r->keep[i], r, nf, home, 0.5); seen |= holes_of(r->keep[i].t) | (r->keep[i].sp ? holes_of(r->keep[i].sp) : 0); }
  for (int i = 0; i < r->nabsent; i++) gen_lp(&r->absent[i], r, nf, home, 0.4);
  for (int i = 0; i < r->ncount; i++) { gen_lp(&r->count[i], r, nf, home, 0.4); r->cnt[i] = (uint32_t)rint_(3); }
  uint32_t mk = chance(0.85) ? (seen | (all & ~nf)) : all;
  for (int m = 0; m < r->nmake; m++) gen_lp(&r->make[m], r, mk, home, 0.6);
  if (r->birth || chance(0.15)) {                          /* a marker make: bear a space */
    int m = rint_(r->nmake);
    r->make[m].mark = true;
    if (!r->make[m].sp) r->make[m].sp = r->fresh >= 0 && r->hsort[r->fresh] == S_SP && chance(0.7) ? r_hole(r->fresh, S_SP) : gen_space();
  }
  if (r->fresh >= 0 && r->hsort[r->fresh] == S_SP && chance(0.6)) {   /* put another make into the new space */
    int m = rint_(r->nmake);
    if (!r->make[m].mark) r->make[m].sp = r_hole(r->fresh, S_SP);
  }
}

/* ---- scenario ---- */
enum { V_FIRE, V_COMMIT, V_EVAL, V_DRY, V_REACH, V_COMMIT_REACH, V_EVAL_REACH, NV };
static const char *VN[NV] = { "tc_fire", "tc_commit_prepared", "tc_eval_prepared_ex", "dry-run+tc_fire", "tc_fire_reach", "tc_commit_prepared+seeds", "tc_eval_prepared_ex+reach" };
static unsigned long n_cmp, n_acc, n_out_setup, n_scen_fail, n_steps, nv[NV], nva[NV], n_birth_acc, n_loc_acc, n_reach_acc;
static LRule rules[6]; static int krule[6], nrules; static Occ maxocc;
static bool verbose;

static bool stores_agree(char *note, int cap) {
  static char ks[1024][200], rs_[1024][200];
  int nk = 0, nr_ = 0;
  for (Occ o = 1; o <= maxocc + 64 && nk < 1024; o++) if (tc_alive(o)) {
    int n = 0; n += k_show(tc_occ_space(o), ks[nk] + n, 200 - n);
    n += snprintf(ks[nk] + n, (size_t)(200 - n), "%s:", tc_occ_marker(o) ? "!" : "");
    k_show(tc_term(o), ks[nk] + n, 200 - n); nk++;
  }
  for (int i = 0; i < st.n && nr_ < 1024; i++) if (st.f[i].alive) {
    int n = 0; n += r_show(st.f[i].sp, rs_[nr_] + n, 200 - n);
    n += snprintf(rs_[nr_] + n, (size_t)(200 - n), "%s:", st.f[i].mark ? "!" : "");
    r_show(st.f[i].t, rs_[nr_] + n, 200 - n); nr_++;
  }
  qsort(ks, (size_t)nk, 200, (int (*)(const void *, const void *))strcmp);
  qsort(rs_, (size_t)nr_, 200, (int (*)(const void *, const void *))strcmp);
  for (int i = 0, j = 0; i < nk || j < nr_;) {
    int c = i == nk ? 1 : j == nr_ ? -1 : strcmp(ks[i], rs_[j]);
    if (!c) { i++; j++; continue; }
    snprintf(note, (size_t)cap, c < 0 ? "kernel has %s, reference does not" : "reference has %s, kernel does not", c < 0 ? ks[i] : rs_[j]);
    return false;
  }
  return true;
}
static void show_lp(const char *what, const LP *p) {
  char a[200], b[200] = "";
  r_show(p->t, a, sizeof a); if (p->sp) r_show(p->sp, b, sizeof b);
  printf(" %s%s %s@%s", what, p->mark ? "(birth)" : "", a, p->sp ? b : (snprintf(b, sizeof b, "s%d", p->space), b));
}
static void show_rule(int k) {
  const LRule *r = &rules[k];
  printf("    rule %d: holes", k);
  for (int h = 0; h < r->nholes; h++) printf(" ?%d:%s", h, r->hsort[h] == S_D ? "D" : r->hsort[h] == S_N ? "N" : r->hsort[h] == S_SP ? "SP" : "T");
  if (r->fresh >= 0) printf(" fresh ?%d", r->fresh);
  if (r->birth) printf(" birth-law");
  printf(" |");
  for (int i = 0; i < r->ntake; i++) show_lp("take", &r->take[i]);
  for (int i = 0; i < r->nkeep; i++) show_lp("keep", &r->keep[i]);
  for (int i = 0; i < r->nabsent; i++) show_lp("absent", &r->absent[i]);
  for (int i = 0; i < r->ncount; i++) { show_lp("count", &r->count[i]); printf("=%u", r->cnt[i]); }
  for (int m = 0; m < r->nmake; m++) show_lp("make", &r->make[m]);
  printf("\n");
}

static bool run(uint64_t seed) {
  rng_s = seed * 0x9E3779B97F4A7C15ull + 0x5151ull; for (int i = 0; i < 8; i++) rnd();
  r_na = 0; memset(&st, 0, sizeof st); maxocc = 0;
  if (!tc_init(1u << 13, 1u << 9)) return false;
  int d = tc_sort(0), n = tc_sort(0), t = tc_sort(SORT_PROVABLE);
  if (d != S_D || n != S_N || t != S_T || tc_space_sort() != S_SP) { n_out_setup++; return true; }
  r_ncon = NCON;
  for (int i = 0; i < NCON; i++) {
    r_con[i] = THEORY[i];
    Binder b[R_MAXAR];
    for (int j = 0; j < THEORY[i].arity; j++) b[j] = (Binder){ THEORY[i].asort[j], 0, 0 };
    if (tc_con(THEORY[i].sort, 0, THEORY[i].arity, b) != i) { n_out_setup++; return true; }
  }
  npremint = 4 + rint_(3);
  for (int i = 0; i < npremint; i++) (void)tc_fresh_name();
  st.next_name = (uint64_t)npremint;
  bool persistent = chance(0.3), sealed = chance(0.85), prot[4];
  for (int s = 0; s < 4; s++) prot[s] = chance(0.4);
  nrules = 2 + rint_(4);
  for (int k = 0; k < nrules; k++) {
    gen_rule(&rules[k], !persistent);
    Binder b[R_MAXH];
    for (int h = 0; h < rules[k].nholes; h++) b[h] = (Binder){ rules[k].hsort[h], 0, 0 };
    if (!tc_ctx(rules[k].nholes, b)) { n_out_setup++; return true; }
    Rule kr; memset(&kr, 0, sizeof kr);
    const LRule *r = &rules[k];
    kr.ntake = (uint8_t)r->ntake; kr.nkeep = (uint8_t)r->nkeep; kr.nabsent = (uint8_t)r->nabsent; kr.ncount = (uint8_t)r->ncount;
    kr.nmake_extra = (uint8_t)(r->nmake - 1); kr.fresh = (int8_t)r->fresh; kr.birth_law = r->birth;
    for (int i = 0; i < r->ntake; i++) kr.take[i] = (Pat){ pat_of(&r->take[i]), (uint8_t)r->take[i].space };
    for (int i = 0; i < r->nkeep; i++) kr.keep[i] = (Pat){ pat_of(&r->keep[i]), (uint8_t)r->keep[i].space };
    for (int i = 0; i < r->nabsent; i++) kr.absent[i] = (Pat){ pat_of(&r->absent[i]), (uint8_t)r->absent[i].space };
    for (int i = 0; i < r->ncount; i++) kr.count[i] = (Count){ pat_of(&r->count[i]), (uint8_t)r->count[i].space, r->cnt[i] };
    kr.make = (Pat){ pat_of(&r->make[0]), (uint8_t)r->make[0].space };
    for (int m = 1; m < r->nmake; m++) kr.make_extra[m - 1] = (Pat){ pat_of(&r->make[m]), (uint8_t)r->make[m].space };
    uint64_t bound = r->fresh >= 0 ? 1ull << r->fresh : 0, made = 0;   /* the caller supplies the other made holes */
    for (int i = 0; i < r->ntake; i++) bound |= lp_holes(&r->take[i]);
    for (int i = 0; i < r->nkeep; i++) bound |= lp_holes(&r->keep[i]);
    for (int m = 0; m < r->nmake; m++) made |= lp_holes(&r->make[m]);
    kr.inputs = made & ~bound;
    if ((krule[k] = tc_rule(&kr)) < 0) { n_out_setup++; return true; }   /* e.g. the fresh hole in a premise */
  }
  /* initial facts: static and dynamic spaces, some birth markers; one dynamic fact always */
  int nf = 4 + rint_(14);
  for (int f = 0; f <= nf; f++) {
    const RT *tt = gen_ground(chance(0.9) ? S_T : S_D, 1 + rint_(2));
    if (f < nf && chance(0.5)) {                           /* an instance of a premise or query pattern */
      const LRule *r = &rules[rint_(nrules)];
      int np = r->ntake + r->nkeep + r->nabsent + r->ncount;
      if (np) {
        int p = rint_(np);
        const LP *lp = p < r->ntake ? &r->take[p] : p < r->ntake + r->nkeep ? &r->keep[p - r->ntake]
                     : p < r->ntake + r->nkeep + r->nabsent ? &r->absent[p - r->ntake - r->nkeep] : &r->count[0];
        const RT *B[R_MAXH]; for (int h = 0; h < r->nholes; h++) B[h] = gen_ground(r->hsort[h], rint_(2));
        tt = r_subst(lp->t, B);
      }
    }
    const RT *sp = f == nf ? r_name(S_SP, 0) : gen_space();
    bool mark = f < nf && sp->id < STATIC_ID(0) && chance(0.25);
    Term kt = k_of(tt), ks = k_of(sp);
    Occ o = kt && ks ? tc_post_at(ks, kt, mark) : 0;
    if (!o) { n_out_setup++; return true; }
    if (o > maxocc) maxocc = o;
    st.f[st.n++] = (LFact){ tt, sp, mark, true, -1, f, o };
  }
  for (int s = 0; s < 4; s++) if (prot[s]) tc_protect((uint8_t)s);
  if (sealed) tc_seal();
  char note[300];
  if (!stores_agree(note, sizeof note)) { printf("seed %llu: initial store differs: %s\n", (unsigned long long)seed, note); n_scen_fail++; return true; }
  for (int step = 0; step < 40; step++) {
    n_steps++;
    if (st.n > LMAX - 8) break;
    if (chance(0.1)) {                                     /* a post after the seal: static or dynamic */
      const RT *tt = gen_ground(S_T, 2), *sp = gen_space();
      bool mark = sp->id < STATIC_ID(0) && chance(0.2);
      bool stat = sp->id >= STATIC_ID(0);
      bool expect = !(sealed && stat && prot[sp->id & 3]) && !(sealed && mark) && l_max_name(tt) <= st.next_name;
      Occ o = tc_post_at(k_of(sp), k_of(tt), mark);
      if ((o != 0) != expect) { printf("seed %llu step %d: tc_post_at kernel %s, reference %s (space %s%llu, marker %d, sealed %d)\n", (unsigned long long)seed, step, o ? "accepts" : "refuses", expect ? "accepts" : "refuses", stat ? "static " : "dynamic ", (unsigned long long)(sp->id & 0xFF), mark, sealed); n_scen_fail++; return true; }
      if (o) { if (o > maxocc) maxocc = o; st.f[st.n++] = (LFact){ tt, sp, mark, true, step, 0, o }; }
      continue;
    }
    int k = rint_(nrules); const LRule *r = &rules[k];
    int ti[2] = { -1, -1 }, ki[3] = { -1, -1, -1 };
    for (int i = 0; i < r->ntake + r->nkeep; i++) {      /* guided: a fact whose term unifies, often */
      int cand[LMAX], nc = 0;
      const LP *p = i < r->ntake ? &r->take[i] : &r->keep[i - r->ntake];
      for (int f = 0; f < st.n; f++) if (st.f[f].alive && !st.f[f].mark) {
        const RT *B2[R_MAXH] = { 0 };
        if (r_unify(p->t, st.f[f].t, B2)) cand[nc++] = f;
      }
      int f = nc && chance(0.9) ? cand[rint_(nc)] : st.n ? rint_(st.n) : -1;
      if (i < r->ntake) ti[i] = f; else ki[i - r->ntake] = f;
    }
    const RT *in[R_MAXH] = { 0 }; bool has_in = chance(0.5);
    if (has_in) for (int h = 0; h < r->nholes; h++) if (h != r->fresh && chance(0.3)) in[h] = gen_ground(r->hsort[h], 1);
    const RT *seeds[4]; int nseed = 1 + rint_(3);
    for (int i = 0; i < nseed; i++) seeds[i] = gen_space();
    int v = rint_(NV);
    bool reach = v >= V_REACH;
    RVerdict rv = l_fire(r, ti, ki, has_in ? in : NULL, seeds, nseed, reach, false, step, NULL);
    Occ tk[2], kk[3]; Term kin[R_MAXH] = { 0 }, kseeds[4];
    for (int i = 0; i < r->ntake; i++) tk[i] = ti[i] >= 0 ? st.f[ti[i]].kocc : 0;
    for (int i = 0; i < r->nkeep; i++) kk[i] = ki[i] >= 0 ? st.f[ki[i]].kocc : 0;
    for (int h = 0; h < r->nholes; h++) if (in[h]) kin[h] = k_of(in[h]);
    for (int i = 0; i < nseed; i++) kseeds[i] = k_of(seeds[i]);
    TcPreparedStep ps = { .rule = krule[k], .take = r->ntake ? tk : NULL, .keep = r->nkeep ? kk : NULL, .inst = has_in ? kin : NULL,
                          .dest = 0, .nseeds = reach ? nseed : 0, .seeds = reach ? kseeds : NULL };
    Occ o = 0; bool kacc = false; TcAdmissionReceipt rc;
    uint64_t name_before = tc_next_name();
    switch (v) {
      case V_FIRE: o = tc_fire(krule[k], ps.take, ps.keep, ps.inst); kacc = o != 0; break;
      case V_COMMIT: case V_COMMIT_REACH: kacc = tc_commit_prepared(&ps, &rc); o = kacc ? rc.out : 0; break;
      case V_EVAL: case V_EVAL_REACH: { Term mt[5], ms[5]; uint8_t mm[5], nm; kacc = tc_eval_prepared_ex(&ps, true, true, true, reach, true, mt, ms, mm, &nm, &o) == TC_PREP_OK && o; break; }
      case V_DRY: {
        Term mt[5], ms[5]; uint8_t mm[5], nm; Occ oo = 0;
        bool dacc = tc_eval_prepared_ex(&ps, true, true, true, false, false, mt, ms, mm, &nm, &oo) == TC_PREP_OK;
        if (dacc != (rv == RV_ACCEPT) || tc_next_name() != name_before || !stores_agree(note, sizeof note)) {
          printf("DISAGREEMENT seed %llu step %d via dry run: kernel %s, reference %s\n", (unsigned long long)seed, step, dacc ? "accepts" : "refuses", rv == RV_ACCEPT ? "accepts" : "refuses");
          for (int q = 0; q < nrules; q++) show_rule(q);
          n_scen_fail++; return true;
        }
        o = tc_fire(krule[k], ps.take, ps.keep, ps.inst); kacc = o != 0; break;
      }
      case V_REACH: o = tc_fire_reach(krule[k], ps.take, ps.keep, ps.inst, kseeds, nseed); kacc = o != 0; break;
    }
    n_cmp++; nv[v]++;
    if (kacc != (rv == RV_ACCEPT)) {
      printf("DISAGREEMENT seed %llu step %d via %s: kernel %s, reference %s (rule %d)\n", (unsigned long long)seed, step, VN[v], kacc ? "accepts" : "refuses", rv == RV_ACCEPT ? "accepts" : "refuses", k);
      if (verbose || n_scen_fail < 6) {
        show_rule(k);
        for (int i = 0; i < r->ntake; i++) if (ti[i] >= 0) { char a[200], b[200]; r_show(st.f[ti[i]].t, a, 200); r_show(st.f[ti[i]].sp, b, 200); printf("      take[%d] = %s@%s%s\n", i, a, b, st.f[ti[i]].mark ? " (marker)" : ""); }
        for (int i = 0; i < r->nkeep; i++) if (ki[i] >= 0) { char a[200], b[200]; r_show(st.f[ki[i]].t, a, 200); r_show(st.f[ki[i]].sp, b, 200); printf("      keep[%d] = %s@%s%s\n", i, a, b, st.f[ki[i]].mark ? " (marker)" : ""); }
        for (int h = 0; h < r->nholes; h++) if (in[h]) { char a[200]; r_show(in[h], a, 200); printf("      ?%d := %s\n", h, a); }
        if (reach) for (int i = 0; i < nseed; i++) { char a[200]; r_show(seeds[i], a, 200); printf("      seed %s\n", a); }
      }
      n_scen_fail++; return true;
    }
    if (kacc) {
      int made[3];
      l_fire(r, ti, ki, has_in ? in : NULL, seeds, nseed, reach, true, step, made);
      n_acc++; nva[v]++;
      if (r->birth) n_birth_acc++;
      bool loc = false; for (int m = 0; m < r->nmake; m++) loc |= r->make[m].sp != NULL; for (int i = 0; i < r->nkeep; i++) loc |= r->keep[i].sp != NULL;
      if (loc) n_loc_acc++;
      if (reach) n_reach_acc++;
      st.f[made[0]].kocc = o; if (o > maxocc) maxocc = o;
      for (int m = 1; m < r->nmake; m++) { Occ e = tc_last_extra(m - 1); st.f[made[m]].kocc = e; if (e > maxocc) maxocc = e; }
    }
    if (!stores_agree(note, sizeof note) || tc_next_name() != st.next_name) {
      printf("DISAGREEMENT seed %llu step %d via %s (store or names): %s\n", (unsigned long long)seed, step, VN[v], note);
      show_rule(k);
      n_scen_fail++; return true;
    }
  }
  return true;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s FIRST_SEED COUNT [--verbose]\n", argv[0]); return 2; }
  uint64_t first = strtoull(argv[1], NULL, 10), count = strtoull(argv[2], NULL, 10);
  verbose = argc > 3 && !strcmp(argv[3], "--verbose");
  r_cap = 1u << 22; r_arena = malloc(r_cap * sizeof *r_arena);
  if (!r_arena) return 3;
  for (uint64_t s = first; s < first + count; s++) if (!run(s)) { printf("tc_init failed\n"); return 3; }
  printf("summary: seeds %llu..%llu; steps %lu; firings compared %lu, accepted %lu (birth-law %lu, located %lu, reach %lu); scenarios set up outside the generator's reach %lu; scenarios ended by a disagreement %lu\n",
         (unsigned long long)first, (unsigned long long)(first + count - 1), n_steps, n_cmp, n_acc, n_birth_acc, n_loc_acc, n_reach_acc, n_out_setup, n_scen_fail);
  for (int v = 0; v < NV; v++) printf("  entry %-28s %lu firings, %lu accepted\n", VN[v], nv[v], nva[v]);
  return n_scen_fail ? 1 : 0;
}
